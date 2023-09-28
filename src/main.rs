//! `cron-wrapper` executable.

// Lint configuration in Cargo.toml isn’t supported by cargo-geiger.
#![forbid(unsafe_code)]

use anyhow::{bail, Context};
use bstr::ByteSlice;
use clap::Parser;
use cron_wrapper::command::{Command, Event};
use cron_wrapper::job_logger::{Destination, JobLogger};
use cron_wrapper::pause_writer::PausableWriter;
use log::{debug, error, info};
use simplelog::{
    ColorChoice, CombinedLogger, Config, ConfigBuilder, LevelFilter,
    TermLogger, TerminalMode,
};
use std::cell::RefCell;
use std::fs;
use std::io::Write;
use std::process;
use std::rc::Rc;
use termcolor::{Color, ColorSpec, WriteColor};

mod params;
use params::{Action, Params, RunParams};

/// Wrapper to handle errors.
///
/// See [`cli()`].
fn main() -> ! {
    process::exit(cli(&Params::parse()).unwrap_or_else(|error| {
        eprintln!("Error: {error:#}");
        1
    }))
}

/// Initialize logging and hand off to the action handler.
///
/// # Errors
///
/// This returns all errors to [`main()`] to be outputted nicely.
fn cli(params: &Params) -> anyhow::Result<i32> {
    init_logging(params)?;

    match &params.action {
        Action::Run(run_params) => action_run(params, run_params),
    }
}

/// Handle the `run` action.
///
/// This is mostly a wrapper around [`start()`].
///
/// # Errors
///
/// This tries to log errors encountered after logging is started, and returns
/// all errors to [`main()`] to be outputted nicely.
fn action_run(global: &Params, params: &RunParams) -> anyhow::Result<i32> {
    let mut job_logger = init_job_logger(params)?;
    start(global, params, &mut job_logger).map_err(|error| {
        if let Err(error2) = job_logger.log_wrapper_error(&error) {
            error!(
                "Encountered error2 while logging another error. \
                Error2: {error2:?}"
            );
        }
        error
    })
}

/// Start the child process.
fn start(
    global: &Params,
    params: &RunParams,
    job_logger: &mut JobLogger,
) -> anyhow::Result<i32> {
    let command = Command {
        command: params.command.clone().into(),
        args: params.args.clone(),
        run_timeout: params.run_timeout.into(),
        idle_timeout: params.idle_timeout.into(),
        buffer_size: params.buffer_size,
    };
    job_logger.set_command(&command);

    let mut child = command.spawn()?;
    job_logger.set_child(&child);

    let out =
        Rc::new(RefCell::new(PausableWriter::stdout(global.color_choice())));
    out.borrow_mut().set_paused(params.start_paused())?;

    if params.log_stdout {
        job_logger.add_destination(Destination::ColorStream(out.clone()));
    }

    let mut err_color = ColorSpec::new();
    err_color.set_fg(Some(Color::Red));
    err_color.set_intense(true);

    while let Some(event) = child.next_event() {
        job_logger.log_event(&event)?;
        match event {
            Event::Stdout(output) => {
                if !output.is_empty() && params.normal_output_enabled() {
                    let mut out = out.borrow_mut();
                    out.write_all(output)?;
                    out.flush()?; // In case there wasn’t a newline.
                }
            }
            Event::Stderr(output) => {
                if params.on_error && out.borrow().is_paused() {
                    debug!("--on-error enabled: unpausing output");
                    out.borrow_mut().unpause()?;
                }

                if !output.is_empty() && params.normal_output_enabled() {
                    let mut out = out.borrow_mut();
                    out.set_color(&err_color)?;
                    out.write_all(output)?;
                    out.reset()?;
                    out.flush()?; // In case there wasn’t a newline.
                }
            }
            Event::Exit(_) => {
                let code = event.exit_code().expect("no exit code for child");

                if code != 0 && params.on_fail && out.borrow().is_paused() {
                    debug!("--on-fail enabled: unpausing output");
                    out.borrow_mut().unpause()?;
                }

                if params.show_exit_code || (params.show_fail_code && code != 0)
                {
                    println!("Exited with code {code}");
                }

                info!(
                    "Exit with {code}: {}",
                    command.command_line_sh().as_bstr()
                );
                return Ok(code);
            }
            Event::Error(error) => {
                // Don’t return this error since that will cause it to be logged
                // again as a “wrapper” error.
                if params.normal_output_enabled() {
                    eprintln!("Error: {error:#}");
                } else if !params.log_stdout {
                    // If log_stdout were enabled it would have already printed
                    // the error to stdout.
                    error!("{error:#}");
                }

                if params.error_signal.is_some() {
                    info!("Sending signal {} to child", params.error_signal);
                    child.kill(params.error_signal)?;
                } else {
                    info!("Skipping sending signal to child");
                }

                return Ok(1);
            }
        }
    }

    unreachable!("should have exited when child did");
}

/// Initialize logging for cron-wrapper itself. This does not deal with logs
/// from child processes; see [`init_job_logger()`].
fn init_logging(params: &Params) -> anyhow::Result<()> {
    let filter = match params.verbose {
        4.. => bail!("-v is only allowed up to 3 times."),
        3 => LevelFilter::Trace,
        2 => LevelFilter::Debug,
        1 => LevelFilter::Info,
        0 => LevelFilter::Warn,
    };

    // Configure different logging for a module (sqlx::query here).
    CombinedLogger::init(vec![
        // Default logger
        new_term_logger(filter, new_logger_config().build()),
    ])
    .unwrap();

    Ok(())
}

/// Convenience function to make creating [`TermLogger`]s clearer.
#[allow(clippy::unnecessary_box_returns)] // Using `Box` isn’t our decision.
fn new_term_logger(level: LevelFilter, config: Config) -> Box<TermLogger> {
    TermLogger::new(level, config, TerminalMode::Mixed, ColorChoice::Auto)
}

/// Convenience function to make creating [`ConfigBuilder`]s clearer.
fn new_logger_config() -> ConfigBuilder {
    let mut builder = ConfigBuilder::new();
    builder.set_target_level(LevelFilter::Error);

    if builder.set_time_offset_to_local().is_err() {
        // We haven’t finished setting up logging, so just print to stderr.
        eprintln!(
            "Warning: could not get local timezone so logging timestamps will \
            be in UTC."
        );
    }

    builder
}

/// Create the [`JobLogger`] based on [`Params`].
///
/// This is _not_ responsible for creating the stdout [`Destination`] if
/// `params.log_stdout` is `true`.
fn init_job_logger(params: &RunParams) -> anyhow::Result<JobLogger> {
    if let Some(path) = &params.log_file {
        if path.as_os_str().is_empty() {
            // Clap actually prevents this, but let’s be sure.
            bail!("A path must be passed to --log-file");
        } else if path.is_dir() {
            bail!(
                "Expected {path:?} to be a file, but it is a directory \
                (specified with --log-file)"
            );
        }

        if let Some(parent) = path.parent() {
            // I think we’ve covered the cases where path.parent() could return
            // None, but if not, it will be caught when we try to create the
            // log file.
            if !parent.exists() {
                fs::create_dir_all(parent).context(format!(
                    "Creating log file directory {parent:?}"
                ))?;
            }
        }

        Ok(JobLogger::new_file(path)?)
    } else if let Some(path) = &params.log_dir {
        if !path.exists() {
            fs::create_dir_all(path)
                .context(format!("Creating log directory {path:?}"))?;
        } else if !path.is_dir() {
            bail!("{path:?} is not a directory (specified with --log-dir)");
        }

        Ok(JobLogger::new_in_directory(path))
    } else {
        Ok(JobLogger::none())
    }
}

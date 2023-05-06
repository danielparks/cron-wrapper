#![forbid(unsafe_code)]

use anyhow::bail;
use clap::Parser;
use cron_wrapper::{command, pause_writer::PausableWriter};
use log::Level::Trace;
use log::{debug, info, log_enabled};
use simplelog::{
    ColorChoice, CombinedLogger, Config, ConfigBuilder, LevelFilter,
    TermLogger, TerminalMode,
};
use std::io::{self, Write};
use std::os::unix::process::ExitStatusExt;
use std::process;

mod params;
use params::Params;

fn main() {
    if let Err(error) = cli(Params::parse()) {
        eprintln!("Error: {:#}", error);
        process::exit(1);
    }
}

fn cli(params: Params) -> anyhow::Result<()> {
    init_logging(&params)?;

    let mut out = PausableWriter::new(io::stdout());
    if params.suppress_output() {
        out.pause();
    } else {
        out.unpause()?;
    }

    let mut child = command::Command {
        command: params.command.clone(),
        args: params.args.clone(),
        run_timeout: params.run_timeout.into(),
        idle_timeout: params.idle_timeout.into(),
        buffer_size: params.buffer_size,
    }
    .start()?;

    while let Some(event) = child.next_event() {
        match event {
            command::Event::Stdout(output) => {
                if !output.is_empty() && !log_enabled!(Trace) {
                    out.write_all(output)?;
                    out.flush()?; // In case there wasn’t a newline.
                }
            }
            command::Event::Stderr(output) => {
                if !output.is_empty() && !log_enabled!(Trace) {
                    if params.on_error && out.is_paused() {
                        debug!("--on-error enabled: unpausing output");
                        out.unpause()?;
                    }

                    out.write_all(output)?;
                    out.flush()?; // In case there wasn’t a newline.
                }
            }
            command::Event::Exit(status) => {
                let code = wait_status_to_code(status)
                    .expect("no exit code for child");
                info!(
                    "Exit with {code}: {:?} {:?}",
                    params.command, params.args
                );

                if code != 0 && params.on_fail && out.is_paused() {
                    debug!("--on-fail enabled: unpausing output");
                    out.unpause()?;
                }

                process::exit(code);
            }
            command::Event::Error(error) => {
                return Err(error.into());
            }
        }
    }

    unreachable!("should have exited when child did");
}

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

fn new_term_logger(level: LevelFilter, config: Config) -> Box<TermLogger> {
    TermLogger::new(level, config, TerminalMode::Mixed, ColorChoice::Auto)
}

fn new_logger_config() -> ConfigBuilder {
    let mut builder = ConfigBuilder::new();
    builder.set_target_level(LevelFilter::Error);

    // FIXME: If this fails it will just print the time in UTC. That might be a
    // little surprising, so this should probably warn the user... except that
    // we haven’t finished setting up logging.
    let _ = builder.set_time_offset_to_local();

    builder
}

/// Get the actual exit code from a finished child process
fn wait_status_to_code(status: process::ExitStatus) -> Option<i32> {
    status.code().or_else(|| Some(128 + status.signal()?))
}

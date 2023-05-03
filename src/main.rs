#![forbid(unsafe_code)]

use anyhow::bail;
use clap::Parser;
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

mod pause_writer;
use pause_writer::PausableWriter;

mod command;
mod timeout;

fn main() {
    if let Err(error) = cli(Params::parse()) {
        eprintln!("Error: {:#}", error);
        process::exit(1);
    }
}

struct Handler {
    pub out: PausableWriter<std::io::Stdout>,
    pub params: Params,
}

impl command::Handler for Handler {
    fn on_out(&mut self, output: &[u8]) -> anyhow::Result<()> {
        if output.is_empty() {
            return Ok(());
        }

        if !log_enabled!(Trace) {
            self.out.write_all(output)?;
            self.out.flush()?; // In case there wasn’t a newline.
        }

        Ok(())
    }

    fn on_err(&mut self, output: &[u8]) -> anyhow::Result<()> {
        if output.is_empty() {
            return Ok(());
        }

        if self.params.on_error && self.out.is_paused() {
            debug!("--on-error enabled: unpausing output");
            self.out.unpause()?;
        }

        if !log_enabled!(Trace) {
            self.out.write_all(output)?;
            self.out.flush()?; // In case there wasn’t a newline.
        }

        Ok(())
    }

    fn on_exit(&mut self, status: process::ExitStatus) -> anyhow::Result<()> {
        let code = wait_status_to_code(status).expect("no exit code for child");
        info!(
            "Exit with {code}: {:?} {:?}",
            self.params.command, self.params.args
        );

        if code != 0 && self.params.on_fail && self.out.is_paused() {
            debug!("--on-fail enabled: unpausing output");
            self.out.unpause()?;
        }

        process::exit(code);
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

    let child = command::Command {
        command: params.command.clone(),
        args: params.args.clone(),
        run_timeout: params.run_timeout.into(),
        idle_timeout: params.idle_timeout.into(),
        buffer_size: params.buffer_size,
    };
    let handler = Handler { out, params };
    child.run(handler)?;

    panic!("how did I get here?");
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

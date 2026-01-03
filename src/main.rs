//! `cron-wrapper` executable.

// Lint configuration in Cargo.toml isn’t supported by cargo-geiger.
#![forbid(unsafe_code)]

use anyhow::bail;
use clap::Parser;
use simplelog::{
    ColorChoice, CombinedLogger, Config, ConfigBuilder, LevelFilter,
    TermLogger, TerminalMode,
};
use std::io::Write;
use std::process;
use termcolor::WriteColor;

mod actions;
use actions::{replay, run};
mod params;
use params::{Action, Params, error_color};

/// Wrapper to handle errors.
///
/// See [`cli()`].
fn main() -> ! {
    let params = Params::parse();
    process::exit(cli(&params).unwrap_or_else(|error| {
        let mut err = params.err_stream();
        err.set_color(&error_color()).unwrap();
        writeln!(err, "Error: {error:#}").unwrap();
        err.reset().unwrap();
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
        Action::Run(run_params) => run(params, run_params),
        Action::Replay(replay_params) => replay(params, replay_params),
    }
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

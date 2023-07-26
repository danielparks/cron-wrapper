//! `replay` executable.

// Most lint configuration is in lints.toml, but it doesn’t support forbid.
#![forbid(unsafe_code)]

use anyhow::{anyhow, bail};
use bstr::ByteSlice;
use clap::{Parser, ValueEnum};
use cron_wrapper::job_logger::parser::parse_log;
use cron_wrapper::job_logger::Kind;
use is_terminal::IsTerminal;
use simplelog::{
    CombinedLogger, Config, ConfigBuilder, LevelFilter, TermLogger,
    TerminalMode,
};
use std::convert::Into;
use std::fs;
use std::io;
use std::io::Write;
use std::path::PathBuf;
use std::process;
use std::str;
use termcolor::{Color, ColorSpec, StandardStream, WriteColor};

/// Parameters for `replay`.
#[derive(Debug, Parser)]
#[clap(version, about)]
#[allow(clippy::struct_excessive_bools)]
struct Params {
    /// The log file to replay
    pub log_file: PathBuf,

    /// Whether or not to output in color
    #[clap(long, default_value = "auto", value_name = "WHEN")]
    pub color: ColorChoice,

    /// Output metadata before actual output.
    #[clap(short, long)]
    pub metadata: bool,

    /// Verbosity (may be repeated up to three times)
    #[clap(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,
}

impl Params {
    /// Get stream to use for standard output.
    pub fn out_stream(&self) -> StandardStream {
        StandardStream::stdout(self.color_choice(&io::stdout()))
    }

    /// Get stream to use for errors.
    pub fn err_stream(&self) -> StandardStream {
        StandardStream::stderr(self.color_choice(&io::stderr()))
    }

    /// Whether or not to output on a stream in color.
    ///
    /// Checks if passed stream is a terminal.
    pub fn color_choice<T: IsTerminal>(
        &self,
        stream: &T,
    ) -> termcolor::ColorChoice {
        if self.color == ColorChoice::Auto && !stream.is_terminal() {
            termcolor::ColorChoice::Never
        } else {
            self.color.into()
        }
    }
}

/// Whether or not to output in color
#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub enum ColorChoice {
    /// Output in color when running in a terminal that supports it
    Auto,

    /// Always output in color
    Always,

    /// Never output in color
    Never,
}

impl Default for ColorChoice {
    fn default() -> Self {
        Self::Auto
    }
}

impl From<ColorChoice> for termcolor::ColorChoice {
    fn from(choice: ColorChoice) -> Self {
        match choice {
            ColorChoice::Auto => Self::Auto,
            ColorChoice::Always => Self::Always,
            ColorChoice::Never => Self::Never,
        }
    }
}

/// Wrapper to handle errors.
///
/// See [`cli()`].
fn main() {
    let params = Params::parse();
    process::exit(cli(&params).unwrap_or_else(|error| {
        let mut err = params.err_stream();
        err.set_color(&error_color()).unwrap();
        writeln!(err, "Error: {error:#}").unwrap();
        err.reset().unwrap();
        1
    }))
}

/// Do the actual work.
///
/// # Errors
///
/// This tries to log errors encountered after logging is started, and returns
/// all errors to [`main()`] to be outputted nicely.
fn cli(params: &Params) -> anyhow::Result<i32> {
    init_logging(params)?;

    let mut out = params.out_stream();
    let mut err = params.err_stream();
    let err_color = error_color();

    let log_file = fs::read(&params.log_file)?;
    let (metadata, records) = parse_log(&log_file).map_err(collapse_error)?;

    if params.metadata {
        for (key, value) in metadata {
            writeln!(out, "{}: {:?}", key.as_bstr(), value.as_bstr())?;
        }
        writeln!(out)?;
    }

    let mut exit_code: Option<i32> = None;

    for record in records {
        match record.kind {
            Kind::Stdout => {
                out.write_all(&record.value)?;
                out.flush()?;
            }
            Kind::Stderr => {
                err.set_color(&err_color)?;
                err.write_all(&record.value)?;
                err.reset()?;
                err.flush()?;
            }
            Kind::Exit => {
                // Keep reading so we don’t accidentally hide output if the
                // logger has some kind of bug.
                if exit_code.is_some() {
                    bail!("Multiple exit records found.");
                }
                exit_code = Some(str::from_utf8(&record.value)?.parse()?);
            }
            Kind::Error => {
                err.set_color(&err_color)?;
                err.write_all(b"Error: ")?;
                err.write_all(&record.value)?;
                err.reset()?;
                err.write_all(b"\n")?;
                err.flush()?;
            }
            Kind::WrapperError => {
                err.set_color(&err_color)?;
                err.write_all(b"Wrapper error: ")?;
                err.write_all(&record.value)?;
                err.reset()?;
                err.write_all(b"\n")?;
                err.flush()?;
            }
        }
    }

    Ok(exit_code.unwrap_or(0))
}

/// Initialize standard logging.
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
    TermLogger::new(
        level,
        config,
        TerminalMode::Mixed,
        simplelog::ColorChoice::Auto,
    )
}

/// Convenience function to make creating [`ConfigBuilder`]s clearer.
fn new_logger_config() -> ConfigBuilder {
    let mut builder = ConfigBuilder::new();
    builder.set_target_level(LevelFilter::Error);

    // FIXME: If this fails it will just print the time in UTC. That might be a
    // little surprising, so this should probably warn the user... except that
    // we haven’t finished setting up logging.
    let _ = builder.set_time_offset_to_local();

    builder
}

/// Returns color used to output errors.
fn error_color() -> ColorSpec {
    let mut color = ColorSpec::new();
    color.set_fg(Some(Color::Red));
    color.set_intense(true);
    color
}

/// Collapse a nom error into something that does not borrow the input.
fn collapse_error(error: nom::Err<nom::error::Error<&[u8]>>) -> anyhow::Error {
    match error {
        nom::Err::Incomplete(_) => anyhow!("unexpected EOF"),
        nom::Err::Error(e) | nom::Err::Failure(e) => {
            // FIXME: This gives terrible errors.
            anyhow!("Parse error {:?} at {:?}", e.code, e.input.as_bstr())
        }
    }
}

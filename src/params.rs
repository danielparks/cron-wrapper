//! Manage parameters for `cron-wrapper`.

use anyhow::anyhow;
use clap::builder::{OsStringValueParser, TryMapValueParser, TypedValueParser};
use clap::{Args, Parser, Subcommand, ValueEnum};
use clap_lex::OsStrExt;
use cron_wrapper::command::{Signal, WordIterator, WordIteratorSource};
use cron_wrapper::lock::default_lock_dir;
use is_terminal::IsTerminal;
use log::{log_enabled, Level::Trace};
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::str::FromStr;
use std::time::Duration;
use termcolor::StandardStream;
use termcolor::{Color, ColorSpec};

/// Parameters for `cron-wrapper`.
#[derive(Debug, Parser)]
#[clap(version, about)]
pub struct Params {
    /// What action to take
    #[command(subcommand)]
    pub action: Action,

    /// Whether or not to output in color
    #[clap(long, default_value = "auto", value_name = "WHEN")]
    pub color: ColorChoice,

    /// Verbosity (may be repeated up to three times)
    #[clap(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,
}

impl Params {
    /// Get stream to use for standard output.
    pub fn out_stream(&self) -> StandardStream {
        StandardStream::stdout(self.out_color_choice())
    }

    /// Get stream to use for errors.
    pub fn err_stream(&self) -> StandardStream {
        StandardStream::stderr(self.err_color_choice())
    }

    /// Whether or not to output on standard output in color.
    pub fn out_color_choice(&self) -> termcolor::ColorChoice {
        self.color_choice(&io::stdout())
    }

    /// Whether or not to output on standard error in color.
    pub fn err_color_choice(&self) -> termcolor::ColorChoice {
        self.color_choice(&io::stderr())
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

/// The actions (subcommands).
#[derive(Debug, Subcommand)]
pub enum Action {
    /// Run a command, only passing though output under certain circumstances.
    Run(RunParams),

    /// Replay a log.
    Replay(ReplayParams),
}

/// Run a command, only passing though output under certain circumstances.
#[derive(Debug, Args)]
#[allow(clippy::struct_excessive_bools)]
pub struct RunParams {
    /// The executable to run
    pub command: OsString,

    /// Arguments to pass to the executable
    #[clap(allow_hyphen_values = true)]
    pub args: Vec<OsString>,

    /// Pass through output if the child wrote to stderr
    #[clap(short = 'E', long)]
    pub on_error: bool,

    /// Pass through output if the child returned a non-0 exit code
    #[clap(short = 'F', long)]
    pub on_fail: bool,

    /// Always print child’s exit code
    #[clap(long)]
    pub show_exit_code: bool,

    /// Print child’s exit code if it’s not 0
    #[clap(short = 'X', long)]
    pub show_fail_code: bool,

    /// Combine stdout and stderr output
    ///
    /// Separate streams can sometimes be read out of order when writes occur
    /// very close together. Combining the streams solves those problems, but
    /// prevents us from determining what is on stdout and what is on stderr.
    #[clap(short = 'C', long)]
    pub combine_output: bool,

    /// Store structured log files in DIRECTORY
    ///
    /// Log files will be named YYYY-mm-ddTHH:MM:SS-ZZ:ZZ.$command.$pid.log. For
    /// example, if you were running /bin/ls, the file name might be
    /// 2023-05-10T20:05:17-07:00.ls.15297.log.
    ///
    /// Conflicts with --log-file <PATH>
    #[clap(short = 'l', long, value_name = "DIRECTORY")]
    pub log_dir: Option<PathBuf>,

    /// Save structured log data to PATH
    ///
    /// This will save structured logging data to PATH. If a file already exists
    /// at PATH, it will be overwritten.
    ///
    /// Conflicts with --log-dir <DIRECTORY>
    #[clap(short = 'L', long, value_name = "PATH", conflicts_with = "log_dir")]
    pub log_file: Option<PathBuf>,

    /// Output structured log to stdout instead of normal output
    ///
    /// This honors --on-error and --on-fail, and can be used in addition to
    /// --log-dir or --log-file.
    #[clap(short = 'S', long)]
    pub log_stdout: bool,

    /// Exit if the child runs for longer than DURATION
    ///
    /// DURATION may by a number representing seconds, or a string like "1s",
    /// "2h", or "2s 50ms". It cannot be more precise than milliseconds.
    ///
    /// The child process will be killed with the signal set by --error-signal
    /// (defaults to SIGTERM).
    #[clap(
        long,
        value_name = "DURATION",
        value_parser = parse_duration,
        allow_hyphen_values = true,
    )]
    pub run_timeout: Option<Duration>,

    /// Exit if the child doesn’t output for longer than DURATION
    ///
    /// DURATION may by a number representing seconds, or a string like "1s",
    /// "2h", or "2s 50ms". It cannot be more precise than milliseconds.
    ///
    /// The child process will be killed with the signal set by --error-signal
    /// (defaults to SIGTERM).
    #[clap(
        long,
        value_name = "DURATION",
        value_parser = parse_duration,
        allow_hyphen_values = true,
    )]
    pub idle_timeout: Option<Duration>,

    /// What signal to send the child process when a timeout or other error
    /// occurs.
    ///
    /// This may be set to "none" to skip killing the child process.
    #[clap(long, default_value = "SIGTERM", value_name = "SIGNAL")]
    pub error_signal: OptionalSignal,

    /// Ensure only one copy of this command runs at once.
    ///
    /// Conflicts with --lock-wait.
    #[clap(short = 's', long, conflicts_with = "lock_wait")]
    pub lock: bool,

    /// Wait for other copies of this command to finish before running.
    ///
    /// Conflicts with --lock.
    #[clap(short = 'w', long, conflicts_with = "lock")]
    pub lock_wait: bool,

    /// Directory to contain lock files used to ensure only one copy of this
    /// command is running at once.
    ///
    /// Specifies a directory in which to place a lock file used to ensure that
    /// only one copy of this command is running at once. If a process is
    /// already using the file, the file contents will be printed and we will
    /// immediately exit.
    ///
    /// Conflicts with --lock-file <PATH>.
    #[clap(long, value_name = "PATH", conflicts_with = "lock_file")]
    pub lock_dir: Option<PathBuf>,

    /// Unique name used to ensure only one copy of this command is running at
    /// once.
    ///
    /// No other copy of cron-wrapper will be able to run at the same time if it
    /// uses the same lock name and the same lock directory.
    ///
    /// May not contain '/'. Conflicts with --lock-file <PATH>.
    #[clap(
        long,
        value_name = "NAME",
        value_parser = file_name_value_parser(),
        conflicts_with = "lock_file",
    )]
    pub lock_name: Option<OsString>,

    /// Unique file to ensure only one copy of this command is running at once.
    ///
    /// Specifies the lock file to use to ensure that only one copy of this
    /// command is running at once. If a process is already using the file, the
    /// file contents will be printed and we will immediately exit.
    ///
    /// Conflicts with --lock-dir <PATH>.
    #[clap(long, value_name = "PATH")]
    pub lock_file: Option<PathBuf>,

    /// Hidden: how large a buffer to use
    #[clap(
        long,
        default_value_t = 4096,
        hide = true,
        allow_hyphen_values = true
    )]
    pub buffer_size: usize,
}

impl RunParams {
    /// Pause output until a condition is met.
    pub const fn start_paused(&self) -> bool {
        self.on_error || self.on_fail
    }

    /// Suppress normal output in favor of some other output.
    pub fn normal_output_enabled(&self) -> bool {
        !log_enabled!(Trace) && !self.log_stdout
    }

    /// Get the command line to run as an iterator over words.
    #[must_use]
    pub const fn command_line(&self) -> WordIterator<Self> {
        WordIterator::new(self)
    }

    /// Return directory to hold locks if locking is desired.
    pub fn lock_dir(&self) -> io::Result<Option<PathBuf>> {
        if self.lock_dir.is_some() {
            Ok(self.lock_dir.clone())
        } else if self.lock || self.lock_wait {
            // Default lock directory
            let path = default_lock_dir()?.join("cron-wrapper");
            if !path.is_dir() {
                fs::create_dir(&path)?;
            }
            Ok(Some(path))
        } else {
            // --lock-file is handled a different way.
            Ok(None)
        }
    }
}

impl<'a> WordIteratorSource<'a> for RunParams {
    fn first(&self) -> &OsString {
        &self.command
    }

    fn iter(&'a self) -> std::slice::Iter<'a, OsString> {
        self.args.iter()
    }
}

/// Replay a log.
#[derive(Debug, Args)]
#[allow(clippy::struct_excessive_bools)]
pub struct ReplayParams {
    /// The log file to replay
    pub log_file: PathBuf,

    /// Output metadata before actual output.
    #[clap(short, long)]
    pub metadata: bool,
}

/// Parse a duration from a parameter.
///
/// This ensures durations are not negative, that raw numbers are treated as
/// seconds, and that durations are not more precise than milliseconds.
fn parse_duration(input: &str) -> anyhow::Result<Duration> {
    let input = input.trim();

    if input.starts_with('-') {
        Err(anyhow!("duration cannot be negative"))
    } else if input.chars().all(|c| c.is_ascii_digit()) {
        // Input is all numbers, so assume it’s seconds.
        input
            .parse::<u64>()
            .map(Duration::from_secs)
            .map_err(Into::into)
    } else {
        let duration = duration_str::parse(input)?;
        // subsec_nanos() will always be >= subsec_millis() * 1e6
        #[allow(clippy::arithmetic_side_effects)]
        if duration.subsec_nanos() == duration.subsec_millis() * 1_000_000 {
            Ok(duration)
        } else {
            Err(anyhow!("duration cannot be more precise than milliseconds"))
        }
    }
}

/// Clap’s `value_parser` parameter can’t parse to Option<Signal>, so this is a
/// hack to allow `--error-signal none`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OptionalSignal {
    /// No signal.
    None,

    /// A normal signal.
    Some(Signal),
}

impl OptionalSignal {
    /// Is this `Some(Signal)`?
    pub const fn is_some(self) -> bool {
        matches!(self, Self::Some(_))
    }
}

impl fmt::Display for OptionalSignal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => f.write_str("none"),
            Self::Some(signal) => signal.fmt(f),
        }
    }
}

impl FromStr for OptionalSignal {
    type Err = nix::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let s = s.to_ascii_uppercase();
        if s == "0" || s == "NONE" {
            Ok(Self::None)
        } else if s.starts_with("SIG") {
            Ok(Self::Some(Signal::from_str(&s)?))
        } else {
            // Not real arithmetic.
            #[allow(clippy::arithmetic_side_effects)]
            let s = "SIG".to_owned() + &s;
            Ok(Self::Some(Signal::from_str(&s)?))
        }
    }
}

impl From<OptionalSignal> for Option<Signal> {
    fn from(signal: OptionalSignal) -> Self {
        match signal {
            OptionalSignal::None => None,
            OptionalSignal::Some(signal) => Some(signal),
        }
    }
}

/// Returns color used to output errors.
pub fn error_color() -> ColorSpec {
    let mut color = ColorSpec::new();
    color.set_fg(Some(Color::Red));
    color.set_intense(true);
    color
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

/// Value parser to validate a file name.
#[allow(clippy::type_complexity)] // Not reused and necessary.
fn file_name_value_parser() -> TryMapValueParser<
    OsStringValueParser,
    fn(OsString) -> Result<OsString, &'static str>,
> {
    /// Validate a file name.
    fn validate_file_name(name: OsString) -> Result<OsString, &'static str> {
        if name.is_empty() {
            Err("name cannot be empty")
        } else if name.starts_with(".") {
            Err("name cannot start with '.'")
        } else if name.contains("/") {
            Err("name cannot contain '/'")
        } else {
            Ok(name)
        }
    }

    OsStringValueParser::new().try_map(validate_file_name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::{check, let_assert};
    use clap::error::{
        ContextKind::InvalidArg, ContextValue::String, ErrorKind,
    };

    #[test]
    fn args_short_verbose_option() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "-v",
                "run",
                "command"
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args.len() == 0);
    }

    #[test]
    fn args_2_short_verbose_option() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "-vv",
                "run",
                "command"
            ])
        );
        check!(params.verbose == 2);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args.len() == 0);
    }

    #[test]
    fn args_invalid_long_option() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
                "--foo",
                "-v",
                "command"
            ])
        );
        check!(error.kind() == ErrorKind::UnknownArgument);
        check!(error.get(InvalidArg) == Some(&String("--foo".into())));
    }

    #[test]
    fn args_invalid_short_option() {
        let_assert!(
            Err(error) =
                Params::try_parse_from(["cron-wrapper", "-!", "-v", "command"])
        );
        check!(error.kind() == ErrorKind::UnknownArgument);
        check!(error.get(InvalidArg) == Some(&String("-!".into())));
    }

    #[test]
    fn args_other_long_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "run",
                "command",
                "--foo",
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["--foo"]);
    }

    #[test]
    fn args_other_short_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "run",
                "command",
                "-f",
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["-f"]);
    }

    #[test]
    fn args_other_mixed_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "run",
                "command",
                "-f",
                "--foo",
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["-f", "--foo"]);
    }

    #[test]
    #[ignore = "clap doesn’t stop parsing after first non-flag."]
    fn args_our_long_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "run",
                "command",
                "--on-error",
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["--on-error"]);
        check!(run_params.on_error == false);
    }

    #[test]
    #[ignore = "clap doesn’t stop parsing after first non-flag"]
    fn args_our_same_long_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "run",
                "command",
                "--verbose",
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["--verbose"]);
    }

    #[test]
    #[ignore = "clap doesn’t stop parsing after first non-flag."]
    fn args_our_short_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "-v",
                "run",
                "command",
                "-E"
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["-E"]);
        check!(run_params.on_error == false);
    }

    #[test]
    #[ignore = "clap doesn’t stop parsing after first non-flag."]
    fn args_our_same_short_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "-v",
                "run",
                "command",
                "-v"
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["-v"]);
    }

    #[test]
    fn args_command_with_args() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "-v",
                "run",
                "command",
                "-abc",
                "foo",
                "--",
                "-s",
                "--bar",
            ])
        );
        check!(params.verbose == 1);
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.command == PathBuf::from("command"));
        check!(run_params.args == ["-abc", "foo", "--", "-s", "--bar"]);
    }

    #[test]
    fn args_buffer_size_negative() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--buffer-size",
                "-2",
                "command",
            ])
        );
        check!(error.kind() == ErrorKind::ValueValidation);
    }

    #[test]
    fn args_idle_timeout_2() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "2",
                "command",
            ])
        );
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.idle_timeout == Some(Duration::from_secs(2)));
    }

    #[test]
    fn args_idle_timeout_2s() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "2s",
                "command",
            ])
        );
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.idle_timeout == Some(Duration::from_secs(2)));
    }

    #[test]
    fn args_idle_timeout_2s_1ms() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "2s 1ms",
                "command",
            ])
        );
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.idle_timeout == Some(Duration::from_millis(2001)));
    }

    #[test]
    fn args_idle_timeout_2h() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "2h",
                "command",
            ])
        );
        let_assert!(Action::Run(run_params) = params.action);
        check!(
            run_params.idle_timeout == Some(Duration::from_secs(2 * 60 * 60))
        );
    }

    #[test]
    fn args_idle_timeout_negative() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "-2s",
                "command",
            ])
        );
        check!(error.kind() == ErrorKind::ValueValidation);
        check!(error.to_string().contains("negative"));
    }

    #[test]
    fn args_idle_timeout_zero() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "0",
                "command",
            ])
        );
        let_assert!(Action::Run(run_params) = params.action);
        check!(run_params.idle_timeout == Some(Duration::ZERO));
    }

    #[test]
    fn args_idle_timeout_maximum() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                &format!("{}ms", i32::MAX),
                "command",
            ])
        );
        let_assert!(Action::Run(run_params) = params.action);
        check!(
            run_params.idle_timeout
                == Some(Duration::from_millis(i32::MAX as u64))
        );
    }

    #[test]
    fn args_idle_timeout_overly_precise() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
                "run",
                "--idle-timeout",
                "2s 2ms 2ns",
                "command",
            ])
        );
        check!(error.kind() == ErrorKind::ValueValidation);
        check!(error.to_string().contains("milliseconds"));
    }
}

use anyhow::anyhow;
use clap::Parser;
use std::ffi::OsString;
use std::path::PathBuf;
use std::time::Duration;

#[derive(Debug, Parser)]
#[clap(version, about)]
pub(crate) struct Params {
    /// The executable to run
    pub command: PathBuf,

    /// Arguments to pass to the executable
    #[clap(allow_hyphen_values = true)]
    pub args: Vec<OsString>,

    /// Output if there is output on stderr
    #[clap(short = 'E', long)]
    pub on_error: bool,

    /// Output if the exit code is not 0
    #[clap(short = 'F', long)]
    pub on_fail: bool,

    /// Always output exit code
    #[clap(long)]
    pub show_exit_code: bool,

    /// Output exit code when it’s not 0
    #[clap(short = 'X', long)]
    pub show_fail_code: bool,

    /// Verbosity (may be repeated up to three times)
    #[clap(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,

    /// Timeout for entire run (e.g. "1s", "1h", or "30ms")
    #[clap(
        long,
        value_name = "DURATION",
        value_parser = parse_duration,
        allow_hyphen_values = true,
    )]
    pub run_timeout: Option<Duration>,

    /// Timeout for individual reads (e.g. "1s", "1h", or "30ms")
    #[clap(
        long,
        value_name = "DURATION",
        value_parser = parse_duration,
        allow_hyphen_values = true,
    )]
    pub idle_timeout: Option<Duration>,

    /// Hidden: how large a buffer to use
    #[clap(
        long,
        default_value_t = 4096,
        hide = true,
        allow_hyphen_values = true
    )]
    pub buffer_size: usize,
}

impl Params {
    /// Whether or not to suppress normal output
    pub fn suppress_output(&self) -> bool {
        self.on_error || self.on_fail
    }
}

fn parse_duration(input: &str) -> anyhow::Result<Duration> {
    let input = input.trim();

    if input.starts_with('-') {
        Err(anyhow!("duration cannot be negative"))
    } else if input.chars().all(|c| c.is_ascii_digit()) {
        // Input is all numbers, so assume it’s seconds.
        input
            .parse::<u64>()
            .map(Duration::from_secs)
            .map_err(|e| e.into())
    } else {
        let duration = duration_str::parse(input)?;
        if duration.subsec_nanos() == duration.subsec_millis() * 1_000_000 {
            Ok(duration)
        } else {
            Err(anyhow!("duration cannot be more precise than milliseconds"))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::{check, let_assert};
    use clap::error::{
        ContextKind::InvalidArg, ContextValue::String, ErrorKind,
    };
    use std::path::PathBuf;
    use std::time::Duration;

    #[test]
    fn args_short_verbose_option() {
        let_assert!(
            Ok(params) =
                Params::try_parse_from(["cron-wrapper", "-v", "command"])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args.len() == 0);
        check!(params.verbose == 1);
    }

    #[test]
    fn args_2_short_verbose_option() {
        let_assert!(
            Ok(params) =
                Params::try_parse_from(["cron-wrapper", "-vv", "command"])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args.len() == 0);
        check!(params.verbose == 2);
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
                "command",
                "--foo",
            ])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["--foo"]);
        check!(params.verbose == 1);
    }

    #[test]
    fn args_other_short_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "command",
                "-f",
            ])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["-f"]);
        check!(params.verbose == 1);
    }

    #[test]
    fn args_other_mixed_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "command",
                "-f",
                "--foo",
            ])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["-f", "--foo"]);
        check!(params.verbose == 1);
    }

    #[test]
    #[ignore] // FIXME clap doesn’t stop parsing after first non-flag.
    fn args_our_long_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "command",
                "--on-error",
            ])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["--on-error"]);
        check!(params.verbose == 1);
        check!(params.on_error == false);
    }

    #[test]
    #[ignore] // FIXME clap doesn’t stop parsing after first non-flag.
    fn args_our_same_long_option_after_command() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--verbose",
                "command",
                "--verbose",
            ])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["--verbose"]);
        check!(params.verbose == 1);
    }

    #[test]
    #[ignore] // FIXME clap doesn’t stop parsing after first non-flag.
    fn args_our_short_option_after_command() {
        let_assert!(
            Ok(params) =
                Params::try_parse_from(["cron-wrapper", "-v", "command", "-E"])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["-E"]);
        check!(params.verbose == 1);
        check!(params.on_error == false);
    }

    #[test]
    #[ignore] // FIXME clap doesn’t stop parsing after first non-flag.
    fn args_our_same_short_option_after_command() {
        let_assert!(
            Ok(params) =
                Params::try_parse_from(["cron-wrapper", "-v", "command", "-v"])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["-v"]);
        check!(params.verbose == 1);
    }

    #[test]
    fn args_command_with_args() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "-v",
                "command",
                "-abc",
                "foo",
                "--",
                "-s",
                "--bar",
            ])
        );
        check!(params.command == PathBuf::from("command"));
        check!(params.args == ["-abc", "foo", "--", "-s", "--bar"]);
        check!(params.verbose == 1);
    }

    #[test]
    fn args_buffer_size_negative() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
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
                "--idle-timeout",
                "2",
                "command",
            ])
        );
        check!(params.idle_timeout == Some(Duration::from_secs(2)));
    }

    #[test]
    fn args_idle_timeout_2s() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--idle-timeout",
                "2s",
                "command",
            ])
        );
        check!(params.idle_timeout == Some(Duration::from_secs(2)));
    }

    #[test]
    fn args_idle_timeout_2s_1ms() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--idle-timeout",
                "2s 1ms",
                "command",
            ])
        );
        check!(params.idle_timeout == Some(Duration::from_millis(2001)));
    }

    #[test]
    fn args_idle_timeout_2h() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--idle-timeout",
                "2h",
                "command",
            ])
        );
        check!(params.idle_timeout == Some(Duration::from_secs(2 * 60 * 60)));
    }

    #[test]
    fn args_idle_timeout_negative() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
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
                "--idle-timeout",
                "0",
                "command",
            ])
        );
        check!(params.idle_timeout == Some(Duration::ZERO));
    }

    #[test]
    fn args_idle_timeout_maximum() {
        let_assert!(
            Ok(params) = Params::try_parse_from([
                "cron-wrapper",
                "--idle-timeout",
                &format!("{}ms", i32::MAX),
                "command",
            ])
        );
        check!(
            params.idle_timeout == Some(Duration::from_millis(i32::MAX as u64))
        );
    }

    #[test]
    fn args_idle_timeout_overly_precise() {
        let_assert!(
            Err(error) = Params::try_parse_from([
                "cron-wrapper",
                "--idle-timeout",
                "2s 2ms 2ns",
                "command",
            ])
        );
        check!(error.kind() == ErrorKind::ValueValidation);
        check!(error.to_string().contains("milliseconds"));
    }
}

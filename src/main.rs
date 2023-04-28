#![forbid(unsafe_code)]

use anyhow::bail;
use bstr::ByteSlice;
use clap::Parser;
use log::Level::Trace;
use log::{debug, error, info, log_enabled, trace};
use popol::set_nonblocking;
use simplelog::{
    ColorChoice, CombinedLogger, Config, ConfigBuilder, LevelFilter,
    TermLogger, TerminalMode,
};
use std::cmp;
use std::io::{self, Read, Write};
use std::os::unix::process::ExitStatusExt;
use std::process;
use std::time::Duration;

mod params;
use params::Params;

mod timeout;
use timeout::Timeout;

#[derive(Clone, PartialEq, Eq, Debug)]
enum PollKey {
    Out,
    Err,
}

// Requires logging to be set up
macro_rules! fail {
    ($($arg:tt)*) => {{
        error!($($arg)*);
        process::exit(1);
    }};
}

/// Maximum timeout that poll allows.
const POLL_MAX_TIMEOUT: Timeout = Timeout::Future {
    timeout: Duration::from_millis(i32::MAX as u64),
};

fn main() {
    if let Err(error) = cli(Params::parse()) {
        eprintln!("Error: {:#}", error);
        process::exit(1);
    }
}

fn cli(params: Params) -> anyhow::Result<()> {
    init_logging(&params)?;

    let run_timeout = Timeout::from(params.run_timeout).start();
    let idle_timeout = Timeout::from(params.idle_timeout);

    info!("Start: {:?} {:?}", params.command, params.args);
    debug!("run timeout {run_timeout}, idle timeout {idle_timeout}");

    let mut child = process::Command::new(&params.command)
        .args(&params.args)
        .stdout(process::Stdio::piped())
        .stderr(process::Stdio::piped())
        .spawn()
        .unwrap_or_else(|err| {
            fail!("Could not run command {:?}: {}", params.command, err);
        });

    let mut sources = popol::Sources::with_capacity(2);
    let mut events = Vec::with_capacity(2);

    let mut child_out = child.stdout.take().expect("child.stdout is None");
    set_nonblocking(&child_out, true)
        .expect("child stdout cannot be set to non-blocking");
    sources.register(PollKey::Out, &child_out, popol::interest::READ);

    let mut child_err = child.stderr.take().expect("child.stderr is None");
    set_nonblocking(&child_err, true)
        .expect("child stderr cannot be set to non-blocking");
    sources.register(PollKey::Err, &child_err, popol::interest::READ);

    let mut out = std::io::stdout();

    let mut buffer = vec![0; params.buffer_size];

    // FIXME? this sometimes messes up the order if stderr and stdout are used
    // in the same line. Not sure this is possible to fix.
    while !sources.is_empty() {
        let timeout = cmp::min(&run_timeout, &idle_timeout);
        if let Some(expired) = timeout.check_expired() {
            timeout_fail(timeout, &expired);
        }

        trace!("poll() with timeout {timeout} (run timeout {run_timeout})");

        match poll(&mut sources, &mut events, timeout) {
            Ok(None) => {} // Success
            Ok(Some(expired)) => timeout_fail(timeout, &expired),
            Err(error) => fail!("Error while waiting for input: {:?}", error),
        }

        for event in events.drain(..) {
            trace!("{event:?}");

            if event.is_readable() {
                loop {
                    let result = if event.key == PollKey::Out {
                        child_out.read(&mut buffer)
                    } else {
                        child_err.read(&mut buffer)
                    };

                    let count = match result {
                        Ok(count) => count,
                        Err(err) => {
                            if err.kind() == io::ErrorKind::WouldBlock {
                                // Done reading.
                                trace!("io::ErrorKind::WouldBlock");

                                break;
                            } else {
                                return Err(err.into());
                            }
                        }
                    };

                    trace!(
                        "{:?}: read {count} bytes: {:?}",
                        event.key,
                        buffer[..count].as_bstr(),
                    );

                    if count > 0 && !log_enabled!(Trace) {
                        // Only output if there’s something to output and we’re
                        // not in trace mode.
                        out.write_all(&buffer[..count])?;
                        out.flush()?; // In case there wasn’t a newline.
                    }

                    if count < buffer.len() {
                        // We could read again and get either 0 bytes or
                        // io::ErrorKind::WouldBlock, but I think this check
                        // makes it more likely the output ordering is correct.
                        // A partial read indicates that the stream had stopped,
                        // so we should check to see if another stream is ready.
                        break;
                    }
                }
            }

            if event.is_hangup() {
                // Remove the stream from poll.
                sources.unregister(&event.key);
            }
        }
    }

    let code =
        wait_status_to_code(child.wait().expect("failed to wait on child"))
            .expect("no exit code or signal for child");
    info!("Exit with {code}: {:?} {:?}", params.command, params.args);
    process::exit(code);
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

/// Display a message about the timeout expiring.
///
/// `timeout` is the original timeout; `expired` is the timeout object after it
/// expired. You can determine the type of timeout based on the variant of
/// `timeout`, since the idle timeout is always `Timeout::Future` or
/// `Timeout::Never` and the overall run timeout is always `Timeout::Pending`
/// or `Timeout::Never`.
fn timeout_fail(timeout: &Timeout, expired: &Timeout) {
    match &timeout {
        Timeout::Never => panic!("timed out when no timeout was set"),
        Timeout::Expired { .. } => panic!("did not expect Timeout::Expired"),
        Timeout::Future { .. } => {
            fail!(
                "Timed out waiting for input after {:?}",
                expired.elapsed_rounded()
            )
        }
        Timeout::Pending { .. } => {
            fail!("Run timed out after {:?}", expired.elapsed_rounded())
        }
    }
}

/// Wait for input.
///
/// Returns:
///  * `Ok(None)`: got input.
///  * `Ok(Some(Timeout::Expired { .. })`: timeout expired without input.
///  * `Err(error)`: an error occurred.
fn poll(
    sources: &mut popol::Sources<PollKey>,
    events: &mut Vec<popol::Event<PollKey>>,
    timeout: &Timeout,
) -> anyhow::Result<Option<Timeout>> {
    // FIXME? handle EINTR? I don’t think it will come up unless we have a
    // signal handler set.
    let timeout = timeout.start();
    while events.is_empty() {
        if let Some(expired) = timeout.check_expired() {
            return Ok(Some(expired));
        }

        let call_timeout = cmp::min(&timeout, &POLL_MAX_TIMEOUT).timeout();
        if let Err(error) = sources.poll(events, call_timeout) {
            // Ignore valid timeouts; they are handled on next loop.
            if call_timeout.is_some() && error.kind() == io::ErrorKind::TimedOut
            {
                continue;
            }

            // Invalid timeout or other error.
            return Err(error.into());
        }
    }

    Ok(None)
}

/// Get the actual exit code from a finished child process
fn wait_status_to_code(status: process::ExitStatus) -> Option<i32> {
    status.code().or_else(|| Some(128 + status.signal()?))
}

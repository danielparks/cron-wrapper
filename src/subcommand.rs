use crate::timeout::Timeout;
use bstr::ByteSlice;
use log::{debug, error, info, trace};
use popol::set_nonblocking;
use std::cmp;
use std::ffi::OsString;
use std::fmt;
use std::io::{self, Read};
use std::process;
use std::time::Duration;
use thiserror::Error;

/// Maximum timeout that poll allows.
const POLL_MAX_TIMEOUT: Timeout = Timeout::Future {
    timeout: Duration::from_millis(i32::MAX as u64),
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StreamType {
    Out,
    Err,
}

impl fmt::Display for StreamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Out => write!(f, "stdout"),
            Self::Err => write!(f, "stderr"),
        }
    }
}

pub trait SubcommandHandler {
    /// Called when the child process emits on stdout.
    fn on_out(&mut self, _output: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }

    /// Called when the child process emits on stderr.
    fn on_err(&mut self, _output: &[u8]) -> anyhow::Result<()> {
        Ok(())
    }

    /// Called when the child process exits.
    fn on_exit(&mut self, _status: process::ExitStatus) -> anyhow::Result<()> {
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum SubcommandError {
    #[error("Could not run command {command:?}: {error}")]
    Spawn { command: OsString, error: io::Error },

    #[error("Error while waiting for input: {error:?}")]
    Poll { error: io::Error },

    #[error("Error reading from child {stream}: {error:?}")]
    Read {
        error: io::Error,
        stream: StreamType,
    },

    #[error("Timed out waiting for input after {:?}", timeout.elapsed_rounded())]
    IdleTimeout { timeout: Timeout },

    #[error("Run timed out after {:?}", timeout.elapsed_rounded())]
    RunTimeout { timeout: Timeout },
}

pub struct Subcommand {
    pub command: OsString,
    pub args: Vec<OsString>,
    pub run_timeout: Timeout,
    pub idle_timeout: Timeout,
    pub buffer_size: usize,
}

impl Subcommand {
    pub fn run(
        &self,
        mut handler: impl SubcommandHandler,
    ) -> anyhow::Result<()> {
        let run_timeout = self.run_timeout.start();

        info!("Start: {:?} {:?}", self.command, self.args);
        debug!(
            "run timeout {run_timeout}, idle timeout {}",
            self.idle_timeout
        );

        let mut child = process::Command::new(&self.command)
            .args(&self.args)
            .stdout(process::Stdio::piped())
            .stderr(process::Stdio::piped())
            .spawn()
            .map_err(|error| SubcommandError::Spawn {
                command: self.command.clone(),
                error,
            })?;

        let mut sources = popol::Sources::with_capacity(2);
        let mut events = Vec::with_capacity(2);

        let mut child_out = child.stdout.take().expect("child.stdout is None");
        set_nonblocking(&child_out, true)
            .expect("child stdout cannot be set to non-blocking");
        sources.register(StreamType::Out, &child_out, popol::interest::READ);

        let mut child_err = child.stderr.take().expect("child.stderr is None");
        set_nonblocking(&child_err, true)
            .expect("child stderr cannot be set to non-blocking");
        sources.register(StreamType::Err, &child_err, popol::interest::READ);

        let mut buffer = vec![0; self.buffer_size];

        // FIXME? this sometimes messes up the order if stderr and stdout are
        // used in the same line. Not sure this is possible to fix.
        while !sources.is_empty() {
            let timeout = cmp::min(&run_timeout, &self.idle_timeout);
            if let Some(expired) = timeout.check_expired() {
                timeout_fail(timeout, &expired)?;
            }

            trace!("poll() with timeout {timeout} (run timeout {run_timeout})");

            poll(&mut sources, &mut events, timeout)?;
            for event in events.drain(..) {
                trace!("{event:?}");

                if event.is_readable() {
                    loop {
                        let result = if event.key == StreamType::Out {
                            child_out.read(&mut buffer)
                        } else {
                            child_err.read(&mut buffer)
                        };

                        let count = match result {
                            Ok(count) => count,
                            Err(error) => {
                                if error.kind() == io::ErrorKind::WouldBlock {
                                    // Done reading.
                                    trace!("io::ErrorKind::WouldBlock");
                                    break;
                                } else {
                                    return Err(SubcommandError::Read {
                                        error,
                                        stream: event.key,
                                    }
                                    .into());
                                }
                            }
                        };

                        trace!(
                            "{:?}: read {count} bytes: {:?}",
                            event.key,
                            buffer[..count].as_bstr(),
                        );

                        if event.key == StreamType::Out {
                            handler.on_out(&buffer[..count])?;
                        } else {
                            handler.on_err(&buffer[..count])?;
                        }

                        if count < buffer.len() {
                            // We could read again and get either 0 bytes or
                            // io::ErrorKind::WouldBlock, but I think this check
                            // makes it more likely the output ordering is
                            // correct. A partial read indicates that the stream
                            // had stopped, so we should check to see if another
                            // stream is ready.
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

        handler.on_exit(child.wait().expect("failed to wait on child"))?;

        Ok(())
    }
}

/// Wait for input.
fn poll(
    sources: &mut popol::Sources<StreamType>,
    events: &mut Vec<popol::Event<StreamType>>,
    timeout: &Timeout,
) -> Result<(), SubcommandError> {
    // FIXME? handle EINTR? I don’t think it will come up unless we have a
    // signal handler set.
    let timeout = timeout.start();
    while events.is_empty() {
        if let Some(expired) = timeout.check_expired() {
            return timeout_fail(&timeout, &expired);
        }

        let call_timeout = cmp::min(&timeout, &POLL_MAX_TIMEOUT).timeout();
        if let Err(error) = sources.poll(events, call_timeout) {
            // Timeouts are handled at the top of the loop. If we get a timeout
            // error here, we ignore it as long as a timeout was specified. If
            // poll() for some reason returned a timeout error before the
            // timeout actually elapsed we just call poll() again.
            if call_timeout.is_some() && error.kind() == io::ErrorKind::TimedOut
            {
                continue;
            }

            // Return all other errors.
            return Err(SubcommandError::Poll { error });
        }
    }

    Ok(())
}

/// Display a message about the timeout expiring.
///
/// `timeout` is the original timeout; `expired` is the timeout object after it
/// expired. You can determine the type of timeout based on the variant of
/// `timeout`, since the idle timeout is always `Timeout::Future` or
/// `Timeout::Never` and the overall run timeout is always `Timeout::Pending`
/// or `Timeout::Never`.
fn timeout_fail(
    timeout: &Timeout,
    expired: &Timeout,
) -> Result<(), SubcommandError> {
    match &timeout {
        Timeout::Never => panic!("timed out when no timeout was set"),
        Timeout::Expired { .. } => panic!("did not expect Timeout::Expired"),
        Timeout::Future { .. } => Err(SubcommandError::IdleTimeout {
            timeout: expired.clone(),
        }),
        Timeout::Pending { .. } => Err(SubcommandError::RunTimeout {
            timeout: expired.clone(),
        }),
    }
}

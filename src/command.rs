use crate::timeout::Timeout;
use bstr::ByteSlice;
use log::{debug, error, info, trace};
use popol::set_nonblocking;
use std::cmp;
use std::collections::VecDeque;
use std::ffi::OsString;
use std::fmt;
use std::io::{self, Read};
use std::process;
use std::time::Duration;
use thiserror::Error;

/// Maximum timeout that poll allows.
///
/// For the standard `poll()` syscall, this is [`i32::MAX`] milliseconds, or
/// just short of 25 days.
const POLL_MAX_TIMEOUT: Timeout = Timeout::Future {
    timeout: Duration::from_millis(i32::MAX as u64),
};

/// Used to indicate either stderr or stdout on the child process.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum StreamType {
    Stdout,
    Stderr,
}

impl fmt::Display for StreamType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Stdout => write!(f, "stdout"),
            Self::Stderr => write!(f, "stderr"),
        }
    }
}

/// Errors that running a command might raise.
#[derive(Debug, Error)]
pub enum Error {
    #[error("Could not run command {command:?}: {error}")]
    Spawn { command: OsString, error: io::Error },

    #[error("Error while waiting for input: {error}")]
    Poll { error: io::Error },

    #[error("Error reading from child {stream}: {error}")]
    Read {
        error: io::Error,
        stream: StreamType,
    },

    #[error("Timed out waiting for input after {:?}", timeout.elapsed_rounded())]
    IdleTimeout { timeout: Timeout },

    #[error("Run timed out after {:?}", timeout.elapsed_rounded())]
    RunTimeout { timeout: Timeout },
}

/// A command to run.
///
/// ```rust
/// use cron_wrapper::command::Command;
/// use cron_wrapper::timeout::Timeout;
///
/// let child = Command {
///     command: "/bin/ls".into(),
///     args: vec!["-l".into(), "/".into()],
///     run_timeout: Timeout::Never,
///     idle_timeout: Timeout::Never,
/// }.start().unwrap();
/// ```
#[derive(Clone, Debug)]
pub struct Command {
    /// The path to the executable to run.
    pub command: OsString,

    /// Arguments to pass, not including the executable’s name.
    pub args: Vec<OsString>,

    /// Timeout for the overall command run.
    pub run_timeout: Timeout,

    /// Timeout for waiting for output from the command.
    pub idle_timeout: Timeout,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Polling,
    Reading(StreamType),
    Exiting,
}

/// A child process did something.
#[derive(Debug)]
pub enum Event<'a> {
    /// There was output on the child’s stdout.
    ///
    /// Note that the byte slice in this event is only valid until the next call
    /// to [`Child::next_event()`].
    Stdout(&'a [u8]),

    /// There was output on the child’s stderr.
    ///
    /// Note that the byte slice in this event is only valid until the next call
    /// to [`Child::next()`].
    Stderr(&'a [u8]),

    /// The child exited.
    Exit(process::ExitStatus),

    /// An error reading from the child.
    Error(Error),
}

/// A running [`Command`].
#[derive(Debug)]
pub struct Child {
    process: process::Child,
    run_timeout: Timeout,
    idle_timeout: Timeout,
    sources: popol::Sources<StreamType>,
    events: VecDeque<popol::Event<StreamType>>,
    stdout: process::ChildStdout,
    stderr: process::ChildStderr,
    state: State,
}

impl Command {
    /// Run the command and produce a [`Child`].
    pub fn start(self) -> Result<Child, Error> {
        let command = self.command;
        let args = self.args;
        let run_timeout = self.run_timeout.start();
        let idle_timeout = self.idle_timeout;

        info!("Start: {command:?} {args:?}");
        debug!("run timeout {run_timeout}, idle timeout {idle_timeout}");

        let mut process = process::Command::new(&command)
            .args(&args)
            .stdout(process::Stdio::piped())
            .stderr(process::Stdio::piped())
            .spawn()
            .map_err(|error| Error::Spawn { command, error })?;

        let mut sources = popol::Sources::with_capacity(2);

        let stdout = process.stdout.take().expect("process.stdout is None");
        set_nonblocking(&stdout, true)
            .expect("child stdout cannot be set to non-blocking");
        sources.register(StreamType::Stdout, &stdout, popol::interest::READ);

        let stderr = process.stderr.take().expect("process.stderr is None");
        set_nonblocking(&stderr, true)
            .expect("child stderr cannot be set to non-blocking");
        sources.register(StreamType::Stderr, &stderr, popol::interest::READ);

        Ok(Child {
            process,
            run_timeout,
            idle_timeout,
            stdout,
            stderr,
            sources,
            events: VecDeque::with_capacity(2),
            state: State::Polling,
        })
    }
}

impl Child {
    /// Get next event from child (will wait).
    ///
    /// This works like an iterator, but the iterator interface cannot return
    /// references to itself.
    pub fn next<'a>(&mut self, buffer: &'a mut [u8]) -> Option<Event<'a>> {
        // FIXME? this sometimes messes up the order if stderr and stdout are
        // used in the same line. Not sure this is possible to fix.

        // Are we still reading?
        if let State::Reading(stream) = self.state {
            match self.read(stream, buffer) {
                Ok(0) => {} // FIXME?
                Ok(length) => {
                    return Some(match stream {
                        StreamType::Stdout => Event::Stdout(&buffer[..length]),
                        StreamType::Stderr => Event::Stderr(&buffer[..length]),
                    });
                }
                Err(error) => {
                    return Some(Event::Error(error));
                }
            }
        }

        loop {
            // Process events even if all sources have been removed.
            while let Some(event) = self.events.pop_front() {
                trace!("{event:?}");

                if event.is_hangup() {
                    // Remove the stream from poll.
                    self.sources.unregister(&event.key);
                }

                if event.is_readable() {
                    match self.read(event.key, buffer) {
                        Ok(0) => {} // FIXME?
                        Ok(length) => {
                            return Some(match event.key {
                                StreamType::Stdout => {
                                    Event::Stdout(&buffer[..length])
                                }
                                StreamType::Stderr => {
                                    Event::Stderr(&buffer[..length])
                                }
                            });
                        }
                        Err(error) => {
                            return Some(Event::Error(error));
                        }
                    }
                }
            }

            if self.sources.is_empty() {
                // All streams have closed. Move on to waiting on child to exit.
                self.state = State::Exiting;
                break;
            }

            if let Err(error) = self.poll() {
                return Some(Event::Error(error));
            }
        }

        if self.state == State::Exiting {
            Some(Event::Exit(
                self.process.wait().expect("failed to wait on child"),
            ))
        } else {
            None
        }
    }

    /// Wait for input.
    ///
    /// This wrapper around [`popol::Sources::poll()`] handles timeouts longer
    /// than [`POLL_MAX_TIMEOUT`].
    ///
    /// If `events` is not empty this will do nothing, not even check if the
    /// timeout is expired.
    fn poll(&mut self) -> Result<(), Error> {
        let original_timeout = cmp::min(&self.run_timeout, &self.idle_timeout);
        trace!(
            "poll() with timeout {original_timeout} (run timeout {})",
            self.run_timeout
        );

        // If this is an overall run timeout, starting it again will just return
        // a clone of it.
        let timeout = original_timeout.start();

        while self.events.is_empty() {
            if let Some(expired) = timeout.check_expired() {
                return Err(timeout_error(original_timeout, expired));
            }

            // If timeout is greater than POLL_MAX_TIMEOUT we may have to call
            // poll() multiple times before we reach the real timeout.
            let call_timeout = cmp::min(&timeout, &POLL_MAX_TIMEOUT).timeout();

            // FIXME? handle EINTR? I don’t think it will come up unless we have
            // a signal handler set.
            if let Err(error) =
                self.sources.poll(&mut self.events, call_timeout)
            {
                // Timeouts are checked at the top of the loop. If we get a
                // timeout error here, we ignore it as long as a timeout was
                // specified. If poll() returned a timeout error before the
                // timeout actually elapsed we just call poll() again.
                if call_timeout.is_none()
                    || error.kind() != io::ErrorKind::TimedOut
                {
                    // Return all other errors.
                    return Err(Error::Poll { error });
                }
            }
        }

        Ok(())
    }

    /// Read from the child’s stdout or stderr.
    ///
    /// Fills `buffer` and returns the number of bytes written or an error.
    fn read(
        &mut self,
        stream: StreamType,
        buffer: &mut [u8],
    ) -> Result<usize, Error> {
        let result = match stream {
            StreamType::Stdout => self.stdout.read(buffer),
            StreamType::Stderr => self.stderr.read(buffer),
        };

        // FIXME treat count == 0 like io::ErrorKind::WouldBlock?
        let count = match result {
            Ok(count) => count,
            Err(error) => {
                // FIXME EINTR?
                if error.kind() == io::ErrorKind::WouldBlock {
                    // Done reading.
                    trace!("{stream:?}: io::ErrorKind::WouldBlock");
                    self.state = State::Polling;
                    return Ok(0);
                } else {
                    // FIXME? should we set state?
                    self.state = State::Reading(stream);
                    return Err(Error::Read { error, stream });
                }
            }
        };

        trace!(
            "{stream:?}: read {count} bytes: {:?}",
            &buffer[..count].as_bstr()
        );

        if count == buffer.len() {
            // read() filled the buffer so there’s likely more to read.
            self.state = State::Reading(stream);
        } else {
            // read() didn’t fill the buffer, so we should check any other
            // events poll() returned and then try poll() again. We could try
            // reading again, but if there was already data available on another
            // stream and then data was added to the current stream then we
            // would read it out of order.
            self.state = State::Polling;
        }

        Ok(count)
    }
}

/// Return the correct error about the timeout expiring.
///
/// `timeout` is the original timeout; `expired` is the timeout object after it
/// expired. You can determine the type of timeout based on the variant of
/// `timeout`, since the idle timeout is always `Timeout::Future` or
/// `Timeout::Never` and the overall run timeout is always `Timeout::Pending`
/// or `Timeout::Never`.
fn timeout_error(timeout: &Timeout, expired: Timeout) -> Error {
    match &timeout {
        Timeout::Never => panic!("timed out when no timeout was set"),
        Timeout::Expired { .. } => panic!("did not expect Timeout::Expired"),
        Timeout::Future { .. } => Error::IdleTimeout { timeout: expired },
        Timeout::Pending { .. } => Error::RunTimeout { timeout: expired },
    }
}

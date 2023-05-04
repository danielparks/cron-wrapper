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
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
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

/// Errors that running a command might raise.
#[derive(Error, Debug)]
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

#[derive(Clone, Debug)]
pub struct Command {
    pub command: OsString,
    pub args: Vec<OsString>,
    pub run_timeout: Timeout,
    pub idle_timeout: Timeout,
    pub buffer_size: usize,
}

#[derive(Clone, Copy, Debug)]
enum State {
    Waiting,
    Reading(StreamType),
}

/// A child process did something.
#[derive(Debug)]
pub enum Event {
    Stdout(Vec<u8>),
    Stderr(Vec<u8>),
    Error(Error),
    Exit(process::ExitStatus),
}

#[derive(Debug)]
pub struct Child {
    process: process::Child,
    run_timeout: Timeout,
    idle_timeout: Timeout,
    sources: popol::Sources<StreamType>,
    events: VecDeque<popol::Event<StreamType>>,
    out: process::ChildStdout,
    err: process::ChildStderr,
    buffer: Vec<u8>,
    state: State,
}

impl Command {
    pub fn start(self) -> Result<Child, Error> {
        let command = self.command;
        let args = self.args;
        let run_timeout = self.run_timeout.start();
        let idle_timeout = self.idle_timeout.clone();

        info!("Start: {command:?} {args:?}");
        debug!(
            "run timeout {run_timeout}, idle timeout {}",
            self.idle_timeout
        );

        let mut process = process::Command::new(&command)
            .args(&args)
            .stdout(process::Stdio::piped())
            .stderr(process::Stdio::piped())
            .spawn()
            .map_err(|error| Error::Spawn { command, error })?;

        let out = process.stdout.take().expect("process.stdout is None");
        let err = process.stderr.take().expect("process.stderr is None");
        let mut child = Child {
            process,
            run_timeout,
            idle_timeout,
            sources: popol::Sources::with_capacity(2),
            events: VecDeque::with_capacity(2),
            out,
            err,
            buffer: vec![0; self.buffer_size],
            state: State::Waiting,
        };

        set_nonblocking(&child.out, true)
            .expect("child stdout cannot be set to non-blocking");
        child.sources.register(
            StreamType::Out,
            &child.out,
            popol::interest::READ,
        );

        set_nonblocking(&child.err, true)
            .expect("child stderr cannot be set to non-blocking");
        child.sources.register(
            StreamType::Err,
            &child.err,
            popol::interest::READ,
        );

        Ok(child)
    }
}

impl Child {
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

    fn read(&mut self, stream: StreamType) -> Option<Event> {
        // Remember which stream we’re reading in case the buffer fills up and
        // we need to read again.
        self.state = State::Reading(stream);

        let result = match stream {
            StreamType::Out => self.out.read(&mut self.buffer),
            StreamType::Err => self.err.read(&mut self.buffer),
        };

        let count = match result {
            Ok(count) => count,
            Err(error) => {
                if error.kind() == io::ErrorKind::WouldBlock {
                    // Done reading.
                    trace!("io::ErrorKind::WouldBlock");
                    self.state = State::Waiting;
                    return None;
                } else {
                    return Some(Event::Error(Error::Read { error, stream }));
                }
            }
        };

        trace!(
            "{stream:?}: read {count} bytes: {:?}",
            self.buffer[..count].as_bstr(),
        );

        if count < self.buffer.len() {
            // read() didn’t fill the buffer.
            //
            // We could read again and get either io::ErrorKind::WouldBlock or 0
            // bytes, but I think this check makes it more likely the output
            // ordering is correct. A partial read indicates that the stream had
            // stopped, so we should check to see if another stream is ready.
            self.state = State::Waiting;
        }

        let output = self.buffer[..count].to_vec();
        Some(match stream {
            StreamType::Out => Event::Stdout(output),
            StreamType::Err => Event::Stderr(output),
        })
    }
}

impl Iterator for Child {
    type Item = Event;

    fn next(&mut self) -> Option<Self::Item> {
        // FIXME? this sometimes messes up the order if stderr and stdout are
        // used in the same line. Not sure this is possible to fix.

        if let State::Reading(stream) = self.state {
            // Try reading again. This will reset self.state if it returns None.
            if let Some(my_event) = self.read(stream) {
                return Some(my_event);
            }
        }

        loop {
            while let Some(event) = self.events.pop_front() {
                trace!("{event:?}");

                if event.is_hangup() {
                    // Remove the stream from poll.
                    self.sources.unregister(&event.key);
                }

                if event.is_readable() {
                    if let Some(my_event) = self.read(event.key) {
                        return Some(my_event);
                    }
                }
            }

            if self.sources.is_empty() {
                // All streams have closed. Time to wait for the child to exit.
                break;
            }

            if let Err(error) = self.poll() {
                return Some(Event::Error(error));
            }
        }

        // FIXME what if they call next() after this?
        Some(Event::Exit(
            self.process.wait().expect("failed to wait on child"),
        ))
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

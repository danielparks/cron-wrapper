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
///
/// let child = Command::new("/bin/date", []).spawn().unwrap();
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

    /// Size of the buffer for reads in bytes, e.g. `4096`.
    pub buffer_size: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    Polling,
    Reading(StreamType),
    Exiting,
    Exited,
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
    /// to [`Child::next_event()`].
    Stderr(&'a [u8]),

    /// The child exited.
    Exit(process::ExitStatus),

    /// There was an error reading from the child or waiting for the child.
    Error(Error),
}

impl<'a> Event<'a> {
    /// Make the correct type of read event given a [`StreamType`].
    fn make_read(stream: StreamType, output: &'a [u8]) -> Self {
        match stream {
            StreamType::Stdout => Self::Stdout(output),
            StreamType::Stderr => Self::Stderr(output),
        }
    }
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
    buffer: Vec<u8>,
}

impl Command {
    /// Produce a new `Command`
    ///
    /// This leaves all timeouts disabled and sets the buffer size to 4 KiB.
    ///
    /// ```rust
    /// use cron_wrapper::command::Command;
    /// use cron_wrapper::timeout::Timeout;
    ///
    /// let command = Command::new("/bin/ls", ["-l", "/"]);
    /// assert!(command.args == ["-l", "/"]);
    /// assert!(command.run_timeout == Timeout::Never);
    /// assert!(command.idle_timeout == Timeout::Never);
    /// assert!(command.buffer_size == 4096);
    /// ```
    pub fn new<S, I>(command: S, args: I) -> Self
    where
        S: Into<OsString>,
        I: IntoIterator<Item = S>,
    {
        Command {
            command: command.into(),
            args: args.into_iter().map(|s| s.into()).collect(),
            run_timeout: Timeout::Never,
            idle_timeout: Timeout::Never,
            buffer_size: 4096,
        }
    }

    /// Set the idle timeout
    ///
    /// This sets how long [`Child::next_event()`] waits for input from the
    /// child before returning `Some(Event::Error(Error::IdleTimeout { .. }))`.
    /// When using [`Command::new()`], the default is [`Timeout::Never`].
    ///
    /// You may pass this anything that can be converted into a [`Timeout`] with
    /// `.into()`:
    ///
    ///   * [`Timeout::Never`]
    ///   * [`Timeout::Future`]
    ///   * [`std::time::Duration`] (will be converted to `Timeout::Future`)
    ///   * [`None`] (will be converted to `Timeout::Never`)
    ///
    /// ```rust
    /// use assert2::let_assert;
    /// use cron_wrapper::command::{Command, Error, Event};
    /// use cron_wrapper::timeout::Timeout;
    /// use std::time::Duration;
    ///
    /// let mut child = Command::new("/bin/sleep", ["1"])
    ///     .idle_timeout(Duration::from_millis(1))
    ///     .spawn()
    ///     .unwrap();
    /// let_assert!(
    ///     Some(Event::Error(Error::IdleTimeout { .. })) =
    ///         child.next_event()
    /// );
    /// ```
    pub fn idle_timeout<T>(&mut self, timeout: T) -> &mut Self
    where
        T: Into<Timeout>,
    {
        self.idle_timeout = timeout.into();
        self
    }

    /// Set the run timeout
    ///
    /// This sets how long the child is allowed to run before a call to
    /// [`Child::next_event()`] returns `Some(Event::Error(Error::RunTimeout {
    /// .. }))`. When using [`Command::new()`], the default is
    /// [`Timeout::Never`].
    ///
    /// You may pass this anything that can be converted into a [`Timeout`] with
    /// `.into()`:
    ///
    ///   * [`Timeout::Never`]
    ///   * [`Timeout::Future`]
    ///   * [`std::time::Duration`] (will be converted to `Timeout::Future`)
    ///   * [`None`] (will be converted to `Timeout::Never`)
    ///
    /// ```rust
    /// use assert2::let_assert;
    /// use cron_wrapper::command::{Command, Error, Event};
    /// use cron_wrapper::timeout::Timeout;
    /// use std::time::Duration;
    ///
    /// let mut child = Command::new("/bin/sleep", ["1"])
    ///     .run_timeout(Duration::from_millis(1))
    ///     .spawn()
    ///     .unwrap();
    /// let_assert!(
    ///     Some(Event::Error(Error::RunTimeout { .. })) =
    ///         child.next_event()
    /// );
    /// ```
    pub fn run_timeout<T>(&mut self, timeout: T) -> &mut Self
    where
        T: Into<Timeout>,
    {
        self.run_timeout = timeout.into();
        self
    }

    /// Set the buffer size
    ///
    /// This sets the size of the buffer used to read child output. It is also
    /// the maximum size of output that will be returned in an [`Event::Stdout`]
    /// or [`Event::Stderr`]. When using [`Command::new()`], the default is 4096
    /// (4 KiB).
    ///
    /// ```rust
    /// use assert2::let_assert;
    /// use cron_wrapper::command::{Command, Event};
    ///
    /// let mut child = Command::new("/bin/echo", ["ab"])
    ///     .buffer_size(1)
    ///     .spawn()
    ///     .unwrap();
    /// let_assert!(Some(Event::Stdout(b"a")) = child.next_event());
    /// let_assert!(Some(Event::Stdout(b"b")) = child.next_event());
    /// let_assert!(Some(Event::Stdout(b"\n")) = child.next_event());
    /// ```
    pub fn buffer_size(&mut self, buffer_size: usize) -> &mut Self {
        self.buffer_size = buffer_size;
        self
    }

    /// Run the command and produce a [`Child`].
    ///
    /// This may be run multiple times to spawn multiple children.
    ///
    /// ```rust
    /// use assert2::{check, let_assert};
    /// use cron_wrapper::command::{Command, Event};
    ///
    /// let command = Command::new("/bin/sleep", ["0"]);
    /// let mut child = command.spawn().unwrap();
    /// let mut child2 = command.spawn().unwrap();
    ///
    /// let_assert!(Some(Event::Exit(status)) = child.next_event());
    /// check!(status.success());
    ///
    /// let_assert!(Some(Event::Exit(status)) = child2.next_event());
    /// check!(status.success());
    /// ```
    pub fn spawn(&self) -> Result<Child, Error> {
        let command = self.command.clone();
        let args = &self.args;
        let run_timeout = self.run_timeout.start();
        let idle_timeout = self.idle_timeout.clone();

        info!("Start: {command:?} {args:?}");
        debug!("run timeout {run_timeout}, idle timeout {idle_timeout}");

        let mut process = process::Command::new(&command)
            .args(args)
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
            buffer: vec![0; self.buffer_size],
        })
    }
}

impl Child {
    /// Get next event from child (will wait).
    ///
    /// This works like an iterator, but the Iterator trait cannot return
    /// references to itself.
    ///
    /// If this returns `Some(Event::Exit(status))` then future calls will
    /// return `None`.
    ///
    /// If an idle timeout is set and this returns
    /// `Some(Event::Error(Error::IdleTimeout { .. }))` then it may be called
    /// again as normal (and may return another timeout if it occurs again).
    ///
    /// If a run timeout is set and this returns
    /// `Some(Event::Error(Error::RunTimeout { .. }))` then this will return
    /// the same thing on every future call.
    pub fn next_event(&mut self) -> Option<Event<'_>> {
        // FIXME? this sometimes messes up the order if stderr and stdout are
        // used in the same line. Not sure this is possible to fix.

        // Are we still reading?
        if let State::Reading(stream) = self.state {
            match self.read(stream) {
                Ok(0) => {} // FIXME?
                Ok(length) => {
                    return Some(Event::make_read(
                        stream,
                        &self.buffer[..length],
                    ));
                }
                Err(error) => {
                    return Some(Event::Error(error));
                }
            }
        }

        while self.state == State::Polling {
            // Process events even if all sources have been removed.
            while let Some(event) = self.events.pop_front() {
                trace!("{event:?}");

                if event.is_hangup() {
                    // Remove the stream from poll.
                    self.sources.unregister(&event.key);
                }

                if event.is_readable() {
                    match self.read(event.key) {
                        Ok(0) => {} // FIXME?
                        Ok(length) => {
                            return Some(Event::make_read(
                                event.key,
                                &self.buffer[..length],
                            ));
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
            let status = self.process.wait().expect("failed to wait on child");
            self.state = State::Exited;
            Some(Event::Exit(status))
        } else if self.state == State::Exited {
            None
        } else {
            unreachable!("state is {:?}", self.state);
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
    /// Fills `self.buffer` and returns the number of bytes written or an error.
    fn read(&mut self, stream: StreamType) -> Result<usize, Error> {
        let result = match stream {
            StreamType::Stdout => self.stdout.read(&mut self.buffer),
            StreamType::Stderr => self.stderr.read(&mut self.buffer),
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
            &self.buffer[..count].as_bstr()
        );

        if count == self.buffer.len() {
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

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::check;

    #[test]
    fn next_after_exit() {
        let mut child = Command {
            command: "/bin/echo".into(),
            args: vec!["ok".into()],
            run_timeout: Timeout::Never,
            idle_timeout: Timeout::Never,
            buffer_size: 4096,
        }
        .spawn()
        .unwrap();

        let mut count = 0;
        while let Some(event) = child.next_event() {
            match event {
                Event::Stdout(output) => {
                    check!(output == b"ok\n");
                    count += 1;
                }
                Event::Stderr(output) => {
                    panic!("unexpected stderr: {output:?}")
                }
                Event::Error(error) => panic!("unexpected error: {error:?}"),
                Event::Exit(status) => {
                    check!(status.success());
                }
            }
        }

        check!(count == 1, "expected only 1 line of output");

        check!(child.next_event().is_none());
        check!(child.next_event().is_none());
    }

    #[test]
    fn next_after_run_timeout() {
        let mut child = Command {
            command: "/bin/sleep".into(),
            args: vec!["1".into()],
            run_timeout: Duration::from_millis(500).into(),
            idle_timeout: Timeout::Never,
            buffer_size: 4096,
        }
        .spawn()
        .unwrap();

        let mut count = 0;
        while let Some(event) = child.next_event() {
            match event {
                Event::Stdout(output) => {
                    panic!("unexpected stdout: {output:?}");
                }
                Event::Stderr(output) => {
                    panic!("unexpected stderr: {output:?}");
                }
                Event::Error(Error::RunTimeout {
                    timeout: Timeout::Expired { .. },
                }) => {
                    count += 1;
                    // It should just repeat this forever.
                    if count > 10 {
                        break;
                    }
                }
                Event::Error(error) => {
                    panic!("unexpected error: {error:?}");
                }
                Event::Exit(status) => {
                    panic!("unexpected exit: {status:?}");
                }
            }
        }

        check!(count == 11, "expected 11 timeout errors");
    }

    #[test]
    fn next_after_idle_timeout() {
        let mut child = Command {
            command: "/bin/sleep".into(),
            args: vec!["1".into()],
            run_timeout: Timeout::Never,
            idle_timeout: Duration::from_millis(10).into(),
            buffer_size: 4096,
        }
        .spawn()
        .unwrap();

        while let Some(event) = child.next_event() {
            match event {
                Event::Stdout(output) => {
                    panic!("unexpected stdout: {output:?}");
                }
                Event::Stderr(output) => {
                    panic!("unexpected stderr: {output:?}");
                }
                Event::Error(Error::IdleTimeout {
                    timeout: Timeout::Expired { .. },
                }) => {
                    // We'll get this multiple times.
                }
                Event::Error(error) => {
                    panic!("unexpected error: {error:?}");
                }
                Event::Exit(status) => {
                    check!(status.success());
                }
            }
        }

        check!(child.next_event().is_none());
        check!(child.next_event().is_none());
    }
}

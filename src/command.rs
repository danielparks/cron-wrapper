//! # Read output from child process as events
//!
//! This allows getting output from a child process on both stdout and stderr
//! as (mostly) in-order [`Event`]s in an iterator. This includes errors reading
//! or waiting for input, and the child exiting.
//!
//! ## Event ordering
//!
//! Events are only _mostly_ in order because there is an unavoidable race
//! condition involved in reading two or more streams. If the child process
//! writes to stdout and then immediately writes to stderr, it may be too fast
//! for the reading process to catch.

use crate::timeout::Timeout;
use bstr::ByteSlice;
use log::{debug, error, info, trace};
use popol::set_nonblocking;
use std::cmp;
use std::collections::VecDeque;
use std::convert::Into;
use std::ffi::OsString;
use std::fmt;
use std::io::{self, Read};
use std::os::unix::process::ExitStatusExt;
use std::path::Path;
use std::process;
use std::time::Duration;
use thiserror::Error;

/// Re-export [`kill()`] and [`Signal`] from [nix] for convenience.
///
/// [`kill()`]: https://docs.rs/nix/latest/nix/sys/signal/fn.kill.html
/// [`Signal`]: https://docs.rs/nix/latest/nix/sys/signal/enum.Signal.html
pub use nix::sys::signal::{kill, Signal};

/// Re-export [`Pid`] from [nix] for convenience.
///
/// [`Pid`]: https://docs.rs/nix/latest/nix/unistd/struct.Pid.html
pub use nix::unistd::Pid;

/// Re-export [`Result`] from [nix] for convenience.
///
/// [`Result`]: https://docs.rs/nix/latest/nix/type.Result.html
pub use nix::Result as NixResult;

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
    /// Child’s standard output stream.
    Stdout,

    /// Child’s standard error stream.
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
    /// Error originating specifically from [`process::Command::spawn()`] (not
    /// all of [`crate::command::Command::spawn()`]).
    #[error("Could not run command {command:?}: {error}")]
    Spawn {
        /// The executable.
        command: OsString,

        /// The error raised by [`process::Command::spawn()`].
        error: io::Error,
    },

    /// Error originating specifically from [`popol::Sources::poll()`].
    #[error("Error while waiting for input: {0}")]
    Poll(io::Error),

    /// Error originating specifically from [`process::Child::wait()`] or
    /// [`process::Child::try_wait()`].
    #[error("Error while waiting for child to exit: {0}")]
    Wait(io::Error),

    /// Error originating specifically from [`process::ChildStdout::read()`] or
    /// [`process::ChildStderr::read()`].
    #[error("Error reading from child {stream}: {error}")]
    Read {
        /// The error raised by the read call ([`process::ChildStdout::read()`]
        /// or [`process::ChildStderr::read()`]).
        error: io::Error,

        /// Which child stream was being read when the error occurred (stdout or
        /// stderr).
        stream: StreamType,
    },

    /// The idle timeout elapsed waiting for input in `poll()`.
    #[error("Timed out waiting for input after {:?}", timeout.elapsed_rounded())]
    IdleTimeout {
        /// Information about the timeout in the form of [`Timeout::Expired`].
        timeout: Timeout,
    },

    /// The run timeout elapsed.
    #[error("Run timed out after {:?}", timeout.elapsed_rounded())]
    RunTimeout {
        /// Information about the timeout in the form of [`Timeout::Expired`].
        timeout: Timeout,
    },
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

/// The state of a [`Child`].
///
/// This tracks what to do on the next call to [`Child::next_event()`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    /// Deal with events in the queue returned by [`Child::poll()`] or call
    /// [`Child::poll()`] again to get the next events.
    Polling,

    /// Read from a child output stream. This happens when the buffer was too
    /// small to read everything on the first call to [`Child::next_event()`].
    Reading(StreamType),

    /// All output streams have closed; all that’s left is to wait for the child
    /// to exit.
    Exiting,

    /// The child already exited. Nothing more to do; [`Child::next_event()`]
    /// should now always return `None`.
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
    const fn make_read(stream: StreamType, output: &'a [u8]) -> Self {
        match stream {
            StreamType::Stdout => Self::Stdout(output),
            StreamType::Stderr => Self::Stderr(output),
        }
    }

    /// Get the exit code from [`Event::Exit`].
    ///
    /// Note that this is _not_ the same as [`process::ExitStatus::code()`].
    /// That does not return exit codes generated by signals; this does in the
    /// same way that exit codes are reported in shells.
    ///
    /// All variants before [`Event::Exit`] return `None`.
    #[must_use]
    pub fn exit_code(&self) -> Option<i32> {
        if let Self::Exit(status) = self {
            // FIXME: broken on windows.
            status
                .code()
                // status.signal() shouldn’t be >32, but we use saturating_add()
                // just to be safe.
                .or_else(|| Some(status.signal()?.saturating_add(128)))
        } else {
            None
        }
    }
}

/// A running [`Command`].
#[derive(Debug)]
pub struct Child {
    /// Underlying [`process::Child`] object.
    process: process::Child,

    /// In progress run timeout. Should be [`Timeout::Never`] or
    /// [`Timeout::Pending`].
    run_timeout: Timeout,

    /// Configured idle timeout. Should be [`Timeout::Never`] or
    /// [`Timeout::Future`].
    idle_timeout: Timeout,

    /// Sources for polling.
    sources: popol::Sources<StreamType>,

    /// Internal events returned by polling.
    events: VecDeque<popol::Event<StreamType>>,

    /// The child’s stdout stream.
    stdout: process::ChildStdout,

    /// The child’s stderr stream.
    stderr: process::ChildStderr,

    /// The current state for [`Child::next_event()`].
    state: State,

    /// The buffer used to store the latest read from an child’s output stream.
    /// This is referenced from [`Event::Stdout`] and [`Event::Stderr`].
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
        Self {
            command: command.into(),
            args: args.into_iter().map(Into::into).collect(),
            run_timeout: Timeout::Never,
            idle_timeout: Timeout::Never,
            buffer_size: 4096,
        }
    }

    /// Set the command arguments
    ///
    /// ```rust
    /// use assert2::let_assert;
    /// use cron_wrapper::command::{Command, Event};
    ///
    /// let mut child = Command::new("/bin/echo", [])
    ///     .args(["hello", "world"])
    ///     .spawn()
    ///     .unwrap();
    /// let_assert!(Some(Event::Stdout(b"hello world\n")) = child.next_event());
    /// ```
    pub fn args<S, I>(&mut self, args: I) -> &mut Self
    where
        S: Into<OsString>,
        I: IntoIterator<Item = S>,
    {
        self.args = args.into_iter().map(Into::into).collect();
        self
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
    /// # Errors
    ///
    /// May return [`Error::Spawn`].
    pub fn spawn(&self) -> Result<Child, Error> {
        let command = self.command.clone();
        let args = &self.args;
        let run_timeout = self.run_timeout.start();
        let idle_timeout = self.idle_timeout.clone();

        info!("Start: {}", self.command_line_sh());
        debug!("run timeout {run_timeout}, idle timeout {idle_timeout}");

        let mut process = process::Command::new(&command)
            .args(args)
            .stdout(process::Stdio::piped())
            .stderr(process::Stdio::piped())
            .spawn()
            .map_err(|error| Error::Spawn { command, error })?;

        debug!("child process id: {}", process.id());

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

    /// Get the executable as a [`Path`].
    #[must_use]
    pub fn command_as_path(&self) -> &Path {
        self.command.as_ref()
    }

    /// Get the command line to run as an iterator over words.
    #[must_use]
    pub const fn command_line(&self) -> WordIterator {
        WordIterator {
            command: self,
            iter: None,
        }
    }

    /// Get the command line to run escaped for the shell.
    ///
    /// Note that this uses a lossy conversion of `OsString` to String.
    #[must_use]
    pub fn command_line_sh(&self) -> String {
        shell_words::join(
            self.command_line()
                .map(|arg| arg.to_string_lossy().into_owned()),
        )
    }
}

impl Child {
    /// Get the child’s process ID.
    #[must_use]
    pub fn id(&self) -> u32 {
        self.process.id()
    }

    /// Get the child’s process ID as a [`Pid`]. This is useful when working
    /// with [nix].
    ///
    /// # Panics
    ///
    /// This will panic if it can’t convert the child PID from `u32` to `i32`,
    /// which should never happen.
    #[must_use]
    pub fn pid(&self) -> Pid {
        Pid::from_raw(self.id().try_into().unwrap())
    }

    /// Get a reference to the underlying [`process::Child`] for the child.
    ///
    /// ```rust
    /// use cron_wrapper::command::Command;
    ///
    /// let mut child = Command::new("/bin/echo", ["hello"]).spawn().unwrap();
    /// assert!(child.process().id() > 0);
    /// ```
    #[must_use]
    pub const fn process(&self) -> &process::Child {
        &self.process
    }

    /// Get a mutable reference to the underlying [`process::Child`] for
    /// the child.
    ///
    /// # Using [`process::Child::kill()`]:
    ///
    /// ```rust
    /// use assert2::{check, let_assert};
    /// use cron_wrapper::command::{Command, Event};
    ///
    /// let mut child = Command::new("/bin/sleep", ["100"]).spawn().unwrap();
    /// child.process_mut().kill().unwrap();
    ///
    /// let_assert!(Some(Event::Exit(status)) = child.next_event());
    /// check!(!status.success());
    /// ```
    ///
    /// # Using [`process::Child::wait()`]:
    ///
    /// ```rust
    /// use cron_wrapper::command::{Command, Event};
    ///
    /// let mut child = Command::new("/bin/echo", ["hello"]).spawn().unwrap();
    /// assert!(child.process_mut().wait().unwrap().success());
    /// ```
    #[must_use]
    pub fn process_mut(&mut self) -> &mut process::Child {
        &mut self.process
    }

    /// Send a signal to the child. See [`nix::sys::signal::kill()`].
    ///
    /// ```rust
    /// use assert2::{check, let_assert};
    /// use cron_wrapper::command::{Command, Event, Signal};
    ///
    /// let mut child = Command::new("/bin/sleep", ["100"]).spawn().unwrap();
    /// child.kill(Signal::SIGKILL).unwrap();
    ///
    /// let_assert!(Some(Event::Exit(status)) = child.next_event());
    /// check!(!status.success());
    /// ```
    ///
    /// # Errors
    ///
    /// This could return errors for reasons that [`kill(2)` might return
    /// errors](https://man7.org/linux/man-pages/man2/kill.2.html#ERRORS). In
    /// practise this means that it will return an error if you try to use it
    /// after the child process has exited and been cleaned up by `next_event()`
    /// or `process_mut().wait()`.
    ///
    /// ```rust
    /// use cron_wrapper::command::{Command, Signal};
    ///
    /// let mut child = Command::new("/bin/test", ["1"]).spawn().unwrap();
    /// child.process_mut().wait().unwrap();
    ///
    /// child.kill(Signal::SIGKILL).unwrap_err();
    /// ```
    pub fn kill<S: Into<Option<Signal>>>(
        &mut self,
        signal: S,
    ) -> NixResult<()> {
        kill(self.pid(), signal)
    }

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
    ///
    /// ```rust
    /// use assert2::{check, let_assert};
    /// use cron_wrapper::command::{Command, Event};
    ///
    /// let mut child = Command::new("/bin/echo", ["hello"]).spawn().unwrap();
    /// let_assert!(Some(Event::Stdout(b"hello\n")) = child.next_event());
    /// let_assert!(Some(Event::Exit(status)) = child.next_event());
    /// check!(status.success());
    /// let_assert!(None = child.next_event());
    /// ```
    pub fn next_event(&mut self) -> Option<Event<'_>> {
        // FIXME? this sometimes messes up the order if stderr and stdout are
        // used in the same line. Not sure this is possible to fix.

        // Are we still reading?
        if let State::Reading(stream) = self.state {
            match self.read(stream) {
                Ok(0) => {
                    // This should have been set by `read()`, but if it didn’t
                    // we could end up at `unreachable!()` below, so we set it
                    // here ot be sure.
                    self.state = State::Polling;
                }
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
                        Ok(0) => {
                            // This should have been set by `read()`, but if it
                            // didn’t we could end up at `unreachable!()` below,
                            // so we set it here ot be sure.
                            self.state = State::Polling;
                        }
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
            match self.wait() {
                Ok(status) => Some(Event::Exit(status)),
                Err(error) => Some(Event::Error(error)),
            }
        } else if self.state == State::Exited {
            None
        } else {
            unreachable!("state is {:?}", self.state);
        }
    }

    /// Wait for the child process to exit.
    ///
    /// This honors timeouts, including [`Command::idle_timeout()`].
    ///
    /// This does a busy wait if a timeout is set since otherwise we’d have to
    /// use a signal, and that could interrupt other threads.
    ///
    /// # Errors
    ///
    /// This may return [`Error::Wait`], [`Error::IdleTimeout`], or
    /// [`Error::RunTimeout`].
    pub fn wait(&mut self) -> Result<process::ExitStatus, Error> {
        let original_timeout = cmp::min(&self.run_timeout, &self.idle_timeout);
        trace!(
            "wait() with timeout {original_timeout} (run timeout {})",
            self.run_timeout
        );

        if original_timeout.is_never() {
            // No timeout, so we can use the normal wait() call.
            let status = self.process.wait().map_err(Error::Wait)?;
            self.state = State::Exited;
            return Ok(status);
        }

        // If this is an overall run timeout, starting it again will just return
        // a clone of it.
        let timeout = original_timeout.start();

        // wait() does this internally, but try_wait() does not.
        drop(self.process.stdin.take());

        loop {
            // Check for time out.
            if let Some(expired) = timeout.check_expired() {
                return Err(timeout_error(original_timeout, expired));
            }

            // Check for child process exit.
            match self.process.try_wait().map_err(Error::Wait)? {
                Some(status) => {
                    self.state = State::Exited;
                    return Ok(status);
                }
                None => {
                    // FIXME: busy wait. Could use a signal? Could sleep for
                    // longer?
                    // FIXME: the timeout comparison doesn’t round, so if it’s
                    // within a 1ms of the timeout it will exit.
                    std::thread::yield_now();
                }
            }
        }
    }

    /// Wait for input.
    ///
    /// This wrapper around [`popol::Sources::poll()`] handles timeouts longer
    /// than [`POLL_MAX_TIMEOUT`].
    ///
    /// If `events` is not empty this will do nothing, not even check if the
    /// timeout is expired.
    ///
    /// # Errors
    ///
    /// May return [`Error::Poll`], [`Error::IdleTimeout`], or
    /// [`Error::RunTimeout`].
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
                    return Err(Error::Poll(error));
                }
            }
        }

        Ok(())
    }

    /// Read from the child’s stdout or stderr.
    ///
    /// Fills `self.buffer` and returns the number of bytes written or an error.
    ///
    /// # Errors
    ///
    /// May return [`Error::Read`].
    fn read(&mut self, stream: StreamType) -> Result<usize, Error> {
        self.state = State::Reading(stream);

        // Loop is only for the case where the read() get EINTR.
        loop {
            let result = match stream {
                StreamType::Stdout => self.stdout.read(&mut self.buffer),
                StreamType::Stderr => self.stderr.read(&mut self.buffer),
            };

            return match result {
                Ok(count) => {
                    trace!(
                        "{stream:?}: read {count} bytes: {:?}",
                        &self.buffer[..count].as_bstr()
                    );

                    if count != self.buffer.len() {
                        // read() didn’t fill the buffer, so we should check any
                        // other events poll() returned and then try poll()
                        // again. We could try reading again, but if there was
                        // already data available on another stream and then
                        // data was added to the current stream then we would
                        // read it out of order.
                        self.state = State::Polling;
                    }

                    Ok(count)
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    // Done reading.
                    trace!("{stream:?}: io::ErrorKind::WouldBlock");
                    self.state = State::Polling;
                    Ok(0)
                }
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {
                    // Try again.
                    trace!("{stream:?}: io::ErrorKind::Interrupted");
                    continue;
                }
                Err(error) => Err(Error::Read { error, stream }),
            };
        }
    }
}

/// An iterator that produces the words in the command line.
pub struct WordIterator<'a> {
    /// The [`Command`] we’re getting the command line for.
    command: &'a Command,

    /// Iterator state:
    ///
    /// * `None`: next is the command itself.
    /// * `Some(iter)`: use `iter` (which points to `self.command.args`).
    iter: Option<std::slice::Iter<'a, OsString>>,
}

impl<'a> Iterator for WordIterator<'a> {
    type Item = &'a OsString;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut iter) = self.iter {
            iter.next()
        } else {
            // First element: command.
            self.iter = Some(self.command.args.iter());
            Some(&self.command.command)
        }
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
    use assert2::{assert, check, let_assert};
    use std::time::{Duration, Instant};

    #[test]
    fn echo_ok() {
        let mut child = Command::new("/bin/echo", ["ok"]).spawn().unwrap();

        let mut count = 0;
        while let Some(event) = child.next_event() {
            #[allow(clippy::arithmetic_side_effects)] // See assert
            match event {
                Event::Stdout(output) => {
                    check!(output == b"ok\n");
                    assert!(count < 10, "expected only 1 line of output");
                    count += 1;
                }
                Event::Stderr(output) => {
                    panic!("unexpected stderr: {output:?}")
                }
                Event::Error(error) => panic!("unexpected error: {error:?}"),
                Event::Exit(status) => {
                    check!(status.success());
                    check!(Some(0) == event.exit_code());
                }
            }
        }

        check!(count == 1, "expected only 1 line of output");

        check!(child.next_event().is_none());
        check!(child.next_event().is_none());
    }

    #[test]
    fn killed() {
        let mut child = Command::new("/bin/sleep", ["1"]).spawn().unwrap();
        child.process_mut().kill().expect("killing child");

        while let Some(event) = child.next_event() {
            match event {
                Event::Stdout(output) => {
                    panic!("unexpected stdout: {output:?}");
                }
                Event::Stderr(output) => {
                    panic!("unexpected stderr: {output:?}")
                }
                Event::Error(error) => panic!("unexpected error: {error:?}"),
                Event::Exit(status) => {
                    check!(!status.success());
                    // Child should return 128 + SIGKILL:
                    check!(Some(137) == event.exit_code());
                }
            }
        }

        check!(child.next_event().is_none());
        check!(child.next_event().is_none());
    }

    #[test]
    fn run_timeout() {
        let mut child = Command::new("/bin/sleep", ["1"])
            .run_timeout(Duration::from_millis(500))
            .spawn()
            .unwrap();

        let mut count = 0;
        while let Some(event) = child.next_event() {
            #[allow(clippy::arithmetic_side_effects)] // See count += 1
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
    fn idle_timeout() {
        let mut child = Command::new("/bin/sleep", ["1"])
            .idle_timeout(Duration::from_millis(10))
            .spawn()
            .unwrap();

        let mut count = 0;
        while let Some(event) = child.next_event() {
            #[allow(clippy::arithmetic_side_effects)] // See assert
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
                    assert!(count < 1000, "expected around 100 idle timeouts");
                    count += 1;
                }
                Event::Error(error) => {
                    panic!("unexpected error: {error:?}");
                }
                Event::Exit(status) => {
                    check!(status.success());
                    check!(Some(0) == event.exit_code());
                }
            }
        }

        check!(count > 50, "expected around 100 idle timeouts");
        check!(count < 150, "expected around 100 idle timeouts");

        check!(child.next_event().is_none());
        check!(child.next_event().is_none());
    }

    #[test]
    fn wait_no_timeout() {
        let start = Instant::now();
        let mut child = Command::new("/bin/sleep", ["0.01"]).spawn().unwrap();

        let_assert!(Ok(status) = child.wait());
        check!(status.success());

        let_assert!(Ok(status) = child.wait());
        check!(status.success());

        check!(start.elapsed() < Duration::from_millis(19));
    }

    #[test]
    fn wait_idle_timeout() {
        let start = Instant::now();
        let mut child = Command::new("/bin/sleep", ["0.02"])
            .idle_timeout(Duration::from_millis(15))
            .spawn()
            .unwrap();

        let_assert!(Err(Error::IdleTimeout { .. }) = child.wait());
        check!(start.elapsed() < Duration::from_millis(20));

        let_assert!(Ok(status) = child.wait());
        check!(status.success());
        check!(start.elapsed() >= Duration::from_millis(20));
    }

    #[test]
    fn wait_run_timeout() {
        let start = Instant::now();
        let mut child = Command::new("/bin/sleep", ["0.02"])
            .run_timeout(Duration::from_millis(15))
            .spawn()
            .unwrap();

        let_assert!(Err(Error::RunTimeout { .. }) = child.wait());
        check!(start.elapsed() < Duration::from_millis(20));

        let_assert!(Err(Error::RunTimeout { .. }) = child.wait());
        check!(start.elapsed() < Duration::from_millis(20));
    }
}

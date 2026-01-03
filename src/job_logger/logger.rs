//! Code to generate a structured log.

use crate::command::{Child, Command, Event};
use crate::job_logger::{Kind, TrailingNewline};
use log::info;
use std::cell::RefCell;
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;
use termcolor::WriteColor;
use thiserror::Error;
use time::OffsetDateTime;
use time::format_description::well_known::{Iso8601, iso8601};

/// Date and time format to use in log file names.
const FILE_NAME_DATE_FORMAT: iso8601::EncodedConfig = iso8601::Config::DEFAULT
    .set_time_precision(iso8601::TimePrecision::Second { decimal_digits: None })
    .encode();

/// An object to optionally log all [`Event`]s from a [`Child`] to a file.
///
/// Example output format:
///
/// ```text
/// Command: ["my-script.sh", "arg1", "arg2"]
/// Start: 2023-05-15T18:31:41.509380000-07:00
///
/// +0.000 out foo bar hey
///            next line whatever
/// +0.010 err NOTICE bar hey
/// +0.100 out mixed \
/// +0.200 out .\
/// +0.340 ERROR IdleTimeout { timeout: Expired { requested: 110ms, actual: 109.566826ms } }
/// ```
#[derive(Debug)]
pub struct JobLogger {
    /// Destinations to which to send logs.
    destinations: Vec<Destination>,

    /// [`Instant`] when the job started, so we can get the elapsed time.
    start_instant: Instant,

    /// [`OffsetDateTime`] when the job started, so we know the absolute time
    /// when the job started.
    start_time: OffsetDateTime,

    /// The [`Command`] used by the job. This is used to name the log file (for
    /// [`Destination::Directory`]) and write the header for the log file.
    ///
    /// This should be set, but it’s convenient to make this optional so that
    /// the job logger can be initialized before the job.
    command: Option<Command>,

    /// The PID of the child process. This is used to name the log file (for
    /// [`Destination::Directory`]).
    ///
    /// This should be set, but it’s convenient to make this optional so that
    /// the job logger can be initialized before the job is started.
    child_id: Option<u32>,

    /// Track what the [`JobLogger`] has already written.
    state: State,
}

/// Errors raised by [`JobLogger`].
#[derive(Debug, Error)]
pub enum Error {
    /// Error formatting date time for metadata or log file name.
    #[error("Error formatting date time: {0}")]
    DateTimeFormat(#[from] time::error::Format),

    /// Some sort of IO error creating a uniquely named log file.
    ///
    /// This will never have a [`io::ErrorKind::AlreadyExists`] error, since
    /// we only return these errors when creating a log file within a directory
    /// ([`Destination::Directory`]). In that case we try multiple times to find
    /// a unique log file name and if we go over a maximum number of attempts
    /// we return [`Error::TooManyAttemptsCreatingUniqueLog`].
    #[error("Could not create unique log file {path:?}: {error}")]
    CreatingLog {
        /// The path for the last log file that failed.
        path: PathBuf,

        /// The error that occurred.
        error: io::Error,
    },

    /// Maxed out attempts at finding a unique log file name.
    #[error(
        "Could not create unique log file after {attempts} attempts. \
        Last: {last:?}"
    )]
    TooManyAttemptsCreatingUniqueLog {
        /// How many names were attempted.
        attempts: usize,

        /// The path that was last attempted.
        last: PathBuf,
    },

    /// Some sort of IO error while writing to a log.
    #[error("Error writing to log {destination}: {error}")]
    WritingLog {
        /// String returned by [`Destination::error_description()`].
        destination: String,

        /// The error that occurred.
        error: io::Error,
    },
}

impl Default for JobLogger {
    fn default() -> Self {
        Self::none()
    }
}

impl JobLogger {
    /// Create a new job logger that will silently discard all logs.
    #[must_use]
    pub fn none() -> Self {
        Self {
            destinations: vec![],
            start_instant: Instant::now(),
            start_time: OffsetDateTime::now_local()
                .unwrap_or_else(|_| OffsetDateTime::now_utc()),
            command: None,
            child_id: None,
            state: State::Initial,
        }
    }

    /// Create a new job logger that will store the log in a new file in the
    /// passed directory.
    ///
    /// The directory must already exist.
    pub fn new_in_directory<P: Into<PathBuf>>(path: P) -> Self {
        let mut job_logger = Self::none();
        job_logger.add_destination(Destination::Directory(path.into()));
        job_logger
    }

    /// Create a new job logger that will store the log in the passed file.
    ///
    /// This opens the file for writing immediately. If the file already exists
    /// it will be overwritten.
    ///
    /// # Errors
    ///
    /// This returns an [`io::Error`] if there is a problem opening `path` for
    /// writing.
    pub fn new_file<P: Into<PathBuf>>(path: P) -> io::Result<Self> {
        let mut job_logger = Self::none();
        let path = path.into();
        let file = fs::File::create(&path)?; // Truncates if it already exists.
        job_logger.add_destination(Destination::File { path, file });
        Ok(job_logger)
    }

    /// Add a destination
    pub fn add_destination(&mut self, destination: Destination) -> &Self {
        self.destinations.push(destination);
        self
    }

    /// Ensure initialization is done.
    ///
    /// This is called on every write, but does nothing after the first call. It
    /// creates log files for all [`Destination::Directory`]s, and writes the
    /// metadata header.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t create a log file, e.g. if there
    /// is a [`Destination::Directory`], or if it can’t write the log metadata
    /// header to all destinations.
    pub fn initialize(&mut self) -> Result<(), Error> {
        if self.state != State::Initial {
            return Ok(());
        }

        // Prevent this from being called from within itself.
        self.state = State::Metadata;

        let mut todo = Vec::new();
        for (i, destination) in self.destinations.iter().enumerate() {
            if let Destination::Directory(path) = destination {
                todo.push((i, path.clone()));
            }
        }

        for (i, path) in todo {
            info!("Saving job output to {path:?}");
            self.destinations[i] = self.create_file_in_directory(&path)?;
        }

        self.write_file_header()?;

        Ok(())
    }

    /// Get the paths to any log files, if available.
    ///
    /// You may wish to call [`Self::initialize()`] first to make sure that
    /// the file has been created. If the logger was created by
    /// [`Self::new_in_directory()`] but nothing has been logged, then the file
    /// will not have been created and this will return an empty `Vec`.
    #[must_use]
    pub fn paths(&self) -> Vec<&PathBuf> {
        self.destinations
            .iter()
            .filter_map(|destination| {
                if let Destination::File { path, .. } = &destination {
                    Some(path)
                } else {
                    None
                }
            })
            .collect()
    }

    /// Record the [`Command`] to run.
    pub fn set_command(&mut self, command: &Command) {
        self.command = Some(command.clone());
    }

    /// Record the PID of the [`Child`] that was spawned.
    pub fn set_child(&mut self, child: &Child) {
        self.child_id = Some(child.id());
    }

    /// Log an error originating in cron-wrapper, not an [`Event::Error`].
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to the log.
    pub fn log_wrapper_error(
        &mut self,
        error: &anyhow::Error,
    ) -> Result<(), Error> {
        self.write_record(Kind::WrapperError, error.to_string().as_bytes())
    }

    /// Log an [`Event`] received from the [`Child`].
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to the log.
    pub fn log_event(&mut self, event: &Event) -> Result<(), Error> {
        match &event {
            Event::Combined(output) => {
                self.write_record(Kind::Combined, output)
            }
            Event::Stdout(output) => self.write_record(Kind::Stdout, output),
            Event::Stderr(output) => self.write_record(Kind::Stderr, output),
            Event::Exit(_) => {
                if let Some(code) = event.exit_code() {
                    self.write_record(Kind::Exit, code.to_string().as_bytes())
                } else {
                    self.write_record(Kind::Exit, b"none")
                }
            }
            Event::Error(error) => {
                self.write_record(Kind::Error, error.to_string().as_bytes())
            }
        }
    }

    /// Private: write standard header to log file.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to the log.
    fn write_file_header(&mut self) -> Result<(), Error> {
        if let Some(command) = &self.command {
            let full_command = command.command_line().collect::<Vec<_>>();
            self.write_metadata(
                "Command",
                format!("{full_command:?}").as_bytes(),
            )?;
        }

        let start = self.start_time.format(&Iso8601::DEFAULT)?;
        self.write_metadata("Start", start.as_bytes())
    }

    /// Private: write a record in the log file.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to the log.
    fn write_record(&mut self, kind: Kind, value: &[u8]) -> Result<(), Error> {
        if self.state == State::Initial {
            self.initialize()?;
        }

        if self.state == State::Metadata {
            self.write_all(b"\n")?;
            self.state = State::Records;
        }

        let time = format!("{:.3}", self.elapsed());
        let indent = time.len().checked_add(5).expect("indent too large");

        let mut buffer = Vec::with_capacity(
            time.len()
                .checked_add(kind.as_bytes().len())
                .expect("buffer too large")
                .checked_add(value.len())
                .expect("buffer too large")
                .checked_add(5)
                .expect("buffer too large"),
        );
        buffer.extend_from_slice(time.as_bytes());

        buffer.push(b' ');
        buffer.extend_from_slice(kind.as_bytes());
        buffer.push(b' ');
        self.write_all(&buffer)?;

        self.write_value(kind, value, indent)
    }

    /// Private: write a metadata line to the top of the log file.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to the log.
    fn write_metadata(&mut self, key: &str, value: &[u8]) -> Result<(), Error> {
        // FIXME? Should this be an error?
        assert!(
            self.state == State::Metadata,
            "Tried to write metadata after a record."
        );

        let mut buffer = Vec::with_capacity(
            key.len()
                .checked_add(value.len())
                .expect("buffer too large")
                .checked_add(2 + 1)
                .expect("buffer too large"),
        );
        buffer.extend_from_slice(key.as_bytes());
        buffer.extend_from_slice(b": ");
        self.write_all(&buffer)?;

        let output = escape_value(value, 4, TrailingNewline::Explicit);
        self.write_all(&output)?;

        Ok(())
    }

    /// Private: write value for metadata or record including trailing newline.
    ///
    /// Returns `Ok(true)` if the input ended with a newline.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to the log.
    fn write_value(
        &mut self,
        kind: Kind,
        input: &[u8],
        indent: usize,
    ) -> Result<(), Error> {
        let output = escape_value(input, indent, kind.newline_behavior());

        let mut color = termcolor::ColorSpec::new();
        color.set_intense(true);

        if kind.is_any_error() {
            color.set_fg(Some(termcolor::Color::Red));
        } else {
            color.set_fg(Some(termcolor::Color::White));
        }

        self.set_color(&color)?;
        self.write_all(&output)?;
        self.reset_color()?;

        Ok(())
    }

    /// Private: write raw data to everything in `self.destinations`.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t write to one of the destinations.
    fn write_all(&mut self, data: &[u8]) -> Result<(), Error> {
        self.initialize()?;

        // FIXME? apply to all destinations even if one returns an error?
        for destination in &mut self.destinations {
            destination
                .write_all(data)
                .map_err(|error| Error::WritingLog {
                    destination: destination.error_description(),
                    error,
                })?;
        }

        Ok(())
    }

    /// Private: Set the color of the output if the destination supports it.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t set the color for one of the
    /// destinations that should support it.
    fn set_color(&mut self, spec: &termcolor::ColorSpec) -> Result<(), Error> {
        self.initialize()?;

        // FIXME? apply to all destinations even if one returns an error?
        for destination in &mut self.destinations {
            destination
                .set_color(spec)
                .map_err(|error| Error::WritingLog {
                    destination: destination.error_description(),
                    error,
                })?;
        }

        Ok(())
    }

    /// Private: Reset the color of the output if the destination supports it.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t reset the color for one of the
    /// destinations that should support it.
    fn reset_color(&mut self) -> Result<(), Error> {
        self.initialize()?;

        // FIXME? apply to all destinations even if one returns an error?
        for destination in &mut self.destinations {
            destination.reset().map_err(|error| Error::WritingLog {
                destination: destination.error_description(),
                error,
            })?;
        }

        Ok(())
    }

    /// Private: create a log file in a given directory.
    ///
    /// # Errors
    ///
    /// This will return an error if it can’t create a log file. It will add a
    /// number to the log file name (before the “.log” extension) and increase
    /// the number until it finds an available name, or after 100 tries.
    ///
    /// It could also return an error if it fails to format the date and time.
    fn create_file_in_directory(
        &self,
        directory: &Path,
    ) -> Result<Destination, Error> {
        /// We only try up to 100 times to create a log file. Since log files
        /// are named with a timestamp and a process ID, this should be way more
        /// than enough.
        const MAX_ATTEMPTS: usize = 100;

        let base = self.generate_file_name_base()?;
        let mut number = String::new();
        let mut file_name = OsString::with_capacity(
            base.len().checked_add(4).expect("buffer too large"),
        );
        let mut path = PathBuf::new();

        // The first attempt won‘t have a number in the file name, and each
        // loop preps the number for the next loop. Thus, the last loop will
        // attempt the file name with number MAX_ATTEMPTS - 1.
        for i in 1..=MAX_ATTEMPTS {
            file_name.clear();
            file_name.push(&base);
            file_name.push(number);
            file_name.push(".log");

            path = directory.join(&file_name);
            match exclusive_create_file(&path) {
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
                    number = format!(".{i}");
                }
                Ok(file) => return Ok(Destination::File { path, file }),
                Err(error) => return Err(Error::CreatingLog { path, error }),
            }
        }

        Err(Error::TooManyAttemptsCreatingUniqueLog {
            attempts: MAX_ATTEMPTS,
            last: path,
        })
    }

    /// Private: generate the first part of a file name for a log.
    ///
    /// # Errors
    ///
    /// This will return an error if it fails to format the date and time.
    fn generate_file_name_base(&self) -> Result<OsString, time::error::Format> {
        let mut file_name = OsString::from(
            self.start_time.format(&Iso8601::<FILE_NAME_DATE_FORMAT>)?,
        );

        let bin_name = self
            .command
            .as_ref()
            .and_then(|command| command.command_as_path().file_name());

        if let Some(bin_name) = bin_name {
            file_name.push(".");
            file_name.push(bin_name);
        }

        if let Some(child_id) = self.child_id {
            file_name.push(".");
            file_name.push(child_id.to_string());
        }

        Ok(file_name)
    }

    /// Private: get the seconds elapsed on the run.
    fn elapsed(&self) -> f64 {
        self.start_instant.elapsed().as_secs_f64()
    }
}

/// Create a file; fail if it already exists.
///
/// # Errors
///
/// It will return an error if the file already exists, or if there was some
/// other reason it could not create the file.
fn exclusive_create_file(path: &Path) -> io::Result<fs::File> {
    fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
}

/// Where logs should go.
pub enum Destination {
    /// Create a file in the passed directory once we receive our first log.
    Directory(PathBuf),

    /// An open file.
    File {
        /// Path to file.
        path: PathBuf,

        /// The actual open file.
        file: fs::File,
    },

    /// A stream, e.g. stdout.
    Stream(Rc<RefCell<dyn io::Write>>),

    /// A stream that might accept color, e.g. stdout.
    ColorStream(Rc<RefCell<dyn WriteColor>>),
}

impl Destination {
    /// Describe the destination for an error message.
    #[must_use]
    pub fn error_description(&self) -> String {
        match self {
            Self::Directory(path) => format!("directory {path:?}"),
            Self::File { path, .. } => format!("file {path:?}"),
            Self::Stream(_) | Self::ColorStream(_) => "stream".to_owned(),
        }
    }
}

impl fmt::Debug for Destination {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Directory(path) => f
                .debug_tuple("Destination::Directory")
                .field(&path)
                .finish(),
            Self::File { path, file } => f
                .debug_struct("Destination::File")
                .field("path", &path)
                .field("file", &file)
                .finish(),
            Self::Stream(_) => f.write_str("Destination::Stream(_)"),
            Self::ColorStream(_) => f.write_str("Destination::ColorStream(_)"),
        }
    }
}

impl io::Write for Destination {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        match self {
            Self::Directory(_) => {
                panic!(
                    "Cannot write to Destination::Directory. Use \
                    into_writable() to get a writable destination."
                );
            }
            Self::File { file, .. } => file.write(buffer),
            Self::Stream(writer) => writer.borrow_mut().write(buffer),
            Self::ColorStream(writer) => writer.borrow_mut().write(buffer),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Directory(_) => {
                panic!(
                    "Cannot write to Destination::Directory. Use \
                    into_writable() to get a writable destination."
                );
            }
            Self::File { file, .. } => file.flush(),
            Self::Stream(writer) => writer.borrow_mut().flush(),
            Self::ColorStream(writer) => writer.borrow_mut().flush(),
        }
    }
}

impl WriteColor for Destination {
    fn supports_color(&self) -> bool {
        if let Self::ColorStream(writer) = self {
            writer.borrow().supports_color()
        } else {
            false
        }
    }

    fn set_color(&mut self, spec: &termcolor::ColorSpec) -> io::Result<()> {
        if let Self::ColorStream(writer) = self {
            writer.borrow_mut().set_color(spec)
        } else {
            Ok(())
        }
    }

    fn reset(&mut self) -> io::Result<()> {
        if let Self::ColorStream(writer) = self {
            writer.borrow_mut().reset()
        } else {
            Ok(())
        }
    }

    fn is_synchronous(&self) -> bool {
        if let Self::ColorStream(writer) = self {
            writer.borrow().is_synchronous()
        } else {
            false
        }
    }
}

/// Private: escape value for metadata or record in the output buffer.
///
/// This always ends output with a newline. It will treat a trailing newline
/// in `input` differently depending on the [`TrailingNewline`] value passed.
fn escape_value(
    input: &[u8],
    indent: usize,
    newline: TrailingNewline,
) -> Vec<u8> {
    // FIXME: maybe this should be a little larger than `input.len()`?
    let mut output: Vec<u8> = Vec::with_capacity(input.len());

    if let Some((&last, input)) = input.split_last() {
        let indent = b" ".repeat(indent);
        for &b in input {
            escape_byte_into(b, &mut output);
            if b == b'\n' {
                output.extend_from_slice(&indent);
            }
        }

        escape_byte_into(last, &mut output);

        if last == b'\n' {
            if newline == TrailingNewline::Explicit {
                output.extend_from_slice(&indent);
                // Must end with a newline.
                output.push(b'\n');
            }
            return output;
        }
    }

    // Input was empty, or otherwise didn’t end with a newline.
    if newline == TrailingNewline::Implicit {
        output.push(b'\\');
    }
    output.push(b'\n');

    output
}

/// Private: escape a byte in a value (metadata or event).
///
/// # Panics
///
/// This has an `unwrap()` call, but `write!` should never fail when writing to
/// a buffer.
#[inline]
fn escape_byte_into(input: u8, output: &mut Vec<u8>) {
    match input {
        // Backspace
        0x08 => output.extend_from_slice(b"\\b"),

        // Carriage return
        b'\r' => output.extend_from_slice(b"\\r"),

        // Newline and tab pass through
        b'\n' | b'\t' => output.push(input),

        // Other control characters are hex-escaped, e.g. \0x7f for DEL
        0..=0x1f | 0x7f => write!(output, "\\x{input:02x}").unwrap(),

        // Backslash
        b'\\' => output.extend_from_slice(b"\\\\"),

        // Pass through
        b => output.push(b),
    }
}

/// The current state of the [`JobLogger`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum State {
    /// Initial state; no metadata written or `Destination`s converted.
    Initial,

    /// `Destination`s have all been converted to writable; writing metadata.
    Metadata,

    /// Writing event records.
    Records,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::command;
    use crate::timeout::Timeout;
    use anyhow::anyhow;
    use assert2::check;
    use bstr::ByteSlice;
    use regex::{Regex, bytes};
    use std::os::unix::process::ExitStatusExt;
    use std::process::ExitStatus;
    use std::time::Duration;
    use tempfile::tempdir;

    /// Process special matchers in regular expression:
    ///
    ///   * <date> becomes \d{4}-\d{2}-\d{2}
    ///   * <time> becomes \d{2}:\d{2}:\d{2}-\d{2}:\d{2}
    ///   * <time+> becomes \d{2}:\d{2}:\d{2}\.\d+-\d{2}:\d{2}
    ///   * \d becomes [0-9]
    fn expand_re(re: &str) -> String {
        re.replace("<date>", r"\d{4}-\d{2}-\d{2}")
            .replace("<time>", r"\d{2}:\d{2}:\d{2}(Z|-\d{2}:\d{2})")
            .replace("<time+>", r"\d{2}:\d{2}:\d{2}\.\d+(Z|-\d{2}:\d{2})")
            .replace(r"\d", "[0-9]")
    }

    /// Check the log file name for a logger.
    ///
    /// re can include special matchers:
    ///   * <date> becomes [0-9]{4}-[0-9]{2}-[0-9]{2}
    ///   * <time> becomes [0-9]{2}:[0-9]{2}:[0-9]{2}-[0-9]{2}:[0-9]{2}
    fn check_file_name(logger: &JobLogger, re: &str) {
        for path in logger.paths() {
            check!(path.exists());
            let file_name =
                path.file_name().expect("log file path is not a file");
            let file_name = file_name.to_string_lossy();
            let re = Regex::new(&expand_re(re)).unwrap();
            check!(
                re.is_match(file_name.as_ref()),
                "log file name {file_name:?} does not match {re:?}"
            );
        }
    }

    /// Create an `IdleTimeout` error event.
    const fn event_idle_timeout() -> Event<'static> {
        Event::Error(command::Error::IdleTimeout {
            timeout: Timeout::Expired {
                requested: Duration::ZERO,
                actual: Duration::ZERO,
            },
        })
    }

    /// Create an exit event.
    fn event_exit(code: i32) -> Event<'static> {
        Event::Exit(ExitStatus::from_raw(code))
    }

    /// Make a `JobLogger` that outputs to a buffer.
    fn make_buffer_logger() -> (JobLogger, Rc<RefCell<Vec<u8>>>) {
        let output = Rc::new(RefCell::new(Vec::with_capacity(1024)));

        let mut logger = JobLogger::none();
        logger.add_destination(Destination::Stream(output.clone()));
        check!(logger.paths().is_empty());

        (logger, output)
    }

    /// Check the output buffer against a regex.
    fn check_output(output: &Rc<RefCell<Vec<u8>>>, re: &str) {
        let output = output.borrow();
        let re = bytes::Regex::new(&expand_re(re)).unwrap();

        check!(!output.contains(&0u8));
        check!(
            re.is_match(&output),
            r#"output "{}" does not match "{re:?}""#,
            output.as_bstr()
        );
    }

    #[test]
    fn none_logger() {
        let mut logger = JobLogger::none();
        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());
    }

    #[test]
    fn stream_logger() {
        let (mut logger, output) = make_buffer_logger();

        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check!(logger.paths().is_empty());

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.000 out abc
        //     0.000 WRAPPER-ERROR uh oh
        //
        check_output(
            &output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} WRAPPER-ERROR uh oh\n$",
        );
    }

    #[test]
    fn stream_logger_escapes() {
        let (mut logger, output) = make_buffer_logger();

        check!(
            logger
                .log_event(&Event::Stdout(
                    b"tab:\t backslash:\\ esc:\x1b 0:\0 CR:\r LF:\n \
                backspace:\x08 del:\x1f done"
                ))
                .is_ok()
        );

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.001 out tab:	 backslash:\\ esc:\x1b 0:\x00 CR:\r LF:
        //                backspace:\b del:\x1f done\
        //
        check_output(
            &output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out tab:\t backslash:\\\\\\\\ esc:\\\\x1b 0:\\\\x00 CR:\\\\r LF:\n\
            [ ]          backspace:\\\\b del:\\\\x1f done\\\\\n$",
        );
    }

    #[test]
    fn stream_logger_continuation() {
        let (mut logger, output) = make_buffer_logger();

        check!(logger.log_event(&Event::Stdout(b"abc")).is_ok());
        check!(logger.log_event(&Event::Stdout(b"def\\")).is_ok());
        check!(logger.log_event(&event_exit(0)).is_ok());

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.000 out abc\
        //     0.000 out def\\\
        //     0.000 exit 0
        //
        check_output(
            &output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\\\\\n\
            \\d\\.\\d{3} out def\\\\\\\\\\\\\\\n\
            \\d\\.\\d{3} exit 0\n$",
        );
    }

    #[test]
    fn stream_logger_recoverable_error() {
        let (mut logger, output) = make_buffer_logger();

        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_event(&event_idle_timeout()).is_ok());
        check!(logger.log_event(&Event::Stdout(b"def\n")).is_ok());

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.000 out abc
        //     0.000 ERROR Timed out waiting for input after 0ns
        //     0.000 out def
        //
        check_output(
            &output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} ERROR Timed out waiting for input after 0ns\n\
            \\d\\.\\d{3} out def\n$",
        );
    }

    #[test]
    fn stream_logger_continuation_recoverable_error() {
        let (mut logger, output) = make_buffer_logger();

        check!(logger.log_event(&Event::Stdout(b"abc")).is_ok());
        check!(logger.log_event(&event_idle_timeout()).is_ok());
        check!(logger.log_event(&Event::Stdout(b"def\n")).is_ok());

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.000 out abc\
        //     0.000 ERROR Timed out waiting for input after 0ns
        //     0.000 out def
        //
        check_output(
            &output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\\\\\n\
            \\d\\.\\d{3} ERROR Timed out waiting for input after 0ns\n\
            \\d\\.\\d{3} out def\n$",
        );
    }

    #[test]
    fn directory_logger_no_metadata() {
        let directory = tempdir().unwrap();

        let mut logger = JobLogger::new_in_directory(directory.path());
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.log$");
    }

    #[test]
    fn directory_and_stream_loggers() {
        let directory = tempdir().unwrap();
        let output = Rc::new(RefCell::new(Vec::with_capacity(1024)));

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.add_destination(Destination::Stream(output.clone()));
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.log$");
        check!(output.borrow().starts_with(b"Start: "));
    }

    #[test]
    fn directory_logger_with_command() {
        let directory = tempdir().unwrap();
        let command = Command::new("/bin/ls", ["/"]);

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.set_command(&command);
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.ls\.log$");
    }

    #[test]
    fn directory_logger_with_child() {
        let directory = tempdir().unwrap();
        let command = Command::new("/bin/ls", ["/"]);
        let mut child = command.spawn().unwrap();

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.set_command(&command);
        logger.set_child(&child);
        check!(logger.paths().is_empty());

        let _ = child.process_mut().wait(); // Just for cleanliness.

        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.ls\.[0-9]+\.log$");
    }

    #[test]
    fn directory_logger_conflicting_file_name() {
        let directory = tempdir().unwrap();

        let mut logger = JobLogger::new_in_directory(directory.path());
        check!(logger.paths().is_empty());
        check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
        check_file_name(&logger, r"^<date>T<time>\.log$");

        // Valid attempts.
        for i in 1..100 {
            // Reset destinations. This is the easiest way to get the logger to
            // generate an identical name for the log file.
            logger.state = State::Initial;
            logger.destinations =
                vec![Destination::Directory(directory.path().to_path_buf())];
            check!(logger.paths().is_empty());
            check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
            check_file_name(&logger, &format!(r"^<date>T<time>\.{i}\.log$"));
        }

        // Reset destinations. This is the easiest way to get the logger to
        // generate an identical name for the log file.
        logger.state = State::Initial;
        logger.destinations =
            vec![Destination::Directory(directory.path().to_path_buf())];
        check!(logger.paths().is_empty());

        check!(let Err(Error::TooManyAttemptsCreatingUniqueLog { .. }) =
            logger.log_event(&Event::Stdout(b"abc\n")));
    }

    /// Helper function to make tests easier to read.
    fn escape_value_str(
        input: &str,
        indent: usize,
        newline: TrailingNewline,
    ) -> String {
        String::from_utf8(escape_value(input.as_bytes(), indent, newline))
            .unwrap()
    }

    #[test]
    fn escape_value_escapes() {
        let nl = TrailingNewline::Explicit;
        check!(escape_value_str("cr:\r", 4, nl) == "cr:\\r\n");
        check!(escape_value_str("tab:\t", 4, nl) == "tab:\t\n");
        check!(escape_value_str("backslash:\\", 4, nl) == "backslash:\\\\\n");
        check!(
            escape_value_str("backspace:\x0b", 4, nl) == "backspace:\\x0b\n"
        );
        check!(escape_value_str("a\r\t\\\x0bb", 4, nl) == "a\\r\t\\\\\\x0bb\n");
    }

    #[test]
    fn escape_value_newline_implicit() {
        let nl = TrailingNewline::Implicit;
        check!(escape_value_str("abc", 4, nl) == "abc\\\n");
        check!(escape_value_str("abc\n", 4, nl) == "abc\n");
        check!(escape_value_str("abc\ndef", 4, nl) == "abc\n    def\\\n");
        check!(escape_value_str("abc\ndef", 1, nl) == "abc\n def\\\n");
        check!(escape_value_str("", 4, nl) == "\\\n");
        check!(escape_value_str("\n", 4, nl) == "\n");
        check!(escape_value_str("\\", 4, nl) == "\\\\\\\n");
        check!(escape_value_str("\\\n", 4, nl) == "\\\\\n");
    }

    #[test]
    fn escape_value_newline_explicit() {
        let nl = TrailingNewline::Explicit;
        check!(escape_value_str("abc", 4, nl) == "abc\n");
        check!(escape_value_str("abc\n", 4, nl) == "abc\n    \n");
        check!(escape_value_str("abc\ndef", 4, nl) == "abc\n    def\n");
        check!(escape_value_str("abc\ndef", 1, nl) == "abc\n def\n");
        check!(escape_value_str("", 4, nl) == "\n");
        check!(escape_value_str("\n", 4, nl) == "\n    \n");
        check!(escape_value_str("\\", 4, nl) == "\\\\\n");
        check!(escape_value_str("\\\n", 4, nl) == "\\\\\n    \n");
    }
}

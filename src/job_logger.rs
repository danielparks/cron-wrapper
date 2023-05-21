use crate::command::{Child, Command, Event};
use log::info;
use std::cell::RefCell;
use std::ffi::OsString;
use std::fmt;
use std::fs;
use std::io::{self, Write};
use std::iter;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::Instant;
use time::format_description::well_known::{iso8601, Iso8601};
use time::OffsetDateTime;

// Date and time format to use in log file names.
const FILE_NAME_DATE_FORMAT: iso8601::EncodedConfig = iso8601::Config::DEFAULT
    .set_time_precision(iso8601::TimePrecision::Second {
        decimal_digits: None,
    })
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
/// +0.100 out mixed
/// +0.200 \ out .
/// +0.340 \ ERROR IdleTimeout { timeout: Expired { requested: 110ms, actual: 109.566826ms } }
/// ```
#[derive(Debug)]
pub struct JobLogger {
    destinations: Vec<Destination>,
    start_instant: Instant,
    start_time: OffsetDateTime,
    command: Option<Command>,
    child_id: Option<u32>,

    /// If we’ve finished writing log metadata and the trailing empty line.
    finished_metadata: bool,

    /// If the last output from the child did *not* end with a newline.
    continued_line: bool,

    /// If initialization has run (should happen on first write).
    ///
    /// Initialization includes creating a log file if the destination is a
    /// directory and writing the metadata header.
    initialized: bool,
}

impl Default for JobLogger {
    fn default() -> Self {
        Self::none()
    }
}

impl JobLogger {
    /// Create a new job logger that will silently discard all logs.
    pub fn none() -> Self {
        JobLogger {
            destinations: vec![],
            start_instant: Instant::now(),
            start_time: OffsetDateTime::now_local()
                .unwrap_or_else(|_| OffsetDateTime::now_utc()),
            command: None,
            child_id: None,
            finished_metadata: false,
            continued_line: false,
            initialized: false,
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
    pub fn initialize(&mut self) -> anyhow::Result<()> {
        if self.initialized {
            return Ok(());
        }

        // Prevent this from being called from within itself.
        self.initialized = true;

        let mut todo = Vec::new();
        for (i, destination) in self.destinations.iter().enumerate() {
            if let Destination::Directory(path) = destination {
                todo.push((i, path.to_owned()));
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
    pub fn log_wrapper_error(
        &mut self,
        error: &anyhow::Error,
    ) -> anyhow::Result<()> {
        self.write_record(Kind::WrapperError, format!("{error:?}").as_bytes())
    }

    /// Log an [`Event`] received from the [`Child`].
    pub fn log_event(&mut self, event: &Event) -> anyhow::Result<()> {
        match &event {
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
                self.write_record(Kind::Error, format!("{error:?}").as_bytes())
            }
        }
    }

    /// Private: write standard header to log file.
    fn write_file_header(&mut self) -> anyhow::Result<()> {
        if let Some(command) = &self.command {
            let full_command = command.command_line().collect::<Vec<_>>();
            self.write_metadata(
                "Command",
                format!("{:?}", full_command).as_bytes(),
            )?;
        }

        let start = self.start_time.format(&Iso8601::DEFAULT)?;
        self.write_metadata("Start", start.as_bytes())
    }

    /// Private: write a record in the log file.
    fn write_record(&mut self, kind: Kind, value: &[u8]) -> anyhow::Result<()> {
        if !self.finished_metadata {
            self.write_all(b"\n")?;
            self.finished_metadata = true;
        }

        let time = format!("{:.3}", self.elapsed());
        let indent = time.len() + 5;

        let mut buffer = Vec::with_capacity(
            time.len() + kind.as_bytes().len() + value.len() + 5,
        );
        buffer.extend_from_slice(time.as_bytes());

        if self.continued_line {
            buffer.extend_from_slice(b" \\");
        }

        buffer.push(b' ');
        buffer.extend_from_slice(kind.as_bytes());
        buffer.push(b' ');
        let newline = self.escape_into(value, indent, &mut buffer);
        buffer.push(b'\n');

        if kind.is_output() {
            // We only care about trailing newlines for output records.
            self.continued_line = !newline;
        }

        self.write_all(&buffer)
    }

    /// Private: write a metadata line to the top of the log file.
    fn write_metadata(
        &mut self,
        key: &str,
        value: &[u8],
    ) -> anyhow::Result<()> {
        if self.finished_metadata {
            // FIXME? Should this be an error?
            panic!("Tried to write metadata after a record.");
        }

        let mut buffer = Vec::with_capacity(key.len() + 2 + value.len() + 1);
        buffer.extend_from_slice(key.as_bytes());
        buffer.extend_from_slice(b": ");
        self.escape_into(value, 4, &mut buffer); // Ignore trailing newlines.
        buffer.push(b'\n');

        self.write_all(&buffer)
    }

    /// Private: escape value for metadata or record in the output buffer.
    ///
    /// Returns true if the output ended with a newline.
    fn escape_into(
        &self,
        input: &[u8],
        indent: usize,
        output: &mut Vec<u8>,
    ) -> bool {
        let indent: Vec<u8> = iter::repeat(b' ').take(indent).collect();
        if let Some((&last, inpu)) = input.split_last() {
            for &b in inpu {
                output.push(b);
                if b == b'\n' {
                    output.extend_from_slice(&indent);
                }
            }

            // FIXME? CR?
            if last == b'\n' {
                // Swallow trailing newline.
                true
            } else {
                output.push(last);
                // No trailing newline.
                false
            }
        } else {
            // input was empty, so no newline.
            false
        }
    }

    /// Private: write raw data to everything in `self.destinations`.
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.initialize()?;

        // FIXME? should this write to all destinations even if one returns
        // an error?
        for destination in self.destinations.iter_mut() {
            destination.write_all(data)?;
        }

        Ok(())
    }

    /// Private: create a log file in a given directory.
    fn create_file_in_directory(
        &self,
        directory: &Path,
    ) -> anyhow::Result<Destination> {
        let base = self.generate_file_name_base()?;
        let mut number = String::new();
        let mut file_name = OsString::with_capacity(base.len() + 4);
        let mut path = PathBuf::new();
        const MAX_ATTEMPTS: usize = 100;

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
                Err(error) => return Err(error.into()),
            }
        }

        Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            format!(
                "Could not create unique log file after {MAX_ATTEMPTS} \
                attempts. Last: {path:?}"
            ),
        )
        .into())
    }

    /// Private: generate the first part of a file name for a log.
    fn generate_file_name_base(&self) -> anyhow::Result<OsString> {
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

    /// Private: reset state for output. Used for testing.
    #[cfg(test)]
    fn reset_output_state(&mut self) {
        self.finished_metadata = false;
        self.continued_line = false;
        self.initialized = false;
    }
}

/// Create a file; fail if it already exists.
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
        }
    }
}

/// Used to keep track of how various event types should be displayed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Kind {
    Stdout,
    Stderr,
    Exit,
    Error,
    WrapperError,
}

impl Kind {
    /// Serialize to a byte string.
    fn as_bytes(&self) -> &[u8] {
        match self {
            Self::Stdout => b"out",
            Self::Stderr => b"err",
            Self::Exit => b"exit",
            Self::Error => b"ERROR",
            Self::WrapperError => b"WRAPPER-ERROR",
        }
    }

    /// Is this an output (stdout or stderr)?
    fn is_output(&self) -> bool {
        matches!(self, Self::Stdout | Self::Stderr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::command;
    use crate::timeout::Timeout;
    use anyhow::anyhow;
    use assert2::{check, let_assert};
    use bstr::ByteSlice;
    use regex::{bytes, Regex};
    use std::cell::RefCell;
    use std::os::unix::process::ExitStatusExt;
    use std::process::ExitStatus;
    use std::rc::Rc;
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

    /// Create an IdleTimeout error event.
    fn event_idle_timeout() -> Event<'static> {
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

    /// Make a JobLogger that outputs to a buffer.
    fn make_buffer_logger() -> (JobLogger, Rc<RefCell<Vec<u8>>>) {
        let output = Rc::new(RefCell::new(Vec::with_capacity(1024)));

        let mut logger = JobLogger::none();
        logger.add_destination(Destination::Stream(output.clone()));
        check!(logger.paths().is_empty());

        (logger, output)
    }

    /// Check the output buffer against a regex.
    fn check_output(output: Rc<RefCell<Vec<u8>>>, re: &str) {
        let output = output.borrow();
        let re = bytes::Regex::new(&expand_re(re)).unwrap();

        check!(!output.contains(&0u8));
        check!(
            re.is_match(&output),
            "output {} does not match {re:?}",
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
            output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} WRAPPER-ERROR uh oh\n$",
        );
    }

    #[test]
    fn stream_logger_continuation() {
        let (mut logger, output) = make_buffer_logger();

        check!(logger.log_event(&Event::Stdout(b"abc")).is_ok());
        check!(logger.log_event(&Event::Stdout(b"def")).is_ok());
        check!(logger.log_event(&event_exit(0)).is_ok());

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.000 out abc
        //     0.000 \ out def
        //     0.000 \ exit 0
        //
        check_output(
            output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} \\\\ out def\n\
            \\d\\.\\d{3} \\\\ exit 0\n$",
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
        //     0.000 ERROR IdleTimeout { ... }
        //     0.000 out def
        //
        check_output(
            output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} ERROR IdleTimeout.*?\n\
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
        //     0.000 out abc
        //     0.000 \ ERROR IdleTimeout { ... }
        //     0.000 \ out def
        //
        check_output(
            output,
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} \\\\ ERROR IdleTimeout.*?\n\
            \\d\\.\\d{3} \\\\ out def\n$",
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
            logger.reset_output_state();
            logger.destinations =
                vec![Destination::Directory(directory.path().to_path_buf())];
            check!(logger.paths().is_empty());
            check!(logger.log_event(&Event::Stdout(b"abc\n")).is_ok());
            check_file_name(&logger, &format!(r"^<date>T<time>\.{i}\.log$"));
        }

        // Reset destinations. This is the easiest way to get the logger to
        // generate an identical name for the log file.
        logger.reset_output_state();
        logger.destinations =
            vec![Destination::Directory(directory.path().to_path_buf())];
        check!(logger.paths().is_empty());

        let_assert!(Err(error) = logger.log_event(&Event::Stdout(b"abc\n")));
        let_assert!(Some(error) = error.downcast_ref::<io::Error>());
        check!(error.kind() == io::ErrorKind::AlreadyExists);
    }
}

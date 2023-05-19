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
        self.write_record("WRAPPER-ERROR", format!("{error:?}").as_bytes())
    }

    /// Log an [`Event`] received from the [`Child`].
    pub fn log_event(&mut self, event: &Event) -> anyhow::Result<()> {
        match &event {
            Event::Stdout(output) => self.write_record("out", output),
            Event::Stderr(output) => self.write_record("err", output),
            Event::Exit(_) => {
                if let Some(code) = event.exit_code() {
                    self.write_record("exit", code.to_string().as_bytes())
                } else {
                    self.write_record("exit", b"none")
                }
            }
            Event::Error(error) => {
                self.write_record("ERROR", format!("{error:?}").as_bytes())
            }
        }
    }

    /// Private: write a record in the log file.
    fn write_record(&mut self, kind: &str, value: &[u8]) -> anyhow::Result<()> {
        let time = format!("{:.3}", self.elapsed());
        let indent = time.len() + 5;
        let value = self.escape(value, indent);

        let mut buffer =
            Vec::with_capacity(time.len() + kind.len() + value.len() + 5);
        buffer.extend_from_slice(time.as_bytes());

        if self.continued_line {
            buffer.extend_from_slice(b" \\");
        }

        buffer.push(b' ');
        buffer.extend_from_slice(kind.as_bytes());
        buffer.push(b' ');
        buffer.extend_from_slice(&value);
        buffer.push(b'\n');

        self.write_all(&buffer)
    }

    /// Private: escape bytes for output as a value in an event.
    fn escape(&mut self, input: &[u8], indent: usize) -> Vec<u8> {
        let indent: Vec<u8> = iter::repeat(b' ').take(indent).collect();
        let mut output = Vec::with_capacity(input.len());
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
                self.continued_line = false;
            } else {
                self.continued_line = true;
                output.push(last);
            }
        }

        output
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

    /// Private: write standard header to log file.
    fn write_file_header(&mut self) -> anyhow::Result<()> {
        if let Some(command) = &self.command {
            self.write_all(
                format!(
                    "Command: {:?}\n",
                    command.command_line().collect::<Vec<_>>()
                )
                .as_bytes(),
            )?;
        }

        let start = self.start_time.format(&Iso8601::DEFAULT)?;
        self.write_all(format!("Start: {start}\n\n").as_bytes())
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
    /// Logs are discarded.
    None,

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
    Stream(Box<Rc<RefCell<dyn io::Write>>>),
}

impl Default for Destination {
    fn default() -> Self {
        Self::None
    }
}

impl fmt::Debug for Destination {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::None => f.write_str("Destination::None"),
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
            Self::None => Ok(buffer.len()),
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
            Self::None => Ok(()),
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

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::anyhow;
    use assert2::{check, let_assert};
    use bstr::ByteSlice;
    use regex::{bytes, Regex};
    use std::cell::RefCell;
    use std::rc::Rc;
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

    #[test]
    fn none_logger() {
        let buffer = b"abc\n";

        let mut logger = JobLogger::none();
        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());
    }

    #[test]
    fn stream_logger() {
        let buffer = b"abc\n";
        let output = Rc::new(RefCell::new(Vec::with_capacity(1024)));

        let mut logger = JobLogger::none();
        logger.add_destination(Destination::Stream(Box::new(output.clone())));
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check!(logger.paths().is_empty());
        check!(!output.borrow().contains(&0u8));

        // Output should look like:
        //
        //     Start: 2023-05-19T22:17:04.858177000-07:00
        //
        //     0.000 out abc
        //     0.000 \ WRAPPER-ERROR uh oh
        //
        let re = bytes::Regex::new(&expand_re(
            "^Start: <date>T<time+>\n\
            \n\
            \\d\\.\\d{3} out abc\n\
            \\d\\.\\d{3} \\\\ WRAPPER-ERROR uh oh\n$",
        ))
        .unwrap();
        check!(
            re.is_match(&output.borrow()),
            "output {:?} does not match {re:?}",
            output.borrow().as_bstr()
        );
    }

    #[test]
    fn directory_logger_no_metadata() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";

        let mut logger = JobLogger::new_in_directory(directory.path());
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.log$");
    }

    #[test]
    fn directory_and_stream_loggers() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";
        let output = Rc::new(RefCell::new(Vec::with_capacity(1024)));

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.add_destination(Destination::Stream(Box::new(output.clone())));
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.log$");
        check!(output.borrow().starts_with(b"Start: "));
    }

    #[test]
    fn directory_logger_with_command() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";
        let command = Command::new("/bin/ls", ["/"]);

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.set_command(&command);
        check!(logger.paths().is_empty());

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.ls\.log$");
    }

    #[test]
    fn directory_logger_with_child() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";
        let command = Command::new("/bin/ls", ["/"]);
        let mut child = command.spawn().unwrap();

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.set_command(&command);
        logger.set_child(&child);
        check!(logger.paths().is_empty());

        let _ = child.process_mut().wait(); // Just for cleanliness.

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.ls\.[0-9]+\.log$");
    }

    #[test]
    fn directory_logger_conflicting_file_name() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";

        let mut logger = JobLogger::new_in_directory(directory.path());
        check!(logger.paths().is_empty());
        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check_file_name(&logger, r"^<date>T<time>\.log$");

        // Valid attempts.
        for i in 1..100 {
            // Reset destinations. This is the easiest way to get the logger to
            // generate an identical name for the log file.
            logger.initialized = false;
            logger.destinations =
                vec![Destination::Directory(directory.path().to_path_buf())];
            check!(logger.paths().is_empty());
            check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
            check_file_name(&logger, &format!(r"^<date>T<time>\.{i}\.log$"));
        }

        // Reset destinations. This is the easiest way to get the logger to
        // generate an identical name for the log file.
        logger.initialized = false;
        logger.destinations =
            vec![Destination::Directory(directory.path().to_path_buf())];
        check!(logger.paths().is_empty());

        let_assert!(Err(error) = logger.log_event(&Event::Stdout(&buffer[..])));
        let_assert!(Some(error) = error.downcast_ref::<io::Error>());
        check!(error.kind() == io::ErrorKind::AlreadyExists);
    }
}

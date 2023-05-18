use crate::command::{Child, Command, Event};
use log::info;
use std::ffi::OsString;
use std::fs;
use std::io::{self, Write};
use std::iter;
use std::path::{Path, PathBuf};
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
    start_instant: Instant,
    start_time: OffsetDateTime,
    destination: Destination,
    command: Option<Command>,
    child_id: Option<u32>,

    /// If the last output from the child did *not* end with a newline.
    continued_line: bool,
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
            start_instant: Instant::now(),
            start_time: OffsetDateTime::now_local()
                .unwrap_or_else(|_| OffsetDateTime::now_utc()),
            destination: Destination::None,
            command: None,
            child_id: None,
            continued_line: false,
        }
    }

    /// Create a new job logger that will store the log in a new file in the
    /// passed directory.
    ///
    /// The directory must already exist.
    pub fn new_in_directory<P: Into<PathBuf>>(path: P) -> Self {
        let mut job_logger = Self::none();
        job_logger.destination = Destination::Directory(path.into());
        job_logger
    }

    /// Ensure the log file (if appropriate) is open.
    ///
    /// This returns `Ok(())` is the logger is configured with the `None`
    /// destination.
    pub fn ensure_open(&mut self) -> anyhow::Result<()> {
        if let Destination::Directory(path) = &self.destination {
            let path = path.join(self.generate_file_name()?);
            let file = fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(&path)?;
            info!("Saving job output to {path:?}");
            self.destination = Destination::File { path, file };
            self.write_file_header()?;
        }

        Ok(())
    }

    /// Get the path to the log file, if available.
    ///
    /// You may wish to call [`Self::ensure_open()`] first to make sure that
    /// the file has been created. If the logger was created by
    /// [`Self::new_in_directory()`] but nothing has been logged, then the file
    /// will not have been created and this will return `None`.
    pub fn path(&self) -> Option<&Path> {
        if let Destination::File { path, .. } = &self.destination {
            Some(path)
        } else {
            None
        }
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

        let mut buffer = vec![0u8; time.len() + kind.len() + value.len() + 5];
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
        let mut output = vec![0u8; input.len()];
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

    /// Private: write raw data to `self.destination`.
    fn write_all(&mut self, data: &[u8]) -> anyhow::Result<()> {
        self.ensure_open()?;
        Ok(self.destination.write_all(data)?)
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

    /// Private: generate a file name for a log.
    fn generate_file_name(&self) -> anyhow::Result<OsString> {
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

        file_name.push(".log");

        Ok(file_name)
    }

    /// Private: get the seconds elapsed on the run.
    fn elapsed(&self) -> f64 {
        self.start_instant.elapsed().as_secs_f64()
    }
}

/// Where logs should go.
#[derive(Debug)]
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
}

impl Default for Destination {
    fn default() -> Self {
        Self::None
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
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use anyhow::anyhow;
    use assert2::check;
    use regex::Regex;
    use tempfile::tempdir;

    /// Check the log file name for a logger.
    ///
    /// re can include special matchers:
    ///   * <date> becomes [0-9]{4}-[0-9]{2}-[0-9]{2}
    ///   * <time> becomes [0-9]{2}:[0-9]{2}:[0-9]{2}-[0-9]{2}:[0-9]{2}
    fn check_file_name(logger: &JobLogger, re: &str) {
        let path = logger.path().expect("no path to log file");
        check!(path.exists());
        let file_name = path.file_name().expect("log file path is not a file");
        let file_name = file_name.to_string_lossy();

        let re = re.replace("<date>", "[0-9]{4}-[0-9]{2}-[0-9]{2}").replace(
            "<time>",
            "[0-9]{2}:[0-9]{2}:[0-9]{2}(Z|-[0-9]{2}:[0-9]{2})",
        );
        let re = Regex::new(&re).unwrap();
        check!(
            re.is_match(file_name.as_ref()),
            "log file name {file_name:?} does not match {re:?}"
        );
    }

    #[test]
    fn none_logger() {
        let buffer = b"abc\n";

        let mut logger = JobLogger::none();
        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());
    }

    #[test]
    fn directory_logger_no_metadata() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";

        let mut logger = JobLogger::new_in_directory(directory.path());
        check!(logger.path().is_none());

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.log$");
    }

    #[test]
    fn directory_logger_with_command() {
        let directory = tempdir().unwrap();
        let buffer = b"abc\n";
        let command = Command::new("/bin/ls", ["/"]);

        let mut logger = JobLogger::new_in_directory(directory.path());
        logger.set_command(&command);
        check!(logger.path().is_none());

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
        check!(logger.path().is_none());

        let _ = child.process_mut().wait(); // Just for cleanliness.

        check!(logger.log_event(&Event::Stdout(&buffer[..])).is_ok());
        check!(logger.log_wrapper_error(&anyhow!("uh oh")).is_ok());

        check_file_name(&logger, r"^<date>T<time>\.ls\.[0-9]+\.log$");
    }
}

//! # Log all events from a [`Command`]
//!
//! This provides a way to produce a structured log file containing information
//! about the run of a [`Command`]. The log will contain the command line, the
//! start time, and a log of all [`Event`]s and their time offset from when the
//! process was spawned.
//!
//! It can also log errors arising from IO with the child process, and errors
//! from the parent process.

mod logger;
pub use logger::*;

/// The kind of record to be written. This is more low-level than [`Event`], and
/// can represent an error in cron-wrapper that could not be represented by
/// [`Event::Error`].
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    /// Output on the child process’s stdout.
    Stdout,

    /// Output on the child process’s stderr.
    Stderr,

    /// Child process exited.
    Exit,

    /// Error reading or polling the child process.
    Error,

    /// Error in cron-wrapper.
    WrapperError,
}

impl Kind {
    /// Serialize to a byte string.
    #[must_use]
    pub const fn as_bytes(self) -> &'static [u8] {
        match self {
            Self::Stdout => b"out",
            Self::Stderr => b"err",
            Self::Exit => b"exit",
            Self::Error => b"ERROR",
            Self::WrapperError => b"WRAPPER-ERROR",
        }
    }

    /// Is this an output (stdout or stderr)?
    #[must_use]
    pub const fn is_output(self) -> bool {
        matches!(self, Self::Stdout | Self::Stderr)
    }

    /// Is this an error (stderr, error, wrapper-error)?
    #[must_use]
    pub const fn is_any_error(self) -> bool {
        matches!(self, Self::Stderr | Self::Error | Self::WrapperError)
    }
}

//! # Log all events from a [`Command`]
//!
//! This provides a way to produce a structured log file containing information
//! about the run of a [`Command`]. The log will contain the command line, the
//! start time, and a log of all [`Event`]s and their time offset from when the
//! process was spawned.
//!
//! It can also log errors arising from IO with the child process, and errors
//! from the parent process.
//!
//! [`Command`]: crate::command::Command
//! [`Event`]: crate::command::Event

mod logger;
pub mod parser;
pub use logger::*;

/// The kind of record to be written. This is more low-level than [`Event`], and
/// can represent an error in cron-wrapper that could not be represented by
/// [`Event::Error`].
///
/// [`Event`]: crate::command::Event
/// [`Event::Error`]: crate::command::Event::Error
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kind {
    /// Output on the child process’s combined stdout + stderr stream.
    Combined,

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
            Self::Combined => b"com",
            Self::Stdout => b"out",
            Self::Stderr => b"err",
            Self::Exit => b"exit",
            Self::Error => b"ERROR",
            Self::WrapperError => b"WRAPPER-ERROR",
        }
    }

    /// Is this an output (combined, stdout, or stderr)?
    #[must_use]
    pub const fn is_output(self) -> bool {
        matches!(self, Self::Combined | Self::Stdout | Self::Stderr)
    }

    /// Is this an error (stderr, error, wrapper-error)?
    #[must_use]
    pub const fn is_any_error(self) -> bool {
        matches!(self, Self::Stderr | Self::Error | Self::WrapperError)
    }

    /// How are trailing newlines handled?
    ///
    /// See [`TrailingNewline`].
    #[must_use]
    pub const fn newline_behavior(self) -> TrailingNewline {
        if self.is_output() {
            TrailingNewline::Implicit
        } else {
            TrailingNewline::Explicit
        }
    }
}

/// How to treat trailing newlines in a value.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TrailingNewline {
    /// Values have an implicit trailing newline; to produce a value without
    /// a trailing newline you have to end the value with a backslash.
    ///
    /// This is only used for output records, i.e. events that have
    /// [`Kind::Stdout`] and [`Kind::Stderr`].
    Implicit,

    /// Values don’t have a trailing newline unless one is explicitly included.
    ///
    /// This is used for everything except output records, e.g. metadata, error
    /// records, and exit records.
    Explicit,
}

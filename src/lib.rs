//! Miscellaneous useful modules that support cron-wrapper.

// Most lint configuration is in Cranky.toml. It requires cargo-cranky.
#![forbid(unsafe_code)]

/// Read output from child process as events.
pub mod command;

/// Log all events from a command.
pub mod job_logger;

/// Optionally buffer all writes to a stream until we decide to unpause it.
pub mod pause_writer;

/// Stateful timeouts.
pub mod timeout;

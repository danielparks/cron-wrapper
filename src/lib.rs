#![warn(missing_docs)]
//! Miscellaneous useful modules that support cron-wrapper.

/// Read output from child process as events.
pub mod command;

/// Optionally buffer all writes to a stream until we decide to unpause it.
pub mod pause_writer;

/// Stateful timeouts.
pub mod timeout;

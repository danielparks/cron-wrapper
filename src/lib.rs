//! Miscellaneous useful modules that support cron-wrapper.

// Lint configuration in Cargo.toml isn’t supported by cargo-geiger.
#![forbid(unsafe_code)]

pub mod command;
pub mod job_logger;
pub mod pause_writer;
pub mod timeout;

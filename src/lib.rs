//! Miscellaneous useful modules that support cron-wrapper.

// Most lint configuration is in lints.toml, but it doesn’t support forbid, nor
// is it supported by cargo-geiger.
#![forbid(unsafe_code)]

pub mod command;
pub mod job_logger;
pub mod lock;
pub mod pause_writer;
pub mod timeout;

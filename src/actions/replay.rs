//! Replay logs

use crate::params::{Params, ReplayParams, error_color};
use anyhow::{anyhow, bail};
use bstr::ByteSlice;
use cron_wrapper::job_logger::Kind;
use cron_wrapper::job_logger::parser::parse_log;
use std::fs;
use std::io::Write;
use std::str;
use termcolor::WriteColor;

/// Handle the `replay` action.
///
/// # Errors
///
/// This tries to log errors encountered after logging is started, and returns
/// all errors to [`main()`] to be outputted nicely.
pub fn replay(global: &Params, params: &ReplayParams) -> anyhow::Result<i32> {
    let mut out = global.out_stream();
    let mut err = global.err_stream();
    let err_color = error_color();

    let log_file = fs::read(&params.log_file)?;
    let (metadata, records) = parse_log(&log_file).map_err(collapse_error)?;

    if params.metadata {
        for (key, value) in metadata {
            writeln!(out, "{}: {:?}", key.as_bstr(), value.as_bstr())?;
        }
        writeln!(out)?;
    }

    let mut exit_code: Option<i32> = None;

    for record in records {
        match record.kind {
            Kind::Stdout | Kind::Combined => {
                out.write_all(&record.value)?;
                out.flush()?;
            }
            Kind::Stderr => {
                err.set_color(&err_color)?;
                err.write_all(&record.value)?;
                err.reset()?;
                err.flush()?;
            }
            Kind::Exit => {
                // Keep reading so we don’t accidentally hide output if the
                // logger has some kind of bug.
                if exit_code.is_some() {
                    bail!("Multiple exit records found.");
                }
                exit_code = Some(str::from_utf8(&record.value)?.parse()?);
            }
            Kind::Error => {
                err.set_color(&err_color)?;
                err.write_all(b"Error: ")?;
                err.write_all(&record.value)?;
                err.reset()?;
                err.write_all(b"\n")?;
                err.flush()?;
            }
            Kind::WrapperError => {
                err.set_color(&err_color)?;
                err.write_all(b"Wrapper error: ")?;
                err.write_all(&record.value)?;
                err.reset()?;
                err.write_all(b"\n")?;
                err.flush()?;
            }
        }
    }

    Ok(exit_code.unwrap_or(0))
}

/// Collapse a nom error into something that does not borrow the input.
fn collapse_error(error: nom::Err<nom::error::Error<&[u8]>>) -> anyhow::Error {
    match error {
        nom::Err::Incomplete(_) => anyhow!("unexpected EOF"),
        nom::Err::Error(e) | nom::Err::Failure(e) => {
            // FIXME: This gives terrible errors.
            anyhow!("Parse error {:?} at {:?}", e.code, e.input.as_bstr())
        }
    }
}

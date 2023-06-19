#![forbid(unsafe_code)]
#![warn(clippy::nursery, clippy::pedantic)]
#![allow(
    clippy::let_underscore_untyped,
    clippy::manual_string_new,
    clippy::map_unwrap_or,
    clippy::module_name_repetitions
)]
// Require docs on everything
#![warn(missing_docs, clippy::missing_docs_in_private_items)]
// Other restriction lints
#![warn(
    clippy::arithmetic_side_effects,
    clippy::as_underscore,
    clippy::assertions_on_result_states, // see if it makes sense
    clippy::dbg_macro,
    clippy::default_union_representation,
    clippy::empty_structs_with_brackets,
    clippy::filetype_is_file, // maybe?
    clippy::fn_to_numeric_cast_any,
    clippy::format_push_string, // maybe? alternative is fallible.
    clippy::get_unwrap,
    clippy::impl_trait_in_params,
    clippy::integer_division,
    clippy::lossy_float_literal,
    clippy::mem_forget,
    clippy::mixed_read_write_in_expression,
    clippy::multiple_inherent_impl,
    clippy::multiple_unsafe_ops_per_block,
    clippy::mutex_atomic,
    clippy::rc_buffer,
    clippy::rc_mutex,
    clippy::same_name_method,
    clippy::semicolon_inside_block,
    clippy::str_to_string, // maybe?
    clippy::string_to_string,
    clippy::undocumented_unsafe_blocks,
    clippy::unnecessary_safety_doc,
    clippy::unnecessary_self_imports,
    clippy::unneeded_field_pattern,
    clippy::verbose_file_reads
)]

//! Test handling of child processes exiting various ways.
use assert2::check;
use bstr::ByteSlice;
use nix::sys::signal::{kill, Signal};
use nix::unistd::Pid;
use std::os::unix::process::ExitStatusExt;
use std::time::{Duration, Instant};

mod helpers;

// child.id() returns u32; nix expects i32.
fn to_pid(id: u32) -> Pid {
    Pid::from_raw(id.try_into().unwrap())
}

#[test]
fn child_success() {
    let output = helpers::run(["true"]).output().unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn child_failure() {
    let output = helpers::run(["false"]).output().unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn child_sigterm() {
    let start = Instant::now();
    let child = helpers::run(["sleep", "60"]).spawn().unwrap();
    kill(to_pid(child.id()), Signal::SIGTERM).unwrap();
    let output = child.wait_with_output().unwrap();

    check!(output.status.signal() == Some(15), "Expected SIGTERM (15)");
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
    check!(start.elapsed() < Duration::from_secs(1));
}

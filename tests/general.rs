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

use assert2::check;
use bstr::{ByteSlice, B};

mod helpers;

#[test]
fn only_out_unconditional() {
    let output = helpers::run(["tests/fixtures/only_out.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "out\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_on_error() {
    let output = helpers::run(["--on-error", "tests/fixtures/only_out.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_fail_unconditional() {
    let output = helpers::run(["tests/fixtures/only_out_fail.sh"])
        .output()
        .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "out\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_fail_on_error() {
    let output =
        helpers::run(["--on-error", "tests/fixtures/only_out_fail.sh"])
            .output()
            .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_fail_on_fail() {
    let output = helpers::run(["--on-fail", "tests/fixtures/only_out_fail.sh"])
        .output()
        .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "out\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn midline_sleep_all() {
    let output = helpers::run(["tests/fixtures/midline_sleep.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111222333\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_unconditional() {
    let output = helpers::run(["tests/fixtures/mixed_output.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111aaa333\nbbb\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_on_error() {
    let output = helpers::run(["--on-error", "tests/fixtures/mixed_output.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111aaa333\nbbb\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_unconditional_color() {
    let output =
        helpers::run(["--color", "always", "tests/fixtures/mixed_output.sh"])
            .output()
            .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111\x1b[0m\x1b[38;5;9maaa\x1b[0m333\n\x1b[0m\x1b[38;5;9mbbb\n\x1b[0m");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_on_fail_color() {
    let output = helpers::run([
        "--color",
        "always",
        "--on-fail",
        "tests/fixtures/mixed_output.sh",
        "1",
    ])
    .output()
    .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "111\x1b[0m\x1b[38;5;9maaa\x1b[0m333\n\x1b[0m\x1b[38;5;9mbbb\n\x1b[0m");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn invalid_utf8() {
    let output = helpers::run(["tests/fixtures/invalid_utf8.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == B(b"bad \xE2(\xA1 bad\n"));
    check!(output.stderr.as_bstr() == "");
}

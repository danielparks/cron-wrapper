use assert2::check;
use bstr::{ByteSlice, B};

mod helpers;

#[test]
fn only_out_unconditional() {
    let output = helpers::run(["run", "tests/fixtures/only_out.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "out\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_on_error() {
    let output =
        helpers::run(["run", "--on-error", "tests/fixtures/only_out.sh"])
            .output()
            .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_fail_unconditional() {
    let output = helpers::run(["run", "tests/fixtures/only_out_fail.sh"])
        .output()
        .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "out\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_fail_on_error() {
    let output =
        helpers::run(["run", "--on-error", "tests/fixtures/only_out_fail.sh"])
            .output()
            .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn only_out_fail_on_fail() {
    let output =
        helpers::run(["run", "--on-fail", "tests/fixtures/only_out_fail.sh"])
            .output()
            .unwrap();

    check!(output.status.code() == Some(1));
    check!(output.stdout.as_bstr() == "out\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn midline_sleep_all() {
    let output = helpers::run(["run", "tests/fixtures/midline_sleep.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111222333\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_unconditional() {
    let output = helpers::run(["run", "tests/fixtures/mixed_output.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111aaa333\nbbb\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_on_error() {
    let output =
        helpers::run(["run", "--on-error", "tests/fixtures/mixed_output.sh"])
            .output()
            .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111aaa333\nbbb\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn mixed_output_unconditional_color() {
    let output = helpers::run([
        "--color",
        "always",
        "run",
        "tests/fixtures/mixed_output.sh",
    ])
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
        "run",
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
fn combined_output() {
    let output = helpers::run([
        "run",
        "--combine-output",
        "tests/fixtures/mixed_output.sh",
    ])
    .output()
    .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111aaa333\nbbb\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn combined_output_unconditional_color() {
    let output = helpers::run([
        "--color",
        "always",
        "run",
        "--combine-output",
        "tests/fixtures/mixed_output.sh",
    ])
    .output()
    .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111aaa333\nbbb\n");
    check!(output.stderr.as_bstr() == "");
}

#[test]
fn invalid_utf8() {
    let output = helpers::run(["run", "tests/fixtures/invalid_utf8.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == B(b"bad \xE2(\xA1 bad\n"));
    check!(output.stderr.as_bstr() == "");
}

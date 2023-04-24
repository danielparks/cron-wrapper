use assert2::check;
use bstr::{ByteSlice, B};

mod helpers;

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
fn mixed_output_no_color_combined() {
    let output = helpers::run(["tests/fixtures/mixed_output.sh"])
        .output()
        .unwrap();

    check!(output.status.success());
    check!(output.stdout.as_bstr() == "111333\n");
    check!(output.stderr.as_bstr() == "aaabbb\n");
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

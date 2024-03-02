use assert2::check;
use bstr::ByteSlice;
use std::ffi::OsStr;
use std::path::PathBuf;
use std::process::Output;
use std::thread;
use std::time::{Duration, Instant};
use tempfile::tempdir;

mod helpers;

fn run_sleep_touch<I, S, F>(args: I, func: F)
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
    F: FnOnce(Output, PathBuf),
{
    // Directory will be deleted on drop.
    let directory = tempdir().unwrap();
    let marker = directory.path().join("marker");
    check!(!marker.is_file(), "marker should not exist yet");

    let output = helpers::run(["run"])
        .args(args)
        .arg("tests/fixtures/sleep_touch.sh")
        .arg(&marker)
        .output()
        .unwrap();
    check!(output.stdout.as_bstr() == "");

    func(output, marker);
}

#[test]
fn sleep_touch_ok() {
    let start = Instant::now();
    run_sleep_touch(["--run-timeout", "1s"], |output, marker| {
        check!(output.stderr.as_bstr() == "");
        check!(output.status.success());
        check!(
            start.elapsed() > Duration::from_millis(100),
            "Should have taken at least 0.1 seconds"
        );
        check!(marker.is_file(), "marker should have been created");
    });
}

#[test]
fn sleep_touch_run_timeout() {
    let start = Instant::now();
    run_sleep_touch(["--run-timeout", "10ms"], |output, marker| {
        check!(output
            .stderr
            .as_bstr()
            .starts_with_str("Error: Run timed out after"));
        check!(output.status.code() == Some(1));
        check!(
            start.elapsed() < Duration::from_millis(100),
            "Should have died with a timeout after 10ms"
        );

        // sleep_touch.sh sleeps for 0.1 seconds (100ms) before creating the
        // marker file, but sometimes it takes just a little longer.
        thread::sleep(Duration::from_millis(200));
        check!(!marker.is_file(), "marker should not have been created");
    });
}

#[test]
fn sleep_touch_run_timeout_no_signal() {
    let start = Instant::now();
    run_sleep_touch(
        ["--error-signal", "none", "--run-timeout", "10ms"],
        |output, marker| {
            check!(output
                .stderr
                .as_bstr()
                .starts_with_str("Error: Run timed out after"));
            check!(output.status.code() == Some(1));
            check!(
                start.elapsed() < Duration::from_millis(100),
                "Should have died with a timeout after 10ms"
            );

            // sleep_touch.sh sleeps for 0.1 seconds (100ms) before creating the
            // marker file, but sometimes it takes just a little longer.
            thread::sleep(Duration::from_millis(200));
            check!(marker.is_file(), "marker should have been created");
        },
    );
}

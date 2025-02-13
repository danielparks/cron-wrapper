//! Test lock options on command line.

use assert2::check;
use bstr::ByteSlice;
use std::thread;
use std::time::{Duration, Instant};
use tempfile::NamedTempFile;

mod helpers;

#[test]
fn lock_conflict_immediate() {
    let lock_path_handle = NamedTempFile::new().unwrap().into_temp_path();
    let lock_path = lock_path_handle.to_path_buf();
    let lock_path2 = lock_path_handle.to_path_buf();

    let handle = thread::spawn(move || {
        let output = helpers::run(["run", "--lock-file"])
            .arg(&lock_path)
            .args(["sleep", "0.5"])
            .output()
            .unwrap();
        check!(output.status.success());
        check!(output.stdout.as_bstr() == "");
        check!(output.stderr.as_bstr() == "");
    });

    thread::sleep(Duration::from_millis(100));

    let handle2 = thread::spawn(move || {
        let output = helpers::run(["run", "--lock-file"])
            .arg(&lock_path2)
            .args(["sleep", "0.5"])
            .output()
            .unwrap();
        check!(!output.status.success(), "Should fail to obtain lock");
        check!(output.stdout.as_bstr() == "");
        check!(output
            .stderr
            .starts_with(b"Error: Lock owned by another process"));
    });

    handle.join().unwrap();
    handle2.join().unwrap();
}

#[test]
fn lock_conflict_wait() {
    let lock_path_handle = NamedTempFile::new().unwrap().into_temp_path();
    let lock_path = lock_path_handle.to_path_buf();
    let lock_path2 = lock_path_handle.to_path_buf();
    let start = Instant::now();

    let handle = thread::spawn(move || {
        let output = helpers::run(["run", "--lock-wait", "--lock-file"])
            .arg(&lock_path)
            .args(["sleep", "0.5"])
            .output()
            .unwrap();
        check!(output.status.success());
        check!(output.stdout.as_bstr() == "");
        check!(output.stderr.as_bstr() == "");
    });

    thread::sleep(Duration::from_millis(100));

    let handle2 = thread::spawn(move || {
        let output = helpers::run(["run", "--lock-wait", "--lock-file"])
            .arg(&lock_path2)
            .args(["sleep", "0.5"])
            .output()
            .unwrap();
        check!(output.status.success());
        check!(output.stdout.as_bstr() == "");
        check!(output.stderr.as_bstr() == "");
    });

    handle.join().unwrap();
    handle2.join().unwrap();
    check!(start.elapsed() > Duration::from_secs(1));
}

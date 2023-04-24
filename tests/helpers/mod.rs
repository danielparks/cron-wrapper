use assert_cmd::prelude::*;
use std::ffi::OsStr;
use std::process::Command;

pub fn run<I, S>(args: I) -> Command
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::cargo_bin("cron-wrapper").unwrap();
    command.args(args);
    command
}

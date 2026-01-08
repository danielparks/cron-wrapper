use assert_cmd::cargo;
use std::ffi::OsStr;
use std::process::Command;

pub fn run<I, S>(args: I) -> Command
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut command = Command::new(cargo::cargo_bin!());
    command.args(args);
    command
}

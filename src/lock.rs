//! # Functions to manage file locks

use bstr::{BString, ByteSlice};
use fd_lock::{RwLock, RwLockWriteGuard};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, ErrorKind, Read, Seek, Write};
use std::os::unix::ffi::OsStrExt;
use std::path::Path;
use std::process;

/// Errors establishing a lock might raise.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Error reading the lock file before getting the lock.
    #[error("Could read lock file: {0}")]
    Read(io::Error),

    /// Error getting the lock on the lock file..
    #[error("Could establish lock: {0}")]
    Lock(io::Error),

    /// Call to get a lock was interrupted by a signal repeatedly.
    #[error("Interupted {attempts} times trying to get lock")]
    LockInterupted {
        /// How many times the attempt to establish a lock was interupted.
        attempts: usize,
    },

    /// The lock was already owned by another process.
    #[error("Lock owned by another process:\n{contents}")]
    AlreadyRunning {
        /// The contents of the lock file.
        contents: BString,
    },
}

/// Open a lock file to ensure `func` is only run once.
///
/// # Errors
///
/// See [`Error`]. This can return an error from the inner function, too.
pub fn try_lock_raw<P, R, F>(path: P, func: F) -> anyhow::Result<R>
where
    P: AsRef<Path>,
    F: FnOnce(RwLockWriteGuard<'_, fs::File>) -> anyhow::Result<R>,
{
    /// Only retry locking after a signal interruption this many times.
    const ATTEMPTS: usize = 10;

    let mut file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(path.as_ref())
        .map_err(Error::Read)?;
    let mut contents = BString::new(vec![]);
    #[allow(clippy::verbose_file_reads)] // Need to keep file open.
    file.read_to_end(&mut contents).map_err(Error::Read)?;

    let mut lock = RwLock::new(file);

    for _ in 0..ATTEMPTS {
        return match lock.try_write() {
            Ok(guard) => func(guard),
            Err(error) => match error.kind() {
                ErrorKind::WouldBlock => {
                    Err(Error::AlreadyRunning { contents }.into())
                }
                ErrorKind::Interrupted => {
                    // Try again
                    continue;
                }
                _ => Err(Error::Lock(error).into()),
            },
        };
    }

    Err(Error::LockInterupted { attempts: ATTEMPTS }.into())
}

/// Open a lock file to ensure `func` is only run once. This writes the standard
/// message to the lock file if it manages to obtain it.
///
/// # Errors
///
/// See [`Error`]. This can return an error from the inner function, too.
pub fn try_lock_standard<P, R, F>(path: P, func: F) -> anyhow::Result<R>
where
    P: AsRef<Path>,
    F: FnOnce() -> anyhow::Result<R>,
{
    try_lock_raw(path, |mut guard| {
        guard.set_len(0)?;
        guard.rewind()?;
        writeln!(guard, "COMMAND={}", args_sh().as_bstr())?;
        writeln!(guard, "PID={}", process::id())?;
        func()
    })
}

/// Get the command line for this run escaped for the shell.
///
/// Note that this might return a literal \0 in its return if it is present
/// in the command or its arguments.
///
/// # Panics
///
/// This should not panic with shlex version 1.3.0. However, future version
/// of shlex may introduce new ways of quoting that may fail.
#[must_use]
pub fn args_sh() -> Vec<u8> {
    let args: Vec<OsString> = env::args_os().collect();
    let args_bytes = args.iter().map(|arg| arg.as_bytes());

    // This cannot fail in shlex 1.3.0:
    shlex::bytes::Quoter::new()
        .allow_nul(true)
        .join(args_bytes)
        .unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert2::{check, let_assert};
    use tempfile::tempdir;

    #[test]
    fn try_lock_raw_basic() {
        let directory = tempdir().unwrap();
        let foo_file = directory.path().join("foo");

        // Check that creating a file works.
        let_assert!(
            Ok(()) = try_lock_raw(&foo_file, |mut guard| {
                guard.set_len(0)?;
                guard.rewind()?;
                writeln!(guard, "Ok")?;
                Ok(())
            })
        );

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(contents.as_bstr() == b"Ok\n".as_bstr());

        // Check that using the file a second time works.
        let_assert!(
            Ok(()) = try_lock_raw(&foo_file, |mut guard| {
                guard.set_len(0)?;
                guard.rewind()?;
                writeln!(guard, "2")?;
                Ok(())
            })
        );

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(contents.as_bstr() == b"2\n".as_bstr());
    }

    #[allow(clippy::naive_bytecount)] // Overkill for this case.
    #[test]
    fn try_lock_standard_basic() {
        let directory = tempdir().unwrap();
        let foo_file = directory.path().join("foo");

        // Check that creating a file works.
        let_assert!(Ok(()) = try_lock_standard(&foo_file, || { Ok(()) }));

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(
            contents.iter().filter(|&c| *c == b'\n').count() == 2,
            "expected contents to have 2 newlines"
        );

        // Check that using the file a second time works.
        let_assert!(Ok(()) = try_lock_standard(&foo_file, || { Ok(()) }));

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(
            contents.iter().filter(|&c| *c == b'\n').count() == 2,
            "expected contents to have 2 newlines"
        );
    }
}

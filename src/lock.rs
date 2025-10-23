//! # Functions to manage file locks

use bstr::{BString, ByteSlice};
use fd_lock::{RwLock, RwLockWriteGuard};
use home::home_dir;
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, ErrorKind, Read, Seek, Write};
use std::os::unix::ffi::OsStrExt;
use std::path::{Path, PathBuf};
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
    #[error("Interrupted {attempts} times trying to get lock")]
    LockInterrupted {
        /// How many times the attempt to establish a lock was interrupted.
        attempts: usize,
    },

    /// The lock was already owned by another process.
    #[error("Lock owned by another process:\n{contents}")]
    AlreadyRunning {
        /// The contents of the lock file.
        contents: BString,
    },
}

/// Should we wait for the lock to be available, or return immediately?
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Behavior {
    /// Return immediately without calling inner function if the lock is held by
    /// another process. [`Error::AlreadyRunning`] will be returned with the
    /// contents of the lock file in this case.
    Return,

    /// Wait for the lock to be available.
    ///
    /// There is no timeout; this may wait forever.
    Wait,
}

impl Behavior {
    /// Try to obtain the lock following the [`Behavior`].
    ///
    /// # Errors
    ///
    /// Depending on `Behavior`, this will either return errors from
    /// [`RwLock::try_write()`] or [`RwLock::write()`].
    pub fn lock<'a, T: std::os::fd::AsFd>(
        &self,
        lock: &'a mut RwLock<T>,
    ) -> io::Result<RwLockWriteGuard<'a, T>> {
        match self {
            Self::Return => lock.try_write(),
            Self::Wait => lock.write(),
        }
    }
}

/// Open a lock file to ensure `func` is only run once.
///
/// `lock_writer` is used to write the message to the lock file. Generally, you
/// will want to use [`standard_message`]. The lock file will be truncated and
/// ready for writing before `lock_writer` is called.
///
/// # Example
///
/// ```rust
/// # let handle = tempfile::NamedTempFile::new().unwrap().into_temp_path();
/// # let path = handle.to_path_buf();
/// use cron_wrapper::lock;
/// lock::lock(&path, lock::Behavior::Wait, lock::standard_message, || {
///     // ... do stuff ...
///     Ok(())
/// }).unwrap();
/// ```
///
/// # Errors
///
/// See [`Error`]. This can return an error from the inner function, too.
pub fn lock<P, R, M, F>(
    path: P,
    behavior: Behavior,
    lock_writer: M,
    func: F,
) -> anyhow::Result<R>
where
    P: AsRef<Path>,
    M: FnOnce(&mut RwLockWriteGuard<'_, fs::File>) -> io::Result<()>,
    F: FnOnce() -> anyhow::Result<R>,
{
    /// Only retry locking after a signal interruption this many times.
    const ATTEMPTS: usize = 10;

    let mut file = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(path.as_ref())
        .map_err(Error::Read)?;
    let mut contents = BString::new(vec![]);
    #[allow(clippy::verbose_file_reads)] // Need to keep file open.
    file.read_to_end(&mut contents).map_err(Error::Read)?;

    let mut lock = RwLock::new(file);

    for _ in 0..ATTEMPTS {
        return match behavior.lock(&mut lock) {
            Ok(mut guard) => {
                guard.set_len(0)?;
                guard.rewind()?;
                lock_writer(&mut guard)?;
                func()
            }
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

    Err(Error::LockInterrupted { attempts: ATTEMPTS }.into())
}

/// Write a standard message to the lock file. Use with [`lock()`].
///
/// The message will look something like:
///
/// ```text
/// COMMAND=my-command -abc arg1 'arg two with whitespace'
/// PID=1234
/// ```
///
/// # Example
///
/// ```rust
/// # let handle = tempfile::NamedTempFile::new().unwrap().into_temp_path();
/// # let path = handle.to_path_buf();
/// use cron_wrapper::lock;
/// lock::lock(&path, lock::Behavior::Wait, lock::standard_message, || {
///     // ... do stuff ...
///     Ok(())
/// }).unwrap();
/// ```
///
/// # Errors
///
/// This can return [`io::Error`] if there’s a problem writing to the file.
pub fn standard_message(
    guard: &mut RwLockWriteGuard<'_, fs::File>,
) -> io::Result<()> {
    writeln!(guard, "COMMAND={}", args_sh().as_bstr())?;
    writeln!(guard, "PID={}", process::id())
}

/// Write a static message to the lock file. Use with [`lock()`].
///
/// This returns a function.
///
/// # Example
///
/// ```rust
/// # let handle = tempfile::NamedTempFile::new().unwrap().into_temp_path();
/// # let path = handle.to_path_buf();
/// use cron_wrapper::lock;
/// lock::lock(&path, lock::Behavior::Wait, lock::static_message("locked"), || {
///     // ... do stuff ...
///     Ok(())
/// }).unwrap();
///
/// assert_eq!(std::fs::read(&path).unwrap(), b"locked");
/// ```
pub fn static_message<S>(
    message: S,
) -> impl FnOnce(&mut RwLockWriteGuard<'_, fs::File>) -> io::Result<()>
where
    S: std::fmt::Display,
{
    let message = message.to_string();
    move |guard| guard.write_all(message.as_bytes())
}

/// Get the default directory to store lock files.
///
/// # Errors
///
/// This will return [`io::Error`] with [`ErrorKind::NotFound`] if it can’t find
/// a default lock directory.
pub fn default_lock_dir() -> io::Result<PathBuf> {
    if let Some(path) = env::var_os("XDG_RUNTIME_DIR") {
        let path = PathBuf::from(path);
        if path.is_dir() {
            return Ok(path);
        }
    }

    let uid = nix::unistd::Uid::effective();
    if uid.is_root() {
        for path in ["/run/lock", "/run", "/var/lock", "/var/run"] {
            let path = PathBuf::from(path);
            if path.is_dir() {
                return Ok(path);
            }
        }
    } else {
        // /run/user/<UID>/ is the current standard on Linux.
        let path = PathBuf::from("/run/user").join(uid.to_string());
        if path.is_dir() {
            return Ok(path);
        }

        // /run/lock/uid-<UID>/ seems reasonable.
        for path in ["/run/lock", "/var/lock"] {
            let path = PathBuf::from(path);
            if path.is_dir() {
                let path = path.join(format!("uid-{uid}"));
                if path.is_dir() || fs::create_dir(&path).is_ok() {
                    return Ok(path);
                }
                // Ignore reason for failing to create directory.
            }
        }

        // ~/.local/run is not actually an official path, but we need a
        // reasonable fallback within $HOME. This will create the whole path if
        // it doesn’t already exist.
        if let Some(home) = home_dir() {
            let path = home.join(".local").join("run");
            if path.is_dir() || fs::create_dir_all(&path).is_ok() {
                return Ok(path);
            }
            // Ignore reason for failing to create directory.
        }
    }

    Err(io::Error::new(
        ErrorKind::NotFound,
        "no default lock file directory",
    ))
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
    fn lock_basic() {
        let directory = tempdir().unwrap();
        let foo_file = directory.path().join("foo");

        // Check that creating a file works.
        let_assert!(
            Ok(()) =
                lock(&foo_file, Behavior::Return, static_message("Ok"), || {
                    Ok(())
                })
        );

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(contents.as_bstr() == b"Ok".as_bstr());

        // Check that using the file a second time works.
        let_assert!(
            Ok(()) =
                lock(&foo_file, Behavior::Return, static_message("2"), || {
                    Ok(())
                })
        );

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(contents.as_bstr() == b"2".as_bstr());
    }

    #[allow(clippy::naive_bytecount)] // Overkill for this case.
    #[test]
    fn lock_standard_basic() {
        let directory = tempdir().unwrap();
        let foo_file = directory.path().join("foo");

        // Check that creating a file works.
        let_assert!(
            Ok(()) =
                lock(&foo_file, Behavior::Return, standard_message, || {
                    Ok(())
                })
        );

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(
            contents.iter().filter(|&c| *c == b'\n').count() == 2,
            "expected contents to have 2 newlines"
        );

        // Check that using the file a second time works.
        let_assert!(
            Ok(()) =
                lock(&foo_file, Behavior::Return, standard_message, || {
                    Ok(())
                })
        );

        let_assert!(Ok(contents) = fs::read(&foo_file));
        check!(
            contents.iter().filter(|&c| *c == b'\n').count() == 2,
            "expected contents to have 2 newlines"
        );
    }
}

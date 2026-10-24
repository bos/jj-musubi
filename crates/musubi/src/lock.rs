//! Lock files, which keep a second daemon or hub from starting where one runs, and two
//! commands from changing musubi's state at once.

use std::fs;
use std::path::Path;

use anyhow::Context as _;

/// Holds a lock file for as long as it lives.
pub struct Lock(#[expect(dead_code, reason = "held for its lock")] fs::File);

/// Takes the lock at `path`, or returns `None` if something else holds it.
pub fn try_lock(path: &Path) -> anyhow::Result<Option<Lock>> {
    let file = open(path)?;
    match file.try_lock() {
        Ok(()) => Ok(Some(Lock(file))),
        Err(fs::TryLockError::WouldBlock) => Ok(None),
        Err(fs::TryLockError::Error(err)) => Err(err).with_context(|| format!("locking {path:?}")),
    }
}

/// Takes the lock at `path`, waiting for whatever holds it to let go.
pub fn lock(path: &Path) -> anyhow::Result<Lock> {
    let file = open(path)?;
    file.lock().with_context(|| format!("locking {path:?}"))?;
    Ok(Lock(file))
}

fn open(path: &Path) -> anyhow::Result<fs::File> {
    if let Some(dir) = path.parent() {
        fs::create_dir_all(dir)?;
    }
    fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .write(true)
        .open(path)
        .with_context(|| format!("opening {path:?}"))
}

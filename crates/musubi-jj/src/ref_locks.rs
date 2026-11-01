//! The lock files git and jj take on refs, which a process killed partway through updating
//! refs leaves behind.
//!
//! git, and gix for jj, update a ref by creating `<ref>.lock` exclusively, writing the new
//! value into it, and renaming it over the ref; `packed-refs.lock` likewise. A process
//! killed between those steps leaves the lock, and every later update of that ref fails
//! until someone removes it, which git never does. A ref lock is held for one update, a few
//! seconds at most even for `git pack-refs` over many refs, and never waits on a person, as
//! `index.lock` does while `git commit -a` has an editor open. A lock records nothing of who
//! took it, and git closes it before renaming it, so only its age tells a lock left behind
//! from one held now. So when one of musubi's ref updates fails, it removes the ref locks
//! older than [`STALE`], and tries again. A process suspended for longer partway through an
//! update, as on a laptop put to sleep, finds its lock gone when it resumes, and fails.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;

/// How old a ref lock is before musubi takes it to be left behind.
pub const STALE: Duration = Duration::from_secs(10 * 60);

/// Runs `update`, which updates refs in the git repository at `git_dir`, and if it fails,
/// runs it once more if a ref lock left behind there was in the way.
pub fn retrying<T, E>(git_dir: &Path, mut update: impl FnMut() -> Result<T, E>) -> Result<T, E> {
    update().or_else(|err| {
        if remove_stale(git_dir) == 0 {
            Err(err)
        } else {
            update()
        }
    })
}

/// Removes the ref locks in the git repository at `git_dir` older than [`STALE`]:
/// `packed-refs.lock`, and every `.lock` file under `refs/`, since no ref's name ends in
/// `.lock`. Returns how many it removed.
pub fn remove_stale(git_dir: &Path) -> usize {
    sweep(git_dir, |common, locks| {
        find_locks(&common.join("refs"), locks);
    })
}

/// [`remove_stale`] for the locks on `refs`, named in full, as `refs/heads/main`, and on
/// `packed-refs`: for a failure that may recur, which would otherwise walk every ref each
/// time.
pub fn remove_stale_of<'a>(git_dir: &Path, refs: impl IntoIterator<Item = &'a str>) -> usize {
    sweep(git_dir, |common, locks| {
        locks.extend(
            refs.into_iter()
                .map(|name| common.join(format!("{name}.lock"))),
        );
    })
}

/// Removes `packed-refs.lock` and the locks `find` adds, given the directory that holds the
/// refs, where they are older than [`STALE`].
fn sweep(git_dir: &Path, find: impl FnOnce(&Path, &mut Vec<PathBuf>)) -> usize {
    // A linked worktree's refs, but for its own few, are in the main repository's.
    let common = match fs::read_to_string(git_dir.join("commondir")) {
        Ok(dir) => git_dir.join(dir.trim()),
        Err(_) => git_dir.to_owned(),
    };
    // Sweeps take turns, so that none removes a lock taken since another removed a stale one
    // where it was. Windows opens no directory as a file, and there they don't.
    let _turn = fs::File::open(&common).and_then(|dir| dir.lock().map(|()| dir));
    let mut locks = vec![common.join("packed-refs.lock")];
    find(&common, &mut locks);
    locks.iter().filter(|lock| remove_if_stale(lock)).count()
}

fn find_locks(dir: &Path, locks: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let Ok(file_type) = entry.file_type() else {
            continue;
        };
        let path = entry.path();
        if file_type.is_dir() {
            find_locks(&path, locks);
        } else if file_type.is_file() && path.extension().is_some_and(|ext| ext == "lock") {
            locks.push(path);
        }
    }
}

fn remove_if_stale(lock: &Path) -> bool {
    let Ok(meta) = fs::symlink_metadata(lock) else {
        return false;
    };
    // A lock dated in the future, by a clock set back, is taken to be new.
    let stale = meta.is_file()
        && meta
            .modified()
            .is_ok_and(|modified| modified.elapsed().is_ok_and(|age| age >= STALE));
    if !stale || fs::remove_file(lock).is_err() {
        return false;
    }
    tracing::warn!(
        "removed {}, a git lock over {} minutes old, left by an update of refs that never \
         finished",
        lock.display(),
        STALE.as_secs() / 60
    );
    true
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::fs::File;
    use std::time::SystemTime;

    use super::*;

    const OLD: Duration = Duration::from_secs(STALE.as_secs() + 60);

    fn lock(path: &Path, modified: SystemTime) {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        File::create(path).unwrap().set_modified(modified).unwrap();
    }

    /// Only ref locks older than [`STALE`] go: not a newer one, which a process may hold
    /// now, nor one dated in the future, nor another of git's locks, such as `index.lock`,
    /// which `git commit -a` holds while its editor is open.
    #[test]
    fn only_stale_ref_locks_go() {
        let dir = musubi_testutil::tempdir();
        let git_dir = dir.path();
        let now = SystemTime::now();
        let stale = [
            git_dir.join("packed-refs.lock"),
            git_dir.join("refs/heads/main.lock"),
            git_dir.join("refs/jj/keep/abc.lock"),
        ];
        let kept = [
            (git_dir.join("refs/heads/new.lock"), now - STALE / 2),
            (git_dir.join("refs/heads/ahead.lock"), now + STALE),
            (git_dir.join("index.lock"), now - OLD),
            (git_dir.join("config.lock"), now - OLD),
            (git_dir.join("refs/heads/main"), now - OLD),
        ];
        for path in &stale {
            lock(path, now - OLD);
        }
        for (path, modified) in &kept {
            lock(path, *modified);
        }
        assert_eq!(remove_stale(git_dir), stale.len());
        assert!(stale.iter().all(|path| !path.exists()));
        assert!(kept.iter().all(|(path, _)| path.exists()));
        assert_eq!(remove_stale(git_dir), 0);
    }

    /// Only the locks on the refs named go, and `packed-refs.lock`, from the main repository
    /// of a linked worktree.
    #[test]
    fn named_refs_locks_go_from_the_common_dir() {
        let dir = musubi_testutil::tempdir();
        let common = dir.path();
        let worktree = common.join("worktrees/other");
        fs::create_dir_all(&worktree).unwrap();
        fs::write(worktree.join("commondir"), "../..\n").unwrap();
        let old = SystemTime::now() - OLD;
        for name in ["packed-refs.lock", "refs/heads/a.lock", "refs/heads/b.lock"] {
            lock(&common.join(name), old);
        }
        assert_eq!(remove_stale_of(&worktree, ["refs/heads/a"]), 2);
        assert!(common.join("refs/heads/b.lock").exists());
    }

    /// A failed update runs again only if a stale lock went.
    #[test]
    fn a_failed_update_is_retried_only_after_a_stale_lock_goes() {
        let dir = musubi_testutil::tempdir();
        let git_dir = dir.path();
        let runs = Cell::new(0);
        let failing = || -> Result<(), ()> {
            runs.set(runs.get() + 1);
            Err(())
        };
        let main = git_dir.join("refs/heads/main.lock");
        lock(&main, SystemTime::now());
        assert!(retrying(git_dir, failing).is_err());
        assert_eq!(runs.replace(0), 1);
        lock(&main, SystemTime::now() - OLD);
        assert!(retrying(git_dir, failing).is_err());
        assert_eq!(runs.get(), 2);
    }
}

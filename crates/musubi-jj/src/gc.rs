//! What jj's own garbage collection (`jj util gc`) would clean up in a machine's
//! repository, short of pruning git objects.
//!
//! A machine stores every operation and commit of its hive, and jj leaves behind files it no
//! longer reads: segments of its extras table that newer ones replaced, and a keep ref for
//! every commit it ever wrote or imported. This removes those, and the operations that no op
//! head reaches, as jj's gc does, once two weeks old. jj's gc then runs a full `git gc` that
//! prunes what no ref reaches; this doesn't. musubi never deletes a git object, and its own
//! `git gc --auto` already packs loose objects (see `objects::git`). So nothing the protocol
//! needs can go missing: not the commits a reachable operation refers to, which jj's index,
//! and so the keep refs left, cover, and not those fetched for operations not yet realized,
//! which nothing refers to yet.
//!
//! It runs only once there is enough to clean up, and a week after it last ran.

use std::collections::HashSet;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;
use std::time::SystemTime;

use jj_lib::backend::CommitId;
use jj_lib::default_backend_factories::default_backend_factories;
use jj_lib::git::GitSubprocessOptions;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use jj_lib::repo::StoreLoadError;
use jj_lib::settings::UserSettings;
use pollster::FutureExt as _;
use thiserror::Error;

use crate::objects::GitObjects;
use crate::objects::KEEP_REFS;
use crate::objects::ObjectError;

/// How long after one run, or one that failed, another may start.
pub const INTERVAL: Duration = Duration::from_secs(7 * 24 * 60 * 60);

/// How old an unreachable operation, extras segment or keep ref must be before it goes:
/// jj's default, so that what a jj command is writing meanwhile is never taken for garbage.
pub const KEEP_NEWER: Duration = Duration::from_secs(14 * 24 * 60 * 60);

/// Files in jj's extras table, almost all replaced segments, worth cleaning up.
const EXTRAS_FILES: usize = 1_000;

/// Keep refs worth cutting down to the heads.
const KEEP_REFS_COUNT: usize = 10_000;

#[derive(Debug, Error)]
pub enum GcError {
    #[error("I/O error on {path}")]
    Io { path: PathBuf, source: io::Error },
    #[error(transparent)]
    Open(#[from] StoreLoadError),
    #[error(transparent)]
    Load(#[from] jj_lib::repo::RepoLoaderError),
    #[error(transparent)]
    OpHeads(#[from] jj_lib::op_heads_store::OpHeadsStoreError),
    #[error(transparent)]
    OpStore(#[from] jj_lib::op_store::OpStoreError),
    #[error(transparent)]
    Index(#[from] jj_lib::index::IndexError),
    #[error(transparent)]
    Config(#[from] jj_lib::config::ConfigGetError),
    #[error(transparent)]
    Objects(#[from] ObjectError),
}

fn io_err(path: &Path) -> impl FnOnce(io::Error) -> GcError + '_ {
    move |source| GcError::Io {
        path: path.to_owned(),
        source,
    }
}

/// The file whose modification time says when gc last ran in the repository.
fn marker(repo_path: &Path) -> PathBuf {
    repo_path.join("musubi/gc")
}

/// What the repository at `repo_path`, its `.jj/repo`, has to clean up: files in jj's extras
/// table, and keep refs. Counted without loading the repository.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cruft {
    pub extras_files: usize,
    pub keep_refs: usize,
}

impl Cruft {
    pub fn of(repo_path: &Path) -> Self {
        let count = |dir: &Path| fs::read_dir(dir).map_or(0, Iterator::count);
        let store = repo_path.join("store");
        // The git backend's `git_target` names its git directory, relative to the store.
        let keep_refs = fs::read_to_string(store.join("git_target")).map_or(0, |target| {
            let git_dir = store.join(target.trim());
            let packed_name = format!(" {KEEP_REFS}");
            let packed = fs::read_to_string(git_dir.join("packed-refs")).map_or(0, |packed| {
                packed
                    .lines()
                    .filter(|line| line.contains(&packed_name))
                    .count()
            });
            count(&git_dir.join(KEEP_REFS)) + packed
        });
        Self {
            extras_files: count(&store.join("extra")),
            keep_refs,
        }
    }

    /// Whether there is enough to make running gc worth it.
    pub fn worth_collecting(self) -> bool {
        self.extras_files > EXTRAS_FILES || self.keep_refs > KEEP_REFS_COUNT
    }
}

/// Whether gc is due in the repository at `repo_path`, its `.jj/repo`: it hasn't run, or
/// failed, in the last [`INTERVAL`]; there is enough to clean up; and the machine isn't on
/// battery.
pub fn due(repo_path: &Path, now: SystemTime) -> bool {
    let last = fs::metadata(marker(repo_path)).and_then(|meta| meta.modified());
    let recent = last.is_ok_and(|last| now.duration_since(last).is_ok_and(|age| age < INTERVAL));
    // Asked last: on macOS, it starts a process.
    !recent && Cruft::of(repo_path).worth_collecting() && !crate::objects::on_battery()
}

/// Runs gc in the repository if it is [`due`], unless another process is running it, and
/// records when it ran, or failed to, so that it waits [`INTERVAL`] before trying again.
/// Returns whether it ran.
pub fn collect_if_due(repo_path: &Path, settings: &UserSettings) -> Result<bool, GcError> {
    let now = SystemTime::now();
    if !due(repo_path, now) {
        return Ok(false);
    }
    let lock_path = repo_path.join("musubi/gc.lock");
    let lock = fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(false)
        .open(&lock_path)
        .map_err(io_err(&lock_path))?;
    match lock.try_lock() {
        Ok(()) => {}
        Err(fs::TryLockError::WouldBlock) => return Ok(false),
        Err(fs::TryLockError::Error(err)) => return Err(io_err(&lock_path)(err)),
    }
    // Another process may have run it while this one waited to look.
    if !due(repo_path, now) {
        return Ok(false);
    }
    let collected = collect(repo_path, settings, now - KEEP_NEWER);
    if !matches!(collected, Ok(false)) {
        let path = marker(repo_path);
        // Its time is what matters, so it is never written to.
        let file = fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)
            .map_err(io_err(&path))?;
        file.set_modified(now).map_err(io_err(&path))?;
    }
    collected
}

/// Cleans up in the repository at `repo_path` what jj's gc would, but for pruning git
/// objects: operations that no op head reaches, then keep refs other than the heads of jj's
/// index, and replaced extras segments, if written before `keep_newer`. Does nothing, and
/// returns `false`, unless the repository has exactly one op head: with more, a merge is due
/// first.
pub fn collect(
    repo_path: &Path,
    settings: &UserSettings,
    keep_newer: SystemTime,
) -> Result<bool, GcError> {
    let loader =
        RepoLoader::init_from_file_system(settings, repo_path, &default_backend_factories())?;
    let heads = loader.op_heads_store().get_op_heads().block_on()?;
    let [head] = heads.as_slice() else {
        return Ok(false);
    };
    let op = loader.load_operation(head).block_on()?;
    let repo = loader.load_at(&op).block_on()?;
    tracing::info!("collecting garbage in {}", repo_path.display());
    repo.op_store()
        .gc(std::slice::from_ref(op.id()), keep_newer)
        .block_on()?;
    if let Ok(backend) = jj_lib::git::get_git_backend(repo.store()) {
        let executable = GitSubprocessOptions::from_settings(settings)?.executable_path;
        let git = GitObjects::new(&executable, backend.git_repo_path());
        let root = repo.store().root_commit_id();
        // Every commit a reachable operation refers to is one of these or an ancestor.
        let heads: HashSet<CommitId> = repo
            .index()
            .all_heads_for_gc()?
            .filter(|id| id != root)
            .collect();
        let removed = git.rebuild_keep_refs(&heads, keep_newer)?;
        git.collect_extras(&repo_path.join("store"), keep_newer)?;
        tracing::info!("removed {removed} keep refs");
    }
    Ok(true)
}

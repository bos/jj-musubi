//! Objects that canonical operations refer to, and moving them between stores.
//!
//! A canonical operation requires the commits its view and `commit_predecessors` mention,
//! plus everything reachable from them. Objects move between stores as bundles, one framed
//! file format for every backend (see [`bundle`]), so the transfer layer never needs to know
//! which backend a hive uses. See "Objects" in docs/design.md.

use std::collections::BTreeSet;
use std::io;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::op_store::Operation;
use jj_lib::op_store::View;
use jj_lib::stacked_table::TableStoreError;
use thiserror::Error;

pub mod bundle;
mod git;
mod simple;

pub use git::ExtrasEntry;
pub use git::GitObjects;
pub use git::GitStore;
pub use git::REPOSITORY_ENV;
pub use git::extras_to_ship;
pub use git::import_extras;
pub use simple::SimpleStore;

#[derive(Debug, Error)]
pub enum ObjectError {
    #[error("failed to run git {args}")]
    Spawn { args: String, source: io::Error },
    #[error("git {args} failed: {stderr}")]
    Git { args: String, stderr: String },
    #[error("I/O error")]
    Io(#[from] io::Error),
    #[error("missing objects after receiving bundle: {0}")]
    NotConnected(String),
    #[error("failed to read commit {0}")]
    ReadCommit(String),
    #[error("backend extras table")]
    Extras(#[from] TableStoreError),
    #[error("malformed extras entry for {0}")]
    MalformedExtras(String),
    #[error("malformed bundle: {0}")]
    MalformedBundle(String),
    #[error("malformed {kind} object {id}")]
    MalformedObject { kind: &'static str, id: String },
    #[error("backend error")]
    Backend(#[from] jj_lib::backend::BackendError),
    /// An error from a caller's record handler, passed through [`bundle::read`].
    #[error(transparent)]
    Nested(Box<dyn std::error::Error + Send + Sync>),
}

/// Every commit `op` requires: those its view refers to, and its recorded predecessors.
/// The caller excludes the backend's root commit, which no store contains.
pub fn referenced_commits(op: &Operation, view: &View) -> BTreeSet<CommitId> {
    let mut ids: BTreeSet<CommitId> = view.head_ids.iter().cloned().collect();
    let targets = view
        .local_bookmarks
        .values()
        .chain(view.local_tags.values())
        .chain(view.git_refs.values())
        .chain(view.git_heads.values())
        .chain(view.remote_views.values().flat_map(|remote| {
            remote
                .bookmarks
                .values()
                .chain(remote.tags.values())
                .map(|r| &r.target)
        }));
    for target in targets {
        ids.extend(target.iter().flatten().cloned());
    }
    ids.extend(view.wc_commit_ids.values().cloned());
    if let Some(predecessors) = &op.commit_predecessors {
        for (commit, preds) in predecessors {
            ids.insert(commit.clone());
            ids.extend(preds.iter().cloned());
        }
    }
    ids
}

/// A store of commits and everything they reach, able to exchange bundles with another
/// store of the same backend.
pub trait ObjectStore {
    /// The subset of `commits` not present.
    fn missing(&self, commits: &[CommitId]) -> Result<Vec<CommitId>, ObjectError>;

    /// Writes a bundle to `out` holding everything reachable from `wants` and not from
    /// `haves`. The receiver must have every object reachable from `haves`; haves this store
    /// lacks are ignored.
    fn export(&self, wants: &[CommitId], haves: &[CommitId], out: &Path)
    -> Result<(), ObjectError>;

    /// Fails unless everything reachable from `wants` is present, given that everything
    /// reachable from `haves` is.
    fn check_connected(&self, wants: &[CommitId], haves: &[CommitId]) -> Result<(), ObjectError>;

    /// The commits reachable from `wants` but not from `haves` whose only parent is the
    /// root commit: in git terms, the parentless commits. Two repositories that share one
    /// share history.
    fn roots(&self, wants: &[CommitId], haves: &[CommitId]) -> Result<Vec<CommitId>, ObjectError>;

    /// Stores a bundle's objects, then fails unless everything reachable from `wants` is
    /// present, given that everything reachable from `haves` was.
    fn import(
        &self,
        bundle: &Path,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<(), ObjectError>;
}

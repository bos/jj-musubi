//! Objects that canonical operations refer to, and moving them between stores.
//!
//! A canonical operation requires the commits its view and `commit_predecessors` mention,
//! plus everything reachable from them. Objects move between stores as bundles, one framed
//! file format for every backend (see [`bundle`]), so the transfer layer never needs to know
//! which backend a hive uses. See "Objects" in docs/design.md.

use std::io;
use std::path::Path;

use jj_lib::backend::CommitId;
use jj_lib::simple_backend::SimpleBackend;
use jj_lib::stacked_table::TableStoreError;
use jj_lib::store::Store;
use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;

use crate::git_command::GitError;

pub mod bundle;
mod git;
mod power;
mod simple;

pub use git::GitObjects;
pub use git::GitStore;
pub use git::Incompleteness;
pub use power::on_battery;
pub use simple::SimpleStore;

/// A backend musubi supports: the kind of repository a hive's machines have, which decides
/// how its objects are stored and moved.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Backend {
    /// jj's git backend, its default.
    Git,
    /// jj's simple backend, which exists mainly for jj's own tests.
    Simple,
}

impl Backend {
    /// The backend of a jj store, if musubi supports it.
    pub fn of(store: &Store) -> Option<Self> {
        if jj_lib::git::get_git_backend(store).is_ok() {
            Some(Self::Git)
        } else if store.backend().name() == SimpleBackend::NAME {
            Some(Self::Simple)
        } else {
            None
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::Git => "git",
            Self::Simple => "simple",
        }
    }

    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "git" => Some(Self::Git),
            "simple" => Some(Self::Simple),
            _ => None,
        }
    }

    /// The backend's root commit, which every view may mention and no store contains.
    pub fn root_commit(self) -> CommitId {
        match self {
            Self::Git => CommitId::from_bytes(&[0; 20]),
            Self::Simple => CommitId::from_bytes(&[0; 64]),
        }
    }
}

#[derive(Debug, Error)]
pub enum ObjectError {
    #[error(transparent)]
    Git(#[from] GitError),
    #[error("reading the git repository")]
    Gix(#[source] Box<dyn std::error::Error + Send + Sync>),
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

    /// Tells a hub's store the visible heads of its accepted head's view, which a store may
    /// index for exporting what they reach.
    fn mark_head(&self, _commits: &[CommitId]) -> Result<(), ObjectError> {
        Ok(())
    }
}

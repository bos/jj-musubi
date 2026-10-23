//! What can go wrong in a node's repository.

use std::io;
use std::path::PathBuf;

use jj_lib::backend::BackendError;
use jj_lib::config::ConfigGetError;
use jj_lib::git::GitExportError;
use jj_lib::lock::FileLockError;
use jj_lib::op_heads_store::OpHeadsStoreError;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::OperationId;
use jj_lib::repo::RepoLoaderError;
use jj_lib::repo::StoreLoadError;
use thiserror::Error;

use crate::canonical::CanonicalError;
use crate::format_guard::FormatError;
use crate::git_command::GitError;
use crate::objects::Incompleteness;
use crate::objects::ObjectError;

#[derive(Debug, Error)]
pub enum NodeError {
    #[error("failed to load repository")]
    Load(#[from] StoreLoadError),
    #[error("unsupported op store {0:?}; musubi needs simple_op_store")]
    UnsupportedOpStore(String),
    #[error(transparent)]
    OpStore(#[from] OpStoreError),
    #[error(transparent)]
    OpHeads(#[from] OpHeadsStoreError),
    #[error(transparent)]
    RepoLoader(#[from] RepoLoaderError),
    /// A jj 0.46 bug, until jj fixes it: jj cannot merge concurrent operations when the
    /// merge would rebase a merge commit onto the root commit, and until then every jj
    /// command fails to load the repository (docs/races.md, "Known jj limitations").
    #[error(
        "jj cannot merge this machine's concurrent operations: the merge would create a merge \
         commit on the root commit (a jj bug). On this machine, run `jj --at-op <head> op log \
         -n1` for each head in .jj/repo/op_heads/heads, then `jj --at-op <head> op revert @` \
         at the head whose operation made the merge commit"
    )]
    RootParentMerge(#[source] RepoLoaderError),
    #[error(transparent)]
    Canonical(#[from] CanonicalError),
    #[error("operation {op}: {source}")]
    Format { op: String, source: FormatError },
    #[error(transparent)]
    GitExport(#[from] GitExportError),
    #[error(transparent)]
    Lock(#[from] FileLockError),
    #[error("I/O error on {path}")]
    Io { path: PathBuf, source: io::Error },
    #[error("the op store wrote realized operation {0} under another id")]
    MisnamedWrite(String),
    #[error("canonical operation {0} is not realized and cannot be: {1}")]
    NotRealizable(String, &'static str),
    #[error("operation {op} names canonical operation {canonical}, which is not stored")]
    DanglingAttribute { op: String, canonical: String },
    #[error("bad hive settings in {op}: {message}")]
    Settings { op: String, message: String },
    /// jj cannot merge this machine's concurrent operations with the hive's, as when two
    /// machines' rebases form a loop: jj 0.46 then panics ("graph has cycle").
    #[error(
        "jj cannot merge this machine's operations with the hive's ({reason}). musubi has not \
         applied the hive's latest operations here, so jj keeps working. To go on, revert this \
         machine's operation that conflicts with them, one of those the hive doesn't have yet \
         (newest first: {listed}), with `jj op revert <id>`; musubi then catches up"
    )]
    Unmergeable {
        /// This machine's operations the hive doesn't have, newest first.
        ours: Vec<OperationId>,
        listed: String,
        reason: String,
    },
    #[error("repo config {path}: {message}")]
    Config { path: PathBuf, message: String },
    #[error(
        "operation {op} realizes canonical operation {canonical} but no longer has its parents \
         (was `jj op abandon` run?); musubi does not replicate op abandon yet, so replication is \
         paused for this repository"
    )]
    RewrittenRealization { op: String, canonical: String },
    /// The hub accepts an operation only with everything it requires, which a shallow or
    /// partial clone can't send.
    #[error(
        "musubi needs all of a repository's history, and this one is {0}. `musubi clone <hive> \
         <dir>` makes a full copy of a hive from its hub, and `jj git clone`, without \
         `--depth`, a full clone of a remote"
    )]
    Incomplete(Incompleteness),
    #[error(transparent)]
    Objects(#[from] ObjectError),
    #[error(transparent)]
    Git(#[from] GitError),
    #[error(transparent)]
    UserSettings(#[from] ConfigGetError),
    #[error(transparent)]
    Backend(#[from] BackendError),
    #[error("musubi supports the git and simple backends, not {0:?}")]
    UnsupportedBackend(String),
    #[error(transparent)]
    CheckOut(#[from] jj_lib::repo::CheckOutCommitError),
    #[error("index error: {0}")]
    Index(String),
    #[error(transparent)]
    Commit(#[from] jj_lib::transaction::TransactionCommitError),
}

//! What can go wrong in a node's repository.

use std::io;
use std::path::PathBuf;

use jj_lib::backend::BackendError;
use jj_lib::config::ConfigGetError;
use jj_lib::git::GitExportError;
use jj_lib::lock::FileLockError;
use jj_lib::op_heads_store::OpHeadsStoreError;
use jj_lib::op_store::OpStoreError;
use jj_lib::repo::RepoLoaderError;
use jj_lib::repo::StoreLoadError;
use thiserror::Error;

use crate::canonical::CanonicalError;
use crate::format_guard::FormatError;
use crate::git_command::GitError;
use crate::objects::Incompleteness;
use crate::objects::ObjectError;
use crate::op_id::LocalOp;

/// What a user sees once this repository lost history the hive has, as after `jj op abandon`,
/// which no retry gets past, and the way on. docs/troubleshooting.md says the rest, such as
/// bringing work across.
const HISTORY_GONE: &str = "this repository lost history the hive has (was `jj op abandon` \
     run?), so it can't sync again: make a new copy with `musubi clone`, bring this one's work \
     across to it, then run `musubi leave --force` here";

/// Why musubi can't inspect, record or prune this copy's unpublished history. None has a
/// source, so a chain of causes ends here as it did when these were plain strings.
#[derive(Debug, Error)]
pub enum PublicationError {
    #[error("cannot establish publication history from {0}")]
    UnreadableMarker(&'static str),
    /// The record of attempted publications doesn't parse, or fails its checksum.
    #[error("cannot read this copy's record of attempted publications: {0}")]
    UnreadableOffers(String),
    #[error("invalid attempted publication identity")]
    InvalidOfferedId,
    #[error("the source history of an attempted publication is missing")]
    MissingOfferedHistory,
    #[error("invalid retained intent: {0}")]
    MalformedIntent(serde_json::Error),
    #[error("invalid retained intent commit id")]
    InvalidIntentCommit,
    #[error("retained intent is not referenced by its operation")]
    UnreferencedIntent,
    #[error("the initial join's source history is missing")]
    MissingJoinSource,
    /// Encoding JSON that musubi itself built, which doesn't fail in practice.
    #[error("{0}")]
    Json(serde_json::Error),
    #[error("the snapshot invocation marker is empty")]
    EmptyInvocation,
    #[error("choose at least one unpublished operation to prune")]
    NothingSelected,
    #[error("{0:?} is not a jj operation id")]
    NotOperationId(String),
    #[error("operation {0} is not unpublished work; run `musubi sync --outgoing`")]
    NotUnpublished(String),
    #[error("operation prefix {0} is ambiguous; use more of its id")]
    AmbiguousPrefix(String),
    #[error(
        "operation {0} was offered to the hub or predates publication tracking; this cleanup \
         only removes history known never to have been offered"
    )]
    AlreadyOffered(String),
    /// An operation's description, which is all a user has to recognize it by.
    #[error(
        "cannot safely prune this history: jj did not record enough information to preserve \
         changes from {0:?}\nHint: run `musubi sync --outgoing` to inspect or approve this work"
    )]
    UncertainIntent(String),
    #[error(
        "reconcile this workspace's operations with `jj status` before choosing snapshots to \
         prune"
    )]
    DivergentHeads,
    #[error("the current operation changed; inspect outgoing work again")]
    PreviewHeadChanged,
    #[error("outgoing work changed; run the cleanup again")]
    OutgoingChanged,
    #[error("invalid cleanup source operation")]
    InvalidCleanupSource,
    #[error("the current operation changed; run the cleanup again")]
    LockedHeadChanged,
    #[error("the current operation changed")]
    AppliedHeadChanged,
    #[error("cannot read workspace {name} at {}: {reason}", .path.display())]
    UnreadableWorkspace {
        name: String,
        path: PathBuf,
        reason: String,
    },
    #[error(
        "workspaces {first} and {second} share a registered path at {}; restore their paths or \
         forget the obsolete workspace before pruning",
        .path.display()
    )]
    SharedWorkspacePath {
        first: String,
        second: String,
        path: PathBuf,
    },
    #[error("cannot locate workspace {0}; recreate or forget it before pruning")]
    MissingWorkspace(String),
    #[error("cannot locate workspace {name}: {reason}")]
    UnlocatableWorkspace { name: String, reason: String },
    #[error(
        "workspace {name} at {} no longer identifies this repo; recreate or forget it before \
         pruning",
        .path.display()
    )]
    ForeignWorkspace { name: String, path: PathBuf },
    #[error("workspace {0} is no longer in the current view")]
    WorkspaceLeftView(String),
    #[error(
        "workspace {name} must be updated before pruning\nHint: run `jj status` in {}",
        .path.display()
    )]
    StaleWorkspace { name: String, path: PathBuf },
    #[error("the source of an unpublished operation is missing")]
    MissingSourceFacts,
    #[error(
        "jj would give distinct operations the same identity; this selection cannot be pruned \
         safely"
    )]
    IdentityCollision,
    #[error("could not prepare the cleanup checkpoint")]
    NoCheckpoint,
    #[error("this cleanup cannot preserve the current repository view")]
    ViewChanged,
    #[error(
        "this selection would change another copy's activity or membership; choose different \
         snapshots or approve publication"
    )]
    ForeignPresenceChanged,
    #[error("this cleanup cannot preserve the current workspace and Git-ref state")]
    StateChanged,
    #[error("a prepared operation is missing")]
    MissingPrepared,
    #[error("this cleanup would change an unselected operation's saved state")]
    UnselectedChanged,
    #[error("this cleanup would discard intentional change history")]
    IntentLost,
    #[error("the prepared cleanup differs from its preview; no history was pruned")]
    PreviewMismatch,
    /// Each workspace whose metadata jj couldn't update, with where it is and why.
    #[error(
        "cleanup finished, but workspace metadata could not be updated for {}",
        .0.join("; ")
    )]
    WorkspacesNotUpdated(Vec<String>),
}

#[derive(Debug, Error)]
pub enum NodeError {
    #[error(transparent)]
    Publication(#[from] PublicationError),
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
    /// An op head whose history is from before this repository joined, as a `jj` command
    /// makes that loaded the repository before `musubi join` and wrote after it: the hive
    /// takes its work only once a merge with this machine's other op heads does.
    #[error(
        "operation {0} comes from before this repository joined its hive; it syncs once jj \
         merges it with the operation history since, as the next jj command does"
    )]
    BeforeJoin(String),
    #[error("the op store wrote realized operation {0} under another id")]
    MisnamedWrite(String),
    #[error("canonical operation {0} is not realized and cannot be: {1}")]
    NotRealizable(String, &'static str),
    #[error("operation {op} names canonical operation {canonical}, which is not stored")]
    DanglingAttribute { op: String, canonical: String },
    #[error(
        "remote destinations disagree with this hive's recorded names: {0}; use distinct remote names for different destinations"
    )]
    RemoteBindings(String),
    /// jj cannot merge this machine's concurrent operations with the hive's, as when two
    /// machines' rebases form a loop: jj 0.47 then panics ("graph has cycle").
    #[error(
        "jj cannot merge this machine's operations with the hive's ({reason}). musubi has not \
         applied the hive's latest operations here, so jj keeps working. {advice}"
    )]
    Unmergeable {
        /// This machine's operations the hive doesn't have, newest first.
        ours: Vec<LocalOp>,
        /// The operation to revert: the newest of this machine's that the hive doesn't have
        /// whose revert lets jj merge the hive's operation, or failing one, the oldest whose
        /// own change jj panics merging with it. `None` where none is found, as when the
        /// failing merge is of this machine's own operations, in which case `advice` lists them.
        culprit: Option<LocalOp>,
        advice: String,
        reason: String,
    },
    #[error("repo config {path}: {message}")]
    Config { path: PathBuf, message: String },
    /// `jj op abandon`, or something else, made operations that the hub accepted unreachable.
    /// musubi doesn't pass that on to other machines, and syncing the history that is left
    /// would put them back.
    #[error("{HISTORY_GONE}")]
    UnreachableHistory,
    /// An operation that realizes one of the hive's no longer has that operation's parents,
    /// as after `jj op abandon`. Which, the log says.
    #[error("{HISTORY_GONE}")]
    RewrittenRealization,
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

//! The independent axes of a realization, which the regression examples and the generated
//! rules compose the same way: `Realization::concurrent(..).beside(..).with_locked_export()`.

use jj_lib::op_store::OperationId;
use jj_lib::op_store::RefTarget;

use super::Model;
use super::Ref;
use super::SharedRefs;

/// A native command whose imports, edit and exports the model predicts. The other machine
/// runs one before publishing; this machine may run one beside the resulting realization.
#[derive(Clone, Debug)]
pub(super) enum RefCommand {
    /// The command moves `x`, `y` or `t` (`Refs::jj_sets`).
    Sets(Ref, RefTarget),
    /// `y` moves in `origin`, and `jj git fetch` fetches it (`Refs::jj_fetches_from`).
    Fetches(RefTarget),
}

/// Whether the other machine first takes this machine's latest operations, or acts on
/// the history both had when they last synced.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum PeerOrder {
    Following,
    Concurrent,
}

/// The physical condition of `refs/heads/x` while this machine realizes and exports.
#[derive(Clone, Copy, Debug)]
pub(super) enum GitExport {
    Writable,
    XLocked,
}

impl GitExport {
    pub(super) fn x_locked(self) -> bool {
        matches!(self, Self::XLocked)
    }
}

/// The independent axes of a realization: the other machine's command and history, the
/// export's access to git, and an optional command here before realizing the published work.
pub(super) struct Realization {
    pub(super) command: RefCommand,
    pub(super) order: PeerOrder,
    pub(super) export: GitExport,
    pub(super) beside: Option<RefCommand>,
}

impl Realization {
    pub(super) fn following(command: RefCommand) -> Self {
        Self {
            command,
            order: PeerOrder::Following,
            export: GitExport::Writable,
            beside: None,
        }
    }

    pub(super) fn concurrent(command: RefCommand) -> Self {
        Self {
            order: PeerOrder::Concurrent,
            ..Self::following(command)
        }
    }

    pub(super) fn beside(self, command: RefCommand) -> Self {
        Self {
            beside: Some(command),
            ..self
        }
    }

    pub(super) fn with_locked_export(self) -> Self {
        Self {
            export: GitExport::XLocked,
            ..self
        }
    }
}

/// The last common operation and model, and this machine's head before a command beside
/// the realization. Native merge parents decide the order in which the model merges them.
pub(super) struct RealizationBase {
    pub(super) synced_op: OperationId,
    pub(super) model: Model,
    pub(super) ours: OperationId,
}

/// The other machine's independently predicted command result and observed shared fields.
pub(super) struct PeerResult {
    pub(super) expected: Model,
    pub(super) canonical: SharedRefs,
}

//! Prepared-view and write-queue ownership for a line of realizations.
//!
//! A queued operation is visible in the in-memory translation map before its write finishes.
//! Settling joins every writer before persisting any translation. Failure or simulated crash
//! invalidates the last-parent, own-workspace and prepared-view caches together, but leaves
//! unrelated published ancestry and kept-name context alone.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::sync::Arc;
use std::thread;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::ref_name::WorkspaceNameBuf;
use pollster::FutureExt as _;

use super::super::NodeError;
use super::super::NodeRepo;
use super::super::view::LocalView;
use super::super::view::PerMachine;
use super::Realization;
use super::workspaces::Kept;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

/// jj's op store syncs each file: bounded parallel writes avoid waiting on each separately.
pub(super) const MAX_UNWRITTEN: usize = 32;

type LastRealized = (LocalOp, Arc<PerMachine>);
type OwnWorkspaces = (LocalOp, Arc<BTreeMap<WorkspaceNameBuf, CommitId>>);

/// Disposable context for constructing and writing local representations. The queue remains
/// owned here until every writer has joined, even when dependent cache entries are invalidated.
#[derive(Default)]
pub(in crate::node) struct State {
    last_realized: Option<LastRealized>,
    unwritten: Vec<Unwritten>,
    prepared: Option<PreparedViews>,
    last_own: Option<OwnWorkspaces>,
    kept: Option<KeptMemo>,
}

struct PreparedViews {
    per_machine: Arc<PerMachine>,
    reserved: Arc<BTreeSet<WorkspaceNameBuf>>,
    views: HashMap<CanonicalOp, LocalView>,
}

struct KeptMemo {
    heads: Vec<LocalOp>,
    start: LocalOp,
    renaming: BTreeSet<WorkspaceNameBuf>,
    kept: Kept,
}

struct Unwritten {
    write: thread::JoinHandle<Result<(), NodeError>>,
    local: LocalOp,
    canonical: CanonicalOp,
}

impl State {
    pub(super) fn last_realized(&self) -> Option<&LastRealized> {
        self.last_realized.as_ref()
    }

    pub(super) fn last_own(&self) -> Option<&OwnWorkspaces> {
        self.last_own.as_ref()
    }

    pub(super) fn remember_last(&mut self, local: LocalOp, fields: Arc<PerMachine>) {
        self.last_realized = Some((local, fields));
    }

    pub(super) fn remember_own(
        &mut self,
        local: LocalOp,
        own: BTreeMap<WorkspaceNameBuf, CommitId>,
    ) {
        self.last_own = Some((local, Arc::new(own)));
    }

    pub(super) fn take_prepared(
        &mut self,
        id: &CanonicalOp,
        per_machine: &Arc<PerMachine>,
        reserved: &Arc<BTreeSet<WorkspaceNameBuf>>,
    ) -> Option<LocalView> {
        let prepared = self.prepared.as_mut()?;
        if Arc::ptr_eq(&prepared.per_machine, per_machine) && prepared.reserved == *reserved {
            prepared.views.remove(id)
        } else {
            None
        }
    }

    pub(super) fn prepare(
        &mut self,
        per_machine: Arc<PerMachine>,
        reserved: Arc<BTreeSet<WorkspaceNameBuf>>,
        views: HashMap<CanonicalOp, LocalView>,
    ) {
        self.prepared = Some(PreparedViews {
            per_machine,
            reserved,
            views,
        });
    }

    pub(super) fn clear_prepared(&mut self) {
        self.prepared = None;
    }

    /// Invalidates exactly the context depending on local representation identities. Writers
    /// are still joined by settle; neither their queue nor independent memo entries are lost.
    pub(in crate::node) fn invalidate(&mut self) {
        self.last_realized = None;
        self.last_own = None;
        self.prepared = None;
    }

    pub(super) fn pending_among(&self, starts: &[LocalOp]) -> bool {
        self.unwritten
            .iter()
            .any(|write| starts.contains(&write.local))
    }

    pub(super) fn kept(
        &self,
        heads: &[LocalOp],
        start: &LocalOp,
        renaming: &BTreeSet<WorkspaceNameBuf>,
    ) -> Option<Kept> {
        let memo = self.kept.as_ref()?;
        (memo.heads.as_slice() == heads && memo.start == *start && memo.renaming == *renaming)
            .then(|| memo.kept.clone())
    }

    pub(super) fn remember_kept(
        &mut self,
        heads: Vec<LocalOp>,
        start: LocalOp,
        renaming: BTreeSet<WorkspaceNameBuf>,
        kept: Kept,
    ) {
        self.kept = Some(KeptMemo {
            heads,
            start,
            renaming,
            kept,
        });
    }

    pub(super) fn advance_kept(&mut self, starts: &[LocalOp], realized: &LocalOp) {
        if let Some(memo) = &mut self.kept
            && starts == [memo.start.clone()]
        {
            memo.start = realized.clone();
        }
    }
}

impl NodeRepo {
    /// Starts writing a realization, after waiting for those being written if there are
    /// already enough of them.
    pub(super) fn write_later(
        &mut self,
        realization: Realization,
        canonical: CanonicalOp,
    ) -> Result<(), NodeError> {
        if self.realizing.unwritten.len() >= MAX_UNWRITTEN {
            self.settle()?;
        }
        let Realization {
            id,
            op,
            view,
            per_machine,
        } = realization;
        let store = self.loader.op_store().clone();
        let expected = id.clone();
        let write = thread::Builder::new()
            .name("write operation".to_owned())
            .spawn(move || {
                let view_id = store.write_view(&view).block_on()?;
                let written = store.write_operation(&op).block_on()?;
                if view_id != op.view_id || written != expected.0 {
                    return Err(NodeError::MisnamedWrite(expected.0.hex()));
                }
                Ok(())
            })
            .map_err(|source| NodeError::Io {
                path: self.repo_path.join("op_store"),
                source,
            })?;
        self.map.insert_unwritten(id.clone(), canonical.clone());
        self.realizing.last_realized = Some((id.clone(), per_machine));
        self.realizing.unwritten.push(Unwritten {
            write,
            local: id,
            canonical,
        });
        Ok(())
    }

    /// Joins every queued realization writer, then records its translation in the map's
    /// file. On success the batch queued for this call is readable from the native stores
    /// and its translations have been appended. This does not move op heads or workspaces,
    /// and makes no guarantee of surviving a power cut.
    ///
    /// If a native write failed, all writers are still joined and the map forgets the whole
    /// batch: a later realization may refer to the failed one. Retrying writes the same
    /// operations unless this machine's own names in its op heads changed meanwhile
    /// (`reserved_names`). A writer's panic is propagated after that same cleanup.
    ///
    /// A translation-file error can leave only part of the batch recorded, while its
    /// mappings remain in memory. The queue has already been consumed: a later empty
    /// `settle` does not retry those appends. Reopen the handle before retrying those
    /// realizations.
    pub fn settle(&mut self) -> Result<(), NodeError> {
        let unwritten = std::mem::take(&mut self.realizing.unwritten);
        let mut failed = None;
        let mut panicked = None;
        let mut translations = vec![];
        for Unwritten {
            write,
            local,
            canonical,
        } in unwritten
        {
            match write.join() {
                Ok(Ok(())) => {}
                Ok(Err(err)) => {
                    failed.get_or_insert(err);
                }
                Err(panic) => {
                    panicked.get_or_insert(panic);
                }
            }
            translations.push((local, canonical));
        }
        if let Some(panic) = panicked {
            for (local, canonical) in &translations {
                self.map.forget(local, canonical);
            }
            self.realizing.invalidate();
            std::panic::resume_unwind(panic);
        }
        if let Some(err) = failed {
            for (local, canonical) in &translations {
                self.map.forget(local, canonical);
            }
            self.realizing.invalidate();
            return Err(err);
        }
        for (local, canonical) in &translations {
            self.map
                .write(local, canonical)
                .map_err(|source| NodeError::Io {
                    path: self.repo_path.join("musubi/translation"),
                    source,
                })?;
        }
        Ok(())
    }
}

// Deliberate test support, compiled for cross-crate integration and fault tests.
// Keep these controls separate from the normal repository API without changing coverage.
impl NodeRepo {
    /// For tests of crashes: waits for the realizations being written, then, as a crash
    /// before [`Self::settle`] would, records none of them, and forgets them as if their
    /// writes had failed. Returns their local ids.
    #[doc(hidden)]
    pub fn crash_before_settling(&mut self) -> Vec<LocalOp> {
        let mut locals = vec![];
        for Unwritten {
            write,
            local,
            canonical,
        } in std::mem::take(&mut self.realizing.unwritten)
        {
            // Whether it wrote everything or failed, a crash would leave it unrecorded.
            drop(write.join());
            self.map.forget(&local, &canonical);
            locals.push(local);
        }
        self.realizing.invalidate();
        locals
    }
}

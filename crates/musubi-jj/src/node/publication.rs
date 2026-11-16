//! Publication budgets for recovery history, inspection, exact approval, and cleanup.
//!
//! `intent` interprets immutable jj transaction facts; `content` walks raw object closures.
//! `accounting` combines those inputs into exact reports and owns its reusable caches.
//! `offers` records attempted publications; `approval` accepts one exact report token.
//! `cleanup` prepares and verifies transactional removal of never-offered recovery history.
//! Native fixtures pin jj's intent boundary; `Musubi.Publication` specifies set accounting.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;

use jj_lib::backend::CommitId;
use jj_lib::op_store::Operation;
use jj_lib::op_store::View;

use super::NodeError;
use super::NodeRepo;
use crate::op_id::CanonicalOp;

mod accounting;
mod approval;
mod cleanup;
mod content;
mod intent;
mod offers;
#[cfg(test)]
mod tests;

pub use accounting::PublicationCache;
pub use accounting::PublicationFile;
pub use accounting::PublicationHeld;
pub use accounting::PublicationLimits;
pub use accounting::PublicationOperation;
pub use accounting::PublicationReport;
pub use approval::APPROVAL_FILE;
pub use approval::approve_publication;
pub use approval::publication_approved;
pub use approval::publication_lock;
pub use cleanup::PublicationCleanup;
pub use intent::CHECKPOINT_ATTRIBUTE;
pub(crate) use intent::INTENT_ATTRIBUTE;
pub use intent::explicit_git_import;
pub(crate) use intent::retained_publication_intent;

use content::ContentGraph;
use intent::Intent;

#[cfg(test)]
use content::Closure;
#[cfg(test)]
use content::FileVersion;
#[cfg(test)]
use intent::view_roots;
#[cfg(test)]
use offers::OFFERS_FILE;

/// The projected survivor that cleanup accounts for before publishing its native operation.
struct Checkpoint {
    id: CanonicalOp,
    operation: Operation,
    required: BTreeSet<CommitId>,
    intentional: BTreeSet<CommitId>,
}

impl NodeRepo {
    /// Namespace and ownership declarations shared by publication checkpoints and fix-ups.
    pub(in crate::node) fn publication_namespace_facts(
        &self,
        head: &CanonicalOp,
    ) -> Result<BTreeMap<String, String>, NodeError> {
        let view = self.canonical.read_operation_view(head)?;
        let presence = self.presence(head)?;
        let namespace = self.workspace_context_of_view(&view, &presence)?;
        let own = crate::canonical::namespace::Namespace {
            source: self.machine.key().to_owned(),
            known: BTreeSet::from([self.machine.key().to_owned()]),
            names: view
                .wc_commit_ids
                .keys()
                .filter_map(|key| {
                    let (owner, name) = crate::workspaces::split_key(key.as_str())?;
                    (owner == self.machine.key())
                        .then(|| (name.to_owned(), key.as_str().to_owned()))
                })
                .collect(),
        };
        Ok(BTreeMap::from([
            (crate::canonical::namespace::ATTRIBUTE.to_owned(), namespace),
            (super::view::LOCAL_WORKSPACES.to_owned(), own.encode()),
        ]))
    }

    fn publication_intent_is_uncertain(
        &self,
        id: &CanonicalOp,
        op: &Operation,
    ) -> Result<bool, NodeError> {
        Intent::new(self).uncertain(id, op)
    }

    fn publication_intentional(
        &self,
        id: &CanonicalOp,
        op: &Operation,
        view: &View,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Intent::new(self).intentional(id, op, view)
    }

    /// Freeze explicit native Git import outputs before private refs are stripped.
    pub(in crate::node) fn publication_git_intent(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<Option<BTreeSet<CommitId>>, NodeError> {
        Intent::new(self).git(op, view)
    }

    fn publication_commit_closure(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        ContentGraph::new(self.loader.store(), &self.repo_path).commits(roots)
    }

    /// Account for immutable recovery history, extending the accepted-basis cache as needed.
    pub fn publication_report(
        &mut self,
        ops: &[CanonicalOp],
        base: &CanonicalOp,
        cache: &mut PublicationCache,
    ) -> Result<PublicationReport, NodeError> {
        self.publication_report_projected(ops, base, cache, None)
    }

    fn publication_report_projected(
        &self,
        ops: &[CanonicalOp],
        base: &CanonicalOp,
        cache: &mut PublicationCache,
        checkpoint: Option<Checkpoint>,
    ) -> Result<PublicationReport, NodeError> {
        accounting::report(self, ops, base, cache, checkpoint)
    }

    /// Reads the latest accepted basis, without contacting the hub or snapshotting files.
    pub fn outgoing_publication(
        &mut self,
        cache: &mut PublicationCache,
    ) -> Result<PublicationReport, NodeError> {
        self.settle()?;
        self.check_abandon()?;
        let base = self
            .stored_base()
            .map_or_else(|| self.canonical.root_operation_id().clone(), |op| op.0);
        let heads = self.canonical_heads()?;
        let excluded: HashSet<_> = self
            .canonical
            .ancestors_until(std::slice::from_ref(&base), |_| false)?
            .into_iter()
            .collect();
        let ops = self
            .canonical
            .ancestors_until(&heads, |id| excluded.contains(id))?;
        self.publication_report(&ops, &base, cache)
    }
}

#[cfg(test)]
impl NodeRepo {
    fn publication_initial_intentional(
        &self,
        join: &CanonicalOp,
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        Intent::new(self).initial_intentional(join)
    }

    fn publication_command_intent(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        Intent::new(self).command(op, view)
    }

    fn publication_selections(
        &self,
        op: &Operation,
        view: &View,
    ) -> Result<(BTreeSet<CommitId>, bool), NodeError> {
        Intent::new(self).selections(op, view)
    }

    fn publication_files(
        &self,
        roots: impl IntoIterator<Item = CommitId>,
        known: &Closure,
        intentional: &Closure,
    ) -> Result<BTreeSet<FileVersion>, NodeError> {
        ContentGraph::new(self.loader.store(), &self.repo_path).files(roots, known, intentional)
    }

    fn publication_content_bytes(&self, file: &FileVersion) -> Result<u64, NodeError> {
        ContentGraph::new(self.loader.store(), &self.repo_path).content_bytes(file)
    }
}

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
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;

use super::NodeError;
use super::NodeRepo;
use super::git;
use crate::op_id::CanonicalOp;
use crate::presence::FORGET_AFTER_ATTRIBUTE;
use crate::presence::WORK_ATTRIBUTE;
use crate::presence::format_forget_after;

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
    /// A cleanup is new local activity, retaining Git expectations and this
    /// copy's lease. Other copies' complete causal presence is checked before publication;
    /// recreating their work under new identities would change later concurrent merges.
    pub(in crate::node) fn publication_state_attributes(
        &self,
        repo: &ReadonlyRepo,
        head: &CanonicalOp,
    ) -> Result<Vec<BTreeMap<String, String>>, NodeError> {
        let known = git::Expected::default();
        let history = git::History {
            known: &known,
            roots: std::slice::from_ref(&self.root_op_id().0),
            is_join: &|op| self.is_join_point(op),
        };
        let expected = git::format_expected(&git::expected_values(
            repo.store(),
            repo.operation(),
            &history,
        )?);
        let presence = self.presence(head)?;
        let mut attrs = BTreeMap::new();
        // Cleanup is genuine activity by this copy. It must not invent new activity by
        // other copies: their causal work/forget identities are checked before publishing.
        attrs.insert(WORK_ATTRIBUTE.to_owned(), self.machine.key().to_owned());
        attrs.insert(
            FORGET_AFTER_ATTRIBUTE.to_owned(),
            format_forget_after(presence.forget_after(self.machine.key())),
        );
        if let Some(expected) = expected {
            attrs.insert(git::EXPECTED_ATTRIBUTE.to_owned(), expected);
        }
        Ok(vec![attrs])
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
        let base = self
            .stored_base()
            .unwrap_or_else(|| self.canonical.root_operation_id().clone());
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

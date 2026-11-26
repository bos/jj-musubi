//! Selection and application of unpublished recovery-history cleanup.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::btree_map::Entry;
use std::hash::Hash;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::ViewId;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::working_copy::LockedWorkingCopy;
use jj_lib::workspace::WorkspaceLoaderFactory as _;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;

use super::Checkpoint;
use super::NodeError;
use super::NodeRepo;
use super::PublicationCache;
use super::PublicationReport;
use super::intent::view_roots;
use crate::node::PublicationError;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationCleanup {
    pub token: String,
    pub selected: Vec<String>,
    pub before: PublicationReport,
    pub after: PublicationReport,
    heads: Vec<String>,
}

impl PublicationCleanup {
    /// The one local head the preview saw, which cleanup rewrites.
    fn source(&self) -> Result<LocalOp, PublicationError> {
        let id = OperationId::try_from_hex(&self.heads[0])
            .ok_or(PublicationError::InvalidCleanupSource)?;
        Ok(LocalOp(id))
    }
}

/// What an applied cleanup did.
#[cfg_attr(
    not(test),
    expect(dead_code, reason = "tests read the images and checkpoint")
)]
pub(super) struct CleanupEffect {
    /// How many operations it removed.
    pub(super) pruned: usize,
    /// Where each unpublished native operation went: its rewrite, itself, or, once removed,
    /// the images of its parents.
    pub(super) images: HashMap<LocalOp, Vec<LocalOp>>,
    /// The checkpoint now at the head.
    pub(super) checkpoint: LocalOp,
}

struct CleanupWorkspace {
    name: WorkspaceNameBuf,
    root: PathBuf,
    locked: Box<dyn LockedWorkingCopy>,
}

/// What an unpublished operation recorded before cleanup: frozen into its rewrite, and
/// compared against what the rewrite records.
struct SourceFacts {
    view: ViewId,
    intentional: BTreeSet<CommitId>,
}

/// The head cleanup rewrites, read under the op-head lock, and what the rewrite must leave
/// as it was.
struct CleanupSource {
    head: LocalOp,
    intentional: BTreeSet<CommitId>,
    repo: Arc<ReadonlyRepo>,
    context: Vec<BTreeMap<String, String>>,
    foreign: String,
    view: ViewId,
    facts: HashMap<OperationId, SourceFacts>,
}

/// The unpublished native ancestry with the selected operations contracted away.
struct Contraction {
    /// The images of the old head, which the checkpoint goes on top of.
    head: Vec<OperationId>,
    movements: HashMap<LocalOp, Vec<LocalOp>>,
}

/// Every node reachable from `start` through `next`, `start` included.
fn reachable<T: Clone + Eq + Hash, E>(
    start: T,
    mut next: impl FnMut(&T) -> Result<Vec<T>, E>,
) -> Result<HashSet<T>, E> {
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if seen.insert(node.clone()) {
            stack.extend(next(&node)?);
        }
    }
    Ok(seen)
}

/// The nearest intentional versions `id` evolved from, looking through automatic ones.
fn nearest_intentional(
    previous: &BTreeMap<CommitId, Vec<CommitId>>,
    intentional: &BTreeSet<CommitId>,
    id: &CommitId,
) -> Vec<CommitId> {
    let mut stack = previous.get(id).cloned().unwrap_or_default();
    let mut seen = HashSet::new();
    let mut predecessors = BTreeSet::new();
    while let Some(old) = stack.pop() {
        if !seen.insert(old.clone()) {
            continue;
        }
        if intentional.contains(&old) {
            predecessors.insert(old);
        } else {
            stack.extend(previous.get(&old).into_iter().flatten().cloned());
        }
    }
    predecessors.into_iter().collect()
}

/// `parents` with each replaced by its images, keeping order and dropping duplicates.
fn contracted_parents(
    images: &HashMap<OperationId, Vec<OperationId>>,
    parents: &[OperationId],
) -> Vec<OperationId> {
    let mut contracted = vec![];
    for parent in parents {
        for image in images
            .get(parent)
            .cloned()
            .unwrap_or_else(|| vec![parent.clone()])
        {
            if !contracted.contains(&image) {
                contracted.push(image);
            }
        }
    }
    contracted
}

impl NodeRepo {
    /// Lock metadata before op heads, as jj does. Cleanup keeps the current view, so
    /// every local working copy needs that exact recorded commit as its snapshot basis.
    /// Otherwise later stale recovery could merge the discarded ancestry back in.
    fn lock_cleanup_workspaces(&self, head: &LocalOp) -> Result<Vec<CleanupWorkspace>, NodeError> {
        let repo = self.repo_at(head)?;
        let canonical = self
            .canonical_of(head)
            .ok_or(PublicationError::LockedHeadChanged)?;
        let mut own: BTreeSet<_> = self
            .own_workspaces(&repo, &canonical)?
            .into_keys()
            .collect();
        own.extend(self.own_names(&canonical)?);
        let mut paths: BTreeMap<PathBuf, WorkspaceNameBuf> = BTreeMap::new();
        let names: BTreeSet<_> = repo
            .view()
            .wc_commit_ids()
            .keys()
            .chain(own.iter())
            .collect();
        for name in names {
            let label = name.as_str();
            match self.loader.workspace_store().get_workspace_path(name) {
                Ok(Some(path)) => {
                    let path = path.canonicalize().map_err(|err| {
                        PublicationError::UnreadableWorkspace {
                            name: label.to_owned(),
                            path: path.clone(),
                            reason: err.to_string(),
                        }
                    })?;
                    match paths.entry(path) {
                        Entry::Vacant(entry) => {
                            entry.insert(name.clone());
                        }
                        Entry::Occupied(entry) => {
                            return Err(PublicationError::SharedWorkspacePath {
                                first: entry.get().as_str().to_owned(),
                                second: label.to_owned(),
                                path: entry.key().clone(),
                            }
                            .into());
                        }
                    }
                }
                Ok(None) if !own.contains(name) => {}
                Ok(None) => {
                    return Err(PublicationError::MissingWorkspace(label.to_owned()).into());
                }
                Err(err) => {
                    return Err(PublicationError::UnlocatableWorkspace {
                        name: label.to_owned(),
                        reason: err.to_string(),
                    }
                    .into());
                }
            }
        }
        let expected_repo = self
            .repo_path
            .canonicalize()
            .map_err(|source| NodeError::Io {
                path: self.repo_path.clone(),
                source,
            })?;
        let mut locked = Vec::new();
        for (root, name) in paths {
            let label = name.as_str();
            let cannot_read = |err: &dyn std::fmt::Display| PublicationError::UnreadableWorkspace {
                name: label.to_owned(),
                path: root.clone(),
                reason: err.to_string(),
            };
            let workspace = jj_lib::workspace::DefaultWorkspaceLoaderFactory
                .create(&root)
                .map_err(|err| cannot_read(&err))?
                .load(
                    self.loader.settings(),
                    &jj_lib::default_backend_factories::default_backend_factories(),
                    &jj_lib::default_backend_factories::default_working_copy_factories(),
                )
                .map_err(|err| cannot_read(&err))?;
            if workspace.workspace_name().as_str() != name.as_str()
                || workspace
                    .repo_path()
                    .canonicalize()
                    .map_err(|err| cannot_read(&err))?
                    != expected_repo
            {
                return Err(PublicationError::ForeignWorkspace {
                    name: label.to_owned(),
                    path: root.clone(),
                }
                .into());
            }
            let guard = workspace
                .working_copy()
                .start_mutation()
                .block_on()
                .map_err(|err| cannot_read(&err))?;
            let recorded = self
                .loader
                .op_store()
                .read_operation(guard.old_operation_id())
                .block_on()
                .map_err(|err| cannot_read(&err))?;
            let view = self
                .loader
                .op_store()
                .read_view(&recorded.view_id)
                .block_on()
                .map_err(|err| cannot_read(&err))?;
            let current = repo
                .view()
                .get_wc_commit_id(&name)
                .ok_or_else(|| PublicationError::WorkspaceLeftView(label.to_owned()))?;
            let commit = repo.store().get_commit_async(current).block_on()?;
            if view.wc_commit_ids.get(&name) != Some(current)
                || guard.old_tree().tree_ids_and_labels() != commit.tree().tree_ids_and_labels()
            {
                return Err(PublicationError::StaleWorkspace {
                    name: label.to_owned(),
                    path: root.clone(),
                }
                .into());
            }
            locked.push(CleanupWorkspace {
                name,
                root,
                locked: guard,
            });
        }
        Ok(locked)
    }

    pub(super) fn publication_foreign_presence(
        &self,
        head: &CanonicalOp,
    ) -> Result<String, NodeError> {
        let stamp = self.presence(head)?.to_stamp(|work| work.original.hex());
        Ok(stamp
            .lines()
            .filter(|line| line.split_whitespace().nth(1) != Some(self.machine.key()))
            .collect::<Vec<_>>()
            .join("\n"))
    }

    pub(super) fn publication_pending(
        &mut self,
    ) -> Result<(CanonicalOp, Vec<CanonicalOp>), NodeError> {
        self.settle()?;
        let base = self
            .stored_base()
            .unwrap_or_else(|| self.canonical.root_operation_id().clone());
        let known: HashSet<_> = self
            .canonical
            .ancestors_until(std::slice::from_ref(&base), |_| false)?
            .into_iter()
            .collect();
        let heads = self.canonical_heads()?;
        let ops = self
            .canonical
            .ancestors_until(&heads, |op| known.contains(op))?;
        Ok((base, ops))
    }

    fn publication_selection(
        &self,
        selectors: &[String],
        ops: &[CanonicalOp],
    ) -> Result<BTreeSet<LocalOp>, NodeError> {
        if selectors.is_empty() {
            return Err(PublicationError::NothingSelected.into());
        }
        let offered = self.publication_offered_origins()?;
        let local: Vec<_> = ops.iter().filter_map(|id| self.local_of(id)).collect();
        let mut selected = BTreeSet::new();
        for prefix in selectors {
            if prefix.is_empty() || !prefix.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err(PublicationError::NotOperationId(prefix.clone()).into());
            }
            let matches: Vec<_> = local
                .iter()
                .filter(|id| id.0.hex().starts_with(prefix))
                .collect();
            match matches.as_slice() {
                [one] => {
                    selected.insert((*one).clone());
                }
                [] => {
                    return Err(PublicationError::NotUnpublished(prefix.clone()).into());
                }
                _ => {
                    return Err(PublicationError::AmbiguousPrefix(prefix.clone()).into());
                }
            }
        }
        for id in &selected {
            if let Some(canonical) = self.canonical_of(id)
                && offered.contains(&self.canonical.original_id(&canonical)?)
            {
                return Err(PublicationError::AlreadyOffered(id.0.hex()).into());
            }
        }
        Ok(selected)
    }

    pub(super) fn publication_kept_versions(
        &self,
        ops: &[CanonicalOp],
    ) -> Result<BTreeSet<CommitId>, NodeError> {
        let mut roots = BTreeSet::new();
        for id in ops {
            let op = self.canonical.read_operation(id)?;
            if self.publication_intent_is_uncertain(id, &op)? {
                return Err(
                    PublicationError::UncertainIntent(op.metadata.description.clone()).into(),
                );
            }
            roots.extend(self.publication_intentional(
                id,
                &op,
                &self.canonical.read_view(&op.view_id)?,
            )?);
        }
        Ok(roots)
    }

    /// Snapshots made by a caller's uniquely marked jj invocation. The CLI uses this to
    /// fold its own pre-cleanup capture into the checkpoint: retaining the capture would
    /// also retain the predecessor containing files the user just deleted. Concurrent
    /// commands and earlier snapshots remain outside this implicit selection.
    pub fn publication_snapshots_from(
        &mut self,
        invocation: &str,
    ) -> Result<Vec<String>, NodeError> {
        if invocation.is_empty() {
            return Err(PublicationError::EmptyInvocation.into());
        }
        let (_, pending) = self.publication_pending()?;
        let mut snapshots = Vec::new();
        for id in pending {
            let Some(local) = self.local_of(&id) else {
                continue;
            };
            let operation = self.loader.op_store().read_operation(&local.0).block_on()?;
            if operation.metadata.is_snapshot
                && OpAttrs(&operation.metadata.attributes)
                    .args()
                    .is_some_and(|args| args.contains(invocation))
            {
                snapshots.push(local.0.hex());
            }
        }
        Ok(snapshots)
    }

    /// Preview whole-operation removal. The current view and every explicit commit version
    /// remain referenced by a new checkpoint; any unwanted content they need remains charged.
    pub fn preview_publication_cleanup(
        &mut self,
        selectors: &[String],
        cache: &mut PublicationCache,
    ) -> Result<PublicationCleanup, NodeError> {
        self.initialize_publication_offers()?;
        let (base, ops) = self.publication_pending()?;
        let heads = self.local_heads()?;
        if heads.len() != 1 {
            return Err(PublicationError::DivergentHeads.into());
        }
        let selected = self.publication_selection(selectors, &ops)?;
        let before = self.publication_report(&ops, &base, cache)?;
        let canonical_head = self
            .canonical_of(&heads[0])
            .ok_or(PublicationError::PreviewHeadChanged)?;
        let mut operation = self.canonical.read_operation(&canonical_head)?;
        let current = self.canonical.read_view(&operation.view_id)?;
        let intentional = self.publication_kept_versions(&ops)?;
        let mut required = view_roots(&current);
        required.extend(intentional.iter().cloned());
        operation.metadata.is_snapshot = true;
        operation.metadata.description = "current working copy".to_owned();
        let remaining: Vec<_> = ops
            .iter()
            .filter(|id| {
                self.local_of(id)
                    .is_none_or(|local| !selected.contains(&local))
            })
            .cloned()
            .collect();
        let after = self.publication_report_projected(
            &remaining,
            &base,
            cache,
            Some(Checkpoint {
                id: canonical_head.clone(),
                operation,
                required,
                intentional: intentional.clone(),
            }),
        )?;
        let selected: Vec<_> = selected.iter().map(|id| id.0.hex()).collect();
        let mut hash = blake3::Hasher::new();
        hash.update(b"musubi-publication-cleanup-v1\0");
        hash.update(before.token.as_bytes());
        for id in &selected {
            hash.update(id.as_bytes());
        }
        for id in &intentional {
            hash.update(id.as_bytes());
        }
        hash.update(&(current.wc_commit_ids.len() as u64).to_le_bytes());
        let repo = self.repo_at(&heads[0])?;
        let context = self.publication_state_attributes(&repo, &canonical_head)?;
        hash.update(&serde_json::to_vec(&context).map_err(PublicationError::Json)?);
        let token = hash.finalize().to_hex().to_string();
        Ok(PublicationCleanup {
            token,
            selected,
            before,
            after,
            heads: heads.iter().map(|id| id.0.hex()).collect(),
        })
    }

    /// Applies a previously reviewed selection. The caller holds the publication lock;
    /// the op-head lock protects the final source comparison and atomic head replacement.
    /// Workspace records move only where their exact old working-copy commit survives.
    pub fn apply_publication_cleanup(
        &mut self,
        selectors: &[String],
        token: &str,
        cache: &mut PublicationCache,
    ) -> Result<usize, NodeError> {
        self.apply_publication_cleanup_mapped(selectors, token, cache)
            .map(|applied| applied.pruned)
    }

    pub(super) fn apply_publication_cleanup_mapped(
        &mut self,
        selectors: &[String],
        token: &str,
        cache: &mut PublicationCache,
    ) -> Result<CleanupEffect, NodeError> {
        let plan = self.preview_publication_cleanup(selectors, cache)?;
        if token != plan.token {
            return Err(PublicationError::OutgoingChanged.into());
        }
        let (base, ops) = self.publication_pending()?;
        let selected = self.publication_selection(selectors, &ops)?;
        let workspaces = self.lock_cleanup_workspaces(&plan.source()?)?;
        let op_heads = self.loader.op_heads_store().clone();
        let lock = self.lock_heads(&*op_heads)?;
        let source = self.locked_cleanup_source(&plan, &ops)?;
        let kept = self.intentional_predecessors(&ops, &source.intentional)?;
        let contraction = self.contract_unpublished(&source, &ops, &selected)?;
        let checkpoint =
            self.write_cleanup_checkpoint(&source, &plan.token, contraction.head, kept)?;
        self.check_prepared_cleanup(
            &source,
            &base,
            &plan.after,
            &selected,
            &contraction.movements,
            &checkpoint,
        )?;
        let checkpoint = LocalOp(checkpoint);
        let read = std::slice::from_ref(&source.head);
        // `jj op abandon` takes no lock: one can have changed the head since it was read.
        if !self.replace_heads(read, std::slice::from_ref(&checkpoint), true)? {
            return Err(PublicationError::OutgoingChanged.into());
        }
        drop(lock);
        self.finish_cleanup(workspaces, &checkpoint)?;
        Ok(CleanupEffect {
            pruned: plan.selected.len(),
            images: contraction.movements,
            checkpoint,
        })
    }

    /// Reads the head under the op-head lock, refusing it unless it is the one the preview
    /// saw, with what each unpublished operation recorded.
    fn locked_cleanup_source(
        &self,
        plan: &PublicationCleanup,
        ops: &[CanonicalOp],
    ) -> Result<CleanupSource, NodeError> {
        let heads = self.local_heads()?;
        if heads.iter().map(|id| id.0.hex()).collect::<Vec<_>>() != plan.heads {
            return Err(PublicationError::OutgoingChanged.into());
        }
        let head = heads[0].clone();
        let canonical_head = self
            .canonical_of(&head)
            .ok_or(PublicationError::AppliedHeadChanged)?;
        let intentional = self.publication_kept_versions(ops)?;
        let repo = self.repo_at(&head)?;
        let context = self.publication_state_attributes(&repo, &canonical_head)?;
        let foreign = self.publication_foreign_presence(&canonical_head)?;
        let view = self.canonical.read_operation(&canonical_head)?.view_id;
        let mut facts = HashMap::new();
        for id in ops {
            if let Some(local) = self.local_of(id) {
                let operation = self.canonical.read_operation(id)?;
                let view = self.canonical.read_view(&operation.view_id)?;
                facts.insert(
                    local.0,
                    SourceFacts {
                        view: operation.view_id.clone(),
                        intentional: self.publication_intentional(id, &operation, &view)?,
                    },
                );
            }
        }
        Ok(CleanupSource {
            head,
            intentional,
            repo,
            context,
            foreign,
            view,
            facts,
        })
    }

    /// Preserve explicit evolution through discarded automatic versions. Content itself
    /// stays immutable; this only reconnects the recorded intentional predecessors.
    fn intentional_predecessors(
        &self,
        ops: &[CanonicalOp],
        intentional: &BTreeSet<CommitId>,
    ) -> Result<BTreeMap<CommitId, Vec<CommitId>>, NodeError> {
        let mut previous: BTreeMap<CommitId, Vec<CommitId>> = BTreeMap::new();
        for id in ops {
            let operation = self.canonical.read_operation(id)?;
            for (id, predecessors) in operation.commit_predecessors.into_iter().flatten() {
                previous.entry(id).or_default().extend(predecessors);
            }
        }
        Ok(intentional
            .iter()
            .map(|id| (id.clone(), nearest_intentional(&previous, intentional, id)))
            .collect())
    }

    /// The native operations in `local` under `head`, each after its parents, which it
    /// visits in order.
    fn unpublished_postorder(
        &self,
        head: &OperationId,
        local: &HashSet<OperationId>,
    ) -> Result<Vec<(OperationId, Operation)>, NodeError> {
        let store = self.loader.op_store();
        let mut order = vec![];
        let mut stack = vec![(head.clone(), false)];
        let mut seen = HashSet::new();
        while let Some((id, expanded)) = stack.pop() {
            if !local.contains(&id) {
                continue;
            }
            let operation = store.read_operation(&id).block_on()?;
            if expanded {
                order.push((id, operation));
            } else if seen.insert(id.clone()) {
                stack.push((id, true));
                stack.extend(
                    operation
                        .parents
                        .iter()
                        .rev()
                        .cloned()
                        .map(|id| (id, false)),
                );
            }
        }
        Ok(order)
    }

    /// Walk only unpublished native ancestry; shared operations are untouched. jj's
    /// standard contraction rule preserves parent order and removes duplicate images.
    fn contract_unpublished(
        &self,
        source: &CleanupSource,
        ops: &[CanonicalOp],
        selected: &BTreeSet<LocalOp>,
    ) -> Result<Contraction, NodeError> {
        let selected: HashSet<_> = selected.iter().map(|id| id.0.clone()).collect();
        let local: HashSet<_> = ops
            .iter()
            .filter_map(|id| self.local_of(id))
            .map(|id| id.0)
            .collect();
        let store = self.loader.op_store();
        let existing = reachable(source.head.0.clone(), |id| {
            Ok::<_, NodeError>(store.read_operation(id).block_on()?.parents)
        })?;
        let order = self.unpublished_postorder(&source.head.0, &local)?;
        let mut images: HashMap<OperationId, Vec<OperationId>> = HashMap::new();
        let mut movements: HashMap<LocalOp, Vec<LocalOp>> = HashMap::new();
        let mut created = HashSet::new();
        for (id, mut operation) in order {
            let parents = contracted_parents(&images, &operation.parents);
            let records_name = Kind::of(&operation.metadata).name.is_some();
            let now = if selected.contains(&id) && !records_name {
                parents
            } else if parents == operation.parents && !selected.contains(&id) {
                vec![id.clone()]
            } else {
                if selected.contains(&id) {
                    // A record of this copy's name is kept, where it was, so that the copy
                    // keeps its name. It changes nothing else: its view becomes its new
                    // parent's, or theirs merged as jj merges operations, which retains
                    // nothing they don't but where the merge rebases commits.
                    operation.view_id = match parents.as_slice() {
                        [parent] => store.read_operation(parent).block_on()?.view_id,
                        _ => {
                            let operations = parents
                                .iter()
                                .map(|id| self.loader.load_operation(id).block_on())
                                .collect::<Result<Vec<_>, _>>()?;
                            let (merged, _) = self
                                .loader
                                .merge_operations(operations, None, None, [])
                                .block_on()?;
                            merged.operation().view_id().clone()
                        }
                    };
                }
                operation.parents = parents;
                let facts = source
                    .facts
                    .get(&id)
                    .ok_or(PublicationError::MissingSourceFacts)?;
                OpAttrs(&mut operation.metadata.attributes)
                    .set_intent(&facts.intentional)
                    .map_err(PublicationError::Json)?;
                for commit in &facts.intentional {
                    operation
                        .commit_predecessors
                        .get_or_insert_with(BTreeMap::new)
                        .entry(commit.clone())
                        .or_default();
                }
                let written = store.write_operation(&operation).block_on()?;
                if written != id
                    && (existing.contains(&written) || !created.insert(written.clone()))
                {
                    return Err(PublicationError::IdentityCollision.into());
                }
                vec![written]
            };
            movements.insert(
                LocalOp(id.clone()),
                now.iter().cloned().map(LocalOp).collect(),
            );
            images.insert(id, now);
        }
        let head = images
            .get(&source.head.0)
            .cloned()
            .unwrap_or_else(|| vec![source.head.0.clone()]);
        Ok(Contraction { head, movements })
    }

    /// Writes the checkpoint on top of `parents`, one operation per step of the state
    /// attributes; the first carries the kept predecessors.
    fn write_cleanup_checkpoint(
        &self,
        source: &CleanupSource,
        token: &str,
        mut parents: Vec<OperationId>,
        mut kept: BTreeMap<CommitId, Vec<CommitId>>,
    ) -> Result<OperationId, NodeError> {
        let store = self.loader.op_store();
        let mut checkpoint = None;
        for (step, mut attributes) in source.context.iter().cloned().enumerate() {
            OpAttrs(&mut attributes).set_checkpoint(token, step);
            let mut tx = source.repo.start_transaction();
            for (key, value) in attributes {
                tx.set_attribute(key, value);
            }
            let staged = tx
                .write("musubi: prune unpublished snapshots")
                .block_on()?
                .leave_unpublished();
            let mut operation = staged.operation().store_operation().clone();
            operation.parents = parents;
            operation.commit_predecessors = Some(if step == 0 {
                std::mem::take(&mut kept)
            } else {
                BTreeMap::new()
            });
            let id = store.write_operation(&operation).block_on()?;
            parents = vec![id.clone()];
            checkpoint = Some(id);
        }
        Ok(checkpoint.ok_or(PublicationError::NoCheckpoint)?)
    }

    /// Validate the *prepared native bodies* through the real canonicalization path, not a
    /// second planner projection. Failure leaves the source op heads untouched.
    fn check_prepared_cleanup(
        &mut self,
        source: &CleanupSource,
        base: &CanonicalOp,
        after: &PublicationReport,
        selected: &BTreeSet<LocalOp>,
        movements: &HashMap<LocalOp, Vec<LocalOp>>,
        checkpoint: &OperationId,
    ) -> Result<(), NodeError> {
        let prepared = self.canonicalize(&LocalOp(checkpoint.clone()))?;
        if self.canonical.read_operation(&prepared)?.view_id != source.view {
            return Err(PublicationError::ViewChanged.into());
        }
        if self.publication_foreign_presence(&prepared)? != source.foreign {
            return Err(PublicationError::ForeignPresenceChanged.into());
        }
        let prepared_repo = self.repo_at(&LocalOp(checkpoint.clone()))?;
        if self.publication_state_attributes(&prepared_repo, &prepared)? != source.context {
            return Err(PublicationError::StateChanged.into());
        }
        for (old, now) in movements {
            if selected.contains(old) {
                continue;
            }
            if let (Some(facts), [now]) = (source.facts.get(&old.0), now.as_slice()) {
                let current = self
                    .canonical_of(now)
                    .ok_or(PublicationError::MissingPrepared)?;
                let operation = self.canonical.read_operation(&current)?;
                let current_view = self.canonical.read_view(&operation.view_id)?;
                if operation.view_id != facts.view
                    || self.publication_intentional(&current, &operation, &current_view)?
                        != facts.intentional
                {
                    return Err(PublicationError::UnselectedChanged.into());
                }
            }
        }
        let known: HashSet<_> = self
            .canonical
            .ancestors_until(std::slice::from_ref(base), |_| false)?
            .into_iter()
            .collect();
        let prepared_ops = self
            .canonical
            .ancestors_until(std::slice::from_ref(&prepared), |id| known.contains(id))?;
        let required = self.publication_commit_closure(self.required_commits(&prepared_ops)?)?;
        if !source.intentional.is_subset(&required)
            || self.publication_kept_versions(&prepared_ops)? != source.intentional
        {
            return Err(PublicationError::IntentLost.into());
        }
        let actual =
            self.publication_report(&prepared_ops, base, &mut PublicationCache::default())?;
        if actual.content != after.content || actual.bytes != after.bytes {
            return Err(PublicationError::PreviewMismatch.into());
        }
        Ok(())
    }

    /// Moves the locked working copies onto the checkpoint now at the head, and forgets
    /// what was derived from the old head.
    fn finish_cleanup(
        &mut self,
        workspaces: Vec<CleanupWorkspace>,
        checkpoint: &LocalOp,
    ) -> Result<(), NodeError> {
        let mut finish_errors = Vec::new();
        for workspace in workspaces {
            if let Err(err) = workspace.locked.finish(checkpoint.0.clone()).block_on() {
                finish_errors.push(format!(
                    "{} at {}: {err}",
                    workspace.name.as_str(),
                    workspace.root.display()
                ));
            }
        }
        self.heads_mapped = false;
        self.invalidate_published_history();
        let approval = self.repo_path.join("musubi").join(super::APPROVAL_FILE);
        if let Err(err) = std::fs::remove_file(approval)
            && err.kind() != std::io::ErrorKind::NotFound
        {
            tracing::warn!("removing old publication approval: {err}");
        }
        // A later jj command can finish on old unpublished ancestry. It is checked by the
        // same publication guard; pruning never grants approval to that late work.
        if !finish_errors.is_empty() {
            return Err(PublicationError::WorkspacesNotUpdated(finish_errors).into());
        }
        Ok(())
    }
}

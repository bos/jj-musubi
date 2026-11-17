//! Selection and application of unpublished recovery-history cleanup.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::btree_map::Entry;
use std::path::PathBuf;

use jj_lib::backend::CommitId;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::ref_name::WorkspaceNameBuf;
use jj_lib::repo::Repo as _;
use jj_lib::working_copy::LockedWorkingCopy;
use jj_lib::workspace::WorkspaceLoaderFactory as _;
use pollster::FutureExt as _;
use serde::Deserialize;
use serde::Serialize;

use super::CHECKPOINT_ATTRIBUTE;
use super::Checkpoint;
use super::NodeError;
use super::NodeRepo;
use super::PublicationCache;
use super::PublicationReport;
use super::intent::view_roots;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct PublicationCleanup {
    pub token: String,
    pub selected: Vec<String>,
    pub before: PublicationReport,
    pub after: PublicationReport,
    heads: Vec<String>,
}

type CleanupEffect = (usize, HashMap<LocalOp, Vec<LocalOp>>, LocalOp);

struct CleanupWorkspace {
    name: WorkspaceNameBuf,
    root: PathBuf,
    locked: Box<dyn LockedWorkingCopy>,
}

fn invalid(message: impl Into<String>) -> NodeError {
    NodeError::Publication(message.into())
}

impl NodeRepo {
    /// Lock metadata before op heads, as jj does. Cleanup keeps the current view, so
    /// every local working copy needs that exact recorded commit as its snapshot basis.
    /// Otherwise later stale recovery could merge the discarded ancestry back in.
    fn lock_cleanup_workspaces(&self, head: &LocalOp) -> Result<Vec<CleanupWorkspace>, NodeError> {
        let repo = self.repo_at(head)?;
        let canonical = self
            .canonical_of(head)
            .ok_or_else(|| invalid("the current operation changed; run the cleanup again"))?;
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
                        invalid(format!(
                            "cannot read workspace {label} at {}: {err}",
                            path.display()
                        ))
                    })?;
                    match paths.entry(path) {
                        Entry::Vacant(entry) => {
                            entry.insert(name.clone());
                        }
                        Entry::Occupied(entry) => {
                            return Err(invalid(format!(
                                "workspaces {} and {label} share a registered path at {}; restore their paths or forget the obsolete workspace before pruning",
                                entry.get().as_str(),
                                entry.key().display()
                            )));
                        }
                    }
                }
                Ok(None) if !own.contains(name) => {}
                Ok(None) => {
                    return Err(invalid(format!(
                        "cannot locate workspace {label}; recreate or forget it before pruning"
                    )));
                }
                Err(err) => return Err(invalid(format!("cannot locate workspace {label}: {err}"))),
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
            let cannot_read = |err: &dyn std::fmt::Display| {
                invalid(format!(
                    "cannot read workspace {label} at {}: {err}",
                    root.display()
                ))
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
                return Err(invalid(format!(
                    "workspace {label} at {} no longer identifies this repo; recreate or forget it before pruning",
                    root.display()
                )));
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
            let current = repo.view().get_wc_commit_id(&name).ok_or_else(|| {
                invalid(format!(
                    "workspace {label} is no longer in the current view"
                ))
            })?;
            let commit = repo.store().get_commit_async(current).block_on()?;
            if view.wc_commit_ids.get(&name) != Some(current)
                || guard.old_tree().tree_ids_and_labels() != commit.tree().tree_ids_and_labels()
            {
                return Err(invalid(format!(
                    "workspace {label} must be updated before pruning\nHint: run `jj status` in {}",
                    root.display()
                )));
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
        self.check_abandon()?;
        let base = self
            .stored_base()
            .map_or_else(|| self.canonical.root_operation_id().clone(), |op| op.0);
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
            return Err(invalid(
                "choose at least one unpublished operation to prune",
            ));
        }
        let offered = self.publication_offered_origins()?;
        let local: Vec<_> = ops.iter().filter_map(|id| self.local_of(id)).collect();
        let mut selected = BTreeSet::new();
        for prefix in selectors {
            if prefix.is_empty() || !prefix.bytes().all(|b| b.is_ascii_hexdigit()) {
                return Err(invalid(format!("{prefix:?} is not a jj operation id")));
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
                    return Err(invalid(format!(
                        "operation {prefix} is not unpublished work; run `musubi sync --outgoing`"
                    )));
                }
                _ => {
                    return Err(invalid(format!(
                        "operation prefix {prefix} is ambiguous; use more of its id"
                    )));
                }
            }
        }
        for id in &selected {
            if let Some(canonical) = self.canonical_of(id)
                && offered.contains(&self.canonical.original_id(&canonical)?)
            {
                return Err(invalid(format!(
                    "operation {} was offered to the hub or predates publication tracking; this cleanup only removes history known never to have been offered",
                    id.0.hex()
                )));
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
                return Err(invalid(format!(
                    "cannot safely prune this history: jj did not record enough information to preserve changes from {:?}\nHint: run `musubi sync --outgoing` to inspect or approve this work",
                    op.metadata.description,
                )));
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
            return Err(invalid("the snapshot invocation marker is empty"));
        }
        let (_, pending) = self.publication_pending()?;
        let mut snapshots = Vec::new();
        for id in pending {
            let Some(local) = self.local_of(&id) else {
                continue;
            };
            let operation = self.loader.op_store().read_operation(&local.0).block_on()?;
            if operation.metadata.is_snapshot
                && operation
                    .metadata
                    .attributes
                    .get("args")
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
            return Err(invalid(
                "reconcile this workspace's operations with `jj status` before choosing snapshots to prune",
            ));
        }
        let selected = self.publication_selection(selectors, &ops)?;
        let before = self.publication_report(&ops, &base, cache)?;
        let canonical_head = self
            .canonical_of(&heads[0])
            .ok_or_else(|| invalid("the current operation changed; inspect outgoing work again"))?;
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
        hash.update(&serde_json::to_vec(&context).map_err(|err| invalid(err.to_string()))?);
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
            .map(|applied| applied.0)
    }

    pub(super) fn apply_publication_cleanup_mapped(
        &mut self,
        selectors: &[String],
        token: &str,
        cache: &mut PublicationCache,
    ) -> Result<CleanupEffect, NodeError> {
        let plan = self.preview_publication_cleanup(selectors, cache)?;
        if token != plan.token {
            return Err(invalid("outgoing work changed; run the cleanup again"));
        }
        let (base, ops) = self.publication_pending()?;
        let selected = self.publication_selection(selectors, &ops)?;
        let source = LocalOp(
            OperationId::try_from_hex(&plan.heads[0])
                .ok_or_else(|| invalid("invalid cleanup source operation"))?,
        );
        let workspaces = self.lock_cleanup_workspaces(&source)?;
        let op_heads = self.loader.op_heads_store().clone();
        let lock = op_heads.lock().block_on()?;
        let heads = self.local_heads()?;
        if heads.iter().map(|id| id.0.hex()).collect::<Vec<_>>() != plan.heads {
            return Err(invalid("outgoing work changed; run the cleanup again"));
        }
        let head = heads[0].clone();
        let selected_ids: HashSet<_> = selected.iter().map(|id| id.0.clone()).collect();
        let canonical_head = self
            .canonical_of(&head)
            .ok_or_else(|| invalid("the current operation changed"))?;
        let intentional = self.publication_kept_versions(&ops)?;
        let repo = self.repo_at(&head)?;
        let attrs = self.publication_state_attributes(&repo, &canonical_head)?;
        let expected_context = attrs.clone();
        let expected_foreign = self.publication_foreign_presence(&canonical_head)?;
        let expected_view = self.canonical.read_operation(&canonical_head)?.view_id;
        let mut source_facts = HashMap::new();
        for id in &ops {
            if let Some(local) = self.local_of(id) {
                let operation = self.canonical.read_operation(id)?;
                let view = self.canonical.read_view(&operation.view_id)?;
                source_facts.insert(
                    local.0,
                    (
                        operation.view_id.clone(),
                        self.publication_intentional(id, &operation, &view)?,
                        self.publication_namespace_facts(id)?,
                    ),
                );
            }
        }

        // Preserve explicit evolution through discarded automatic versions. Content itself
        // stays immutable; this only reconnects the recorded intentional predecessors.
        let mut previous: BTreeMap<CommitId, Vec<CommitId>> = BTreeMap::new();
        for id in &ops {
            let operation = self.canonical.read_operation(id)?;
            for (id, predecessors) in operation.commit_predecessors.into_iter().flatten() {
                previous.entry(id).or_default().extend(predecessors);
            }
        }
        let mut kept = BTreeMap::new();
        for id in &intentional {
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
            kept.insert(id.clone(), predecessors.into_iter().collect());
        }

        // Walk only unpublished native ancestry; shared operations are untouched. jj's
        // standard contraction rule preserves parent order and removes duplicate images.
        let local_ops: HashSet<_> = ops
            .iter()
            .filter_map(|id| self.local_of(id))
            .map(|id| id.0)
            .collect();
        let store = self.loader.op_store().clone();
        let mut source_ids = HashSet::new();
        let mut source_stack = vec![head.0.clone()];
        while let Some(id) = source_stack.pop() {
            if source_ids.insert(id.clone()) {
                source_stack.extend(store.read_operation(&id).block_on()?.parents);
            }
        }
        let mut order = vec![];
        let mut stack = vec![(head.0.clone(), false)];
        let mut seen = HashSet::new();
        while let Some((id, expanded)) = stack.pop() {
            if !local_ops.contains(&id) {
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
        let mut images: HashMap<OperationId, Vec<OperationId>> = HashMap::new();
        let mut movements: HashMap<LocalOp, Vec<LocalOp>> = HashMap::new();
        let mut created = HashSet::new();
        for (id, mut operation) in order {
            let mut parents = vec![];
            for parent in &operation.parents {
                for image in images
                    .get(parent)
                    .cloned()
                    .unwrap_or_else(|| vec![parent.clone()])
                {
                    if !parents.contains(&image) {
                        parents.push(image);
                    }
                }
            }
            let now = if selected_ids.contains(&id) {
                parents
            } else if parents == operation.parents {
                vec![id.clone()]
            } else {
                operation.parents = parents;
                let (_, frozen, namespace) = source_facts
                    .get(&id)
                    .ok_or_else(|| invalid("the source of an unpublished operation is missing"))?;
                let encoded: Vec<_> = frozen.iter().map(|id| id.hex()).collect();
                operation.metadata.attributes.insert(
                    super::INTENT_ATTRIBUTE.to_owned(),
                    serde_json::to_string(&encoded).map_err(|err| invalid(err.to_string()))?,
                );
                operation.metadata.attributes.extend(namespace.clone());
                for commit in frozen {
                    operation
                        .commit_predecessors
                        .get_or_insert_with(BTreeMap::new)
                        .entry(commit.clone())
                        .or_default();
                }
                let written = store.write_operation(&operation).block_on()?;
                if written != id
                    && (source_ids.contains(&written) || !created.insert(written.clone()))
                {
                    return Err(invalid(
                        "jj would give distinct operations the same identity; this selection cannot be pruned safely",
                    ));
                }
                vec![written]
            };
            movements.insert(
                LocalOp(id.clone()),
                now.iter().cloned().map(LocalOp).collect(),
            );
            images.insert(id, now);
        }
        let mut parents = images
            .get(&head.0)
            .cloned()
            .unwrap_or_else(|| vec![head.0.clone()]);
        let mut checkpoint = None;
        for (step, mut attributes) in attrs.into_iter().enumerate() {
            attributes.insert(
                CHECKPOINT_ATTRIBUTE.to_owned(),
                format!("{}:{step}", plan.token),
            );
            let mut tx = repo.start_transaction();
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
                kept.clone()
            } else {
                BTreeMap::new()
            });
            let id = store.write_operation(&operation).block_on()?;
            parents = vec![id.clone()];
            checkpoint = Some(id);
        }
        let checkpoint =
            checkpoint.ok_or_else(|| invalid("could not prepare the cleanup checkpoint"))?;
        // Validate the *prepared native bodies* through the real canonicalization path,
        // not a second planner projection. Failure leaves the source op heads untouched.
        let prepared = self.canonicalize_unchecked(&LocalOp(checkpoint.clone()))?;
        if self.canonical.read_operation(&prepared)?.view_id != expected_view {
            return Err(invalid(
                "this cleanup cannot preserve the current repository view",
            ));
        }
        if self.publication_foreign_presence(&prepared)? != expected_foreign {
            return Err(invalid(
                "this selection would change another copy's activity or membership; choose different snapshots or approve publication",
            ));
        }
        let prepared_repo = self.repo_at(&LocalOp(checkpoint.clone()))?;
        if self.publication_state_attributes(&prepared_repo, &prepared)? != expected_context {
            return Err(invalid(
                "this cleanup cannot preserve the current workspace and Git-ref state",
            ));
        }
        for (old, now) in &movements {
            if selected.contains(old) {
                continue;
            }
            if let (Some((view, frozen, _)), [now]) = (source_facts.get(&old.0), now.as_slice()) {
                let current = self
                    .canonical_of(now)
                    .ok_or_else(|| invalid("a prepared operation is missing"))?;
                let operation = self.canonical.read_operation(&current)?;
                let current_view = self.canonical.read_view(&operation.view_id)?;
                if operation.view_id != *view
                    || self.publication_intentional(&current, &operation, &current_view)? != *frozen
                {
                    return Err(invalid(
                        "this cleanup would change an unselected operation's saved state",
                    ));
                }
            }
        }
        let known: HashSet<_> = self
            .canonical
            .ancestors_until(std::slice::from_ref(&base), |_| false)?
            .into_iter()
            .collect();
        let prepared_ops = self
            .canonical
            .ancestors_until(std::slice::from_ref(&prepared), |id| known.contains(id))?;
        let required = self.publication_commit_closure(self.required_commits(&prepared_ops)?)?;
        if !intentional.is_subset(&required)
            || self.publication_kept_versions(&prepared_ops)? != intentional
        {
            return Err(invalid(
                "this cleanup would discard intentional change history",
            ));
        }
        let actual =
            self.publication_report(&prepared_ops, &base, &mut PublicationCache::default())?;
        if actual.content != plan.after.content || actual.bytes != plan.after.bytes {
            return Err(invalid(
                "the prepared cleanup differs from its preview; no history was pruned",
            ));
        }
        op_heads
            .update_op_heads(std::slice::from_ref(&head.0), &checkpoint)
            .block_on()?;
        drop(lock);
        let contraction = movements;
        let checkpoint = LocalOp(checkpoint);
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
        self.abandon.recheck();
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
            return Err(invalid(format!(
                "cleanup finished, but workspace metadata could not be updated for {}",
                finish_errors.join("; ")
            )));
        }
        Ok((plan.selected.len(), contraction, checkpoint))
    }
}

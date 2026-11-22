//! Canonicalizing local operations, and finding the local operation for a canonical one.

use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use crate::canonical::CanonicalError;
use crate::canonical::Work;
use crate::format_guard;
use crate::format_guard::FormatError;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;
use crate::presence::Presence;
use crate::remote_url::without_credentials;
use crate::workspaces;

impl NodeRepo {
    /// The canonical form of each local op head, but for one from before this repository
    /// joined, which has none until a merge takes it in (see [`Self::canonicalize`]).
    pub fn canonical_heads(&mut self) -> Result<Vec<CanonicalOp>, NodeError> {
        let heads = self.local_heads()?;
        let mut canonical = vec![];
        for head in &heads {
            match self.canonicalize(head) {
                Ok(id) => canonical.push(id),
                Err(NodeError::BeforeJoin(_)) => {}
                Err(err) => return Err(err),
            }
        }
        // Reparenting may need a genuinely missing realization. Its first step must not
        // recurse here: every reachable operation, including source aliases, is mapped now.
        self.heads_mapped = true;
        if !self.late.is_empty()
            && let Err(err) = self.reparent_late(&heads)
        {
            self.heads_mapped = false;
            return Err(err);
        }
        Ok(canonical)
    }

    /// Reparents the local operations canonicalized on a local operation that isn't the
    /// preferred realization of its canonical parent onto that realization, as their canonical
    /// operations have them, and moves the op heads among them there: before anything merges
    /// them, which would merge against an older common ancestor.
    fn reparent_late(&mut self, heads: &[LocalOp]) -> Result<(), NodeError> {
        let mut tips: Vec<_> = heads
            .iter()
            .filter_map(|head| self.canonical_of(head))
            .collect();
        let mut late: HashMap<CanonicalOp, Vec<LocalOp>> = HashMap::new();
        for local in &self.late {
            if let Some(canonical) = self.canonical_of(local) {
                late.entry(canonical.clone())
                    .or_insert_with(|| {
                        tips.push(canonical);
                        vec![]
                    })
                    .push(local.clone());
            }
        }
        if late.is_empty() {
            self.late.clear();
            return Ok(());
        }

        // A cached descendant on another native alias may never have been queued.
        // Visit descendants in canonical order so every branch uses the same physical
        // parent, even when the branches reached it through different native operations.
        let published = self.published_realizations(heads)?;
        let order = self.canonical.ancestors_until(&tips, |_| false)?;
        let op_store = self.loader.op_store().clone();
        let mut normalized = HashMap::new();
        let mut rewrites = HashMap::new();
        for canonical in order {
            let parents = self.canonical.parents(&canonical)?;
            let sources = late.remove(&canonical);
            if sources.is_none() && !parents.iter().any(|parent| normalized.contains_key(parent)) {
                continue;
            }
            let local = match published
                .get(&canonical)
                .cloned()
                .or_else(|| self.local_of(&canonical))
            {
                Some(local) => local,
                None => self.realize(&canonical)?,
            };
            let mut op = op_store.read_operation(&local.0).block_on()?;
            let mut local_parents = Vec::with_capacity(parents.len());
            for parent in &parents {
                // A delayed command can make a cached source reachable again. Use the
                // preferred realization for that parent even if it wasn't queued again.
                let local = normalized
                    .get(parent)
                    .cloned()
                    .or_else(|| self.local_of(parent));
                let local = match local {
                    Some(local) => local,
                    None => self.realize(parent)?,
                };
                local_parents.push(local.0);
            }
            let rewrite = if local_parents == op.parents
                && (sources.is_none()
                    || OpAttrs(&op.metadata.attributes).canonical()
                        == Some(canonical.0.hex().as_str()))
            {
                local.clone()
            } else {
                // A marker ends the native walk for private ownership. Capture that evidence
                // before replacing the parents, so that this marked copy is self-contained.
                let view = op_store.read_view(&op.view_id).block_on()?;
                let own = self.own_of_view(view.wc_commit_ids, &canonical, &op)?;
                self.record_private_workspaces(&mut op.metadata, own.into_keys(), &canonical)?;
                op.parents = local_parents;
                OpAttrs(&mut op.metadata.attributes).set_canonical(&canonical);
                let rewrite = LocalOp(op_store.write_operation(&op).block_on()?);
                rewrites.insert(local, vec![rewrite.clone()]);
                rewrite
            };
            for source in sources
                .into_iter()
                .flatten()
                .filter(|source| source != &rewrite)
            {
                rewrites.insert(source, vec![rewrite.clone()]);
            }
            self.insert_map(rewrite.clone(), canonical.clone())?;
            normalized.insert(canonical, rewrite);
        }
        // Read again if a `jj` command changes the op heads before they move.
        let moved = loop {
            let heads = self.local_heads()?;
            let mut from = HashMap::new();
            for head in &heads {
                if let Some(rewrite) = self
                    .canonical_of(head)
                    .and_then(|canonical| normalized.get(&canonical))
                    && rewrite != head
                {
                    from.insert(head.clone(), vec![rewrite.clone()]);
                }
            }
            if from.is_empty() {
                break from;
            }
            let mut seen = HashSet::new();
            let new: Vec<LocalOp> = heads
                .iter()
                .flat_map(|head| {
                    from.get(head)
                        .cloned()
                        .unwrap_or_else(|| vec![head.clone()])
                })
                .filter(|op| seen.insert(op.clone()))
                .collect();
            if self.replace_heads(&heads, &new, true)? {
                break from;
            }
        };
        rewrites.extend(moved);
        self.late.clear();
        self.move_workspaces(&rewrites)
    }

    /// The canonical parents of a local operation. Also whether a preferred local realization
    /// of one of them is another local operation than the parent.
    fn current_parents(&self, parents: &[LocalOp]) -> (Vec<CanonicalOp>, bool) {
        let mut renamed = false;
        let mut current = vec![];
        for parent in parents {
            if self.joins.before.contains(parent) {
                continue;
            }
            let canonical = self
                .canonical_of(parent)
                .expect("parents canonicalized first");
            // A warm cache can know an old source and its realization under the same
            // canonical id. New children must use the preferred physical parent.
            renamed |= self
                .map
                .local_of(&canonical)
                .is_some_and(|preferred| preferred != parent);
            if !current.contains(&canonical) {
                current.push(canonical);
            }
        }
        (current, renamed)
    }

    pub fn canonical_of(&self, local: &LocalOp) -> Option<CanonicalOp> {
        if local == self.root_op_id() {
            return Some(self.canonical.root_operation_id().clone());
        }
        self.map.canonical_of(local).cloned()
    }

    pub fn local_of(&self, canonical: &CanonicalOp) -> Option<LocalOp> {
        if canonical == self.canonical.root_operation_id() {
            return Some(self.root_op_id().clone());
        }
        self.map.local_of(canonical).cloned()
    }

    /// Returns the canonical id of a local operation, canonicalizing it and any
    /// not-yet-canonicalized ancestors.
    ///
    /// The history from before a repository joined isn't the hive's: the join operation
    /// stands for it. A `jj` command that loaded the repository before `musubi join` and wrote
    /// after it, or one run with `--at-op` at an operation from then, makes an operation on
    /// that history. Such an operation has no canonical form, and this fails with
    /// [`NodeError::BeforeJoin`] for it. A merge of it with this machine's later history,
    /// which jj makes, has the merged view, so it leaves the parents from before the join
    /// out of its canonical form.
    pub fn canonicalize(&mut self, local: &LocalOp) -> Result<CanonicalOp, NodeError> {
        let op_store = self.loader.op_store().clone();
        // Post-order walk: an operation is canonicalized once all its parents are.
        let mut stack: Vec<(LocalOp, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if id == *self.root_op_id()
                || self.map.canonical_of(&id).is_some()
                || self.joins.before.contains(&id)
            {
                continue;
            }
            let op = match loaded {
                Some(op) => op,
                None => op_store.read_operation(&id.0).block_on()?,
            };
            // A join point that `jj op abandon` rewrote, abandoning history from before the
            // join, which no other machine has: its parents are from before the join.
            if OpAttrs(&op.metadata.attributes).canonical().is_none()
                && let Some(join) = self.joins.join_of(&op)
            {
                let join = join.clone();
                self.insert_map(id, join)?;
                continue;
            }
            let parents = LocalOp::parents_of(&op);
            let missing: Vec<_> = parents
                .iter()
                .filter(|parent| {
                    *parent != self.root_op_id()
                        && self.map.canonical_of(parent).is_none()
                        && !self.joins.before.contains(*parent)
                })
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            let late = parents.iter().any(|parent| self.late.contains(parent));
            let canonical_id = if let Some(canonical) = OpAttrs(&op.metadata.attributes).canonical()
            {
                self.realized_canonical(&id, &op, canonical)?
            } else if self.is_before_join(&id, &op)? {
                self.joins.before.insert(id);
                continue;
            } else {
                let (parents, renamed) = self.current_parents(&parents);
                if renamed || late {
                    self.late.push(id.clone());
                }
                self.write_canonical(&id, &op, parents)?
            };
            self.insert_map(id, canonical_id)?;
        }
        match self.canonical_of(local) {
            Some(canonical) => Ok(canonical),
            None => Err(NodeError::BeforeJoin(local.0.hex())),
        }
    }

    /// Whether a local operation that isn't a join point or a realization, whose parents are
    /// canonicalized or from before the join, is from before the join too: all of its
    /// parents are, or it is the first of the history before a join, on the root. Another
    /// operation on the root, as `jj op abandon` leaves when it abandons everything below
    /// one, is the hive's, which then finds the history it had abandoned.
    fn is_before_join(&mut self, id: &LocalOp, op: &StoreOperation) -> Result<bool, NodeError> {
        let parents = LocalOp::parents_of(op);
        if parents
            .iter()
            .all(|parent| self.joins.before.contains(parent))
        {
            return Ok(!parents.is_empty());
        }
        if parents.as_slice() != std::slice::from_ref(self.root_op_id()) || self.joins.is_empty() {
            return Ok(false);
        }
        Ok(self.join_ancestors()?.contains(id))
    }

    /// The ancestors of the join points reachable from the op heads, but for the root: the
    /// history before the joins. A join point `jj op abandon` rewrote is one by its
    /// fingerprint, as `canonicalize` takes it, with the rewritten history below it.
    fn join_ancestors(&mut self) -> Result<Arc<HashSet<LocalOp>>, NodeError> {
        if let Some(ancestors) = &self.joins.ancestors {
            return Ok(ancestors.clone());
        }
        let op_store = self.loader.op_store().clone();
        let root = self.root_op_id().clone();
        let mut seen = HashSet::new();
        let mut stack = self.local_heads()?;
        let mut below_joins: Vec<LocalOp> = vec![];
        while let Some(id) = stack.pop() {
            if id == root || !seen.insert(id.clone()) {
                continue;
            }
            let op = op_store.read_operation(&id.0).block_on()?;
            if self.joins.points.contains(&id)
                || (OpAttrs(&op.metadata.attributes).canonical().is_none()
                    && self.joins.join_of(&op).is_some())
            {
                below_joins.extend(LocalOp::parents_of(&op));
            } else {
                stack.extend(LocalOp::parents_of(&op));
            }
        }
        let mut ancestors = HashSet::new();
        let mut stack = below_joins;
        while let Some(id) = stack.pop() {
            if id == *self.root_op_id() || !ancestors.insert(id.clone()) {
                continue;
            }
            stack.extend(LocalOp::parents_of(
                &op_store.read_operation(&id.0).block_on()?,
            ));
        }
        let ancestors = Arc::new(ancestors);
        self.joins.ancestors = Some(ancestors.clone());
        Ok(ancestors)
    }

    /// The canonical operation a realization names in its `musubi.canonical` attribute.
    /// `jj op abandon` rewrites the operations above the ones it abandons, keeping their
    /// metadata, so a rewritten realization still names its canonical operation, but has other
    /// parents: it is the hive's operation on parents that are not its own, which stops this
    /// copy syncing where the abandon dropped operations the hive has. Its parents must already
    /// be canonicalized.
    fn realized_canonical(
        &mut self,
        id: &LocalOp,
        op: &StoreOperation,
        canonical: &str,
    ) -> Result<CanonicalOp, NodeError> {
        let named = OperationId::try_from_hex(canonical)
            .map(CanonicalOp)
            .filter(|c| self.canonical.has_operation(c))
            .ok_or_else(|| NodeError::DanglingAttribute {
                op: id.0.hex(),
                canonical: canonical.to_owned(),
            })?;
        let local_parents = LocalOp::parents_of(op);
        let canonical_id = named;
        let (parents, renamed) = self.current_parents(&local_parents);
        if renamed
            || local_parents
                .iter()
                .any(|parent| self.late.contains(parent))
        {
            self.late.push(id.clone());
        }
        let wanted = self.canonical.parents(&canonical_id)?;
        if parents != wanted && self.reaches_all(&parents, &wanted)? && !self.late.contains(id) {
            // Put back on the parents it names, with what is above it, before anything else
            // reads the op heads (`reparent_late`).
            self.late.push(id.clone());
        }
        if parents != wanted && !self.reaches_all(&parents, &wanted)? {
            if !OpAttrs(&op.metadata.attributes).has_original_parents() {
                // An operation this machine wrote, which musubi rewrote and marked
                // (`reparent_late`, `with_per_machine`), cut off from what its canonical
                // operation stands on by `jj op abandon` below it. Translate it afresh, on the
                // parents it has, as an unmarked one: whether the abandon took history the hub
                // has is for the fetch base and the accepted push to say
                // (`NodeAdapter::read_heads`).
                let mut op = op.clone();
                OpAttrs(&mut op.metadata.attributes).remove_canonical();
                return self.write_canonical(id, &op, parents);
            }
            // For the daemon's log: the error says what a user needs.
            tracing::info!(
                "operation {} realizes canonical operation {} but no longer has its parents",
                id.0.hex(),
                canonical_id.0.hex()
            );
            return Err(NodeError::RewrittenRealization);
        }
        Ok(canonical_id)
    }

    /// Whether every one of `wanted` is one of `have` or below one. `jj op abandon` of an
    /// operation this copy hasn't sent puts a realization that was beside it on the abandoned
    /// operation's parent, and so on more history than the hive's operation has, but not on
    /// less: nothing the hive's operation stands on is gone, and `reparent_late` puts it back.
    /// Where an abandon cut off something it stands on, `wanted` is not all reached.
    fn reaches_all(&self, have: &[CanonicalOp], wanted: &[CanonicalOp]) -> Result<bool, NodeError> {
        for want in wanted {
            let mut found = false;
            for parent in have {
                if parent == want || self.canonical.is_ancestor_of(want, parent)? {
                    found = true;
                    break;
                }
            }
            if !found {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn write_canonical(
        &mut self,
        id: &LocalOp,
        op: &StoreOperation,
        parents: Vec<CanonicalOp>,
    ) -> Result<CanonicalOp, NodeError> {
        let (canonical_op, presence, kind) =
            self.canonical_form(id, op, parents, |view| self.canonical.write_view(view))?;
        let canonical = self.canonical.write_operation(&canonical_op)?;
        let work = Work::of(&self.canonical, &canonical)?;
        self.remember_presence(canonical.clone(), presence.apply(&work, &kind));
        Ok(canonical)
    }

    /// The canonical form of local operation `id`, `op`, on `parents`, its view given an id by
    /// `view_id`, which may store it; and the presence its parents give it, and its kind.
    fn canonical_form(
        &self,
        id: &LocalOp,
        op: &StoreOperation,
        parents: Vec<CanonicalOp>,
        view_id: impl FnOnce(&View) -> Result<ViewId, CanonicalError>,
    ) -> Result<(StoreOperation, Presence<Work>, Kind), NodeError> {
        self.check_format(id, op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let mut metadata = op.metadata.clone();
        let mut commit_predecessors = op.commit_predecessors.clone();
        if let Some(roots) = self.publication_git_intent(op, &view)? {
            OpAttrs(&mut metadata.attributes)
                .set_intent(&roots)
                .map_err(super::PublicationError::Json)?;
            let records = commit_predecessors.get_or_insert_default();
            for root in roots {
                records.entry(root).or_default();
            }
        }
        let mut attributes = OpAttrs(&mut metadata.attributes);
        attributes.remove_private_workspaces();
        attributes.remove_reconciled_from();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let Some(canonical) = self.canonical_of(&LocalOp(target))
            && self.canonical.is_ancestor(&canonical, &parents)?
        {
            metadata.description = format!("{prefix}{}", canonical.0.hex());
        }
        // jj records the command that made an operation, which may name an http(s) URL with
        // a token meant for this machine only.
        if let Some(args) = OpAttrs(&mut metadata.attributes).args_mut() {
            *args = without_credentials(args);
        }
        // Which workspace made an operation is per-machine, like the view's working copies:
        // qualify it, so that each machine can tell its own workspaces' operations from
        // another machine's workspace of the same name (see `realized_workspace_name`).
        metadata.workspace_name = metadata
            .workspace_name
            .map(|name| workspaces::workspace_key(self.machine.key(), name.as_str()));
        let kind = Kind::of(&metadata);
        let (view, presence) =
            self.canonical_view(id, view, &parents, commit_predecessors.as_ref(), &kind)?;
        let view_id = view_id(&view)?;
        let canonical_op = StoreOperation {
            view_id,
            parents: parents.into_iter().map(|parent| parent.0).collect(),
            metadata,
            commit_predecessors,
        };
        Ok((canonical_op, presence, kind))
    }

    /// Refuses operations whose files contain fields this jj-lib would drop.
    pub(super) fn check_format(&self, id: &LocalOp, op: &StoreOperation) -> Result<(), NodeError> {
        let op_store_dir = self.repo_path.join("op_store");
        type Check = fn(&[u8]) -> Result<(), FormatError>;
        let checks: [(PathBuf, Check); 2] = [
            (
                op_store_dir.join("operations").join(id.0.hex()),
                format_guard::check_operation,
            ),
            (
                op_store_dir.join("views").join(op.view_id.hex()),
                format_guard::check_view,
            ),
        ];
        for (path, check) in checks {
            if op.view_id.as_bytes().iter().all(|&b| b == 0) && path.ends_with(op.view_id.hex()) {
                continue;
            }
            let bytes = fs::read(&path).map_err(|source| NodeError::Io { path, source })?;
            check(&bytes).map_err(|source| NodeError::Format {
                op: id.0.hex(),
                source,
            })?;
        }
        Ok(())
    }

    pub(super) fn root_op_id(&self) -> &LocalOp {
        &self.local_root
    }
}

/// Descriptions in which jj names an operation's target by its id. `jj undo` and `jj redo`
/// read the id back to find where their undo stacks continue, so musubi translates it
/// between this machine's ids and canonical ones. Only targets that are ancestors are
/// translated, as they always are for undo and redo: those are canonicalized and realized
/// first, so the translation never depends on the order operations arrive in.
///
/// The `revert operation` forms of undo and redo are from a proposed jj change that makes
/// `jj undo` revert this workspace's latest operation when others' are on top of it.
const TARGET_PREFIXES: [&str; 6] = [
    "undo: restore to operation ",
    "redo: restore to operation ",
    "undo: revert operation ",
    "redo: revert operation ",
    "restore to operation ",
    "revert operation ",
];

pub(super) fn target_of(description: &str) -> Option<(&'static str, OperationId)> {
    TARGET_PREFIXES.iter().find_map(|prefix| {
        let target = OperationId::try_from_hex(description.strip_prefix(prefix)?)?;
        Some((*prefix, target))
    })
}

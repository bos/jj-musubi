//! Canonicalizing local operations, and finding the local operation for a canonical one.

use std::collections::HashSet;
use std::fs;
use std::path::PathBuf;
use std::sync::Arc;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::CANONICAL_ATTRIBUTE;
use super::NodeError;
use super::NodeRepo;
use super::join::fingerprint;
use super::supersede::FIXUP_ATTRIBUTE;
use crate::format_guard;
use crate::format_guard::FormatError;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::presence::Kind;
use crate::remote_url::without_credentials;
use crate::workspaces;

impl NodeRepo {
    /// The canonical form of each local op head, but for one from before this repository
    /// joined, which has none until a merge takes it in (see [`Self::canonicalize`]). A `jj op
    /// abandon` is noticed first, as in [`Self::merge_heads`].
    pub fn canonical_heads(&mut self) -> Result<Vec<CanonicalOp>, NodeError> {
        self.check_abandon()?;
        let heads = self.local_heads()?;
        let mut canonical = vec![];
        for head in &heads {
            match self.canonicalize(head) {
                Ok(id) => canonical.push(id),
                Err(NodeError::BeforeJoin(_)) => {}
                Err(err) => return Err(err),
            }
        }
        if !self.late.is_empty() {
            self.reparent_late()?;
        }
        Ok(canonical)
    }

    /// Reparents the local operations canonicalized on operations a renaming superseded
    /// onto the rewrites, as their canonical operations have them, and moves the op heads
    /// among them there: before anything merges them with the renamed history, which would
    /// merge against an older common ancestor.
    fn reparent_late(&mut self) -> Result<(), NodeError> {
        let late = self.late.clone();
        let op_store = self.loader.op_store().clone();
        let mut rewrites: std::collections::HashMap<LocalOp, LocalOp> =
            std::collections::HashMap::new();
        for local in &late {
            let Some(canonical) = self.canonical_of(local) else {
                continue;
            };
            let mut op = op_store.read_operation(&local.0).block_on()?;
            let parents: Option<Vec<OperationId>> = self
                .canonical
                .parents(&canonical)?
                .iter()
                .map(|parent| Some(self.local_of(parent)?.0))
                .collect();
            let Some(parents) = parents else {
                tracing::info!(
                    "operation {} stays on the history it was written on",
                    local.0.hex()
                );
                continue;
            };
            if parents == op.parents {
                continue;
            }
            op.parents = parents;
            let rewrite = LocalOp(op_store.write_operation(&op).block_on()?);
            self.insert_map(rewrite.clone(), canonical)?;
            rewrites.insert(local.clone(), rewrite);
        }
        let heads = self.local_heads()?;
        for head in &heads {
            if let Some(rewrite) = rewrites.get(head) {
                self.loader
                    .op_heads_store()
                    .update_op_heads(std::slice::from_ref(&head.0), &rewrite.0)
                    .block_on()?;
            }
        }
        self.late.clear();
        let rewrites = rewrites
            .into_iter()
            .map(|(old, new)| (old, vec![new]))
            .collect();
        self.move_workspaces(&rewrites)
    }

    /// The canonical parents of a local operation, as they are now: what renamings
    /// superseded, renamed. Also whether any was.
    fn current_parents(&self, parents: &[LocalOp]) -> (Vec<CanonicalOp>, bool) {
        let mut renamed = false;
        let mut current = vec![];
        for parent in parents {
            if self.before_join.contains(parent) {
                continue;
            }
            let canonical = self
                .canonical_of(parent)
                .expect("parents canonicalized first");
            let now = self.current_ids(&canonical);
            renamed |= now != [canonical];
            for op in now {
                if !current.contains(&op) {
                    current.push(op);
                }
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
        if self.canonical_of(local).is_none() {
            self.check_abandon()?;
        }
        let op_store = self.loader.op_store().clone();
        // Post-order walk: an operation is canonicalized once all its parents are.
        let mut stack: Vec<(LocalOp, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.canonical_of(&id).is_some() || self.before_join.contains(&id) {
                continue;
            }
            let op = match loaded {
                Some(op) => op,
                None => op_store.read_operation(&id.0).block_on()?,
            };
            // A join point that `jj op abandon` rewrote, abandoning history from before the
            // join, which no other machine has: its parents are from before the join.
            if !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                && let Some(join) = self.joins.get(&fingerprint(&op))
            {
                let join = join.clone();
                self.insert_map(id, join)?;
                continue;
            }
            let parents = LocalOp::parents_of(&op);
            let missing: Vec<_> = parents
                .iter()
                .filter(|parent| {
                    self.canonical_of(parent).is_none() && !self.before_join.contains(*parent)
                })
                .cloned()
                .collect();
            if !missing.is_empty() {
                stack.push((id, Some(op)));
                stack.extend(missing.into_iter().map(|parent| (parent, None)));
                continue;
            }
            let late = parents.iter().any(|parent| self.late.contains(parent));
            let canonical_id =
                if let Some(canonical) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) {
                    self.realized_canonical(&id, &op, canonical)?
                } else if self.is_before_join(&id, &op)? {
                    self.before_join.insert(id);
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
            .all(|parent| self.before_join.contains(parent))
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
        if let Some(ancestors) = &self.join_ancestors {
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
            if self.join_points.contains(&id)
                || (!op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                    && self.joins.contains_key(&fingerprint(&op)))
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
        self.join_ancestors = Some(ancestors.clone());
        Ok(ancestors)
    }

    /// The canonical operation a realization names in its `musubi.canonical` attribute, as
    /// renamings have it now. `jj op abandon` rewrites the operations above the ones it
    /// abandons, keeping their metadata, so a rewritten realization still names its canonical
    /// operation, but has other parents: musubi notices the abandon, and rewrites it again,
    /// before canonicalizing anything (`NodeRepo::notice_abandon`). Its parents must already
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
        let canonical_id = match self.current_ids(&named).as_slice() {
            [now] => now.clone(),
            _ => named,
        };
        let local_parents = LocalOp::parents_of(op);
        let (parents, renamed) = self.current_parents(&local_parents);
        if renamed
            || local_parents
                .iter()
                .any(|parent| self.late.contains(parent))
        {
            self.late.push(id.clone());
        }
        if parents != self.canonical.parents(&canonical_id)? {
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

    fn write_canonical(
        &self,
        id: &LocalOp,
        op: &StoreOperation,
        parents: Vec<CanonicalOp>,
    ) -> Result<CanonicalOp, NodeError> {
        self.check_format(id, op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let Some(canonical) = self.canonical_of(&LocalOp(target))
            && self.canonical.is_ancestor(&canonical, &parents)?
        {
            metadata.description = format!("{prefix}{}", canonical.0.hex());
        }
        // jj records the command that made an operation, which may name an http(s) URL with
        // a token meant for this machine only.
        if !self.share_credentials()
            && let Some(args) = metadata.attributes.get_mut("args")
        {
            *args = without_credentials(args);
        }
        // Which workspace made an operation is per-machine, like the view's working copies:
        // qualify it, so that each machine can tell its own workspaces' operations from
        // another machine's workspace of the same name (see `realized_workspace_name`).
        metadata.workspace_name = metadata
            .workspace_name
            .map(|name| workspaces::workspace_key(self.machine.key(), name.as_str()));
        let kind = Kind::of(&metadata);
        // A fix-up changes no view: it restores what musubi works out from history alone.
        let (view_id, presence) = match parents.as_slice() {
            [parent] if metadata.attributes.contains_key(FIXUP_ATTRIBUTE) => (
                self.canonical.read_operation(parent)?.view_id,
                (*self.presence(parent)?).clone(),
            ),
            _ => {
                let (view, presence) = self.canonical_view(
                    id,
                    view,
                    &parents,
                    op.commit_predecessors.as_ref(),
                    &kind,
                )?;
                (self.canonical.write_view(&view)?, presence)
            }
        };
        let canonical_op = StoreOperation {
            view_id,
            parents: parents.into_iter().map(|parent| parent.0).collect(),
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        let canonical = self.canonical.write_operation(&canonical_op)?;
        self.remember_presence(canonical.clone(), presence.apply(&canonical, &kind));
        Ok(canonical)
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

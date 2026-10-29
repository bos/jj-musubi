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
use crate::format_guard;
use crate::format_guard::FormatError;
use crate::presence::Kind;
use crate::remote_url::without_credentials;
use crate::workspaces;

impl NodeRepo {
    /// The canonical form of each local op head, but for one from before this repository
    /// joined, which has none until a merge takes it in (see [`Self::canonicalize`]).
    pub fn canonical_heads(&mut self) -> Result<Vec<OperationId>, NodeError> {
        let heads = self.local_heads()?;
        let mut canonical = vec![];
        for head in &heads {
            match self.canonicalize(head) {
                Ok(id) => canonical.push(id),
                Err(NodeError::BeforeJoin(_)) => {}
                Err(err) => return Err(err),
            }
        }
        Ok(canonical)
    }

    pub fn canonical_of(&self, local: &OperationId) -> Option<OperationId> {
        if local == self.root_op_id() {
            return Some(self.canonical.root_operation_id().clone());
        }
        self.map.canonical_of(local).cloned()
    }

    pub fn local_of(&self, canonical: &OperationId) -> Option<OperationId> {
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
    pub fn canonicalize(&mut self, local: &OperationId) -> Result<OperationId, NodeError> {
        let op_store = self.loader.op_store().clone();
        // Post-order walk: an operation is canonicalized once all its parents are.
        let mut stack: Vec<(OperationId, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.canonical_of(&id).is_some() || self.before_join.contains(&id) {
                continue;
            }
            let op = match loaded {
                Some(op) => op,
                None => op_store.read_operation(&id).block_on()?,
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
            let missing: Vec<_> = op
                .parents
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
            let canonical_id =
                if let Some(canonical) = op.metadata.attributes.get(CANONICAL_ATTRIBUTE) {
                    self.realized_canonical(&id, &op, canonical)?
                } else if self.is_before_join(&id, &op)? {
                    self.before_join.insert(id);
                    continue;
                } else {
                    let parents: Vec<OperationId> = op
                        .parents
                        .iter()
                        .filter(|parent| !self.before_join.contains(*parent))
                        .map(|parent| {
                            self.canonical_of(parent)
                                .expect("parents canonicalized first")
                        })
                        .collect();
                    self.write_canonical(&id, &op, parents)?
                };
            self.insert_map(id, canonical_id)?;
        }
        match self.canonical_of(local) {
            Some(canonical) => Ok(canonical),
            None => Err(NodeError::BeforeJoin(local.hex())),
        }
    }

    /// Whether a local operation that isn't a join point or a realization, whose parents are
    /// canonicalized or from before the join, is from before the join too: all of its
    /// parents are, or it is the first of the history before a join, on the root. Another
    /// operation on the root, as `jj op abandon` leaves when it abandons everything below
    /// one, is the hive's, which then finds the history it had abandoned.
    fn is_before_join(&mut self, id: &OperationId, op: &StoreOperation) -> Result<bool, NodeError> {
        if op
            .parents
            .iter()
            .all(|parent| self.before_join.contains(parent))
        {
            return Ok(!op.parents.is_empty());
        }
        if op.parents.as_slice() != std::slice::from_ref(self.root_op_id()) || self.joins.is_empty()
        {
            return Ok(false);
        }
        Ok(self.join_ancestors()?.contains(id))
    }

    /// The ancestors of the join points reachable from the op heads, but for the root: the
    /// history before the joins. A join point `jj op abandon` rewrote is one by its
    /// fingerprint, as `canonicalize` takes it, with the rewritten history below it.
    fn join_ancestors(&mut self) -> Result<Arc<HashSet<OperationId>>, NodeError> {
        if let Some(ancestors) = &self.join_ancestors {
            return Ok(ancestors.clone());
        }
        let op_store = self.loader.op_store().clone();
        let root = self.root_op_id().clone();
        let mut seen = HashSet::new();
        let mut stack = self.local_heads()?;
        let mut below_joins: Vec<OperationId> = vec![];
        while let Some(id) = stack.pop() {
            if id == root || !seen.insert(id.clone()) {
                continue;
            }
            let op = op_store.read_operation(&id).block_on()?;
            if self.join_points.contains(&id)
                || (!op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                    && self.joins.contains_key(&fingerprint(&op)))
            {
                below_joins.extend(op.parents);
            } else {
                stack.extend(op.parents);
            }
        }
        let mut ancestors = HashSet::new();
        let mut stack = below_joins;
        while let Some(id) = stack.pop() {
            if id == *self.root_op_id() || !ancestors.insert(id.clone()) {
                continue;
            }
            stack.extend(op_store.read_operation(&id).block_on()?.parents);
        }
        let ancestors = Arc::new(ancestors);
        self.join_ancestors = Some(ancestors.clone());
        Ok(ancestors)
    }

    /// The canonical operation a realization names in its `musubi.canonical` attribute.
    /// `jj op abandon` rewrites the operations above the ones it abandons, keeping their
    /// metadata, so a rewritten realization still names its canonical operation, but has
    /// other parents. Its parents must already be canonicalized.
    fn realized_canonical(
        &self,
        id: &OperationId,
        op: &StoreOperation,
        canonical: &str,
    ) -> Result<OperationId, NodeError> {
        let canonical_id = OperationId::try_from_hex(canonical)
            .filter(|c| self.canonical.has_operation(c))
            .ok_or_else(|| NodeError::DanglingAttribute {
                op: id.hex(),
                canonical: canonical.to_owned(),
            })?;
        let parents: Vec<OperationId> = op
            .parents
            .iter()
            .map(|parent| {
                self.canonical_of(parent)
                    .expect("parents canonicalized first")
            })
            .collect();
        if parents != self.canonical.parents(&canonical_id)? {
            return Err(NodeError::RewrittenRealization {
                op: id.hex(),
                canonical: canonical_id.hex(),
            });
        }
        Ok(canonical_id)
    }

    fn write_canonical(
        &self,
        id: &OperationId,
        op: &StoreOperation,
        parents: Vec<OperationId>,
    ) -> Result<OperationId, NodeError> {
        self.check_format(id, op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let mut metadata = op.metadata.clone();
        if let Some((prefix, target)) = target_of(&metadata.description)
            && let Some(canonical) = self.canonical_of(&target)
            && self.canonical.is_ancestor(&canonical, &parents)?
        {
            metadata.description = format!("{prefix}{}", canonical.hex());
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
        let (view, presence) =
            self.canonical_view(id, view, &parents, op.commit_predecessors.as_ref(), &kind)?;
        let canonical_op = StoreOperation {
            view_id: self.canonical.write_view(&view)?,
            parents,
            metadata,
            commit_predecessors: op.commit_predecessors.clone(),
        };
        let canonical = self.canonical.write_operation(&canonical_op)?;
        self.remember_presence(canonical.clone(), presence.apply(&canonical, &kind));
        Ok(canonical)
    }

    /// Refuses operations whose files contain fields this jj-lib would drop.
    pub(super) fn check_format(
        &self,
        id: &OperationId,
        op: &StoreOperation,
    ) -> Result<(), NodeError> {
        let op_store_dir = self.repo_path.join("op_store");
        type Check = fn(&[u8]) -> Result<(), FormatError>;
        let checks: [(PathBuf, Check); 2] = [
            (
                op_store_dir.join("operations").join(id.hex()),
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
                op: id.hex(),
                source,
            })?;
        }
        Ok(())
    }

    pub(super) fn root_op_id(&self) -> &OperationId {
        self.loader.op_store().root_operation_id()
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

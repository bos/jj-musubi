//! Canonicalizing local operations, and finding the local operation for a canonical one.

use std::fs;
use std::path::PathBuf;

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
    /// The canonical form of each local op head.
    pub fn canonical_heads(&mut self) -> Result<Vec<OperationId>, NodeError> {
        let heads = self.local_heads()?;
        heads.iter().map(|head| self.canonicalize(head)).collect()
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
    pub fn canonicalize(&mut self, local: &OperationId) -> Result<OperationId, NodeError> {
        let op_store = self.loader.op_store().clone();
        // Post-order walk: an operation is canonicalized once all its parents are.
        let mut stack: Vec<(OperationId, Option<StoreOperation>)> = vec![(local.clone(), None)];
        while let Some((id, loaded)) = stack.pop() {
            if self.canonical_of(&id).is_some() {
                continue;
            }
            let op = match loaded {
                Some(op) => op,
                None => op_store.read_operation(&id).block_on()?,
            };
            let missing: Vec<_> = op
                .parents
                .iter()
                .filter(|parent| self.canonical_of(parent).is_none())
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
                } else if let Some(join) = self.joins.get(&fingerprint(&op)) {
                    // A join point that `jj op abandon` rewrote, abandoning history from before
                    // the join, which no other machine has.
                    join.clone()
                } else {
                    self.write_canonical(&id, &op)?
                };
            self.insert_map(id, canonical_id)?;
        }
        Ok(self.canonical_of(local).expect("canonicalized above"))
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
    ) -> Result<OperationId, NodeError> {
        self.check_format(id, op)?;
        let view = self.loader.op_store().read_view(&op.view_id).block_on()?;
        let parents: Vec<OperationId> = op
            .parents
            .iter()
            .map(|parent| {
                self.canonical_of(parent)
                    .expect("parents canonicalized first")
            })
            .collect();
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

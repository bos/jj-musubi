//! History identity and abandonment. A native abandon can preserve an operation's body
//! while changing its parents; these queries retain the distinction between exact native
//! versions, immutable originals and metadata that is insufficient to identify either.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_sync::OpId;

use crate::identity::{HistoryKey, SourceKey};

use super::AbandonedOperation;
use super::MERGE_KEY_TEMPLATE;
use super::OP_KEY_TEMPLATE;
use super::OperationHistory;
use super::World;
use super::join_fingerprint;
use super::merge_key;
use super::operation_header;
use super::single;

impl World {
    /// The `merge_key` of every operation in machine `m`'s history, read in process: a `jj`
    /// command could merge op heads.
    pub(super) fn merge_keys(&self, m: usize) -> BTreeSet<SourceKey> {
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let root = store.root_operation_id().clone();
        let mut keys = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut stack: Vec<jj_lib::op_store::OperationId> = self
            .op_heads(m)
            .iter()
            .map(|hex| jj_lib::op_store::OperationId::try_from_hex(hex).unwrap())
            .collect();
        while let Some(id) = stack.pop() {
            if id == root || !seen.insert(id.clone()) {
                continue;
            }
            let Ok(op) = futures::executor::block_on(store.read_operation(&id)) else {
                continue;
            };
            keys.insert(merge_key(&op));
            stack.extend(op.parents.iter().cloned());
        }
        keys
    }

    /// Machine `m` runs `jj op abandon` of its native operation `op`.
    pub fn op_abandon(&mut self, m: usize, op: &str) {
        // The id the command records differs between runs of a case; what the operation did
        // does not.
        let what = self.op_description(m, op);
        self.record(format!(
            "{}: abandoning the operation {what:?}",
            self.machine(m)
        ));
        self.abandon_ops(m, op, &[op.to_owned()]);
    }

    pub(crate) fn operation_history(&self, m: usize, exact: bool) -> OperationHistory {
        let mut result = OperationHistory {
            copy: Some(self.fx.machine_key(m)),
            ..OperationHistory::default()
        };
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        for id in self.replicated_history(m).into_keys() {
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            let header = operation_header(&op);
            result.native.insert(id.clone());
            result
                .native_by_header
                .entry(header.clone())
                .or_default()
                .insert(id.clone());
            result.headers.insert(header.clone());
            if exact {
                match self.known_original(m, &id) {
                    Some(original) => {
                        result.native_originals.insert(id.clone(), original.clone());
                        result
                            .originals_by_header
                            .entry(header)
                            .or_default()
                            .insert(original.clone());
                        result.originals.insert(original);
                    }
                    None => {
                        result.unknown.insert(header);
                    }
                }
            }
        }
        result
    }

    pub(super) fn hub_operation_history(&self) -> OperationHistory {
        let store = self.fx.hive.hub.store();
        let canonical = store.canonical();
        let head = CanonicalOp(store.head().1.clone());
        let mut result = OperationHistory::default();
        for id in canonical.ancestors_until(&[head], |_| false).unwrap() {
            let op = canonical.read_operation(&id).unwrap();
            result.headers.insert(operation_header(&op));
            result.originals.insert(canonical.original_id(&id).unwrap());
        }
        result
    }

    /// Qualify an already-known native alias before using its immutable original identity.
    /// A mapping to an unrelated current parent is not evidence about this operation.
    pub(crate) fn known_original(&self, m: usize, id: &OpId) -> Option<OpId> {
        let node = self.fx.hive.members[m].adapter.repo();
        let native =
            futures::executor::block_on(node.loader().op_store().read_operation(id)).ok()?;
        let marked = native
            .metadata
            .attributes
            .get(musubi_jj::node::CANONICAL_ATTRIBUTE)
            .and_then(OpId::try_from_hex)
            .map(CanonicalOp);
        // An explicit stored identity survives loss of the disposable translation cache.
        // Read only established bodies; never canonicalize or mint an identity for proof.
        node.canonical_of(&LocalOp(id.clone()))
            .into_iter()
            .chain(marked)
            .find_map(|canonical| {
                let source = node.canonical_store().read_operation(&canonical).ok()?;
                (operation_header(&native) == operation_header(&source))
                    .then(|| node.canonical_store().original_id(&canonical).ok())
                    .flatten()
            })
    }

    /// `jj op abandon` of `spec` on machine `m`: one operation, or a range `x..y`, which drops
    /// the native operations `dropped`. An operation with another reachable local version
    /// has not been removed from the replicated history.
    pub fn abandon_ops(&mut self, m: usize, spec: &str, dropped: &[String]) {
        self.observe_published_operations();
        let store = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .clone();
        let dropped: Vec<_> = dropped
            .iter()
            .map(|op| {
                let at = OpId::try_from_hex(op).unwrap();
                let body = futures::executor::block_on(store.read_operation(&at)).unwrap();
                AbandonedOperation {
                    by: m,
                    key: self.op_key(m, op),
                    header: operation_header(&body),
                    copy: self.fx.machine_key(m),
                    shared: self
                        .evidence
                        .published_headers
                        .contains(&operation_header(&body)),
                    native_witnesses: BTreeMap::new(),
                    originals: self.known_original(m, &at).map(|id| BTreeSet::from([id])),
                    native: at,
                }
            })
            .collect();
        // Every survivor keeps its view when jj changes its parents, including commands
        // with one parent. Pin that independent source for the reference.
        let before = self.ops_by_key(m);
        let prior_originals: BTreeMap<_, _> = before
            .values()
            .flatten()
            .map(|hex| {
                let id = OpId::try_from_hex(hex).unwrap();
                let original = self.known_original(m, &id);
                (id, original)
            })
            .collect();
        self.jj(m, &["op", "abandon", spec]);
        let after = self.ops_by_key(m);
        let mut survivor_links = BTreeMap::new();
        for (key, old) in &before {
            // Only a key one operation had before, and has after: operations sharing a key,
            // as two merges a node makes at one tick of its clock can, can't be told apart,
            // and stay jj's merges of their parents.
            let (Some(old), Some(new)) = (single(Some(old)), single(after.get(key))) else {
                continue;
            };
            if old == new {
                continue;
            }
            let id = jj_lib::op_store::OperationId::try_from_hex(old).unwrap();
            let op = futures::executor::block_on(store.read_operation(&id)).unwrap();
            let new_id = OpId::try_from_hex(new).unwrap();
            let mut new_body = futures::executor::block_on(store.read_operation(&new_id)).unwrap();
            new_body.parents = op.parents.clone();
            if new_body == op {
                // A realization jj reparented keeps its records, as the import check reads
                // them (`Imports::native_rewrites`): through an earlier rewrite, to the first.
                if op
                    .metadata
                    .attributes
                    .contains_key(musubi_jj::node::CANONICAL_ATTRIBUTE)
                    && let Some(rewrites) = self.imports.native_rewrites.get_mut(m)
                {
                    let original = rewrites.get(&id).cloned().unwrap_or_else(|| op.clone());
                    rewrites.insert(new_id.clone(), original);
                }
                survivor_links.insert(new_id.clone(), (id.clone(), prior_originals[&id].clone()));
                let copy = self.fx.machine_key(m);
                for dropped in &mut self.abandoned {
                    let key = (copy.clone(), id.clone());
                    if dropped.native_witnesses.contains_key(&key) {
                        if let Some(original) = &prior_originals[&id] {
                            dropped.qualify_native(&key, original.clone());
                        }
                        dropped
                            .native_witnesses
                            .entry((copy.clone(), new_id.clone()))
                            .or_insert(None);
                    }
                }
            }
            let replaced = self.retained_source(m, &op);
            self.remember_retained(key.clone(), replaced);
        }
        let retained = self.operation_history(m, true);
        let copy = self.fx.machine_key(m);
        for mut op in dropped {
            op.native_witnesses = retained
                .native_by_header
                .get(&op.header)
                .into_iter()
                .flatten()
                .map(|id| {
                    (
                        (copy.clone(), id.clone()),
                        retained.native_originals.get(id).cloned(),
                    )
                })
                .collect();
            // A native parent rewrite preserves the source body. Its already-established
            // identity was kept too, even if the new physical alias has no mapping yet.
            // Record the old id's identity, never assign it to the new native id: a new
            // parent version can acquire a different original when first canonicalized.
            for (_, id) in op.native_witnesses.keys().cloned().collect::<Vec<_>>() {
                if let Some((source, original)) = survivor_links.get(&id) {
                    op.native_witnesses
                        .insert((copy.clone(), source.clone()), original.clone());
                }
            }
            // Only a surviving alias of this original suppresses the obligation. An
            // independently reparented original with the same metadata does not.
            if !retained.proves_present(&op) {
                self.abandoned.push(op);
            }
        }
    }

    /// Machine `m`'s operations by `merge_key`, with their ids: more than one where
    /// operations share a key, as two merges a node makes at one tick of its clock can.
    pub(super) fn ops_by_key(&self, m: usize) -> BTreeMap<SourceKey, BTreeSet<String>> {
        let template = format!(r#"{MERGE_KEY_TEMPLATE} ++ "\t" ++ id ++ "\n""#);
        self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                &template,
            ],
        )
        .lines()
        .filter_map(|line| line.rsplit_once('\t'))
        .fold(BTreeMap::new(), |mut merges, (key, id)| {
            merges
                .entry(SourceKey::from_template(key))
                .or_insert_with(BTreeSet::new)
                .insert(id.to_owned());
            merges
        })
    }

    /// The key of machine `m`'s operation `op`, as `op_keys` has it.
    pub fn op_key(&self, m: usize, op: &str) -> HistoryKey {
        let key = self.raw_jj(
            m,
            &[
                "--at-op",
                op,
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                OP_KEY_TEMPLATE,
            ],
        );
        HistoryKey::from_template(key.trim_end_matches('\n'))
    }

    /// The replicated portion of the native history, stopping at this copy's join point.
    /// A native abandon can reparent a join point above shared history; its parents are
    /// still private, even if some of those operations once belonged to the hive.
    pub fn op_keys(&self, m: usize) -> BTreeSet<HistoryKey> {
        let history = self.replicated_history(m);
        self.op_ids_and_keys(m, None)
            .into_iter()
            .filter(|(id, _)| history.contains_key(&OpId::try_from_hex(id).unwrap()))
            .map(|(_, key)| key)
            .collect()
    }

    /// Native ids and merge keys above the independently observed join boundary.
    pub(crate) fn replicated_history(&self, m: usize) -> BTreeMap<OpId, SourceKey> {
        let store = self.fx.hive.members[m].adapter.repo().loader().op_store();
        let mut pending = self.fx.hive.members[m]
            .adapter
            .repo()
            .local_heads()
            .unwrap();
        let mut history = BTreeMap::new();
        while let Some(local) = pending.pop() {
            if history.contains_key(&local.0) {
                continue;
            }
            let op = futures::executor::block_on(store.read_operation(&local.0)).unwrap();
            history.insert(local.0, merge_key(&op));
            if join_fingerprint(&op) != self.evidence.join_points[m] {
                pending.extend(op.parents.into_iter().map(LocalOp));
            }
        }
        history
    }
}

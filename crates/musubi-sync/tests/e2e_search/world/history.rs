//! History identity and abandonment. A native abandon can preserve an operation's body
//! while changing its parents; these queries retain the distinction between exact native
//! versions, immutable originals and metadata that is insufficient to identify either.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use jj_lib::object_id::ObjectId as _;
use musubi_core::hub::HubStorage as _;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::op_id::LocalOp;
use musubi_sync::OpId;

use crate::identity::{HistoryKey, SourceKey};

use super::AbandonedOperation;
use super::LateOp;
use super::MERGE_KEY_TEMPLATE;
use super::OP_KEY_TEMPLATE;
use super::OperationHistory;
use super::World;
use super::join_fingerprint;
use super::merge_key;
use super::operation_header;
use super::single;

impl World {
    /// From a hive of four, a merge the hub accepted that one machine drops, another keeps,
    /// and a third took the drop of without advancing, before the hub went back and the
    /// keeper published it again: what survives of it is two operations, neither below the
    /// other (`races::history`, `Survivors::Apart`). Alpha commits work and delta takes it;
    /// the hub goes back, and gamma commits separate work; delta merges without publishing, and
    /// alpha's merge of them, which gamma keeps, is accepted. Alpha abandons its merge alone,
    /// and publishes that; beta, with `work` of its own (files it commits), takes the record
    /// and realizes the hub's head, then restarts. The hub goes back to gamma's work, losing the
    /// record, and gamma publishes the merge again. An hour passes after each time the hub goes
    /// back, so that it prunes as soon as every machine has taken its records. Returns it.
    pub fn hold_dropped_merge(&mut self, work: &[usize]) -> OpId {
        assert_eq!(self.nodes(), 4);
        let base = self.hub_seq();
        for &file in work {
            self.commit(1, 0, file);
        }
        self.commit(0, 0, 0);
        self.sync(0);
        self.sync(3);
        self.hub_goes_back(usize::try_from(self.hub_seq() - base).unwrap());
        self.an_hour_passes();
        self.commit(2, 0, 1);
        self.sync(2);
        let q = self.hub_seq();
        self.sync_realizing(3, usize::MAX);
        self.sync(0);
        let ours = self.fx.hive.hub_head();
        self.sync(2);
        self.sync(3);
        let both = self.fx.hive.hub_head();
        self.sync(0);
        self.jj(0, &["describe", "-m", "after survivor merge"]);
        self.sync(0);
        let (theirs, kept) = {
            let node = self.fx.node(0);
            let parents = node
                .canonical_store()
                .parents(&CanonicalOp(both.clone()))
                .unwrap();
            if parents.len() != 2 || !parents.contains(&CanonicalOp(ours.clone())) {
                self.fail(&format!("the merge of both isn't on alpha's: {parents:?}"));
            }
            let node = self.fx.node(0);
            let theirs = parents.into_iter().find(|op| op.0 != ours).unwrap();
            let local = |op: &CanonicalOp| node.local_of(op).unwrap().0.hex();
            (local(&theirs), local(&CanonicalOp(ours.clone())))
        };
        // Only alpha's merge: delta's has both its parents.
        self.abandon_ops(0, &format!("{theirs}..{kept}"), std::slice::from_ref(&kept));
        self.sync(0);
        if self.fx.hive.hub.store().record_count() != 1 {
            self.fail("alpha's abandon was not published");
        }
        self.sync_taking(1);
        self.restart(1);
        self.hub_goes_back(usize::try_from(self.hub_seq() - q).unwrap());
        self.an_hour_passes();
        self.sync(2);
        if self.fx.hive.hub_head() != ours {
            self.fail("gamma did not publish the dropped merge again");
        }
        ours
    }

    /// Machine `m` alone published the drop of `kept`: the hub dropped it, and `m` merged
    /// what survives of it with its own work, three operations, in one operation.
    pub fn check_dropped_by(&mut self, m: usize, kept: &OpId) {
        if !self.fx.hive.hub.is_dropped(kept, &[]).unwrap() {
            self.fail(&format!(
                "{} did not publish the drop of the merge",
                self.machine(m)
            ));
        }
        let merges = self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-T",
                r#"if(parents.len() == 3, description.first_line() ++ "\n")"#,
            ],
        );
        if !merges
            .lines()
            .any(|d| d == "reconcile divergent operations")
        {
            self.fail(&format!(
                "{} did not merge what survives with its work at once",
                self.machine(m)
            ));
        }
    }

    /// The `merge_key` of every operation of the hub's history.
    pub(super) fn hub_merge_keys(&self) -> BTreeSet<SourceKey> {
        let store = self.fx.hive.hub.store();
        let canonical = store.canonical();
        let head = CanonicalOp(store.head().1.clone());
        canonical
            .ancestors_until(&[head], |_| false)
            .unwrap()
            .iter()
            .map(|op| merge_key(&canonical.read_operation(op).unwrap()))
            .collect()
    }

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

    /// Publishes new work, pauses before advancing the base to that push, then trims all
    /// history below it. Unlike single-operation abandonment, this can drop the old base
    /// and every join while keeping an accepted operation outside the base's ancestry.
    pub fn trim_below_accepted_push(&mut self, m: usize) {
        self.sync(m);
        let (base, dropped) = self.trim_range(m);
        let description = self.message(m);
        // A fresh child works even when a cloned workspace is at an immutable commit.
        self.jj(m, &["new", "-m", &description]);
        self.sync_partial(m, 1, None);
        self.abandon_ops(m, &format!("..{base}"), &dropped);
        self.sync(m);
    }

    /// Accept a forget, keep the old saved base, then trim both beneath unpublished work.
    /// If the other copy is already forgotten, this also reaches a newer saved base with
    /// an older accepted own push, without manufacturing adapter state.
    pub fn trim_below_accepted_forget(&mut self, m: usize, other: usize) {
        self.sync(m);
        self.forget_copy(m, other);
        self.sync_partial(m, 1, None);
        let (base, dropped) = self.trim_range(m);
        let description = self.message(m);
        self.jj(m, &["new", "-m", &description]);
        self.abandon_ops(m, &format!("..{base}"), &dropped);
        self.sync(m);
    }

    /// Publishes machine `m`'s work, makes a change the hub hasn't accepted, and trims all
    /// history below it, as `jj op abandon ..@-` does, leaving it alone on the root. Returns
    /// jj's id of the op head the trim left, from before the node handles the trim: a command
    /// that loaded the repository then, or runs `--at-op` that id, writes on it.
    pub fn trim_to_unpublished_root(&mut self, m: usize) -> String {
        self.sync(m);
        let (base, dropped) = self.trim_range(m);
        let description = self.message(m);
        self.jj(m, &["new", "-m", &description]);
        self.abandon_ops(m, &format!("..{base}"), &dropped);
        let head = match &self.op_heads(m)[..] {
            [head] => head.clone(),
            heads => self.fail(&format!(
                "{} has op heads {heads:?} after a trim",
                self.machine(m)
            )),
        };
        self.trims[m] += 1;
        self.remember_late_op(m, &head);
        head
    }

    /// The operations machine `m`'s full trims to the root left, before its node handled
    /// them, and the late commands and merges written on those, newest first. No op head
    /// reaches one once the node has handled its trim, or once a later trim has dropped it,
    /// but jj still loads it by its id: a command that loaded the repository then, or one run
    /// `--at-op` it, writes on it.
    pub fn late_ops(&self, m: usize) -> Vec<LateOp> {
        self.late_ops[m].clone()
    }

    /// How many full trims to the root machine `m` has made (`trim_to_unpublished_root`).
    pub fn trims(&self, m: usize) -> usize {
        self.trims[m]
    }

    /// Whether operation `id` was written with the clock stepped back (`late_command`).
    pub fn stepped_back(&self, id: &str) -> bool {
        self.stepped_back.contains(id)
    }

    fn remember_late_op(&mut self, m: usize, id: &str) {
        if self.late_ops[m].iter().any(|op| op.id == id) {
            return;
        }
        let described = self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "--at-op",
                id,
                "op",
                "log",
                "--no-graph",
                "-n",
                "1",
                "-T",
                r#"parents.len() ++ " " ++ description.first_line()"#,
            ],
        );
        let (parents, description) = described.split_once(' ').unwrap();
        let op = LateOp {
            id: id.to_owned(),
            description: description.to_owned(),
            trim: self.trims[m],
            merge: parents != "1",
        };
        self.late_ops[m].insert(0, op);
    }

    /// Runs a command at machine `m`'s late operation `op` (`late_ops`), as `jj_at_op` does,
    /// and remembers what it wrote as late operations too. With `stepped_back`, the machine's
    /// clock has stepped back, as an NTP correction or a reset clock can: the command's
    /// operation ends before every other of the case, so jj puts it first among the parents
    /// of a merge, which it orders by when they ended. Each such command gets a time of its
    /// own, all of them before the tests' epoch, where every other operation's time is: two
    /// operations at one time are ordered by their ids, which differ between runs of a case.
    pub fn late_command(&mut self, m: usize, op: &str, args: &[&str], stepped_back: bool) {
        let heads_before = self.op_heads(m);
        if stepped_back {
            let second = self.stepped_back.len();
            let time = format!(
                "2000-12-31T{:02}:{:02}:{:02}.000+00:00",
                second / 3600,
                second / 60 % 60,
                second % 60
            );
            let config = format!("debug.operation-timestamp=\"{time}\"");
            let mut full = vec!["--config", config.as_str()];
            full.extend_from_slice(args);
            self.jj_at_op(m, op, &full);
        } else {
            self.jj_at_op(m, op, args);
        }
        // At most one, since a command writes one operation, or none if it changed nothing:
        // the pool's order mustn't depend on the order of operation ids, which differ between
        // runs.
        let new: Vec<String> = self
            .op_heads(m)
            .into_iter()
            .filter(|head| !heads_before.contains(head))
            .collect();
        if new.len() > 1 {
            self.fail(&format!(
                "{}'s late command left new op heads {new:?}",
                self.machine(m)
            ));
        }
        for head in new {
            if stepped_back {
                self.stepped_back.insert(head.clone());
            }
            self.remember_late_op(m, &head);
        }
    }

    /// Has machine `m`, if it has several op heads, run a `jj` command, which merges them
    /// first, and remembers the merge as a late operation. Returns the heads it merged.
    pub fn merge_late_heads(&mut self, m: usize) -> Vec<String> {
        let heads = self.op_heads(m);
        if heads.len() < 2 {
            return vec![];
        }
        self.jj(m, &["status"]);
        // The merge, below whatever the command wrote after it: snapshots and imports.
        let ops = self.raw_jj(
            m,
            &[
                "--ignore-working-copy",
                "op",
                "log",
                "--no-graph",
                "-n",
                "8",
                "-T",
                r#"id ++ " " ++ parents.map(|p| p.id()).join(" ") ++ "\n""#,
            ],
        );
        let merge = ops.lines().find_map(|line| {
            let mut ids = line.split(' ');
            let id = ids.next()?;
            let mut parents: Vec<&str> = ids.collect();
            parents.sort_unstable();
            (parents == heads).then(|| id.to_owned())
        });
        let Some(merge) = merge else {
            self.fail(&format!(
                "{} merged its op heads {heads:?} without a merge",
                self.machine(m)
            ));
        };
        self.remember_late_op(m, &merge);
        heads
    }

    pub(super) fn trim_range(&self, m: usize) -> (String, Vec<String>) {
        let history = self.op_ids_and_keys(m, None);
        let base = history[0].0.clone();
        let root = self.fx.hive.members[m]
            .adapter
            .repo()
            .loader()
            .op_store()
            .root_operation_id()
            .hex();
        let dropped = history
            .into_iter()
            .map(|(id, _)| id)
            .filter(|id| *id != root)
            .collect();
        (base, dropped)
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
        self.begin_workspace_trim(m);
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
                    merge: merge_key(&body),
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
        // and internal fix-ups with one parent. Pin that independent source for the reference.
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

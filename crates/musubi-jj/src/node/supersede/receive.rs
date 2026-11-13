//! Preparing and adopting the hub's records, including interrupted adoption.

use std::collections::HashMap;
use std::collections::HashSet;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::Earlier;
use super::NodeError;
use super::NodeRepo;
use super::Realign;
use super::Taking;
use super::TakingStop;
use super::digests;

use crate::canonical::Contraction;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::records::HubOp;
use crate::records::Record;
use crate::records::RecordDigest;
use crate::records::RecordPrefix;

impl NodeRepo {
    /// Gets ready to take `records`, the hub's, after the first ones `prefix` stands for:
    /// renames this node's history as they name it, writing the rewrites of its local
    /// operations beside them, without moving its op heads. Returns whether they drop an op
    /// head. `prefix` is this node's, or none, or this node is [fresh](Self::is_fresh).
    pub fn prepare_records(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
    ) -> Result<bool, NodeError> {
        if self
            .records
            .taking
            .as_ref()
            .is_none_or(|taking| taking.prefix != *prefix || taking.records != records)
        {
            self.prepare(prefix, records)?;
        } else {
            self.prepare_again_if_moved()?;
        }
        let taking = self.records.taking.as_ref().expect("prepared above");
        if taking.switched {
            return Ok(false);
        }
        let heads = self.local_heads()?;
        Ok(heads.iter().any(|head| {
            self.canonical_of(head)
                .is_some_and(|c| taking.dropped.contains(&c))
        }))
    }

    /// Whether received records remain in custody. Taking the hub's next announcement either
    /// applies them or, if the hub lost them, makes their drops pending, even when it announces
    /// the records this node already applied.
    pub fn has_record_custody(&self) -> bool {
        !self.records.custody.is_empty()
    }

    /// Keeps in custody `records`, after those `prefix` stands for, beyond the first `common`
    /// this node holds, before anything written for them or named as they name the history
    /// is: its history may then leave out what they drop, though it takes them only later, as
    /// while they drop an op head, or never, if the hub loses them first. Writes only records
    /// it doesn't hold or keep already.
    fn keep_custody(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
        common: usize,
    ) -> Result<(), NodeError> {
        let chain = digests(&prefix.digest, records);
        let new: Vec<Earlier> = {
            let held: HashSet<&RecordDigest> = self.records.digests.iter().collect();
            let kept: HashSet<&RecordDigest> = self
                .records
                .custody
                .iter()
                .map(|custody| &custody.digest)
                .collect();
            (common..records.len())
                .filter(|&k| !held.contains(&chain[k + 1]) && !kept.contains(&chain[k + 1]))
                .map(|k| Earlier {
                    digest: chain[k + 1].clone(),
                    before: chain[k].clone(),
                    record: records[k].clone(),
                })
                .collect()
        };
        if new.is_empty() {
            return Ok(());
        }
        let checkpoint = self.records.checkpoint();
        self.records.custody.extend(new);
        if let Err(err) = self.save_records() {
            self.records.restore(checkpoint);
            return Err(err);
        }
        Ok(())
    }

    /// Renames this node's history as `records` name it, writing the rewrites of its local
    /// operations, from scratch.
    fn prepare(&mut self, prefix: &RecordPrefix, records: &[Record]) -> Result<(), NodeError> {
        self.records.taking = None;
        // The hub-to-node translation as it is with no records being taken, which
        // `rename_for` uses.
        self.forget_to_node();
        let taking = self.rename_for(prefix, records)?;
        self.records.taking = Some(taking);
        self.forget_to_node();
        Ok(())
    }

    /// Prepares the records being taken again if the op heads moved since they were
    /// prepared, as a `jj` command moves them. Their rewrites are only of what was reachable
    /// from the op heads then, and a sync's next step gives the operation such a command wrote
    /// a canonical form, as `realize` does on a node opened since, on the history the records
    /// rename: taken without renaming it, it would bring back what they drop. Does nothing if
    /// the op heads moved there already.
    fn prepare_again_if_moved(&mut self) -> Result<(), NodeError> {
        let Some(taking) = self
            .records
            .taking
            .as_ref()
            .filter(|taking| !taking.switched)
        else {
            return Ok(());
        };
        let mut heads = self.local_heads()?;
        heads.sort();
        if heads == taking.heads {
            return Ok(());
        }
        let (prefix, records) = (taking.prefix.clone(), taking.records.clone());
        self.prepare(&prefix, &records)
    }

    /// The renaming that taking `records`, after those `prefix` stands for, makes, its local
    /// rewrites written.
    fn rename_for(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
    ) -> Result<Taking, NodeError> {
        // Only a node with nothing of the hive's takes records it knows only by their count
        // and digest: it has nothing they drop. Any node may take records all whole in place
        // of those it knew so: whichever of them drops what it has, it drops by name.
        if *prefix != self.records.prefix && prefix.count > 0 && !self.is_fresh() {
            return Err(NodeError::PrunedRecords);
        }
        let applied = self.records.applied.clone();
        let common = if *prefix == self.records.prefix {
            applied
                .iter()
                .zip(records)
                .take_while(|(a, b)| a == b)
                .count()
        } else {
            0
        };
        // Before anything below, or anything named as they name the history, writes a local
        // operation.
        self.keep_custody(prefix, records, common)?;
        self.check_abandon()?;
        let heads = self.local_heads()?;
        // A command can publish after the policy read heads_for. Translate this exact
        // captured history on its actual parents before contracting away their views.
        for head in &heads {
            match self.canonicalize_unchecked(head) {
                Ok(_) | Err(NodeError::BeforeJoin(_)) => {}
                Err(err) => return Err(err),
            }
        }
        let mut native_heads = heads
            .iter()
            .map(|head| self.loader.load_operation(&head.0).block_on())
            .collect::<Result<Vec<_>, _>>()?;
        // As jj orders heads before merging their views.
        native_heads.sort_by_key(|op| op.metadata().time.end.timestamp);
        let own = self.merged_local_workspaces(&native_heads)?;
        let store = &self.canonical;
        let (mapped, unmapped) = self.local_walk(&heads)?;
        // Records in custody that these lack: the hub lost them, and this node publishes what
        // they drop, as of records it took that the hub lost. It never took them, so its
        // history may still have what they drop, which it drops now too.
        let incoming: HashSet<RecordDigest> =
            digests(&prefix.digest, records).into_iter().collect();
        let lost_custody: Vec<&Earlier> = self
            .records
            .custody
            .iter()
            .filter(|custody| !incoming.contains(&custody.digest))
            .collect();
        // Another raw version of a dropped original may be here without the record that
        // renamed it. Match physical history, not old bodies in the canonical cache.
        let mut local_versions: HashMap<OperationId, Vec<CanonicalOp>> = HashMap::new();
        if common < records.len() || !lost_custody.is_empty() {
            let wanted: HashSet<OperationId> = records[common..]
                .iter()
                .chain(lost_custody.iter().map(|custody| &custody.record))
                .flat_map(Record::ops)
                .filter(|op| store.has_operation(&op.0))
                .map(|op| store.original_id(&op.0))
                .collect::<Result<_, _>>()?;
            let tops: Vec<CanonicalOp> = mapped.into_iter().map(|(_, op)| op).collect();
            for op in store.ancestors_until(&tops, |_| false)? {
                let original = store.original_id(&op)?;
                if wanted.contains(&original) {
                    local_versions.entry(original).or_default().push(op);
                }
            }
        }
        // A hub name from after the `from`th record this node took, as the history named the
        // operation after the records the hub and this node share: back through how each
        // record since renamed the hub's history. An operation made since has no such name,
        // and keeps its own.
        let hub_renamings = &self.records.hub_renamings;
        let back = |op: &CanonicalOp, from: usize| {
            (common..from).rev().fold(op.clone(), |op, k| {
                match hub_renamings.get(k).and_then(|renaming| renaming.get(&op)) {
                    Some(old) => old.clone(),
                    None => op,
                }
            })
        };
        // What this node dropped beyond the records they share: its own pending drops, and
        // its records the hub lacks (as after the hub went back), named so.
        let mut mine: Vec<CanonicalOp> = self
            .records
            .pending
            .ops()
            .iter()
            .map(|op| back(&op.0, applied.len()))
            .collect();
        for (k, record) in applied.iter().enumerate().skip(common) {
            mine.extend(record.ops().iter().map(|op| back(&op.0, k)));
        }
        // Named as the history this node realized named them; `name_pending_as` names them as
        // the hub's does, by their originals.
        let mut to_drop = vec![];
        // What the records both hold drop already is no drop of this node's.
        let mut shared_originals = HashSet::new();
        for op in applied[..common].iter().flat_map(Record::ops) {
            if store.has_operation(&op.0) {
                shared_originals.insert(store.original_id(&op.0)?);
            }
        }
        for custody in &lost_custody {
            for op in custody.record.ops() {
                if store.has_operation(&op.0)
                    && shared_originals.contains(&store.original_id(&op.0)?)
                {
                    continue;
                }
                mine.push(op.0.clone());
                if store.has_operation(&op.0)
                    && let Some(versions) = local_versions.get(&store.original_id(&op.0)?)
                {
                    to_drop.extend(versions.iter().cloned());
                }
            }
        }
        let lost_custody: HashSet<RecordDigest> = lost_custody
            .into_iter()
            .map(|custody| custody.digest.clone())
            .collect();
        // Where the hub lost records this machine took, it may have lost the base too: the
        // root is accepted wherever the hub went back to, at the cost of fetching everything.
        let mut base = if common < applied.len() {
            Some(store.root_operation_id().clone())
        } else {
            self.stored_base().map(|base| base.0)
        };
        // Then forward through the hub's records, one at a time, keeping how each renames
        // the hub's history below the base; and the node names of what they drop, but what
        // this node dropped already, whose node names are what is left below it.
        let mut renamings: Vec<HashMap<CanonicalOp, CanonicalOp>> = vec![];
        for record in &records[common..] {
            let names: Vec<CanonicalOp> = record.ops().iter().map(|op| op.0.clone()).collect();
            let dropped_here: HashSet<CanonicalOp> = mine.iter().cloned().collect();
            for op in &names {
                if let Some(versions) = local_versions.get(&store.original_id(op)?) {
                    to_drop.extend(versions.iter().cloned());
                }
                let shared = renamings.iter().rev().fold(op.clone(), |op, renaming| {
                    renaming.get(&op).cloned().unwrap_or(op)
                });
                if dropped_here.contains(op)
                    || self.records.dropped.contains(&shared)
                    || !store.has_operation(&shared)
                {
                    continue;
                }
                let original = store.original_id(&shared)?;
                for image in self.to_node_ids(&shared)? {
                    if store.original_id(&image)? == original {
                        to_drop.push(image);
                    }
                }
            }
            let mut contraction =
                Contraction::new(store, names.iter().cloned())?.sharing(self.presences.clone());
            // An operation made after the records they share has no name from before them,
            // so its history names the record's operations as renamed since: it is named as
            // this machine's history names it, as any machine that has it pushes it.
            let mut ours =
                Contraction::new(store, to_drop.iter().cloned())?.sharing(self.presences.clone());
            let theirs: HashSet<&CanonicalOp> = names.iter().collect();
            // A record drops an original, whatever it names it: what this node dropped as
            // another version of one the record names is published by it, as another machine
            // published it under the name the hub's history gave it.
            let mut theirs_originals = HashSet::new();
            for op in names.iter().filter(|op| store.has_operation(op)) {
                theirs_originals.insert(store.original_id(op)?);
            }
            let mut renamed = vec![];
            for op in mine.iter().filter(|op| !theirs.contains(op)) {
                if !store.has_operation(op) {
                    renamed.push(op.clone());
                    continue;
                }
                if theirs_originals.contains(&store.original_id(op)?) {
                    continue;
                }
                let images = contraction.images(store, op)?;
                if images == std::slice::from_ref(op) {
                    if ours.drops(op) {
                        renamed.push(op.clone());
                    } else {
                        renamed.extend(ours.images(store, op)?);
                    }
                } else {
                    renamed.extend(images);
                }
            }
            mine = renamed;
            if let Some(old) = base.take() {
                base = if store.has_operation(&old) {
                    contraction.images(store, &old)?.first().cloned()
                } else {
                    Some(old)
                };
            }
            let dropped = contraction.dropped().clone();
            renamings.push(
                contraction
                    .into_images()
                    .into_iter()
                    .filter(|(old, _)| !dropped.contains(old))
                    .filter_map(|(old, new)| match new.as_slice() {
                        [new] => Some((new.clone(), old)),
                        _ => None,
                    })
                    .collect(),
            );
        }
        let mut contraction = Contraction::new(store, to_drop)?.sharing(self.presences.clone());
        let locals =
            self.rewrite_locals(&mut contraction, &heads, &HashMap::new(), &unmapped, None)?;
        let mut heads = heads;
        heads.sort();
        Ok(Taking {
            prefix: prefix.clone(),
            records: records.to_vec(),
            common,
            hub_renamings: renamings,
            dropped: contraction.dropped().clone(),
            switched: false,
            own,
            renaming: contraction.into_images(),
            pending: Record::new(mine.into_iter().map(HubOp)),
            locals,
            heads,
            base: base.map(HubOp),
            lost_custody,
        })
    }

    /// Whether records are being taken whose renaming the op heads haven't moved to.
    pub(in super::super) fn taking_unswitched(&self) -> bool {
        self.records
            .taking
            .as_ref()
            .is_some_and(|taking| !taking.switched)
    }

    /// Whether the prepared base is the root: a trim removed the accepted local base, or
    /// the hub lost records this copy held. Publication must retain this copy's current
    /// Git state, including where a root child was realized before these records arrived.
    pub(in super::super) fn taking_root_base(&mut self) -> Result<bool, NodeError> {
        self.prepare_again_if_moved()?;
        Ok(self.records.taking.as_ref().is_some_and(|taking| {
            !taking.switched
                && taking
                    .base
                    .as_ref()
                    .is_some_and(|base| base.0 == *self.canonical.root_operation_id())
        }))
    }

    /// The op heads that moving them where the records being taken name them leaves beside
    /// `head`, as they name them: `max(images(heads) ∪ {head}) \ {head}`. Empty if no records
    /// are being taken, or the op heads are there already.
    pub(in super::super) fn taken_beside(
        &mut self,
        head: &LocalOp,
    ) -> Result<Vec<LocalOp>, NodeError> {
        self.prepare_again_if_moved()?;
        let Some(taking) = self
            .records
            .taking
            .as_ref()
            .filter(|taking| !taking.switched)
        else {
            return Ok(vec![]);
        };
        let mut beside = self.moved_heads(&self.local_heads()?, &taking.locals, Some(head))?;
        beside.retain(|op| op != head);
        Ok(beside)
    }

    /// Takes the records being taken, and moves the op heads where they name them, and to
    /// `head` too if given: `heads := max(images(heads) ∪ {head})`, with `merged`, if given, a
    /// merge of `head` with heads [`Self::taken_beside`] it, in place of those it merges,
    /// preparing the records again first if the op heads moved
    /// ([`Self::prepare_again_if_moved`]). Does nothing if no records are being taken, or the
    /// op heads are there already. The caller moves the workspaces after
    /// ([`Self::move_taken_workspaces`]), holding no lock of jj's: jj takes a workspace's lock
    /// before its colocated git lock.
    pub(in super::super) fn switch_to_taken(
        &mut self,
        head: Option<&LocalOp>,
        merged: Option<&LocalOp>,
    ) -> Result<(), NodeError> {
        self.prepare_again_if_moved()?;
        let Some(mut taking) = self.records.taking.take() else {
            return Ok(());
        };
        if !taking.switched {
            // Translation no longer names the history as `taking` does, whether this fails,
            // dropping it, or holds it, its pending drops becoming this node's.
            self.forget_to_node();
            // Every operation the move names written first, which the realizations are by now.
            self.settle()?;
            let heads = self.local_heads()?;
            let to = self.new_heads(&heads, &taking.locals, head, merged)?;
            let renamed = taking
                .locals
                .iter()
                .filter(|(old, new)| new.as_slice() != std::slice::from_ref(*old))
                .flat_map(|(old, new)| std::iter::once(old).chain(new));
            let canonical = heads
                .iter()
                .chain(&to)
                .chain(renamed)
                .filter_map(|local| Some((local.clone(), self.canonical_of(local)?)))
                .collect();
            let from = heads
                .iter()
                .map(|head| {
                    let new = taking.locals.get(head).cloned();
                    (head.clone(), new.unwrap_or_else(|| vec![head.clone()]))
                })
                .collect();
            let realign = Realign {
                from,
                to: to.clone(),
                canonical,
            };
            self.hold_taken(&mut taking, realign)?;
            self.stop_taking(TakingStop::Heads)?;
            self.publish_heads(&heads, &to)?;
            self.forget_local_caches();
            taking.switched = true;
        }
        self.records.taking = Some(taking);
        Ok(())
    }

    /// Whether one of the local operations `canonical` names that stands for an operation a
    /// renaming superseded is below `heads`.
    pub(super) fn superseded_below(
        &self,
        heads: &[LocalOp],
        canonical: &HashMap<LocalOp, CanonicalOp>,
    ) -> Result<bool, NodeError> {
        let mut superseded: HashMap<&LocalOp, &CanonicalOp> = HashMap::new();
        for (local, c) in canonical {
            if self.current_ids(c)? != std::slice::from_ref(c) {
                superseded.insert(local, c);
            }
        }
        // Below the lowest of them, an operation that stands for one of the store's has none
        // of them below it. One written on one of them, canonicalized on what that became, is
        // as high as that one, at least.
        let mut floor = u64::MAX;
        for c in superseded.values() {
            if self.canonical.has_operation(c) {
                floor = floor.min(self.canonical.generation(c)?);
            }
        }
        let op_store = self.loader.op_store();
        let mut stack = heads.to_vec();
        let mut seen = HashSet::new();
        while let Some(local) = stack.pop() {
            if !seen.insert(local.clone()) || self.before_join.contains(&local) {
                continue;
            }
            if superseded.contains_key(&local) {
                return Ok(true);
            }
            if self
                .canonical_of(&local)
                .is_some_and(|c| self.canonical.generation(&c).is_ok_and(|g| g < floor))
            {
                continue;
            }
            let op = op_store.read_operation(&local.0).block_on()?;
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(false)
    }

    /// Makes the records being taken the records this node holds, and what they rename its
    /// history, pending drops and fix-up as, in the write that counts their renaming, before
    /// the op heads move there: counted alone, the renaming would leave what they drop
    /// dropped here, but neither pending nor in a record this node holds, so that if the hub
    /// lost them, nothing here would publish it again. The op heads and the workspaces move
    /// after, as `realign` says, which the write records, so that a restart moves them if
    /// they hadn't (`realign_heads`). If the write fails, this node holds what it did, as
    /// `records.json` still says.
    fn hold_taken(&mut self, taking: &mut Taking, realign: Realign) -> Result<(), NodeError> {
        // Appended first, each counting only once `records.json` says so.
        self.write_hub_renamings(
            &taking.prefix.digest,
            &taking.records,
            taking.common,
            &taking.hub_renamings,
        )?;
        // Delayed commands can still name an unmarked native source after cache loss.
        // The held step must preserve its observed pre-contraction identity too.
        let sources: HashMap<LocalOp, CanonicalOp> = realign
            .canonical
            .iter()
            .filter(|(local, _)| {
                taking
                    .locals
                    .get(local)
                    .is_some_and(|now| now.as_slice() != [(*local).clone()])
            })
            .filter_map(|(local, canonical)| {
                let op = self.loader.op_store().read_operation(&local.0).block_on();
                match op {
                    Ok(op)
                        if !op
                            .metadata
                            .attributes
                            .contains_key(crate::node::CANONICAL_ATTRIBUTE) =>
                    {
                        Some(Ok((local.clone(), canonical.clone())))
                    }
                    Ok(_) => None,
                    Err(err) => Some(Err(err)),
                }
            })
            .collect::<Result<_, _>>()?;
        let step = self.append_step(taking.renaming.clone(), &taking.dropped, &sources)?;
        let checkpoint = self.records.checkpoint();
        // Its own drops published, the fix-up goes with them.
        if taking.pending.is_empty() {
            self.records.fixup = None;
            self.records.fixup_written = false;
            self.records.fixup_from = None;
        } else if let Some(fixup) = &self.records.fixup
            && let Some(expected) = &fixup.expected
        {
            // The op head the expected values were worked out at, as the records renamed it,
            // unless they dropped it or made it several.
            let at = OperationId::try_from_hex(&expected.at)
                .map(LocalOp)
                .filter(|at| {
                    !self
                        .canonical_of(at)
                        .is_some_and(|c| taking.dropped.contains(&c))
                });
            let now = at.and_then(|at| match taking.locals.get(&at).map(Vec::as_slice) {
                Some([now]) => Some(now.clone()),
                Some(_) => None,
                None => Some(at),
            });
            let fixup = self.records.fixup.as_mut().expect("matched above");
            match now {
                Some(now) => fixup.expected.as_mut().expect("matched above").at = now.0.hex(),
                None => fixup.expected = None,
            }
        }
        // Lost receipts have now had their effects applied with the incoming records. Keep
        // their readable prefixes as earlier records, without ever reporting them as the
        // current applied list. The hold's reachability cleanup discards unknown prefixes.
        let earlier: HashSet<RecordDigest> = self
            .records
            .earlier
            .iter()
            .map(|entry| entry.digest.clone())
            .collect();
        self.records.earlier.extend(
            self.records
                .custody
                .iter()
                .filter(|entry| {
                    taking.lost_custody.contains(&entry.digest) && !earlier.contains(&entry.digest)
                })
                .cloned(),
        );
        self.records
            .hold(taking.prefix.clone(), taking.records.clone());
        // Custody taken, or lost and now pending, in the same write.
        let held: HashSet<RecordDigest> = self.records.digests.iter().cloned().collect();
        self.records.custody.retain(|custody| {
            !held.contains(&custody.digest) && !taking.lost_custody.contains(&custody.digest)
        });
        self.records.fresh = false;
        self.records.pending = taking.pending.clone();
        self.records.steps += usize::from(step.is_some());
        self.records.realign = Some(realign);
        if let Err(err) = self
            .stop_taking(TakingStop::Hold)
            .and_then(|()| self.save_records())
        {
            self.records.restore(checkpoint);
            return Err(err);
        }
        if let Some(step) = step {
            self.records.compose(step);
        }
        self.records.hub_renamings.truncate(taking.common);
        self.records
            .hub_renamings
            .extend(std::mem::take(&mut taking.hub_renamings));
        self.forget_to_node();
        Ok(())
    }

    /// Moves the workspaces' recorded operations where the records taken name them, once the
    /// op heads are there, which is the last of taking them.
    pub(in super::super) fn move_taken_workspaces(&mut self) -> Result<(), NodeError> {
        let Some(taking) = self.records.taking.take_if(|taking| taking.switched) else {
            return Ok(());
        };
        self.stop_taking(TakingStop::Workspaces)?;
        self.move_workspaces(&taking.locals)?;
        self.records.realign = None;
        self.save_records()
    }

    /// For tests of errors: the next write that holds records taken fails, as an I/O error
    /// would, having written none of it.
    pub fn fail_holding_records(&mut self) {
        self.records.stop = Some(TakingStop::Hold);
    }

    /// For tests of crashes: the next taking of records stops, failing, once it holds them,
    /// before the op heads move there, or, if `heads_moved`, once they have, before the
    /// workspaces. Reopening the repository then is a crash there.
    pub fn crash_taking_records(&mut self, heads_moved: bool) {
        self.records.stop = Some(if heads_moved {
            TakingStop::Workspaces
        } else {
            TakingStop::Heads
        });
    }

    /// For tests of crashes: the next move of the op heads, as taking records makes it,
    /// stops, failing, once the new op heads are in, before the old ones come out, as a crash
    /// in jj's update of them leaves them.
    pub fn crash_publishing_taken_heads(&mut self) {
        self.records.stop = Some(TakingStop::Publishing);
    }

    /// Fails, once, if a test said to stop taking records `at`.
    pub(super) fn stop_taking(&mut self, at: TakingStop) -> Result<(), NodeError> {
        if self.records.stop != Some(at) {
            return Ok(());
        }
        self.records.stop = None;
        Err(NodeError::Io {
            path: self.records_path(),
            source: std::io::Error::other(format!("stopped for a test: {at:?}")),
        })
    }

    /// Takes the hub's records, after the first ones `prefix` stands for, none of which drops
    /// an op head. Returns the operation the hub accepted that this machine fetches from, as
    /// they name it.
    pub fn adopt_records(
        &mut self,
        prefix: &RecordPrefix,
        records: &[Record],
    ) -> Result<Option<HubOp>, NodeError> {
        self.prepare_records(prefix, records)?;
        self.switch_to_taken(None, None)?;
        let base = self
            .records
            .taking
            .as_ref()
            .expect("prepared above")
            .base
            .clone();
        self.move_taken_workspaces()?;
        Ok(base)
    }
}

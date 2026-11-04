//! Detecting local jj op abandon and reconciling the history it leaves.

use std::collections::HashMap;
use std::collections::HashSet;
use std::fs;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation as StoreOperation;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::ACCEPTED_PUSH;
use super::NodeError;
use super::NodeRepo;
use super::Realign;
use super::dedup;

use crate::canonical::Contraction;
use crate::node::CANONICAL_ATTRIBUTE;
use crate::node::join::fingerprint;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;
use crate::records::HubOp;
use crate::records::Record;

/// The local operations a walk from the op heads met: those a canonical operation stands for,
/// with it, and the rest, read, parents first.
type LocalWalk = (Vec<(LocalOp, CanonicalOp)>, Vec<(LocalOp, StoreOperation)>);

impl NodeRepo {
    /// The local operations reachable from `heads`: those the translation map, a join point
    /// or the history from before the join account for, where the walk stops, and the rest,
    /// parents first.
    pub(super) fn local_walk(&self, heads: &[LocalOp]) -> Result<LocalWalk, NodeError> {
        let op_store = self.loader.op_store();
        let mut mapped = vec![];
        let mut unmapped = vec![];
        let mut seen = HashSet::new();
        // (operation, read, whether its parents were pushed)
        let mut stack: Vec<(LocalOp, Option<StoreOperation>)> =
            heads.iter().map(|h| (h.clone(), None)).collect();
        while let Some((id, read)) = stack.pop() {
            if let Some(op) = read {
                unmapped.push((id, op));
                continue;
            }
            if !seen.insert(id.clone()) || self.before_join.contains(&id) {
                continue;
            }
            if let Some(canonical) = self.canonical_of(&id) {
                // An alias establishes identity, not that a pending physical move finished.
                if !self.records.moving || self.records.source(&id).is_none() {
                    mapped.push((id, canonical));
                    continue;
                }
            }
            let op = op_store.read_operation(&id.0).block_on()?;
            if !op.metadata.attributes.contains_key(CANONICAL_ATTRIBUTE)
                && let Some(join) = self.joins.get(&fingerprint(&op))
            {
                mapped.push((id, join.clone()));
                continue;
            }
            let parents = LocalOp::parents_of(&op);
            stack.push((id, Some(op)));
            stack.extend(parents.into_iter().map(|p| (p, None)));
        }
        Ok((mapped, unmapped))
    }

    /// Whether every one of `bases` is below one of the canonical operations `mapped` has.
    pub(super) fn reaches(
        &self,
        bases: &[CanonicalOp],
        mapped: &[(LocalOp, CanonicalOp)],
    ) -> Result<bool, NodeError> {
        for base in bases {
            let mut found = false;
            for (_, c) in mapped {
                if self.canonical.is_ancestor_of(base, c)? {
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

    /// Maps what [`Self::local_walk`] found as canonicalizing would, where the hive has the
    /// canonical operations already: join points, and each of `unmapped`, parents first, with
    /// its canonical form (`exact_canonical`). Where the translation cache was lost, that is
    /// every local operation but jj's rewrites and those new since the last sync. Notes those
    /// from before the join too. Returns whether it mapped or noted any of `unmapped`.
    pub(super) fn map_exactly(
        &mut self,
        mapped: &[(LocalOp, CanonicalOp)],
        unmapped: &[(LocalOp, StoreOperation)],
    ) -> Result<bool, NodeError> {
        for (local, canonical) in mapped {
            if self.canonical_of(local).is_none() {
                self.insert_map(local.clone(), canonical.clone())?;
            }
        }
        let mut found = false;
        for (id, op) in unmapped {
            match self.exact_canonical(id, op) {
                Ok(Some(canonical)) => {
                    self.insert_map(id.clone(), canonical)?;
                    found = true;
                }
                Ok(None) => found |= self.before_join.contains(id),
                // Canonicalizing refuses it too; matching it otherwise is left to the caller.
                Err(NodeError::Format { .. }) => {}
                Err(err) => return Err(err),
            }
        }
        Ok(found)
    }

    /// The operation the hub accepted that this machine fetches from (the sync adapter's
    /// `accepted_base`), a hub name, if it has one.
    pub(super) fn stored_base(&self) -> Option<HubOp> {
        self.stored_op("accepted_base")
    }

    /// A hub name the sync adapter keeps in `name` in the musubi directory, if it keeps one.
    fn stored_op(&self, name: &str) -> Option<HubOp> {
        let hex = fs::read_to_string(self.repo_path.join("musubi").join(name)).ok()?;
        OperationId::try_from_hex(hex.trim()).map(|op| HubOp(CanonicalOp(op)))
    }

    /// Notices a `jj op abandon` of operations the hub accepted, before anything is
    /// canonicalized on what it rewrote, once for each set of op heads. Returns whether it
    /// noticed one. It must run before the op heads are read for anything else: jj rewrites
    /// every operation above the abandoned ones that isn't below them, putting on their parent
    /// even what was beside them, as a realization merged with them, and musubi puts that
    /// back, so an op head read before is one it no longer reaches.
    pub fn check_abandon(&mut self) -> Result<bool, NodeError> {
        let base = self.stored_base();
        // This machine's push the hub took, which the base may not have moved to yet, as where
        // a sync stopped right after the reply, or lost it: an abandon of it is one of an
        // operation the hub accepted all the same. Both it and the base outlive the hub going
        // back: another machine may have taken them (design.md, "Publishing an abandon").
        let pushed = self
            .stored_op(ACCEPTED_PUSH)
            .filter(|pushed| Some(pushed) != base.as_ref());
        let heads = self.local_heads()?;
        let checked = (heads, base, pushed);
        // A move that taking records left to do, as after an error, is done whether or not
        // the op heads changed since.
        if self.abandon_checked.as_ref() == Some(&checked) && self.records.realign.is_none() {
            return Ok(false);
        }
        let (heads, base, pushed) = checked;
        self.realign_heads(&heads)?;
        // Inspect both accepted histories together. The push may contain a surviving
        // operation above a base that was dropped in full: treating it as new while
        // inspecting only the base loses its original identity and presence.
        let watched: Vec<HubOp> = base.iter().chain(pushed.iter()).cloned().collect();
        let noticed = self.notice_abandons(&watched)?;
        // Only the op heads checked: a `jj op abandon` that moved them meanwhile, remembered as
        // checked, would go unnoticed, and the sync would fail for good. Moved here, they're
        // checked again next time.
        if noticed {
            self.abandon_noticed = true;
        } else {
            self.abandon_checked = Some((heads, base, pushed));
        }
        Ok(noticed)
    }

    /// Whether a local operation that stands for a canonical one, as `counterparts` say, is
    /// on parents that don't stand for that operation's parents.
    fn out_of_place(
        &self,
        counterparts: &HashMap<LocalOp, CanonicalOp>,
        unmapped: &[(LocalOp, StoreOperation)],
    ) -> Result<bool, NodeError> {
        for (id, op) in unmapped {
            let Some(c) = counterparts.get(id) else {
                continue;
            };
            let mut parents = vec![];
            for parent in LocalOp::parents_of(op) {
                if self.before_join.contains(&parent) {
                    continue;
                }
                // As the records name it now, as counterparts are named, and as canonicalizing
                // names a parent (`current_parents`).
                let now = match counterparts.get(&parent) {
                    Some(c) => vec![c.clone()],
                    None => match self.canonical_of(&parent) {
                        Some(c) => self.current_ids(&c)?,
                        None => return Ok(true),
                    },
                };
                for p in now {
                    if !parents.contains(&p) {
                        parents.push(p);
                    }
                }
            }
            if parents != self.canonical.parents(c)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Whether [`Self::check_abandon`] noticed a `jj op abandon` since this last said so, by
    /// whatever ran it: what was staged in the history before is stale.
    pub fn take_abandon_noticed(&mut self) -> bool {
        std::mem::take(&mut self.abandon_noticed)
    }

    /// Moves the op heads and the workspaces where records this node took move them, if a
    /// crash or an error stopped that, exactly as they would have, where the op heads are
    /// still those it moves from or to; and where others are beside some it moves from,
    /// those to what each becomes. Op heads a `jj` command made in place of all of them are
    /// left to [`Self::notice_abandon`] and canonicalizing, as any other, which find what the
    /// operations the move names stood for even where the translation cache lost it since.
    /// Then moves each op head that stands for an operation a renaming superseded to the
    /// local operation of what it became, as a crash between recording the renaming and
    /// moving the op heads leaves them.
    fn realign_heads(&mut self, heads: &[LocalOp]) -> Result<(), NodeError> {
        if let Some(realign) = self.records.realign.clone() {
            if !self.records.realign_mapped {
                for (local, canonical) in &realign.canonical {
                    if self.canonical_of(local).is_none() {
                        self.insert_map(local.clone(), canonical.clone())?;
                    }
                }
                self.records.realign_mapped = true;
            }
            let now: HashSet<&LocalOp> = heads.iter().collect();
            let to: HashSet<&LocalOp> = realign.to.iter().collect();
            let ours = now == realign.from.keys().collect() || now == to;
            // Op heads beside some it moves from, as a crash while moving them leaves them,
            // jj putting each new op head in before taking the old ones out, or a `jj`
            // command made: those it moves from move, each where it was to, and the rest stay.
            let beside = !ours && heads.iter().any(|head| realign.from.contains_key(head));
            if ours && now != to {
                self.publish_heads(heads, &realign.to)?;
            } else if beside {
                self.move_heads(heads, &realign.from, None, None)?;
            }
            let moved = ours || beside;
            if moved {
                self.forget_local_caches();
                self.move_workspaces(&HashMap::new())?;
            }
            // What the operations stood for is kept until none that a renaming superseded is
            // below the op heads, as one a `jj` command wrote on is until it is reparented,
            // canonicalized or not: the translation cache can be lost again before then.
            // Nothing moves from it again.
            let heads = if moved {
                self.local_heads()?
            } else {
                heads.to_vec()
            };
            let renamed = !self.superseded_below(&heads, &realign.canonical)?;
            // Written only where it changes: once, then once more, when it goes.
            let moving = !realign.from.is_empty() || !realign.to.is_empty();
            if renamed || moving {
                self.records.realign = (!renamed).then(|| Realign {
                    from: HashMap::new(),
                    to: vec![],
                    canonical: realign.canonical,
                });
                self.save_records()?;
            }
            if moved {
                return Ok(());
            }
        }
        let mut moved = false;
        for head in heads {
            let Some(canonical) = self.canonical_of(head) else {
                continue;
            };
            if let [now] = self.current_ids(&canonical)?.as_slice()
                && *now != canonical
                && let Some(local) = self.local_of(now)
            {
                self.loader
                    .op_heads_store()
                    .update_op_heads(std::slice::from_ref(&head.0), &local.0)
                    .block_on()?;
                moved = true;
            }
        }
        if moved {
            self.move_workspaces(&HashMap::new())?;
        }
        Ok(())
    }

    /// Notices a `jj op abandon` of operations the hub accepted: `base`, a hub name for an
    /// accepted operation here, is no longer below the op heads. Works out what was dropped,
    /// renames this node's history as contraction does, rewrites its local operations to
    /// match, and records the drops to publish, with the fix-up that goes first. Returns
    /// whether it noticed one.
    pub fn notice_abandon(&mut self, base: &HubOp) -> Result<bool, NodeError> {
        self.notice_abandons(std::slice::from_ref(base))
    }

    fn notice_abandons(&mut self, watched: &[HubOp]) -> Result<bool, NodeError> {
        let root = self.canonical.root_operation_id().clone();
        let mut bases = vec![];
        for base in watched {
            bases.extend(self.to_node_ids(&base.0)?);
        }
        let bases: Vec<CanonicalOp> = dedup(bases).into_iter().filter(|op| *op != root).collect();
        if bases.is_empty() || bases.iter().any(|op| !self.canonical.has_operation(op)) {
            return Ok(false);
        }
        let heads = self.local_heads()?;
        let (mut mapped, mut unmapped) = self.local_walk(&heads)?;
        let mut reached = self.reaches(&bases, &mapped)?;
        // So too where the translation cache was lost: look again once what canonicalizes to
        // an operation the hive has is mapped, as canonicalizing would map it.
        if !reached && self.map_exactly(&mapped, &unmapped)? {
            (mapped, unmapped) = self.local_walk(&heads)?;
            reached = self.reaches(&bases, &mapped)?;
        }
        if reached && !self.records.moving {
            return Ok(false);
        }
        let frontier: Vec<CanonicalOp> = mapped.iter().map(|(_, c)| c.clone()).collect();
        // The history below what is intact stays; what was above it, and below the base, is
        // where the abandoned operations were, and what jj rewrote stands for.
        let mut kept: HashSet<CanonicalOp> = self
            .canonical
            .ancestors_until(&frontier, |_| false)?
            .into_iter()
            .collect();
        kept.insert(root.clone());
        kept.extend(frontier.iter().cloned());
        let region = self
            .canonical
            .ancestors_until(&bases, |op| kept.contains(op))?;
        let ambiguous = |this: &Self| -> Result<NodeError, NodeError> {
            for local in bases.iter().filter_map(|c| this.local_of(c)) {
                match this.loader.op_store().read_operation(&local.0).block_on() {
                    Ok(_) => return Ok(NodeError::AmbiguousAbandon(local.0.hex())),
                    Err(jj_lib::op_store::OpStoreError::ObjectNotFound { .. }) => {}
                    Err(err) => return Err(err.into()),
                }
            }
            Ok(NodeError::UnreachableHistory)
        };
        let mut surviving_fingerprints = HashSet::new();
        for (local, _) in &mapped {
            let op = self.loader.op_store().read_operation(&local.0).block_on()?;
            surviving_fingerprints.insert(fingerprint(&op));
        }
        let mut by_fingerprint: HashMap<String, Option<CanonicalOp>> = HashMap::new();
        for c in &region {
            let original = self.canonical.original_id(c)?;
            let fingerprints = self
                .originals
                .fingerprints(&original)
                .ok_or(NodeError::UnreachableHistory)?;
            for key in fingerprints {
                if surviving_fingerprints.contains(key) {
                    return Err(ambiguous(self)?);
                }
                by_fingerprint
                    .entry(key.clone())
                    .and_modify(|found| *found = None)
                    .or_insert_with(|| Some(c.clone()));
            }
        }
        // What each rewritten local operation stands for: the canonical operation a
        // realization names, or the one its old self, jj's, was.
        let mut counterparts: HashMap<LocalOp, CanonicalOp> = HashMap::new();
        for (id, op) in &unmapped {
            let named = self
                .records
                .source(id)
                .cloned()
                .or_else(|| {
                    op.metadata
                        .attributes
                        .get(CANONICAL_ATTRIBUTE)
                        .and_then(OperationId::try_from_hex)
                        .map(CanonicalOp)
                })
                .filter(|c| self.canonical.has_operation(c));
            let named = match named {
                Some(c) => match self.current_ids(&c)?.as_slice() {
                    [now] => Some(now.clone()),
                    _ => None,
                },
                None => None,
            };
            let fingerprint = by_fingerprint.get(&fingerprint(op));
            if named.is_none() && matches!(fingerprint, Some(None)) {
                return Err(ambiguous(self)?);
            }
            let found = named.or_else(|| fingerprint.cloned().flatten());
            if let Some(c) = found {
                counterparts.insert(id.clone(), c);
            }
        }
        // Dropped: what this machine had below the base, or below what jj rewrote, that no
        // operation it reaches stands for now.
        if self.records.moving {
            // A rewrite recorded before a restart: move the op heads it didn't.
            let mut nothing = Contraction::new(&self.canonical, std::iter::empty())?;
            let locals = self.rewrite_locals(&mut nothing, &heads, &counterparts, &unmapped)?;
            self.add_step(HashMap::new(), &HashSet::new(), &counterparts)?;
            self.finish_local_move(&heads, &locals)?;
            return Ok(true);
        }
        // jj op abandon rewrites what was above what it abandoned. Where nothing was, the
        // base is out of reach for some other reason, which this doesn't explain: dropping
        // everything below it would drop what the hive keeps.
        if unmapped.is_empty() {
            return Ok(false);
        }
        let stands: HashSet<CanonicalOp> = counterparts.values().cloned().collect();
        let mut tops: Vec<CanonicalOp> = bases.clone();
        tops.extend(stands.iter().cloned());
        let dropped: Vec<CanonicalOp> = self
            .canonical
            .ancestors_until(&tops, |op| kept.contains(op))?
            .into_iter()
            .filter(|op| !stands.contains(op))
            .collect();
        // Nothing dropped, though the base is out of reach: whatever jj abandoned came back,
        // as a command in a workspace whose working copy recorded an operation the abandon
        // rewrote brings it back with `snapshot.auto-update-stale`, and a later abandon moved
        // it, so that operations jj rewrote stand for the hive's elsewhere than the hive has
        // them. Put them back where the hive has them, publishing nothing, as jj keeps what
        // came back on one machine.
        if dropped.is_empty() && self.out_of_place(&counterparts, &unmapped)? {
            let mut nothing = Contraction::new(&self.canonical, std::iter::empty())?;
            let locals = self.rewrite_locals(&mut nothing, &heads, &counterparts, &unmapped)?;
            // As below: a restart partway resumes the move, and jj's rewrites keep the
            // identities established here.
            self.add_step(HashMap::new(), &HashSet::new(), &counterparts)?;
            self.records.moving = true;
            self.finish_local_move(&heads, &locals)?;
            return Ok(true);
        }
        if dropped.is_empty() {
            return Ok(false);
        }
        tracing::info!(
            "jj op abandon dropped {} operations the hive has",
            dropped.len()
        );
        let old_head = self.standing_for(&heads, &counterparts, &bases)?;
        let mut contraction = Contraction::new(&self.canonical, dropped.iter().cloned())?
            .sharing(self.presences.clone());
        let new_head = match &old_head {
            Some(old) => contraction.images(&self.canonical, old)?.first().cloned(),
            None => None,
        };
        let locals = self.rewrite_locals(&mut contraction, &heads, &counterparts, &unmapped)?;
        let mut hub_names = HashMap::new();
        for base in watched {
            hub_names.extend(self.hub_names(&base.0)?);
        }
        let pending = self.records.pending.ops().iter().cloned().chain(
            dropped
                .iter()
                .map(|op| HubOp(hub_names.get(op).cloned().unwrap_or_else(|| op.clone()))),
        );
        self.records.pending = Record::new(pending);
        self.forget_to_node();
        // Restoring the state from before the first abandon not yet published, the fix-up
        // covers every such abandon.
        let (from, expected) = match (&self.records.fixup_from, self.records.fixup_written) {
            (Some(from), false) => {
                let expected = self.records.fixup.as_ref().and_then(|f| f.expected.clone());
                let expected = expected.and_then(|mut expected| {
                    let at = LocalOp(OperationId::try_from_hex(&expected.at)?);
                    let now = self.rekeyed(&at, contraction.dropped(), &unmapped, &locals)?;
                    expected.at = now.0.hex();
                    Some(expected)
                });
                if let Some(fixup) = &mut self.records.fixup {
                    fixup.expected.clone_from(&expected);
                }
                (Some(from.clone()), expected)
            }
            _ => {
                let expected = match &old_head {
                    Some(old) => {
                        self.expectation(&heads, old, &counterparts, &unmapped, &locals)?
                    }
                    None => None,
                };
                (old_head, expected)
            }
        };
        if let (Some(old), Some(new)) = (from, new_head) {
            let mut fixup = self.fixup_between(&old, &new)?;
            fixup.expected = expected;
            // A fix-up this one replaces may have been written in part, before a crash: the
            // op head then has its work, so decide as it did.
            if let Some(replaced) = &self.records.fixup
                && !self.records.fixup_written
            {
                for work in &mut fixup.work {
                    work.forgotten = replaced
                        .work
                        .iter()
                        .find(|was| was.copy == work.copy)
                        .and_then(|was| was.forgotten);
                }
            }
            self.records.fixup = Some(fixup);
            self.records.fixup_written = false;
            self.records.fixup_from = Some(old);
        }
        // Recorded before the op heads move, so that a restart in between resumes the move; a
        // renaming appended without them doesn't count.
        let dropped_here = contraction.dropped().clone();
        self.add_step(contraction.into_images(), &dropped_here, &counterparts)?;
        self.records.moving = true;
        self.finish_local_move(&heads, &locals)?;
        Ok(true)
    }

    /// Finishes a recorded local rewrite, or resumes it after a restart. Keep its state on
    /// disk until both the op heads and the workspaces have moved.
    fn finish_local_move(
        &mut self,
        heads: &[LocalOp],
        locals: &HashMap<LocalOp, Vec<LocalOp>>,
    ) -> Result<(), NodeError> {
        self.save_records()?;
        self.move_heads(heads, locals, None, None)?;
        self.move_workspaces(locals)?;
        self.records.moving = false;
        self.save_records()?;
        self.forget_local_caches();
        Ok(())
    }
}

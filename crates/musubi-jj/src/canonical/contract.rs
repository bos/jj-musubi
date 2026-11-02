//! Contracting dropped operations out of a canonical history (docs/internals/design.md,
//! "Contraction"), as `formal/Musubi/Contract.lean` defines it: each surviving operation's
//! parents have every dropped parent replaced, where it stands, by that parent's own parents,
//! themselves so replaced, and then each duplicate after the first removed. A survivor whose
//! parents change is written again with the new ones, its view and metadata as they were, and
//! so gets a new id; the others keep theirs. It is stamped with the presence it had, where the
//! presence worked out from its new parents would differ (`formal/Musubi/PresenceContract.lean`;
//! docs/internals/design.md, "Presence through an abandon"). Every party that drops the same
//! operations from the same history writes the same operations, with the same ids.

use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::sync::Arc;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;

use super::CanonicalError;
use super::CanonicalStore;
use super::origin;
use super::presence::PresenceMemo;
use super::presence::Work;
use super::presence::merge;
use super::presence::stamp_name;
use crate::op_id::CanonicalOp;
use crate::presence::Kind;
use crate::presence::Presence;

/// The contraction of a store's history by a set of dropped operations, worked out as far as
/// it has been asked about. Each call takes the store whose history it is.
#[derive(Clone, Debug, Default)]
pub struct Contraction {
    dropped: HashSet<CanonicalOp>,
    /// The lowest generation of a stored dropped operation: an operation no higher keeps its
    /// id, having no dropped proper ancestor.
    floor: u64,
    /// What each operation met becomes, where that isn't just itself: its rewrite, or, for a
    /// dropped one, what its parents become (`Contract.exp`).
    images: HashMap<CanonicalOp, Vec<CanonicalOp>>,
    /// The operations met that keep their ids.
    same: HashSet<CanonicalOp>,
    /// Each original may occur only once in the input history, even when it came from a
    /// peer. A store can hold many historical versions; one history cannot contain two.
    checked: HashSet<CanonicalOp>,
    /// Presence at the operations met and their rewrites, to stamp the rewrites with.
    presences: Arc<PresenceMemo>,
}

impl Contraction {
    /// The contraction of `store`'s history by `dropped`. The root is never dropped, and a
    /// dropped operation the store lacks changes nothing here.
    pub fn new(
        store: &CanonicalStore,
        dropped: impl IntoIterator<Item = CanonicalOp>,
    ) -> Result<Self, CanonicalError> {
        let root = store.root_operation_id();
        let dropped: HashSet<CanonicalOp> = dropped
            .into_iter()
            .filter(|op| op != root && store.has_operation(op))
            .collect();
        let mut floor = u64::MAX;
        for op in &dropped {
            floor = floor.min(store.generation(op)?);
        }
        Ok(Self {
            dropped,
            floor,
            images: HashMap::new(),
            same: HashSet::new(),
            checked: HashSet::new(),
            presences: Arc::default(),
        })
    }

    /// This contraction, working out presence with `presences`, the store's: presence at an
    /// operation is the same whoever works it out, and one that remembers the history's spares
    /// a walk of all of it.
    pub fn sharing(mut self, presences: Arc<PresenceMemo>) -> Self {
        self.presences = presences;
        self
    }

    /// Whether this contraction drops nothing the store has.
    pub fn is_empty(&self) -> bool {
        self.dropped.is_empty()
    }

    /// Whether `op` is dropped.
    pub fn drops(&self, op: &CanonicalOp) -> bool {
        self.dropped.contains(op)
    }

    /// The dropped operations.
    pub fn dropped(&self) -> &HashSet<CanonicalOp> {
        &self.dropped
    }

    /// Whether `op`, a stored operation, may change: it is dropped, or high enough to have a
    /// dropped proper ancestor.
    pub fn may_change(
        &self,
        store: &CanonicalStore,
        op: &CanonicalOp,
    ) -> Result<bool, CanonicalError> {
        Ok(self.dropped.contains(op) || store.generation(op)? > self.floor)
    }

    /// What `op` becomes: itself or its rewrite if it survives, and what its parents become if
    /// it is dropped. Rewrites are written to `store`, ancestors first.
    pub fn images(
        &mut self,
        store: &CanonicalStore,
        op: &CanonicalOp,
    ) -> Result<Vec<CanonicalOp>, CanonicalError> {
        if !self.is_empty() {
            self.check_origins(store, op)?;
        }
        self.work_out(store, op)?;
        Ok(self.image(op))
    }

    /// Check before writing anything, including the low generations the rewrite skips.
    /// Content hashing authenticates bytes, but does not establish unique originals.
    fn check_origins(
        &mut self,
        store: &CanonicalStore,
        head: &CanonicalOp,
    ) -> Result<(), CanonicalError> {
        if self.checked.contains(head) {
            return Ok(());
        }
        let mut origins: HashMap<OperationId, CanonicalOp> = HashMap::new();
        let mut seen = HashSet::new();
        let mut complete = true;
        let mut stack = vec![head.clone()];
        while let Some(id) = stack.pop() {
            if id == *store.root_operation_id() || !seen.insert(id.clone()) {
                continue;
            }
            // Translation also asks about names not downloaded yet. They remain themselves;
            // do not cache an incomplete closure as validated when their bytes may arrive.
            if !store.has_operation(&id) {
                complete = false;
                continue;
            }
            let op = store.read_operation(&id)?;
            let origin = origin::identity(&op)?;
            if let Some(other) = origins.get(&origin) {
                if *other != id {
                    return Err(CanonicalError::MalformedOperation(id.0.hex()));
                }
            } else {
                origins.insert(origin, id.clone());
            }
            stack.extend(CanonicalOp::parents_of(&op));
        }
        if complete {
            self.checked.extend(seen);
        }
        Ok(())
    }

    /// What the operations worked out so far become, where that isn't just themselves.
    pub fn images_so_far(&self) -> &HashMap<CanonicalOp, Vec<CanonicalOp>> {
        &self.images
    }

    /// What `op` becomes, once worked out.
    fn image(&self, op: &CanonicalOp) -> Vec<CanonicalOp> {
        match self.images.get(op) {
            Some(images) => images.clone(),
            None => {
                debug_assert!(self.same.contains(op), "not worked out");
                vec![op.clone()]
            }
        }
    }

    /// Works out what `op` and everything it needs become, without recursing.
    fn work_out(&mut self, store: &CanonicalStore, op: &CanonicalOp) -> Result<(), CanonicalError> {
        // (operation, whether its parents have been pushed)
        let mut stack = vec![(op.clone(), false)];
        while let Some((id, expanded)) = stack.pop() {
            if self.same.contains(&id) || self.images.contains_key(&id) {
                continue;
            }
            if !expanded {
                if !self.dropped.contains(&id)
                    && (id == *store.root_operation_id()
                        || !store.has_operation(&id)
                        || store.generation(&id)? <= self.floor)
                {
                    self.same.insert(id);
                    continue;
                }
                let parents = store.parents(&id)?;
                stack.push((id, true));
                stack.extend(
                    parents
                        .into_iter()
                        .filter(|p| !self.same.contains(p) && !self.images.contains_key(p))
                        .map(|p| (p, false)),
                );
                continue;
            }
            let parents = store.parents(&id)?;
            let mut contracted: Vec<CanonicalOp> = vec![];
            let mut seen = HashSet::new();
            for parent in &parents {
                for image in self.image(parent) {
                    if seen.insert(image.clone()) {
                        contracted.push(image);
                    }
                }
            }
            if self.dropped.contains(&id) {
                self.images.insert(id, contracted);
            } else if contracted == parents {
                self.same.insert(id);
            } else {
                let mut operation = store.read_operation(&id)?;
                let was = self.presences.presence(store, &id)?;
                operation.parents = contracted.iter().map(|op| op.0.clone()).collect();
                self.stamp(store, &mut operation, &contracted, &was)?;
                let rewritten = CanonicalOp(store.shared.write_original(&operation)?);
                store.note_generation(&rewritten, &contracted);
                self.images.insert(id, vec![rewritten]);
            }
        }
        Ok(())
    }

    /// Stamps `operation`, rewritten onto `parents`, with `was`, the presence it had, where
    /// working it out from its new parents would give another, and only there.
    fn stamp(
        &self,
        store: &CanonicalStore,
        operation: &mut Operation,
        parents: &[CanonicalOp],
        was: &Presence<Work>,
    ) -> Result<(), CanonicalError> {
        operation.metadata.attributes.remove(origin::PRESENCE);
        let mut of_parents = Vec::with_capacity(parents.len());
        for parent in parents {
            of_parents.push((parent.clone(), self.presences.presence(store, parent)?));
        }
        let work = Work {
            original: origin::identity(operation)?,
            op: None,
        };
        let worked_out = merge(store, &of_parents)?.apply(&work, &Kind::of(&operation.metadata));
        if worked_out != *was {
            let stamp = was.to_stamp(stamp_name);
            // Copies are named by keys without whitespace (`Kind::of`), and works by ids, so
            // every presence reads back.
            debug_assert!(
                Presence::from_stamp(&stamp, stamp_name, |hex| Some(Work {
                    original: crate::translation_map::whole_id(hex)?,
                    op: None,
                }))
                .is_some(),
                "unreadable stamp {stamp:?}"
            );
            operation
                .metadata
                .attributes
                .insert(origin::PRESENCE.to_owned(), stamp);
        }
        Ok(())
    }

    /// What every operation worked out so far becomes, where that isn't just itself.
    pub fn into_images(self) -> HashMap<CanonicalOp, Vec<CanonicalOp>> {
        self.images
    }
}

/// What `op` is now, where `superseded` has what each operation a contraction superseded
/// became then: what it became, each superseded since replaced in turn by what that became,
/// the first of each kept. Each contraction renames only what none before it superseded, so
/// each has one entry, and composing them on lookup costs only the entries met, where
/// composing each into every entry before it costs, over many, the square of their number.
pub fn current<Op: Clone + Eq + Hash>(superseded: &HashMap<Op, Vec<Op>>, op: &Op) -> Vec<Op> {
    if !superseded.contains_key(op) {
        return vec![op.clone()];
    }
    // What each one met is now, worked out once: histories merge, and so do renamings.
    let mut now: HashMap<&Op, Vec<Op>> = HashMap::new();
    let mut started = HashSet::new();
    let mut stack = vec![(op, false)];
    while let Some((id, expanded)) = stack.pop() {
        if now.contains_key(id) {
            continue;
        }
        let Some(became) = superseded.get(id) else {
            now.insert(id, vec![id.clone()]);
            continue;
        };
        if expanded {
            let mut seen = HashSet::new();
            let ops = became
                .iter()
                .flat_map(|b| now.get(b).cloned().unwrap_or_default())
                .filter(|op| seen.insert(op.clone()))
                .collect();
            now.insert(id, ops);
            continue;
        }
        // Met again before it is worked out, below itself: a contraction never names as
        // superseded what it or one after it made, so only a corrupt map loops, and the loop
        // is cut where it closes.
        if !started.insert(id) {
            continue;
        }
        stack.push((id, true));
        stack.extend(became.iter().rev().map(|b| (b, false)));
    }
    now.remove(op).unwrap_or_default()
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use hegel::TestCase;
    use hegel::generators as gs;
    use jj_lib::backend::CommitId;
    use jj_lib::op_store::View;

    use super::*;

    /// `Contract.CId`, with byte hashes as immutable content symbols instead of naturals.
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct CId(OperationId, Vec<Self>);

    fn stored_cid(store: &CanonicalStore, id: &CanonicalOp) -> CId {
        CId(
            store.original_id(id).unwrap(),
            store
                .parents(id)
                .unwrap()
                .iter()
                .map(|parent| stored_cid(store, parent))
                .collect(),
        )
    }

    #[test]
    fn contraction_does_not_recreate_a_dropped_id() {
        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), CommitId::from_bytes(&[0; 20])).unwrap();
        let view = store
            .write_view(&View::make_root(CommitId::from_bytes(&[0; 20])))
            .unwrap();
        let mut op = Operation::make_root(view);
        op.parents = vec![store.root_operation_id().0.clone()];
        let a = store.write_operation(&op).unwrap();
        op.parents = vec![a.0.clone()];
        let x = store.write_operation(&op).unwrap();
        assert_ne!(a, x);
        let mut contraction = Contraction::new(&store, [a.clone()]).unwrap();
        let image = contraction.images(&store, &x).unwrap();
        assert_ne!(image, vec![a]);
    }

    #[test]
    fn peer_cannot_put_two_versions_of_one_original_in_a_history() {
        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), CommitId::from_bytes(&[0; 20])).unwrap();
        let ids = history(&store, &[vec![0], vec![1]], &[0, 1]);
        let mut forged = store.read_operation(&ids[1]).unwrap();
        forged.parents = vec![ids[2].0.clone()];
        let id = CanonicalOp(OperationId::new(
            jj_lib::content_hash::blake2b_hash(&forged).to_vec(),
        ));
        store
            .import_operation(&id, &super::super::codec::encode_operation(&forged))
            .unwrap();
        let count = store.operation_ids().unwrap().len();
        let mut contraction = Contraction::new(&store, [ids[2].clone()]).unwrap();
        assert!(contraction.images(&store, &id).is_err());
        assert_eq!(
            store.operation_ids().unwrap().len(),
            count,
            "refuse before rewriting"
        );
    }

    /// An operation received with a stamp that isn't one is refused: presence at it, and at
    /// everything after it, could not be read. One that reads is taken.
    #[test]
    fn a_received_stamp_must_read() {
        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), CommitId::from_bytes(&[0; 20])).unwrap();
        let ids = history(&store, &[vec![0]], &[0]);
        for (stamp, taken) in [
            ("known a b", false),
            ("latest a xyz", false),
            ("known a", true),
        ] {
            let mut op = store.read_operation(&ids[1]).unwrap();
            op.metadata
                .attributes
                .insert(origin::PRESENCE.to_owned(), stamp.to_owned());
            let id = CanonicalOp(OperationId::new(
                jj_lib::content_hash::blake2b_hash(&op).to_vec(),
            ));
            let imported = store.import_operation(&id, &super::super::codec::encode_operation(&op));
            assert_eq!(imported.is_ok(), taken, "{stamp:?}");
        }
    }

    /// A history of `parents.len()` operations on the root, the `i`th with the given parents
    /// among those before it, allowing equal nonparent content. Identical initial operations
    /// are one original, so only those are given distinct descriptions. Content 3 or 4 makes
    /// an operation work by copy `c3` or `c4`, 4 recording its forget-after too; 5 or 6 a
    /// forget of `c3` or `c4`.
    fn history(
        store: &CanonicalStore,
        parents: &[Vec<usize>],
        contents: &[u8],
    ) -> Vec<CanonicalOp> {
        let view = store
            .write_view(&View::make_root(CommitId::from_bytes(&[0; 20])))
            .unwrap();
        let mut ids = vec![store.root_operation_id().clone()];
        for (i, ps) in parents.iter().enumerate() {
            let mut op = Operation::make_root(view.clone());
            op.parents = ps.iter().map(|&p| ids[p].0.clone()).collect();
            op.metadata.description = format!("content {}", contents[i]);
            match contents[i] {
                3 | 4 => {
                    op.metadata.attributes.insert(
                        crate::presence::WORK_ATTRIBUTE.to_owned(),
                        format!("c{}", contents[i]),
                    );
                    if contents[i] == 4 {
                        op.metadata.attributes.insert(
                            crate::presence::FORGET_AFTER_ATTRIBUTE.to_owned(),
                            format!("{}h", i + 1),
                        );
                    }
                }
                5 | 6 => {
                    op.metadata.attributes.insert(
                        crate::presence::FORGET_ATTRIBUTE.to_owned(),
                        format!("c{}", contents[i] - 2),
                    );
                }
                _ => {}
            }
            let mut id = store.write_operation(&op).unwrap();
            if ids.contains(&id) {
                op.metadata.description = format!("distinct op {i}");
                id = store.write_operation(&op).unwrap();
            }
            ids.push(id);
        }
        ids
    }

    /// Dropping one set and then another, named as the first left them, gives the ids that
    /// dropping both at once gives (`Contract.cid_union`, and with stamps,
    /// `PresenceContract.sid_union`), and a survivor's parents are its parents with each
    /// dropped one replaced by its own, recursively, duplicates removed (`Contract.cpar`).
    /// Presence at every survivor is what it was (`PresenceContract.pres_eq`), worked out
    /// afresh.
    #[hegel::test(test_cases = 200)]
    fn dropping_twice_is_dropping_both(tc: TestCase) {
        let count = tc.draw(gs::integers::<usize>().min_value(1).max_value(10));
        let parents: Vec<Vec<usize>> = (1..=count)
            .map(|i| {
                let first = tc.draw(gs::integers::<usize>().max_value(i - 1));
                if tc.draw(gs::booleans()) {
                    let second = tc.draw(gs::integers::<usize>().max_value(i - 1));
                    if second != first {
                        return vec![first, second];
                    }
                }
                vec![first]
            })
            .collect();
        let ops: Vec<usize> = (1..=count).collect();
        let first: HashSet<usize> = ops
            .iter()
            .copied()
            .filter(|_| tc.draw(gs::booleans()))
            .collect();
        let second: HashSet<usize> = ops
            .iter()
            .copied()
            .filter(|_| tc.draw(gs::booleans()))
            .collect();
        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), CommitId::from_bytes(&[0; 20])).unwrap();
        let contents: Vec<u8> = (0..count)
            .map(|_| tc.draw(gs::integers::<u8>().max_value(6)))
            .collect();
        let ids = history(&store, &parents, &contents);
        // Asked about in any order, as a machine's translation is.
        let mut order: Vec<usize> = (1..=count).collect();
        for i in (1..order.len()).rev() {
            order.swap(i, tc.draw(gs::integers::<usize>().max_value(i)));
        }
        let mut shuffled =
            Contraction::new(&store, first.union(&second).map(|&i| ids[i].clone())).unwrap();
        let in_order: HashMap<usize, Vec<CanonicalOp>> = order
            .iter()
            .map(|&i| (i, shuffled.images(&store, &ids[i]).unwrap()))
            .collect();

        let mut once = Contraction::new(&store, first.iter().map(|&i| ids[i].clone())).unwrap();
        let after_first: Vec<Vec<CanonicalOp>> = ids
            .iter()
            .map(|id| once.images(&store, id).unwrap())
            .collect();
        let renamed = second
            .iter()
            .filter(|i| !first.contains(i))
            .map(|&i| after_first[i][0].clone());
        let mut twice = Contraction::new(&store, renamed).unwrap();
        let both_sets = first.union(&second).map(|&i| ids[i].clone());
        let mut both = Contraction::new(&store, both_sets).unwrap();
        // What each original contracts to, by the definition, as indices.
        let mut expected: Vec<Vec<usize>> = vec![vec![0]];
        let mut terms = vec![CId(store.original_id(&ids[0]).unwrap(), vec![])];
        for i in 1..=count {
            let mut contracted = vec![];
            for &p in &parents[i - 1] {
                for &q in &expected[p] {
                    if !contracted.contains(&q) {
                        contracted.push(q);
                    }
                }
            }
            let dropped = first.contains(&i) || second.contains(&i);
            // `cid_eq_mk`: immutable content and the ids of `cpar`'s parents. Unlike the
            // implementation, this builds terms from the generated graph, with no hashes
            // of rewritten operations and no store traversal.
            terms.push(CId(
                store.original_id(&ids[i]).unwrap(),
                contracted.iter().map(|&q| terms[q].clone()).collect(),
            ));
            expected.push(if dropped { contracted.clone() } else { vec![i] });
            let images = both.images(&store, &ids[i]).unwrap();
            assert_eq!(in_order[&i], images, "op {i}, asked out of order");
            if dropped {
                // What a dropped operation's parents became (`Contract.exp`).
                let parents: Vec<CanonicalOp> = contracted
                    .iter()
                    .map(|&q| both.images(&store, &ids[q]).unwrap()[0].clone())
                    .collect();
                assert_eq!(images, parents, "dropped op {i}");
                continue;
            }
            let id = images;
            assert_eq!(id.len(), 1);
            assert_eq!(stored_cid(&store, &id[0]), terms[i]);
            for &old in first.union(&second) {
                assert_ne!(id[0], ids[old], "a dropped id cannot return");
            }
            assert_eq!(
                store.original_id(&id[0]).unwrap(),
                store.original_id(&ids[i]).unwrap()
            );
            let via_first = twice.images(&store, &after_first[i][0]).unwrap();
            assert_eq!(via_first, id, "op {i}");
            let fresh = || PresenceMemo::default();
            assert_eq!(
                fresh().presence(&store, &id[0]).unwrap(),
                fresh().presence(&store, &ids[i]).unwrap(),
                "presence at op {i}"
            );
            let image_parents: Vec<CanonicalOp> = contracted
                .iter()
                .map(|&q| both.images(&store, &ids[q]).unwrap()[0].clone())
                .collect();
            assert_eq!(store.parents(&id[0]).unwrap(), image_parents, "op {i}");
        }
    }
}

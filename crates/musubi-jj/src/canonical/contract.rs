//! Contracting dropped operations out of a canonical history (docs/internals/design.md,
//! "Contraction"), as `formal/Musubi/Contract.lean` defines it: each surviving operation's
//! parents have every dropped parent replaced, where it stands, by that parent's own parents,
//! themselves so replaced, and then each duplicate after the first removed. A survivor whose
//! parents change is written again with the new ones, its view and metadata as they were, and
//! so gets a new id; the others keep theirs. It is stamped with the presence it had, where the
//! presence worked out from its new parents would differ (docs/internals/design.md,
//! "Presence through an abandon"). Every party that drops the same
//! operations from the same history writes the same operations, with the same ids.
//!
//! Only tests use this now. `formal/Musubi/Contract.lean` keeps `cpar`, `exp` and the ancestry
//! of survivors, which `musubi sync --prune` relies on, but no longer the ids, their
//! composition or the presence stamps that the comments below name; they were lemmas of the
//! deleted model of replicated `jj op abandon`.

use std::collections::HashMap;
use std::collections::HashSet;
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
use crate::op_attrs::OpAttrs;
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
        OpAttrs(&mut operation.metadata.attributes).remove_presence();
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
            OpAttrs(&mut operation.metadata.attributes).set_presence(stamp);
        }
        Ok(())
    }

    /// What every operation worked out so far becomes, where that isn't just itself.
    pub fn into_images(self) -> HashMap<CanonicalOp, Vec<CanonicalOp>> {
        self.images
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::collections::BTreeSet;

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
        let ids = history(
            &store,
            &[vec![0], vec![1]],
            &[Content::Plain(0), Content::Plain(1)],
        );
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
        let ids = history(&store, &[vec![0]], &[Content::Plain(0)]);
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

    /// Equal symbols allow operations with equal nonparent content. Work and forgets make
    /// contraction preserve presence too, including a copy's recorded expiry policy.
    #[derive(Clone, Copy, Debug)]
    enum Content {
        Plain(u8),
        WorkByC3,
        LeasedWorkByC4,
        ForgetC3,
        ForgetC4,
    }

    impl Content {
        /// Every variant, plain operations first so a shrunk history has none of the
        /// others.
        fn generator() -> impl hegel::generators::PrintableGenerator<Self> {
            gs::sampled_from(vec![
                Self::Plain(0),
                Self::Plain(1),
                Self::Plain(2),
                Self::WorkByC3,
                Self::LeasedWorkByC4,
                Self::ForgetC3,
                Self::ForgetC4,
            ])
        }

        fn apply(self, op: &mut Operation, index: usize) {
            let symbol = match self {
                Self::Plain(symbol) => symbol,
                Self::WorkByC3 => 3,
                Self::LeasedWorkByC4 => 4,
                Self::ForgetC3 => 5,
                Self::ForgetC4 => 6,
            };
            op.metadata.description = format!("content {symbol}");
            let attributes = &mut op.metadata.attributes;
            match self {
                Self::WorkByC3 | Self::LeasedWorkByC4 => {
                    attributes.insert(
                        crate::presence::WORK_ATTRIBUTE.to_owned(),
                        format!("c{symbol}"),
                    );
                    if matches!(self, Self::LeasedWorkByC4) {
                        attributes.insert(
                            crate::presence::FORGET_AFTER_ATTRIBUTE.to_owned(),
                            format!("{}h", index + 1),
                        );
                    }
                }
                Self::ForgetC3 | Self::ForgetC4 => {
                    attributes.insert(
                        crate::presence::FORGET_ATTRIBUTE.to_owned(),
                        format!("c{}", symbol - 2),
                    );
                }
                Self::Plain(_) => {}
            }
        }
    }

    /// A history on the root, with parents indexed among the root (0) and earlier operations.
    /// Equal initial operations would be one original, so give only those distinct descriptions.
    fn history(
        store: &CanonicalStore,
        parents: &[Vec<usize>],
        contents: &[Content],
    ) -> Vec<CanonicalOp> {
        let view = store
            .write_view(&View::make_root(CommitId::from_bytes(&[0; 20])))
            .unwrap();
        let mut ids = vec![store.root_operation_id().clone()];
        for (i, ps) in parents.iter().enumerate() {
            let mut op = Operation::make_root(view.clone());
            op.parents = ps.iter().map(|&p| ids[p].0.clone()).collect();
            contents[i].apply(&mut op, i);
            let mut id = store.write_operation(&op).unwrap();
            if ids.contains(&id) {
                op.metadata.description = format!("distinct op {i}");
                id = store.write_operation(&op).unwrap();
            }
            ids.push(id);
        }
        ids
    }

    /// The shared input for every contraction law: a small DAG and two possibly overlapping
    /// drop sets. All laws use this one history and store.
    #[derive(Debug)]
    struct ContractionCase {
        parents: Vec<Vec<usize>>,
        first: BTreeSet<usize>,
        second: BTreeSet<usize>,
    }

    /// Drawn as one value, so a failure prints the graph and both drop sets once.
    #[hegel::composite]
    fn contraction_case(tc: &TestCase) -> ContractionCase {
        let count = tc.draw(gs::integers::<usize>().min_value(1).max_value(10));
        let parents = (1..=count)
            .map(|i| {
                // One or two parents, the first kept if both are the same operation.
                let drawn = tc.draw(
                    gs::vecs(gs::integers::<usize>().max_value(i - 1))
                        .min_size(1)
                        .max_size(2),
                );
                if drawn.len() == 2 && drawn[0] == drawn[1] {
                    return vec![drawn[0]];
                }
                drawn
            })
            .collect();
        let ops: Vec<usize> = (1..=count).collect();
        let first = ops
            .iter()
            .copied()
            .filter(|_| tc.draw(gs::booleans()))
            .collect();
        let second = ops
            .iter()
            .copied()
            .filter(|_| tc.draw(gs::booleans()))
            .collect();
        ContractionCase {
            parents,
            first,
            second,
        }
    }

    impl ContractionCase {
        fn drops(&self, op: usize) -> bool {
            self.first.contains(&op) || self.second.contains(&op)
        }
    }

    /// The graph definition, independent of contraction's store traversal and hashes of
    /// rewritten operations: replace dropped parents recursively, retaining the first of
    /// each duplicate (`Contract.cpar`), then build structural terms (`cid_eq_mk`).
    struct ContractedGraph {
        parents: Vec<Vec<usize>>,
        terms: Vec<CId>,
    }

    impl ContractedGraph {
        fn from_graph(case: &ContractionCase, store: &CanonicalStore, ids: &[CanonicalOp]) -> Self {
            let mut images = vec![vec![0]];
            let mut parents = vec![vec![]];
            let mut terms = vec![CId(store.original_id(&ids[0]).unwrap(), vec![])];
            for (i, id) in ids.iter().enumerate().skip(1) {
                let mut expanded = vec![];
                for &p in &case.parents[i - 1] {
                    for &q in &images[p] {
                        if !expanded.contains(&q) {
                            expanded.push(q);
                        }
                    }
                }
                terms.push(CId(
                    store.original_id(id).unwrap(),
                    expanded.iter().map(|&q| terms[q].clone()).collect(),
                ));
                images.push(if case.drops(i) {
                    expanded.clone()
                } else {
                    vec![i]
                });
                parents.push(expanded);
            }
            Self { parents, terms }
        }
    }

    /// Expand every first-stage image through the second contraction, keeping the first
    /// occurrence of each result (`Contract.exp_union`, with `dd` removing duplicates).
    fn compose_images(
        store: &CanonicalStore,
        second: &mut Contraction,
        first: &[CanonicalOp],
    ) -> Vec<CanonicalOp> {
        let mut images = vec![];
        for image in first {
            for next in second.images(store, image).unwrap() {
                if !images.contains(&next) {
                    images.push(next);
                }
            }
        }
        images
    }

    /// A surviving operation has one image, with its original immutable content and the
    /// structurally contracted parents, and never borrows the identity of a dropped operation.
    fn assert_survivor_identity(
        store: &CanonicalStore,
        case: &ContractionCase,
        ids: &[CanonicalOp],
        op: usize,
        images: &[CanonicalOp],
        term: &CId,
    ) {
        assert_eq!(images.len(), 1, "one image for survivor {op}");
        assert_eq!(
            stored_cid(store, &images[0]),
            *term,
            "content of survivor {op}"
        );
        for &old in case.first.union(&case.second) {
            assert_ne!(images[0], ids[old], "a dropped id cannot return");
        }
        assert_eq!(
            store.original_id(&images[0]).unwrap(),
            store.original_id(&ids[op]).unwrap(),
            "original identity of survivor {op}"
        );
    }

    /// Recompute both answers without a memo shared with contraction.
    fn assert_presence_preserved(
        store: &CanonicalStore,
        before: &CanonicalOp,
        after: &CanonicalOp,
    ) {
        assert_eq!(
            PresenceMemo::default().presence(store, after).unwrap(),
            PresenceMemo::default().presence(store, before).unwrap(),
            "presence at {before:?}"
        );
    }

    /// Dropping first and then second gives the same images as dropping their union
    /// (`Contract.exp_union`), including dropped operations; surviving ids agree too
    /// (`Contract.cid_union`, and with stamps). Also check lookup-order independence, parent
    /// expansion (`Contract.cpar` and `Contract.exp`), survivor identities (`cid_eq_mk`), and
    /// presence preservation.
    #[hegel::test(test_cases = 200)]
    fn dropping_twice_is_dropping_both(tc: TestCase) {
        let case = tc.draw(contraction_case());
        let count = case.parents.len();
        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), CommitId::from_bytes(&[0; 20])).unwrap();
        let contents = tc.draw(
            gs::vecs(Content::generator())
                .min_size(count)
                .max_size(count),
        );
        let ids = history(&store, &case.parents, &contents);

        // Query a separate contraction in arbitrary order, as a machine's translation does.
        let order = tc.draw(gs::permutations((1..=count).collect::<Vec<usize>>()));
        let mut shuffled = Contraction::new(
            &store,
            case.first.union(&case.second).map(|&i| ids[i].clone()),
        )
        .unwrap();
        let out_of_order: HashMap<usize, Vec<CanonicalOp>> = order
            .iter()
            .map(|&i| (i, shuffled.images(&store, &ids[i]).unwrap()))
            .collect();

        // Sequential dropping renames the second set through the first contraction.
        let mut once =
            Contraction::new(&store, case.first.iter().map(|&i| ids[i].clone())).unwrap();
        let after_first: Vec<Vec<CanonicalOp>> = ids
            .iter()
            .map(|id| once.images(&store, id).unwrap())
            .collect();
        let renamed = case
            .second
            .iter()
            .filter(|i| !case.first.contains(i))
            .map(|&i| after_first[i][0].clone());
        let mut twice = Contraction::new(&store, renamed).unwrap();
        let both_sets = case.first.union(&case.second).map(|&i| ids[i].clone());
        let mut both = Contraction::new(&store, both_sets).unwrap();
        let expected = ContractedGraph::from_graph(&case, &store, &ids);

        for (i, first) in after_first.iter().enumerate() {
            assert_eq!(
                compose_images(&store, &mut twice, first),
                both.images(&store, &ids[i]).unwrap(),
                "sequential dropping at op {i}"
            );
        }

        for i in 1..=count {
            let images = both.images(&store, &ids[i]).unwrap();
            assert_eq!(out_of_order[&i], images, "lookup order at op {i}");
            if case.drops(i) {
                let parents: Vec<CanonicalOp> = expected.parents[i]
                    .iter()
                    .map(|&q| both.images(&store, &ids[q]).unwrap()[0].clone())
                    .collect();
                assert_eq!(images, parents, "expansion of dropped op {i}");
                continue;
            }
            assert_survivor_identity(&store, &case, &ids, i, &images, &expected.terms[i]);
            // The composed law deduplicates expansions; raw survivor images must be unique too.
            let via_first = twice.images(&store, &after_first[i][0]).unwrap();
            assert_eq!(via_first, images, "raw sequential images of survivor {i}");
            assert_presence_preserved(&store, &ids[i], &images[0]);
            let parents: Vec<CanonicalOp> = expected.parents[i]
                .iter()
                .map(|&q| both.images(&store, &ids[q]).unwrap()[0].clone())
                .collect();
            assert_eq!(
                store.parents(&images[0]).unwrap(),
                parents,
                "parents of survivor {i}"
            );
        }
    }
}

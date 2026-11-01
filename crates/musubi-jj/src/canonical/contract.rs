//! Contracting dropped operations out of a canonical history (docs/internals/design.md,
//! "Contraction"), as `formal/Musubi/Contract.lean` defines it: each surviving operation's
//! parents have every dropped parent replaced, where it stands, by that parent's own parents,
//! themselves so replaced, and then each duplicate after the first removed. A survivor whose
//! parents change is written again with the new ones, its view and metadata as they were, and
//! so gets a new id; the others keep theirs. Every party that drops the same operations from
//! the same history writes the same operations, with the same ids.

use std::collections::HashMap;
use std::collections::HashSet;

use jj_lib::op_store::OperationId;

use super::CanonicalError;
use super::CanonicalStore;

/// The contraction of a store's history by a set of dropped operations, worked out as far as
/// it has been asked about. Each call takes the store whose history it is.
#[derive(Clone, Debug, Default)]
pub struct Contraction {
    dropped: HashSet<OperationId>,
    /// The lowest generation of a stored dropped operation: an operation no higher keeps its
    /// id, having no dropped proper ancestor.
    floor: u64,
    /// What each operation met becomes, where that isn't just itself: its rewrite, or, for a
    /// dropped one, what its parents become (`Contract.exp`).
    images: HashMap<OperationId, Vec<OperationId>>,
    /// The operations met that keep their ids.
    same: HashSet<OperationId>,
}

impl Contraction {
    /// The contraction of `store`'s history by `dropped`. The root is never dropped, and a
    /// dropped operation the store lacks changes nothing here.
    pub fn new(
        store: &CanonicalStore,
        dropped: impl IntoIterator<Item = OperationId>,
    ) -> Result<Self, CanonicalError> {
        let root = store.root_operation_id();
        let dropped: HashSet<OperationId> = dropped
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
        })
    }

    /// Whether this contraction drops nothing the store has.
    pub fn is_empty(&self) -> bool {
        self.dropped.is_empty()
    }

    /// Whether `op` is dropped.
    pub fn drops(&self, op: &OperationId) -> bool {
        self.dropped.contains(op)
    }

    /// The dropped operations.
    pub fn dropped(&self) -> &HashSet<OperationId> {
        &self.dropped
    }

    /// Whether `op`, a stored operation, may change: it is dropped, or high enough to have a
    /// dropped proper ancestor.
    pub fn may_change(
        &self,
        store: &CanonicalStore,
        op: &OperationId,
    ) -> Result<bool, CanonicalError> {
        Ok(self.dropped.contains(op) || store.generation(op)? > self.floor)
    }

    /// What `op` becomes: itself or its rewrite if it survives, and what its parents become if
    /// it is dropped. Rewrites are written to `store`, ancestors first.
    pub fn images(
        &mut self,
        store: &CanonicalStore,
        op: &OperationId,
    ) -> Result<Vec<OperationId>, CanonicalError> {
        self.work_out(store, op)?;
        Ok(self.image(op))
    }

    /// What the operations worked out so far become, where that isn't just themselves.
    pub fn images_so_far(&self) -> &HashMap<OperationId, Vec<OperationId>> {
        &self.images
    }

    /// What `op` becomes, once worked out.
    fn image(&self, op: &OperationId) -> Vec<OperationId> {
        match self.images.get(op) {
            Some(images) => images.clone(),
            None => {
                debug_assert!(self.same.contains(op), "not worked out");
                vec![op.clone()]
            }
        }
    }

    /// Works out what `op` and everything it needs become, without recursing.
    fn work_out(&mut self, store: &CanonicalStore, op: &OperationId) -> Result<(), CanonicalError> {
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
            let mut contracted: Vec<OperationId> = vec![];
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
                operation.parents = contracted;
                let rewritten = store.write_operation(&operation)?;
                store.note_generation(&rewritten, &operation.parents);
                self.images.insert(id, vec![rewritten]);
            }
        }
        Ok(())
    }

    /// What every operation worked out so far becomes, where that isn't just itself.
    pub fn into_images(self) -> HashMap<OperationId, Vec<OperationId>> {
        self.images
    }
}

/// What `op` is now, where `superseded` has what each operation a contraction superseded
/// became then: what it became, each superseded since replaced in turn by what that became,
/// the first of each kept. Each contraction renames only what none before it superseded, so
/// each has one entry, and composing them on lookup costs only the entries met, where
/// composing each into every entry before it costs, over many, the square of their number.
pub fn current(
    superseded: &HashMap<OperationId, Vec<OperationId>>,
    op: &OperationId,
) -> Vec<OperationId> {
    if !superseded.contains_key(op) {
        return vec![op.clone()];
    }
    // What each one met is now, worked out once: histories merge, and so do renamings.
    let mut now: HashMap<&OperationId, Vec<OperationId>> = HashMap::new();
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
    use jj_lib::op_store::Operation;
    use jj_lib::op_store::View;

    use super::*;

    /// A history of `parents.len()` operations on the root, the `i`th with the given parents
    /// among those before it (`None` for the root), each told apart by its description.
    fn history(store: &CanonicalStore, parents: &[Vec<usize>]) -> Vec<OperationId> {
        let view = store
            .write_view(&View::make_root(CommitId::from_bytes(&[0; 20])))
            .unwrap();
        let mut ids = vec![store.root_operation_id().clone()];
        for (i, ps) in parents.iter().enumerate() {
            let mut op = Operation::make_root(view.clone());
            op.parents = ps.iter().map(|&p| ids[p].clone()).collect();
            op.metadata.description = format!("op {i}");
            ids.push(store.write_operation(&op).unwrap());
        }
        ids
    }

    /// Dropping one set and then another, named as the first left them, gives the ids that
    /// dropping both at once gives (`Contract.cid_union`), and a survivor's parents are its
    /// parents with each dropped one replaced by its own, recursively, duplicates removed
    /// (`Contract.cpar`).
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
        let ids = history(&store, &parents);
        // Asked about in any order, as a machine's translation is.
        let mut order: Vec<usize> = (1..=count).collect();
        for i in (1..order.len()).rev() {
            order.swap(i, tc.draw(gs::integers::<usize>().max_value(i)));
        }
        let mut shuffled =
            Contraction::new(&store, first.union(&second).map(|&i| ids[i].clone())).unwrap();
        let in_order: HashMap<usize, Vec<OperationId>> = order
            .iter()
            .map(|&i| (i, shuffled.images(&store, &ids[i]).unwrap()))
            .collect();

        let mut once = Contraction::new(&store, first.iter().map(|&i| ids[i].clone())).unwrap();
        let after_first: Vec<Vec<OperationId>> = ids
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
            expected.push(if dropped { contracted.clone() } else { vec![i] });
            let images = both.images(&store, &ids[i]).unwrap();
            assert_eq!(in_order[&i], images, "op {i}, asked out of order");
            if dropped {
                // What a dropped operation's parents became (`Contract.exp`).
                let parents: Vec<OperationId> = contracted
                    .iter()
                    .map(|&q| both.images(&store, &ids[q]).unwrap()[0].clone())
                    .collect();
                assert_eq!(images, parents, "dropped op {i}");
                continue;
            }
            let id = images;
            assert_eq!(id.len(), 1);
            let via_first = twice.images(&store, &after_first[i][0]).unwrap();
            assert_eq!(via_first, id, "op {i}");
            let image_parents: Vec<OperationId> = contracted
                .iter()
                .map(|&q| both.images(&store, &ids[q]).unwrap()[0].clone())
                .collect();
            assert_eq!(store.parents(&id[0]).unwrap(), image_parents, "op {i}");
        }
    }
}

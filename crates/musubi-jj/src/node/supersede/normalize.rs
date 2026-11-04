//! Naming operations after dropped originals, with cached ancestry and contractions.

use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use jj_lib::op_store::OperationId;

use super::NodeError;

use crate::canonical;
use crate::canonical::CanonicalStore;
use crate::canonical::Contraction;
use crate::op_id::CanonicalOp;

/// What a canonical operation is made of that naming it needs: its parents and its original.
/// Immutable, so kept whatever this node drops.
#[derive(Clone)]
pub(super) struct Fact {
    pub(super) parents: Vec<CanonicalOp>,
    pub(super) original: OperationId,
}

/// The facts read so far, and the normalizer for what this node drops now, until that changes.
#[derive(Default)]
pub(super) struct Normal {
    pub(super) facts: HashMap<CanonicalOp, Fact>,
    pub(super) normalizer: Option<Normalizer>,
}

/// Where a raw operation stands, given the originals a history drops.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Class {
    /// Neither it nor anything below it is a version of one.
    Same,
    /// A version of one.
    Drop,
    /// Something below it is.
    Changed,
}

/// Names raw operations as a history that drops `dropped`, originals, does: any operation
/// that is, or is above, another version of one of them, as another history names it,
/// becomes its contraction by every version of them below it. A contraction keeps the
/// original. On shared history with the received records retained, dropping the same
/// originals gives the hub's names; this does not reconstruct unowned missing ancestry.
/// A version of a dropped original becomes what its parents do.
pub(super) struct Normalizer {
    dropped: HashSet<OperationId>,
    class: HashMap<CanonicalOp, Class>,
    /// Every operation classed as a version of one so far.
    drops: Vec<CanonicalOp>,
    /// The contraction by `drops`, made again when they grow: one that drops nothing below
    /// an operation names it as one that doesn't drop that at all.
    contraction: Option<Contraction>,
    /// What those made before it worked out, and whether each is dropped: still what this
    /// one works out, as every closure they worked out was whole when classed, and nothing
    /// found since is below it.
    worked: HashMap<CanonicalOp, (Vec<CanonicalOp>, bool)>,
}

pub(super) fn fact(
    store: &CanonicalStore,
    facts: &mut HashMap<CanonicalOp, Fact>,
    op: &CanonicalOp,
) -> Result<Fact, NodeError> {
    if let Some(fact) = facts.get(op) {
        return Ok(fact.clone());
    }
    let (operation, original) = store.read_operation_and_original(op)?;
    let fact = Fact {
        parents: CanonicalOp::parents_of(&operation),
        original,
    };
    facts.insert(op.clone(), fact.clone());
    Ok(fact)
}

impl Normalizer {
    pub(super) fn new(dropped: HashSet<OperationId>) -> Self {
        Self {
            dropped,
            class: HashMap::new(),
            drops: vec![],
            contraction: None,
            worked: HashMap::new(),
        }
    }

    /// What `op` is named as. Itself if nothing below it is a version of a dropped original,
    /// or if the store lacks something below it: then nothing is worked out, nor kept, so
    /// that what arrives later is looked at.
    pub(super) fn names(
        &mut self,
        store: &CanonicalStore,
        presences: &Arc<canonical::PresenceMemo>,
        facts: &mut HashMap<CanonicalOp, Fact>,
        op: &CanonicalOp,
    ) -> Result<Vec<CanonicalOp>, NodeError> {
        Ok(self
            .complete_names(store, presences, facts, op)?
            .unwrap_or_else(|| vec![op.clone()]))
    }

    /// [`Self::names`], or none if the store lacks something below `op`.
    pub(super) fn complete_names(
        &mut self,
        store: &CanonicalStore,
        presences: &Arc<canonical::PresenceMemo>,
        facts: &mut HashMap<CanonicalOp, Fact>,
        op: &CanonicalOp,
    ) -> Result<Option<Vec<CanonicalOp>>, NodeError> {
        if self.dropped.is_empty() {
            return Ok(Some(vec![op.clone()]));
        }
        match self.classify(store, facts, op)? {
            None => Ok(None),
            Some(Class::Same) => Ok(Some(vec![op.clone()])),
            Some(Class::Drop | Class::Changed) => {
                if let Some((images, _)) = self.worked.get(op) {
                    return Ok(Some(images.clone()));
                }
                if self.contraction.is_none() {
                    self.contraction = Some(
                        Contraction::new(store, self.drops.iter().cloned())?
                            .sharing(presences.clone()),
                    );
                }
                let contraction = self.contraction.as_mut().expect("made above");
                // Checks the whole history below it before writing any rewrite.
                Ok(Some(contraction.images(store, op)?))
            }
        }
    }

    /// What each operation worked out so far became, where that isn't just itself, and
    /// whether it is dropped.
    pub(super) fn worked_out(
        &self,
    ) -> impl Iterator<Item = (&CanonicalOp, &Vec<CanonicalOp>, bool)> {
        self.worked
            .iter()
            .map(|(op, (images, dropped))| (op, images, *dropped))
            .chain(self.contraction.iter().flat_map(|contraction| {
                contraction
                    .images_so_far()
                    .iter()
                    .map(|(op, images)| (op, images, contraction.drops(op)))
            }))
    }

    /// Keeps what the contraction worked out, which a contraction by more drops is about to
    /// replace.
    fn retire(&mut self) {
        let Some(contraction) = self.contraction.take() else {
            return;
        };
        for (op, images) in contraction.into_images() {
            let dropped = self.class.get(&op) == Some(&Class::Drop);
            self.worked.insert(op, (images, dropped));
        }
    }

    /// The class of `op`, or none if the store lacks something below it. Looks only at what
    /// it hasn't classed yet.
    fn classify(
        &mut self,
        store: &CanonicalStore,
        facts: &mut HashMap<CanonicalOp, Fact>,
        op: &CanonicalOp,
    ) -> Result<Option<Class>, NodeError> {
        let root = store.root_operation_id();
        let mut incomplete: HashSet<CanonicalOp> = HashSet::new();
        // (operation, whether its parents have been pushed)
        let mut stack = vec![(op.clone(), false)];
        while let Some((id, expanded)) = stack.pop() {
            if self.class.contains_key(&id) || incomplete.contains(&id) {
                continue;
            }
            if id == *root {
                self.class.insert(id, Class::Same);
                continue;
            }
            if !store.has_operation(&id) {
                incomplete.insert(id);
                continue;
            }
            let fact = fact(store, facts, &id)?;
            if !expanded {
                stack.push((id, true));
                stack.extend(
                    fact.parents
                        .into_iter()
                        .filter(|p| !self.class.contains_key(p) && !incomplete.contains(p))
                        .map(|p| (p, false)),
                );
                continue;
            }
            if fact.parents.iter().any(|p| incomplete.contains(p)) {
                incomplete.insert(id);
                continue;
            }
            let class = if self.dropped.contains(&fact.original) {
                self.drops.push(id.clone());
                self.retire();
                Class::Drop
            } else if fact
                .parents
                .iter()
                .any(|p| self.class.get(p) != Some(&Class::Same))
            {
                Class::Changed
            } else {
                Class::Same
            };
            self.class.insert(id, class);
        }
        Ok(self.class.get(op).copied())
    }
}

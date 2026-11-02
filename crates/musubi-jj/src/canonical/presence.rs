//! Which copies are present at canonical operations (see `crate::presence`), worked out from
//! a canonical store, for a node and for a hub alike. Presence names work by its original
//! identity, which a contraction keeps, and at an operation a contraction stamped it is the
//! stamp (docs/internals/design.md, "Presence through an abandon").

use std::cmp::Ordering;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;

use super::CanonicalError;
use super::CanonicalStore;
use super::origin;
use crate::op_id::CanonicalOp;
use crate::presence::Kind;
use crate::presence::Presence;
use crate::translation_map::whole_id;

/// Work as presence names it: by its original identity (`CanonicalStore::original_id`), with
/// the operation that stands for it in the history at hand, none if an abandon dropped it.
/// Equal, and ordered, by the original alone.
#[derive(Clone, Debug)]
pub struct Work {
    pub original: OperationId,
    pub op: Option<CanonicalOp>,
}

impl PartialEq for Work {
    fn eq(&self, other: &Self) -> bool {
        self.original == other.original
    }
}

impl Eq for Work {}

impl PartialOrd for Work {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Work {
    fn cmp(&self, other: &Self) -> Ordering {
        self.original.cmp(&other.original)
    }
}

impl Work {
    /// Whether this work is in the history below `other`, as presence asks it ([`merge`]): work
    /// an abandon dropped counts as below every operation.
    pub fn below(&self, store: &CanonicalStore, other: &Self) -> Result<bool, CanonicalError> {
        work_below(store, self, other)
    }

    /// Operation `op`, for asking what is below it, and nothing else.
    fn at(op: &CanonicalOp) -> Self {
        Self {
            original: OperationId::new(vec![]),
            op: Some(op.clone()),
        }
    }

    /// No operation's work: what [`Presence::apply`] is given for an operation that isn't
    /// work, which it doesn't look at.
    fn unnamed() -> Self {
        Self {
            original: OperationId::new(vec![]),
            op: None,
        }
    }

    /// Canonical operation `op` of `store`, as presence names it.
    pub fn of(store: &CanonicalStore, op: &CanonicalOp) -> Result<Self, CanonicalError> {
        Ok(Self {
            original: store.original_id(op)?,
            op: Some(op.clone()),
        })
    }
}

/// How many operations' presence to remember: those computed last, which the next
/// operations' parents mostly are.
const REMEMBERED: usize = 256;

/// Presence at canonical operations, remembering it for those computed last.
#[derive(Debug, Default)]
pub struct PresenceMemo {
    remembered: Mutex<Remembered>,
}

#[derive(Debug, Default)]
struct Remembered {
    presences: HashMap<CanonicalOp, Arc<Presence<Work>>>,
    order: VecDeque<CanonicalOp>,
}

impl Remembered {
    fn get(&self, op: &CanonicalOp) -> Option<Arc<Presence<Work>>> {
        self.presences.get(op).cloned()
    }

    fn insert(&mut self, op: CanonicalOp, presence: Arc<Presence<Work>>) {
        if self.presences.insert(op.clone(), presence).is_none() {
            self.order.push_back(op);
        }
        while self.order.len() > REMEMBERED {
            if let Some(old) = self.order.pop_front() {
                self.presences.remove(&old);
            }
        }
    }
}

impl PresenceMemo {
    fn lock(&self) -> MutexGuard<'_, Remembered> {
        self.remembered
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
    }

    /// The copies present at `op`, an operation of `store`. Unless an ancestor's presence is
    /// remembered, this reads the history below `op`, once.
    pub fn presence(
        &self,
        store: &CanonicalStore,
        op: &CanonicalOp,
    ) -> Result<Arc<Presence<Work>>, CanonicalError> {
        let root = store.root_operation_id();
        if op == root {
            return Ok(Arc::default());
        }
        if let Some(presence) = self.lock().get(op) {
            return Ok(presence);
        }
        // The operations whose presence isn't known, ancestors first, each read once, then each
        // one's from its parents', keeping each only until the last of its children in the
        // walk needs it.
        let mut ops: Vec<(CanonicalOp, Walked)> = vec![];
        let mut seen: HashSet<CanonicalOp> = HashSet::new();
        let mut stack: Vec<(CanonicalOp, Option<Operation>)> = vec![(op.clone(), None)];
        while let Some((id, stored)) = stack.pop() {
            match stored {
                Some(stored) => ops.push((id, Walked::of(stored))),
                None => {
                    if !seen.insert(id.clone()) || id == *root || self.lock().get(&id).is_some() {
                        continue;
                    }
                    let stored = store.read_operation(&id)?;
                    let parents: Vec<CanonicalOp> = CanonicalOp::parents_of(&stored)
                        .into_iter()
                        .filter(|parent| !seen.contains(parent))
                        .collect();
                    stack.push((id, Some(stored)));
                    stack.extend(parents.into_iter().map(|parent| (parent, None)));
                }
            }
        }
        // Another thread worked it out meanwhile.
        if ops.last().map(|(id, _)| id) != Some(op) {
            let remembered = self.lock().get(op);
            return remembered.map_or_else(|| self.presence(store, op), Ok);
        }
        let mut children: HashMap<CanonicalOp, usize> = HashMap::new();
        for (_, walked) in &ops {
            for parent in &walked.parents {
                *children.entry(parent.clone()).or_default() += 1;
            }
        }
        let mut done: HashMap<CanonicalOp, Arc<Presence<Work>>> = HashMap::new();
        let mut presence = Arc::default();
        for (id, walked) in ops {
            let parents = &walked.parents;
            store.note_generation(&id, parents);
            let mut of_parents = Vec::with_capacity(parents.len());
            for parent in parents {
                let known = match done.get(parent) {
                    Some(known) => known.clone(),
                    None if parent == root => Arc::default(),
                    None => {
                        // Not under the lock: working it out takes it.
                        let remembered = self.lock().get(parent);
                        match remembered {
                            Some(known) => known,
                            None => self.presence(store, parent)?,
                        }
                    }
                };
                of_parents.push((parent.clone(), known));
            }
            presence = at(store, &id, &walked, &of_parents)?;
            for parent in parents {
                if let Some(left) = children.get_mut(parent) {
                    *left -= 1;
                    if *left == 0 {
                        done.remove(parent);
                    }
                }
            }
            if children.get(&id).is_some_and(|&left| left > 0) {
                done.insert(id, presence.clone());
            }
        }
        self.lock().insert(op.clone(), presence.clone());
        Ok(presence)
    }

    /// Remembers the presence at `op`, just written.
    pub fn remember(&self, op: CanonicalOp, presence: Presence<Work>) {
        self.lock().insert(op, Arc::new(presence));
    }
}

/// What a walk keeps of an operation until it works out presence there: the whole operation
/// only where its identity is needed, as for work or a stamp.
struct Walked {
    parents: Vec<CanonicalOp>,
    kind: Kind,
    op: Option<Operation>,
}

impl Walked {
    fn of(op: Operation) -> Self {
        let kind = Kind::of(&op.metadata);
        let keep = kind.work.is_some() || op.metadata.attributes.contains_key(origin::PRESENCE);
        Self {
            parents: CanonicalOp::parents_of(&op),
            kind,
            op: keep.then_some(op),
        }
    }
}

/// Presence at `id`, `walked`, an operation of `store`, from its parents': its stamp, or its
/// own effect on what its parents' give.
fn at(
    store: &CanonicalStore,
    id: &CanonicalOp,
    walked: &Walked,
    parents: &[(CanonicalOp, Arc<Presence<Work>>)],
) -> Result<Arc<Presence<Work>>, CanonicalError> {
    let kind = &walked.kind;
    let Some(op) = &walked.op else {
        if let ([(_, only)], true) = (parents, kind.forgets.is_empty()) {
            return Ok(only.clone());
        }
        // Neither work nor stamped: a forget or a merge, which names no work.
        return Ok(Arc::new(
            merge(store, parents)?.apply(&Work::unnamed(), kind),
        ));
    };
    let merged = merge(store, parents)?;
    let original = origin::identity(op)?;
    if let Some(stamp) = op.metadata.attributes.get(origin::PRESENCE) {
        return Ok(Arc::new(read_stamp(id, &original, stamp, &merged)?));
    }
    let work = Work {
        original,
        op: Some(id.clone()),
    };
    Ok(Arc::new(merged.apply(&work, kind)))
}

/// The presence `id`, with original `original`, is stamped with: each work it names as the
/// operation that stands for it here, if any. That is `id` itself, or one its parents' merged
/// presence, `merged`, names: work at an operation that survives a contraction is maximal
/// below it, and so below a parent that has it.
fn read_stamp(
    id: &CanonicalOp,
    original: &OperationId,
    stamp: &str,
    merged: &Presence<Work>,
) -> Result<Presence<Work>, CanonicalError> {
    let mut standing: HashMap<&OperationId, &CanonicalOp> = HashMap::new();
    for work in merged.ops() {
        if let Some(op) = &work.op {
            standing.insert(&work.original, op);
        }
    }
    let parse = |hex: &str| {
        let work_original = whole_id(hex)?;
        let op = if work_original == *original {
            Some(id.clone())
        } else {
            standing.get(&work_original).map(|op| (*op).clone())
        };
        Some(Work {
            original: work_original,
            op,
        })
    };
    Presence::from_stamp(stamp, stamp_name, parse)
        .ok_or_else(|| CanonicalError::MalformedOperation(id.0.hex()))
}

/// Refuses `op`, received from a peer, if it has a stamp that isn't one: presence at it and
/// everything after would be unreadable.
pub(super) fn check_stamp(op: &Operation) -> Result<(), ()> {
    let Some(stamp) = op.metadata.attributes.get(origin::PRESENCE) else {
        return Ok(());
    };
    let parse = |hex: &str| {
        Some(Work {
            original: whole_id(hex)?,
            op: None,
        })
    };
    Presence::from_stamp(stamp, stamp_name, parse)
        .map(|_| ())
        .ok_or(())
}

/// How a stamp names work: by its original identity.
pub(super) fn stamp_name(work: &Work) -> String {
    work.original.hex()
}

/// Presence before an operation's own effect, from its parents', operations of `store`.
pub fn merge(
    store: &CanonicalStore,
    parents: &[(CanonicalOp, Arc<Presence<Work>>)],
) -> Result<Presence<Work>, CanonicalError> {
    if let [(_, only)] = parents {
        return Ok((**only).clone());
    }
    // A parent stands only for where it is: `Presence::merge` asks only what is below it.
    let works: Vec<(Work, &Presence<Work>)> = parents
        .iter()
        .map(|(op, presence)| (Work::at(op), presence.as_ref()))
        .collect();
    Presence::merge(&works, |a, b| work_below(store, a, b))
}

/// Whether work `a` is in the history below `b`, an operation of `store`, as presence asks
/// it: work an abandon dropped counts as below every operation, so a merge keeps it only
/// where every parent does (`formal/Musubi/PresenceContract.lean`, `seen`).
fn work_below(store: &CanonicalStore, a: &Work, b: &Work) -> Result<bool, CanonicalError> {
    match (&a.op, &b.op) {
        (Some(a), Some(b)) => store.is_ancestor_of(a, b),
        (None, Some(_)) => Ok(true),
        // Between two works dropped, or below one, nothing says which came first: neither.
        (_, None) => Ok(false),
    }
}

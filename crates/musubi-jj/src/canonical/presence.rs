//! Which copies are present at canonical operations (see `crate::presence`), worked out from
//! a canonical store, for a node and for a hub alike.

use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::MutexGuard;
use std::sync::PoisonError;

use super::CanonicalError;
use super::CanonicalStore;
use crate::op_id::CanonicalOp;
use crate::presence::Kind;
use crate::presence::Presence;

/// How many operations' presence to remember: those computed last, which the next
/// operations' parents mostly are.
const REMEMBERED: usize = 256;

/// Presence at canonical operations, remembering it for those computed last.
#[derive(Default)]
pub struct PresenceMemo {
    remembered: Mutex<Remembered>,
}

#[derive(Default)]
struct Remembered {
    presences: HashMap<CanonicalOp, Arc<Presence<CanonicalOp>>>,
    order: VecDeque<CanonicalOp>,
}

impl Remembered {
    fn get(&self, op: &CanonicalOp) -> Option<Arc<Presence<CanonicalOp>>> {
        self.presences.get(op).cloned()
    }

    fn insert(&mut self, op: CanonicalOp, presence: Arc<Presence<CanonicalOp>>) {
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
    ) -> Result<Arc<Presence<CanonicalOp>>, CanonicalError> {
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
        let mut ops: Vec<(CanonicalOp, Vec<CanonicalOp>, Kind)> = vec![];
        let mut seen: HashSet<CanonicalOp> = HashSet::new();
        let mut stack: Vec<(CanonicalOp, Option<jj_lib::op_store::Operation>)> =
            vec![(op.clone(), None)];
        while let Some((id, stored)) = stack.pop() {
            match stored {
                Some(stored) => ops.push((
                    id,
                    CanonicalOp::parents_of(&stored),
                    Kind::of(&stored.metadata),
                )),
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
        if ops.last().map(|(id, _, _)| id) != Some(op) {
            let remembered = self.lock().get(op);
            return remembered.map_or_else(|| self.presence(store, op), Ok);
        }
        let mut children: HashMap<CanonicalOp, usize> = HashMap::new();
        for (_, parents, _) in &ops {
            for parent in parents {
                *children.entry(parent.clone()).or_default() += 1;
            }
        }
        let mut walked: HashMap<CanonicalOp, Arc<Presence<CanonicalOp>>> = HashMap::new();
        let mut presence = Arc::default();
        for (id, parents, kind) in ops {
            store.note_generation(&id, &parents);
            let mut of_parents = Vec::with_capacity(parents.len());
            for parent in &parents {
                let known = match walked.get(parent) {
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
            presence = if let ([(_, only)], None, true) =
                (of_parents.as_slice(), &kind.work, kind.forgets.is_empty())
            {
                only.clone()
            } else {
                Arc::new(merge(store, &of_parents)?.apply(&id, &kind))
            };
            for parent in &parents {
                if let Some(left) = children.get_mut(parent) {
                    *left -= 1;
                    if *left == 0 {
                        walked.remove(parent);
                    }
                }
            }
            if children.get(&id).is_some_and(|&left| left > 0) {
                walked.insert(id, presence.clone());
            }
        }
        self.lock().insert(op.clone(), presence.clone());
        Ok(presence)
    }

    /// Remembers the presence at `op`, just written.
    pub fn remember(&self, op: CanonicalOp, presence: Presence<CanonicalOp>) {
        self.lock().insert(op, Arc::new(presence));
    }
}

/// Presence before an operation's own effect, from its parents', operations of `store`.
pub fn merge(
    store: &CanonicalStore,
    parents: &[(CanonicalOp, Arc<Presence<CanonicalOp>>)],
) -> Result<Presence<CanonicalOp>, CanonicalError> {
    let parents: Vec<(CanonicalOp, &Presence<CanonicalOp>)> = parents
        .iter()
        .map(|(op, presence)| (op.clone(), presence.as_ref()))
        .collect();
    Presence::merge(&parents, |a, b| store.is_ancestor_of(a, b))
}

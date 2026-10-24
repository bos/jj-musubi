//! Which copies a hive shows: the rule of `formal/Musubi/Presence.lean` (docs/internals/design.md,
//! "Copies that go away").
//!
//! An operation may be *work* by a copy, one its own `jj` made or musubi made for it, as its
//! join, or a *forget* of copies, as `musubi forget` and `musubi leave` write. A copy is present
//! at an operation when some of its work in the operation's history is in the history of no
//! forget of it there: a forget removes the work it saw, and only work brings a copy back.
//!
//! [`Presence`] keeps, for each copy present at an operation, its latest work that no forget saw
//! (`UMax` in the model), which decides presence at the operation's descendants without walking
//! the history again: [`Presence::merge`] and [`Presence::apply`] are `umax_merge`,
//! `umax_work` and `umax_forget`. It keeps each copy's latest work, whether or not a forget saw
//! it, too ([`Presence::worked`]), which the model leaves out: it decides nothing about
//! presence, only what a forgotten copy's own workspaces are.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::sync::Arc;

use jj_lib::op_store::OperationMetadata;

use crate::workspaces;

/// The attribute of an operation that forgets copies: their machine keys, separated by spaces.
pub const FORGET_ATTRIBUTE: &str = "musubi.forget";

/// The attribute of an operation musubi writes as a copy's own work, such as its join: the
/// copy's machine key.
pub const WORK_ATTRIBUTE: &str = "musubi.work";

/// What an operation is to presence: whose work it is, and which copies it forgets.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Kind {
    pub work: Option<String>,
    pub forgets: BTreeSet<String>,
}

impl Kind {
    /// The kind of a canonical operation: work by the copy whose workspace made it, or that
    /// [`WORK_ATTRIBUTE`] names, and a forget of the copies [`FORGET_ATTRIBUTE`] names.
    pub fn of(metadata: &OperationMetadata) -> Self {
        let work = metadata
            .workspace_name
            .as_ref()
            .and_then(|key| workspaces::split_key(key.as_str()))
            .map(|(machine, _)| machine.to_owned())
            .or_else(|| metadata.attributes.get(WORK_ATTRIBUTE).cloned());
        let forgets = metadata
            .attributes
            .get(FORGET_ATTRIBUTE)
            .map(|keys| keys.split_whitespace().map(str::to_owned).collect())
            .unwrap_or_default();
        Self { work, forgets }
    }
}

/// The copies present at an operation, each with its latest work that no forget saw. A copy
/// present has at least one; usually it has exactly one, its latest work. With them, every
/// copy the operation's history has known, present or not, by whose work or forget, and each
/// one's latest work, whether or not a forget saw it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Presence<Op> {
    latest: BTreeMap<String, BTreeSet<Op>>,
    known: Arc<BTreeSet<String>>,
    worked: Arc<BTreeMap<String, BTreeSet<Op>>>,
}

impl<Op> Default for Presence<Op> {
    fn default() -> Self {
        Self {
            latest: BTreeMap::new(),
            known: Arc::default(),
            worked: Arc::default(),
        }
    }
}

impl<Op: Clone + Ord> Presence<Op> {
    pub fn is_present(&self, copy: &str) -> bool {
        self.latest.contains_key(copy)
    }

    /// The copies present, in order.
    pub fn copies(&self) -> impl Iterator<Item = &str> {
        self.latest.keys().map(String::as_str)
    }

    /// A present copy's latest work that no forget saw.
    pub fn latest(&self, copy: &str) -> Option<&BTreeSet<Op>> {
        self.latest.get(copy)
    }

    /// Every copy the history has known: worked, joined, or been forgotten.
    pub fn known(&self) -> &BTreeSet<String> {
        &self.known
    }

    /// A copy's latest work in the history, whether or not a forget saw it: what it last
    /// did, as of an operation where it is forgotten. Usually one operation; more where the
    /// copy worked on two lines of history that a merge joined.
    pub fn worked(&self, copy: &str) -> Option<&BTreeSet<Op>> {
        self.worked.get(copy)
    }

    /// Presence before an operation's own effect, from its parents' (`umax_merge`): the
    /// latest work of each copy that the parents keep, each kept unless a parent whose
    /// history has it doesn't keep it, as when a forget there saw it, or later work there
    /// followed it. One parent's is the operation's. Each copy's latest work regardless of
    /// forgets is the parents' latest, but for any that is an ancestor of another.
    /// `is_ancestor(a, b)` is whether `a` is `b` or an ancestor of it.
    pub fn merge<E>(
        parents: &[(Op, &Self)],
        mut is_ancestor: impl FnMut(&Op, &Op) -> Result<bool, E>,
    ) -> Result<Self, E> {
        match parents {
            [] => return Ok(Self::default()),
            [(_, only)] => return Ok((*only).clone()),
            _ => {}
        }
        let mut known = parents[0].1.known.clone();
        let mut worked = parents[0].1.worked.clone();
        for (_, presence) in &parents[1..] {
            if !Arc::ptr_eq(&known, &presence.known) && !known.is_superset(&presence.known) {
                Arc::make_mut(&mut known).extend(presence.known.iter().cloned());
            }
            if !Arc::ptr_eq(&worked, &presence.worked) {
                for (copy, ops) in presence.worked.iter() {
                    let Some(have) = worked.get(copy) else {
                        Arc::make_mut(&mut worked).insert(copy.clone(), ops.clone());
                        continue;
                    };
                    if have.is_superset(ops) {
                        continue;
                    }
                    // Each set is the latest already: only one of each against the other's
                    // can be older.
                    let new: Vec<&Op> = ops.difference(have).collect();
                    let mut older: BTreeSet<&Op> = BTreeSet::new();
                    for a in have.difference(ops) {
                        for &b in &new {
                            if is_ancestor(a, b)? {
                                older.insert(a);
                            } else if is_ancestor(b, a)? {
                                older.insert(b);
                            }
                        }
                    }
                    let latest: BTreeSet<Op> = have
                        .iter()
                        .chain(new)
                        .filter(|op| !older.contains(op))
                        .cloned()
                        .collect();
                    Arc::make_mut(&mut worked).insert(copy.clone(), latest);
                }
            }
        }
        let copies: BTreeSet<&String> = parents
            .iter()
            .flat_map(|(_, presence)| presence.latest.keys())
            .collect();
        let mut latest = BTreeMap::new();
        for copy in copies {
            let candidates: BTreeSet<&Op> = parents
                .iter()
                .filter_map(|(_, presence)| presence.latest.get(copy))
                .flatten()
                .collect();
            let mut kept = BTreeSet::new();
            'candidates: for &candidate in &candidates {
                for (op, presence) in parents {
                    let has = presence
                        .latest
                        .get(copy)
                        .is_some_and(|ops| ops.contains(candidate));
                    if !has && is_ancestor(candidate, op)? {
                        continue 'candidates;
                    }
                }
                kept.insert(candidate.clone());
            }
            if !kept.is_empty() {
                latest.insert(copy.clone(), kept);
            }
        }
        Ok(Self {
            latest,
            known,
            worked,
        })
    }

    /// Presence at operation `op` of `kind`, from [`Self::merge`] of its parents': its work is
    /// its copy's latest (`umax_work`), and the copies it forgets are absent (`umax_forget`).
    pub fn apply(mut self, op: &Op, kind: &Kind) -> Self {
        for copy in kind.work.iter().chain(&kind.forgets) {
            if !self.known.contains(copy) {
                Arc::make_mut(&mut self.known).insert(copy.clone());
            }
        }
        if let Some(copy) = &kind.work {
            self.latest
                .insert(copy.clone(), BTreeSet::from([op.clone()]));
            Arc::make_mut(&mut self.worked).insert(copy.clone(), BTreeSet::from([op.clone()]));
        }
        for copy in &kind.forgets {
            self.latest.remove(copy);
        }
        self
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::convert::Infallible;

    use super::*;

    /// `parents[x]` are `x`'s parents, all smaller.
    fn ancestor(parents: &[Vec<usize>]) -> impl Fn(&usize, &usize) -> Result<bool, Infallible> {
        move |&a, &b| {
            let mut stack = vec![b];
            while let Some(x) = stack.pop() {
                if x == a {
                    return Ok(true);
                }
                stack.extend(parents[x].iter().filter(|&&p| p >= a));
            }
            Ok(false)
        }
    }

    fn presences(parents: &[Vec<usize>], kinds: &[Kind]) -> Vec<Presence<usize>> {
        let mut out: Vec<Presence<usize>> = vec![];
        for (x, kind) in kinds.iter().enumerate() {
            let ps: Vec<(usize, &Presence<usize>)> =
                parents[x].iter().map(|&p| (p, &out[p])).collect();
            let merged = Presence::merge(&ps, ancestor(parents)).unwrap();
            let next = merged.apply(&x, kind);
            out.push(next);
        }
        out
    }

    fn work(copy: &str) -> Kind {
        Kind {
            work: Some(copy.to_owned()),
            ..Kind::default()
        }
    }

    fn forget(copy: &str) -> Kind {
        Kind {
            forgets: BTreeSet::from([copy.to_owned()]),
            ..Kind::default()
        }
    }

    /// A copy's latest work, whatever forgets saw: its work replaces it, forgets leave it, and
    /// a merge keeps each line's latest, but for one the other line has seen.
    #[test]
    fn worked_is_the_latest_work_through_forgets() {
        let parents = vec![
            vec![],     // 0: k works
            vec![0],    // 1: k works again
            vec![0],    // 2: a daemon forgets k, having seen only 0
            vec![1, 2], // 3: merge
            vec![1],    // 4: a daemon forgets k, having seen 1
            vec![0],    // 5: k works on another line
            vec![4, 5], // 6: merge
        ];
        let kinds = vec![
            work("k"),
            work("k"),
            forget("k"),
            Kind::default(),
            forget("k"),
            work("k"),
            Kind::default(),
        ];
        let p = presences(&parents, &kinds);
        assert_eq!(p[2].worked("k"), Some(&BTreeSet::from([0])));
        assert_eq!(p[3].worked("k"), Some(&BTreeSet::from([1])));
        assert!(!p[4].is_present("k"));
        assert_eq!(p[4].worked("k"), Some(&BTreeSet::from([1])));
        assert_eq!(p[6].worked("k"), Some(&BTreeSet::from([1, 5])));
    }

    /// A forget concurrent with work it didn't see leaves the copy present; one that saw all
    /// of it doesn't, and nothing but more work brings it back.
    #[test]
    fn forgets_remove_only_what_they_saw() {
        let parents = vec![
            vec![],     // 0: k works
            vec![0],    // 1: a daemon forgets k
            vec![0],    // 2: k works again, concurrently
            vec![1, 2], // 3: merge
            vec![1],    // 4: k's daemon writes something of its own
            vec![3, 4], // 5: merge
        ];
        let kinds = vec![
            work("k"),
            forget("k"),
            work("k"),
            Kind::default(),
            Kind::default(),
            Kind::default(),
        ];
        let p = presences(&parents, &kinds);
        assert!(p[0].is_present("k"));
        assert!(!p[1].is_present("k"));
        assert_eq!(p[3].latest("k"), Some(&BTreeSet::from([2])));
        assert!(!p[4].is_present("k"));
        assert_eq!(p[5].latest("k"), Some(&BTreeSet::from([2])));
    }
}

//! Safety laws checked after every generated step, and the fixed point required after
//! reliable delivery resumes (docs/internals/protocol.md, "Properties").
//!
//! These checks only observe the stores and the history recorded by the harness. Their
//! exceptions are local to the assumptions a fault invalidates: a false reply relaxes the
//! misled node's provenance and known-head checks; rollback relaxes merge ownership.

use std::collections::BTreeSet;

use musubi_core::message::Head;

use super::super::model::Op;
use super::super::model::ROOT;
use super::super::model::Univ;
use super::super::model::flat;
use super::World;

impl World {
    /// A merge includes some unaccepted work of its own node. Rollback or a false reply
    /// can leave the node believing otherwise, so the law applies only before those faults.
    pub(super) fn check_merge_ownership(&self, node: usize, merge: Op, parents: &[Op]) {
        if self.went_back || self.misled[node] {
            return;
        }
        let univ = self.univ.borrow();
        let accepted = univ.ancestors(self.hub.head);
        assert!(
            parents
                .iter()
                .any(|p| univ.creator[*p as usize] == Some(node) && !accepted.contains(p)),
            "MergeOwnership: merge {merge} on node {node} has no unaccepted parent of its own: {parents:?}"
        );
    }

    /// The hub is closed; each node is closed and has only justified operations and
    /// knowledge; accepted heads advance; and no participant drops its own head or root.
    pub fn check_invariants(&self) {
        let univ = self.univ.borrow();
        assert!(self.hub.closed(self.hub.head), "HubClosed");
        let accepted = self.ever_accepted(&univ);
        for n in 0..self.nodes() {
            self.check_node_safety(&univ, &accepted, n);
        }
        self.check_hub_monotonicity(&univ);
        self.check_drop_consistency();
    }

    /// Locality, NodeClosed and KnownIsHubHistory, including staged operations and the
    /// antichain of heads. A misled node may hold what a false reply offered it; its storage
    /// must still be closed and its heads must still be an antichain.
    fn check_node_safety(&self, univ: &Univ, accepted: &BTreeSet<Op>, n: usize) {
        let repo = &self.repos[n];
        let offered = |x: &Op| self.misled[n] && self.offered.contains(x);
        for &x in &repo.lops {
            assert!(
                univ.creator[x as usize] == Some(n) || accepted.contains(&x) || offered(&x),
                "Locality: node {n} has {x}, neither its own nor accepted"
            );
            assert!(
                univ.parents[x as usize]
                    .iter()
                    .all(|p| repo.lops.contains(p)),
                "NodeClosed: parents"
            );
            assert!(
                univ.objs[x as usize].iter().all(|o| repo.lobj.contains(o)),
                "NodeClosed: objects"
            );
        }
        assert!(
            !repo.heads.is_empty() && repo.heads.is_subset(&repo.lops),
            "NodeClosed: heads"
        );
        for op in repo.sops.keys() {
            assert!(
                accepted.contains(op) || offered(op),
                "node {n} staged {op}, which the hub never accepted"
            );
        }
        assert_eq!(
            univ.maximal(&repo.heads),
            repo.heads,
            "heads form an antichain"
        );
        let (seq, head) = self.known(n);
        assert!(
            self.misled[n]
                || self.hist.get(seq as usize) == Some(&head)
                || self.lost.contains(&(seq, head)),
            "KnownIsHubHistory on node {n}"
        );
    }

    /// Each accepted head descends from the one before, or is above everything that
    /// survives of it when accepting through a contraction (`imageAccept`'s `acceptDrops`).
    fn check_hub_monotonicity(&self, univ: &Univ) {
        for (seq, pair) in (1..).zip(self.hist.windows(2)) {
            if self.contracted_accepts.contains(&seq) {
                let drops = flat(&self.hub.record_hist[seq as usize]);
                assert!(
                    univ.below(&drops, pair[0], pair[1]),
                    "HubMonotone, contracted"
                );
            } else {
                assert!(univ.is_ancestor(pair[0], pair[1]), "HubMonotone");
            }
        }
    }

    /// `SInv`: no head is in its holder's dropped set, the root is in none, and taking a
    /// record drops everything it names.
    fn check_drop_consistency(&self) {
        let hub_dropped = self.hub.dropped();
        assert!(
            !hub_dropped.contains(&self.hub.head),
            "the hub's head is dropped"
        );
        assert!(!hub_dropped.contains(&ROOT), "the hub dropped the root");
        for (n, repo) in self.repos.iter().enumerate() {
            assert!(
                repo.heads.iter().all(|head| !repo.dropped.contains(head)),
                "node {n} has a head it dropped"
            );
            assert!(!repo.dropped.contains(&ROOT), "node {n} dropped the root");
            assert!(
                flat(&repo.applied).is_subset(&repo.dropped),
                "node {n} took records it doesn't drop"
            );
        }
    }

    /// Every node has the hub's head and sequence, and has taken exactly its records and
    /// dropped exactly what those records name.
    pub fn converged(&self) -> bool {
        self.repos.iter().zip(&self.cores).all(|(repo, core)| {
            repo.heads == BTreeSet::from([self.hub.head])
                && *core.known()
                    == Head {
                        seq: self.hub.seq,
                        head: self.hub.head,
                    }
                && repo.applied == self.hub.records
                && repo.dropped == self.hub.dropped()
        })
    }
}

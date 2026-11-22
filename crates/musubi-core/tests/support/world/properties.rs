//! Safety laws checked after every generated step, and the fixed point required after
//! reliable delivery resumes (docs/internals/protocol.md, "Properties").
//!
//! These checks only observe the stores and the history recorded by the harness. Their
//! exceptions are local to the assumptions a fault invalidates: a false reply relaxes the
//! misled node's provenance and known-head checks; rollback relaxes merge ownership.

use std::collections::BTreeSet;

use musubi_core::message::Head;

use super::super::model::Op;
use super::super::model::Univ;
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
    /// knowledge; and accepted heads advance.
    pub fn check_invariants(&self) {
        let univ = self.univ.borrow();
        assert!(self.hub.closed(self.hub.head), "HubClosed");
        let accepted = self.ever_accepted(&univ);
        for n in 0..self.nodes() {
            self.check_node_safety(&univ, &accepted, n);
        }
        self.check_hub_monotonicity(&univ);
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

    /// Each accepted head descends from the one before.
    fn check_hub_monotonicity(&self, univ: &Univ) {
        for pair in self.hist.windows(2) {
            assert!(univ.is_ancestor(pair[0], pair[1]), "HubMonotone");
        }
    }

    /// Every node has the hub's head and sequence.
    pub fn converged(&self) -> bool {
        self.repos.iter().zip(&self.cores).all(|(repo, core)| {
            repo.heads == BTreeSet::from([self.hub.head])
                && *core.known()
                    == Head {
                        seq: self.hub.seq,
                        head: self.hub.head,
                    }
        })
    }
}

//! Failure/recovery observations. Reopening the fake keeps its logical persisted data;
//! there are no jj/gix handles or translation caches in this abstraction.

use super::*;

struct NodeRetained {
    ops: BTreeSet<Op>,
    objs: BTreeSet<Obj>,
    staged: BTreeSet<Op>,
    staged_objs: BTreeSet<Obj>,
    heads: BTreeSet<Op>,
}

pub(super) struct Retained {
    hub_ops: BTreeSet<Op>,
    hub_objs: BTreeSet<Obj>,
    hub_head: Op,
    nodes: Vec<NodeRetained>,
}

impl World {
    /// Counts actual fallible trait calls, globally across the hub and nodes. An event can
    /// call fewer than `at`; that is a successful no-fault replay, not an error to invent.
    pub fn arm_storage(&mut self, at: usize, timing: Timing) {
        self.faults.borrow_mut().arm(at, timing);
    }

    /// Stops injecting, returning the calls reached and the one failure, if reached.
    pub fn stop_storage(&mut self) -> (Vec<&'static str>, Option<StorageError>) {
        let mut faults = self.faults.borrow_mut();
        faults.disarm();
        (std::mem::take(&mut faults.calls), faults.failed.take())
    }

    pub(super) fn storage_begin(&self) -> Option<Retained> {
        let mut faults = self.faults.borrow_mut();
        faults.check_observed();
        faults.begin();
        faults.active().then(|| Retained {
            hub_ops: self.hub.ops.clone(),
            hub_objs: self.hub.objs.clone(),
            hub_head: self.hub.head,
            nodes: self
                .repos
                .iter()
                .map(|repo| NodeRetained {
                    ops: repo.lops.clone(),
                    objs: repo.lobj.clone(),
                    staged: repo.sops.keys().copied().collect(),
                    staged_objs: repo.sobj.clone(),
                    heads: repo.heads.clone(),
                })
                .collect(),
        })
    }

    pub(super) fn storage_failed(
        &mut self,
        node: Option<usize>,
        before: Option<Retained>,
        error: StorageError,
        mut actions: Vec<Value>,
    ) {
        let before = before.expect("only an armed adapter can fail");
        let mut faults = self.faults.borrow_mut();
        faults.observe(&error);
        actions.extend(faults.effects.iter().cloned());
        let outside = faults.outside_model;
        drop(faults);
        self.trace
            .push(json!({"marker": "storageError", "call": error.call,
            "timing": format!("{:?}", error.timing), "node": node, "outsideModel": outside}));
        if outside {
            // A merged Push has no model step for storing just its operations, or only
            // some bundle entries. Do not add fictitious messages to make it fit. Continue
            // checking safety/retention/convergence, but retire this case's oracle.
            if let Some(oracle) = self.oracle.take() {
                self.retired_oracle = Some(oracle);
            }
        } else {
            self.act_all(actions);
        }
        if let Some(node) = node
            && let Some((op, parents, _)) = self.repos[node].last_merge.clone()
            && error.call == "node.merge_heads"
            && error.timing == Timing::After
        {
            self.check_merge_ownership(node, op, &parents);
        }
        // Observe the failure before recovery can hide a bad publication or deletion.
        self.check_invariants();
        self.check_retained(&before);
        // The daemon reopens after a failed sync, falling back to restart if that fails
        // (daemon.rs). All of this fake's store data survives reopen. A hub error is sent
        // back to the requesting node; the HubService retains its adapter.
        if let Some(node) = node {
            self.crash_node(node);
        }
        self.check_invariants();
        self.check_retained(&before);
    }

    fn check_retained(&self, before: &Retained) {
        assert!(
            before.hub_ops.is_subset(&self.hub.ops),
            "storage error lost hub operations"
        );
        assert!(
            before.hub_objs.is_subset(&self.hub.objs),
            "storage error lost hub objects"
        );
        let univ = self.univ.borrow();
        assert!(
            univ.is_ancestor(before.hub_head, self.hub.head),
            "storage error regressed hub head"
        );
        for (node, (old, repo)) in before.nodes.iter().zip(&self.repos).enumerate() {
            assert!(
                old.ops.is_subset(&repo.lops),
                "storage error lost node {node}'s operations"
            );
            assert!(
                old.objs.is_subset(&repo.lobj),
                "storage error lost node {node}'s objects"
            );
            assert!(
                old.staged.iter().all(|op| repo.sops.contains_key(op)),
                "storage error lost staged operations"
            );
            assert!(
                old.staged_objs.is_subset(&repo.sobj),
                "storage error lost staged objects"
            );
            for &head in &old.heads {
                assert!(
                    repo.heads.iter().any(|&new| univ.is_ancestor(head, new)),
                    "storage error made node {node}'s retained head {head} unreachable"
                );
            }
        }
    }
}

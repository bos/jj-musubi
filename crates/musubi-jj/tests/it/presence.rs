//! The presence rule as musubi computes it (`musubi_jj::presence`) against the Lean model's
//! executable form, through the oracle (docs/internals/conformance.md, "Presence"): for
//! random histories, the copies present at every operation, with each one's latest work that
//! no forget saw, are what the model says; and so they stay at every operation a contraction
//! keeps, as a canonical store works them out.

#![allow(clippy::unwrap_used)]

use std::cell::Cell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::convert::Infallible;

use hegel::HealthCheck;
use hegel::TestCase;
use hegel::generators as gs;
use jj_lib::backend::CommitId;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use musubi_jj::canonical::CanonicalStore;
use musubi_jj::canonical::Contraction;
use musubi_jj::canonical::PresenceMemo;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::presence::FORGET_ATTRIBUTE;
use musubi_jj::presence::Kind;
use musubi_jj::presence::Presence;
use musubi_jj::presence::WORK_ATTRIBUTE;
use serde_json::Value;
use serde_json::json;

use crate::oracle::Oracle;

/// How many copies and operations a history has at most: enough for a copy's work to race
/// forgets of it from two sides, and for merges of merges.
const COPIES: u64 = 3;
const OPS: usize = 12;

/// An operation: its parents, all earlier, and what it is to presence, as musubi makes
/// operations: work by one copy, or a forget of some, never both.
struct Op {
    parents: Vec<usize>,
    work: Option<u64>,
    forgets: BTreeSet<u64>,
}

fn history(tc: &TestCase) -> Vec<Op> {
    let len = tc.draw(gs::integers::<usize>().min_value(1).max_value(OPS));
    let copy = || gs::integers::<u64>().max_value(COPIES - 1);
    (0..len)
        .map(|x| {
            let mut parents = BTreeSet::new();
            if x > 0 {
                let count = tc.draw(gs::integers::<usize>().min_value(1).max_value(x.min(3)));
                for _ in 0..count {
                    parents.insert(tc.draw(gs::integers::<usize>().max_value(x - 1)));
                }
            }
            let work = tc.draw(gs::booleans()).then(|| tc.draw(copy()));
            let mut forgets = BTreeSet::new();
            if work.is_none() {
                for _ in 0..tc.draw(gs::integers::<usize>().max_value(2)) {
                    forgets.insert(tc.draw(copy()));
                }
            }
            Op {
                parents: parents.into_iter().collect(),
                work,
                forgets,
            }
        })
        .collect()
}

/// Each operation's copies with their latest work, as `Presence::merge` and
/// `Presence::apply` compute them from the parents'.
fn computed(ops: &[Op]) -> Vec<BTreeMap<u64, BTreeSet<usize>>> {
    let is_ancestor = |a: &usize, b: &usize| -> Result<bool, Infallible> {
        let mut stack = vec![*b];
        while let Some(x) = stack.pop() {
            if x == *a {
                return Ok(true);
            }
            stack.extend(ops[x].parents.iter().filter(|&&p| p >= *a));
        }
        Ok(false)
    };
    let mut presences: Vec<Presence<usize>> = vec![];
    for (x, op) in ops.iter().enumerate() {
        let parents: Vec<(usize, &Presence<usize>)> =
            op.parents.iter().map(|&p| (p, &presences[p])).collect();
        let kind = Kind {
            work: op.work.map(|k| k.to_string()),
            forgets: op.forgets.iter().map(u64::to_string).collect(),
            ..Kind::default()
        };
        let presence = Presence::merge(&parents, is_ancestor)
            .unwrap()
            .apply(&x, &kind);
        presences.push(presence);
    }
    presences
        .iter()
        .map(|presence| {
            presence
                .copies()
                .map(|k| (k.parse().unwrap(), presence.latest(k).unwrap().clone()))
                .collect()
        })
        .collect()
}

/// The model's answer for the same history.
fn modelled(oracle: &mut Oracle, ops: &[Op]) -> Vec<BTreeMap<u64, BTreeSet<usize>>> {
    let ops: Vec<Value> = ops
        .iter()
        .map(|op| json!({"parents": op.parents, "work": op.work, "forgets": op.forgets}))
        .collect();
    let reply = oracle.call(&json!({"op": "presence", "ops": ops}));
    assert_eq!(reply["ok"], true, "the oracle refused the history: {reply}");
    reply["presence"]
        .as_array()
        .unwrap()
        .iter()
        .map(|at| {
            at.as_array()
                .unwrap()
                .iter()
                .map(|entry| {
                    let latest = entry["latest"].as_array().unwrap();
                    let latest = latest.iter().map(|c| c.as_u64().unwrap() as usize);
                    (entry["copy"].as_u64().unwrap(), latest.collect())
                })
                .collect()
        })
        .collect()
}

// Each case asks the Lean oracle, a process of its own, which on a small machine running other
// tests at once can slow generating cases past Hegel's health check.
#[hegel::test(test_cases = cases(), suppress_health_check = [HealthCheck::TooSlow])]
fn conformance(tc: TestCase) {
    // One oracle for every case: presence requests leave it as they found it.
    thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
    let mut oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
    let ops = history(&tc);
    let (computed, modelled) = (computed(&ops), modelled(&mut oracle, &ops));
    ORACLE.set(Some(oracle));
    for (x, (computed, modelled)) in computed.iter().zip(&modelled).enumerate() {
        assert_eq!(computed, modelled, "at operation {x}");
    }
}

/// Each operation's copies with their latest work, as a canonical store works them out at
/// what each operation becomes once those `dropped` are contracted out, stamps and all: for
/// those it keeps, what the model says (`PresenceContract.pres_eq`).
fn contracted(
    ops: &[Op],
    dropped: &BTreeSet<usize>,
) -> Vec<Option<BTreeMap<u64, BTreeSet<usize>>>> {
    let dir = musubi_testutil::tempdir();
    let store = CanonicalStore::open(dir.path(), CommitId::from_bytes(&[0; 20])).unwrap();
    let view = store
        .write_view(&View::make_root(CommitId::from_bytes(&[0; 20])))
        .unwrap();
    let mut ids: Vec<CanonicalOp> = vec![];
    let mut index: BTreeMap<OperationId, usize> = BTreeMap::new();
    for (x, op) in ops.iter().enumerate() {
        let mut operation = Operation::make_root(view.clone());
        operation.parents = if op.parents.is_empty() {
            vec![store.root_operation_id().0.clone()]
        } else {
            op.parents.iter().map(|&p| ids[p].0.clone()).collect()
        };
        operation.metadata.description = format!("op {x}");
        let attributes = &mut operation.metadata.attributes;
        if let Some(copy) = op.work {
            attributes.insert(WORK_ATTRIBUTE.to_owned(), copy.to_string());
        }
        if !op.forgets.is_empty() {
            let copies: Vec<String> = op.forgets.iter().map(u64::to_string).collect();
            attributes.insert(FORGET_ATTRIBUTE.to_owned(), copies.join(" "));
        }
        let id = store.write_operation(&operation).unwrap();
        index.insert(store.original_id(&id).unwrap(), x);
        ids.push(id);
    }
    let mut contraction =
        Contraction::new(&store, dropped.iter().map(|&x| ids[x].clone())).unwrap();
    let memo = PresenceMemo::default();
    (0..ops.len())
        .map(|x| {
            if dropped.contains(&x) {
                return None;
            }
            let image = contraction.images(&store, &ids[x]).unwrap();
            let presence = memo.presence(&store, &image[0]).unwrap();
            Some(
                presence
                    .copies()
                    .map(|k| {
                        let latest = presence.latest(k).unwrap();
                        let latest = latest.iter().map(|work| index[&work.original]);
                        (k.parse().unwrap(), latest.collect())
                    })
                    .collect(),
            )
        })
        .collect()
}

// As `conformance`, with some operations dropped.
#[hegel::test(test_cases = cases(), suppress_health_check = [HealthCheck::TooSlow])]
fn contraction_keeps_presence(tc: TestCase) {
    thread_local!(static ORACLE: Cell<Option<Oracle>> = const { Cell::new(None) });
    let mut oracle = ORACLE.take().unwrap_or_else(Oracle::spawn);
    let ops = history(&tc);
    let dropped: BTreeSet<usize> = (0..ops.len()).filter(|_| tc.draw(gs::booleans())).collect();
    let (contracted, modelled) = (contracted(&ops, &dropped), modelled(&mut oracle, &ops));
    ORACLE.set(Some(oracle));
    for (x, (contracted, modelled)) in contracted.iter().zip(&modelled).enumerate() {
        if let Some(contracted) = contracted {
            assert_eq!(
                contracted, modelled,
                "at operation {x}, {dropped:?} dropped"
            );
        }
    }
}

/// How many histories to try: `MUSUBI_CONFORMANCE_CASES`, as for the protocol's
/// conformance test, or else enough to find each mistake the test is known to catch.
fn cases() -> u64 {
    std::env::var("MUSUBI_CONFORMANCE_CASES")
        .ok()
        .and_then(|cases| cases.parse().ok())
        .unwrap_or(300)
}

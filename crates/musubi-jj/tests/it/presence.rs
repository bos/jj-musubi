//! The presence rule as musubi computes it (`musubi_jj::presence`) against the Lean model's
//! executable form, through the oracle (docs/internals/conformance.md, "Presence"): for
//! random histories, the copies present at every operation, with each one's latest work that
//! no forget saw, the name it last recorded (`NameIs`), and the generation since which it
//! has had it (`SinceIs`), are what the model says.

#![allow(clippy::unwrap_used)]

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::convert::Infallible;

use hegel::TestCase;
use hegel::generators as gs;
use musubi_jj::presence::Kind;
use musubi_jj::presence::Presence;
use serde_json::Value;
use serde_json::json;

use crate::oracle::Oracle;

/// How many copies and operations a history has at most: enough for a copy's work to race
/// forgets of it from two sides, and for merges of merges; and how many names copies record,
/// few, so that records on two lines of history differ and agree.
const COPIES: u64 = 3;
const OPS: usize = 12;
const NAMES: u64 = 3;

/// An operation: its parents, all earlier, and what it is to presence, as musubi makes
/// operations: work by one copy, which may record its name, or a forget of some, never both.
#[derive(Debug)]
struct Op {
    parents: Vec<usize>,
    work: Option<u64>,
    name: Option<u64>,
    forgets: BTreeSet<u64>,
}

/// What a copy present at an operation is: its latest work that no forget saw, the name it
/// last recorded, and the generation since which it has had its name.
type Copy = (BTreeSet<usize>, Option<u64>, u64);

/// Drawn as one value, so a failure prints the history once, as the operations it has.
#[hegel::composite]
fn history(tc: &TestCase) -> Vec<Op> {
    let len = tc.draw(gs::integers::<usize>().min_value(1).max_value(OPS));
    let copy = || gs::integers::<u64>().max_value(COPIES - 1);
    (0..len)
        .map(|x| {
            let parents = if x == 0 {
                BTreeSet::new()
            } else {
                tc.draw(
                    gs::btree_sets(gs::integers::<usize>().max_value(x - 1))
                        .min_size(1)
                        .max_size(x.min(3)),
                )
            };
            // No work is the ordinary operation: it forgets nothing either, once shrunk.
            let work = tc.draw(gs::optional(copy()));
            let (forgets, name) = if work.is_none() {
                (tc.draw(gs::btree_sets(copy()).max_size(2)), None)
            } else {
                let name = gs::integers::<u64>().max_value(NAMES - 1);
                (BTreeSet::new(), tc.draw(gs::optional(name)))
            };
            Op {
                parents: parents.into_iter().collect(),
                work,
                name,
                forgets,
            }
        })
        .collect()
}

/// Each operation's copies, as `Presence::merge` and `Presence::apply` compute them from the
/// parents', each operation's generation one more than its parents' greatest.
fn computed(ops: &[Op]) -> Vec<BTreeMap<u64, Copy>> {
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
    let mut generations: Vec<u64> = vec![];
    for (x, op) in ops.iter().enumerate() {
        let parents: Vec<(usize, &Presence<usize>)> =
            op.parents.iter().map(|&p| (p, &presences[p])).collect();
        // Names as single digits, which order as the numbers they stand for.
        let kind = Kind {
            work: op.work.map(|k| k.to_string()),
            forgets: op.forgets.iter().map(u64::to_string).collect(),
            name: op.name.map(|n| n.to_string()),
            ..Kind::default()
        };
        let generation = 1 + op
            .parents
            .iter()
            .map(|&p| generations[p])
            .max()
            .unwrap_or(0);
        let presence = Presence::merge(&parents, is_ancestor)
            .unwrap()
            .apply(&x, &kind, generation);
        presences.push(presence);
        generations.push(generation);
    }
    presences
        .iter()
        .map(|presence| {
            presence
                .copies()
                .map(|k| {
                    let copy = (
                        presence.latest(k).unwrap().clone(),
                        presence.recorded_name(k).map(|n| n.parse().unwrap()),
                        presence.since(k),
                    );
                    (k.parse().unwrap(), copy)
                })
                .collect()
        })
        .collect()
}

/// The model's answer for the same history.
fn modelled(oracle: &mut Oracle, ops: &[Op]) -> Vec<BTreeMap<u64, Copy>> {
    let ops: Vec<Value> = ops
        .iter()
        .map(|op| {
            json!({"parents": op.parents, "work": op.work, "forgets": op.forgets, "name": op.name})
        })
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
                    let copy = (
                        latest.collect(),
                        entry["name"].as_u64(),
                        entry["since"].as_u64().unwrap(),
                    );
                    (entry["copy"].as_u64().unwrap(), copy)
                })
                .collect()
        })
        .collect()
}

#[hegel::test(profile = "presence")]
fn conformance(tc: TestCase) {
    let ops = tc.draw(history());
    let computed = computed(&ops);
    // Presence requests leave the oracle as they found it.
    let modelled = Oracle::with(|oracle| modelled(oracle, &ops));
    for (x, (computed, modelled)) in computed.iter().zip(&modelled).enumerate() {
        assert_eq!(computed, modelled, "at operation {x}");
    }
}

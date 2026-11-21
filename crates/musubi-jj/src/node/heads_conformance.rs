//! `heads::plan`, what musubi decides about the op heads it moves, against `OpHeads.lean`,
//! through the oracle (docs/internals/conformance.md, "Moving op heads"): for random operation
//! graphs, heads and watches, what `look` takes out and puts back and what it goes on watching;
//! what `entries` makes to watch of a move; how `compose` adds to the watch; and when the op
//! heads are the same.
//!
//! Operations are numbers, each after its parents; a fingerprint is a number too, drawn from
//! few so that operations share them, as jj's rewrites of an operation share its own.

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::convert::Infallible;

use hegel::TestCase;
use hegel::generators as gs;
use serde_json::Value;
use serde_json::json;

use super::heads::plan::Graph;
use super::heads::plan::Look;
use super::heads::plan::Node;
use super::heads::plan::Replaced;
use super::heads::plan::compose;
use super::heads::plan::entries;
use super::heads::plan::look;
use super::heads::plan::same;
use crate::oracle::Oracle;

/// How many operations a graph has at most: room for an operation below an op head, a merge of a
/// replacement with other work, and a few more.
const OPS: usize = 9;
/// How many fingerprints: few enough that an operation's fingerprint is often another's.
const PRINTS: usize = 2;

#[derive(Clone, Debug)]
struct Op {
    parents: Vec<u32>,
    fp: u64,
    known: bool,
}

#[derive(Debug)]
struct Ops(Vec<Op>);

impl Graph<u32> for Ops {
    type Error = Infallible;

    fn read(&self, id: &u32) -> Result<Node<u32>, Infallible> {
        let op = &self.0[*id as usize];
        Ok(Node {
            parents: op.parents.clone(),
            fingerprint: op.fp.to_string(),
        })
    }

    fn known(&self, id: &u32) -> bool {
        self.0[*id as usize].known
    }
}

impl Ops {
    fn json(&self) -> Value {
        Value::Array(
            self.0
                .iter()
                .map(|op| json!({"parents": op.parents, "fp": op.fp, "known": op.known}))
                .collect(),
        )
    }

    fn print(&self, id: u32) -> String {
        self.0[id as usize].fp.to_string()
    }
}

/// Operations each after its parents, which are few; a quarter of them known to the cache.
#[hegel::composite]
fn ops(tc: &TestCase) -> Ops {
    let len = tc.draw(gs::integers::<usize>().min_value(2).max_value(OPS));
    Ops((0..len)
        .map(|x| {
            let parents = if x == 0 {
                BTreeSet::new()
            } else {
                tc.draw(gs::btree_sets(gs::integers::<u32>().max_value(x as u32 - 1)).max_size(3))
            };
            Op {
                parents: parents.into_iter().collect(),
                fp: tc.draw(gs::integers::<u64>().max_value(PRINTS as u64 - 1)),
                known: tc.draw(gs::integers::<u8>().max_value(3)) == 0,
            }
        })
        .collect())
}

/// Some of the operations, in any order.
fn some(tc: &TestCase, ops: &Ops, max: usize) -> Vec<u32> {
    let ids = tc.draw(
        gs::btree_sets(gs::integers::<u32>().max_value(ops.0.len() as u32 - 1)).max_size(max),
    );
    let mut ids: Vec<u32> = ids.into_iter().collect();
    if tc.draw(gs::booleans()) {
        ids.reverse();
    }
    ids
}

/// Entries of a watch: an op head taken out, mostly with its own fingerprint, with some of what
/// replaced it among `heads`, which are mostly what musubi put in.
fn watch(tc: &TestCase, ops: &Ops, heads: &[u32]) -> Vec<Replaced<u32>> {
    let len = tc.draw(gs::integers::<usize>().max_value(3));
    (0..len)
        .map(|_| {
            let head = tc.draw(gs::integers::<u32>().max_value(ops.0.len() as u32 - 1));
            let own = tc.draw(gs::integers::<u8>().max_value(3)) > 0;
            let fingerprint = if own {
                ops.print(head)
            } else {
                tc.draw(gs::integers::<u64>().max_value(PRINTS as u64 - 1))
                    .to_string()
            };
            // Mostly some of the op heads, as what replaced it, and sometimes other work.
            let mut by: Vec<u32> = vec![];
            for head in heads {
                if tc.draw(gs::integers::<u8>().max_value(2)) > 0 {
                    by.push(*head);
                }
            }
            by.extend(some(tc, ops, 1));
            by.dedup();
            Replaced {
                head,
                fingerprint,
                images: some(tc, ops, 2),
                by,
            }
        })
        .collect()
}

fn replaced_json(r: &Replaced<u32>) -> Value {
    json!({
        "head": r.head,
        "fp": r.fingerprint.parse::<u64>().unwrap(),
        "images": r.images,
        "by": r.by,
    })
}

fn list_json(rs: &[Replaced<u32>]) -> Value {
    Value::Array(rs.iter().map(replaced_json).collect())
}

fn look_json(look: &Look<u32>) -> Value {
    match look {
        Look::Nothing { kept } => json!({"ok": true, "look": "nothing", "kept": list_json(kept)}),
        Look::Retire(r) => json!({
            "ok": true, "look": "retire", "out": r.out, "back": r.back,
            "kept": list_json(&r.kept), "rewritten": r.rewritten,
        }),
    }
}

fn ask(request: &Value) -> Value {
    // These requests leave the oracle as they found it.
    Oracle::with(|oracle| oracle.call(request))
}

fn look_conforms(ops: &Ops, heads: &[u32], watched: &[Replaced<u32>]) -> Look<u32> {
    let computed = look(heads, watched.to_vec(), ops).unwrap();
    let modelled = ask(&json!({
        "op": "opHeads", "call": "look", "ops": ops.json(), "heads": heads,
        "watch": list_json(watched),
    }));
    assert_eq!(
        look_json(&computed),
        modelled,
        "{ops:?}, heads {heads:?}, watching {watched:?}"
    );
    computed
}

/// What musubi takes out and puts back, and goes on watching, for any op heads, watch and
/// history.
#[hegel::test(profile = "op-heads")]
fn look_conformance(tc: TestCase) {
    let ops = tc.draw(ops());
    let heads = some(&tc, &ops, 3);
    // Half of the op heads are what musubi put in, the rest beside them.
    let mut put = vec![];
    for head in &heads {
        if tc.draw(gs::booleans()) {
            put.push(*head);
        }
    }
    let watched = watch(&tc, &ops, &put);
    look_conforms(&ops, &heads, &watched);
}

/// Each way `look` can go is reached: nothing, with and without a watch to keep, and taking out
/// with and without putting back; and the rewrite is an op head, not an operation below one.
#[test]
fn look_examples() {
    let op = |parents: &[u32], fp: u64, known: bool| Op {
        parents: parents.to_vec(),
        fp,
        known,
    };
    // `0` was replaced by `2`; `1` is jj's rewrite of `0`, beside it.
    let ops = Ops(vec![op(&[], 0, true), op(&[], 0, false), op(&[], 5, true)]);
    let entry = Replaced {
        head: 0,
        fingerprint: "0".into(),
        images: vec![2],
        by: vec![2],
    };
    let Look::Retire(r) = look_conforms(&ops, &[1, 2], std::slice::from_ref(&entry)) else {
        panic!("a rewrite beside a replacement is taken out")
    };
    assert_eq!((r.out, r.back, r.kept.len()), (vec![2], vec![], 0));
    // The replacement `2` alone: nothing beside it, and the watch is kept.
    let Look::Nothing { kept } = look_conforms(&ops, &[2], std::slice::from_ref(&entry)) else {
        panic!("nothing beside the replacement")
    };
    assert_eq!(kept, vec![entry.clone()]);
    // The replacement gone: the entry is forgotten.
    let Look::Nothing { kept } = look_conforms(&ops, &[1], std::slice::from_ref(&entry)) else {
        panic!("nothing is watched once its replacement is gone")
    };
    assert_eq!(kept, vec![]);
    // A merge `4` of the replacement `2` and other work `3`: taking `4` out puts `3` back.
    let ops = Ops(vec![
        op(&[], 0, true),
        op(&[], 0, false),
        op(&[], 5, true),
        op(&[], 7, false),
        op(&[2, 3], 6, true),
    ]);
    let entry = Replaced {
        by: vec![2, 4],
        ..entry
    };
    let Look::Retire(r) = look_conforms(&ops, &[1, 4], std::slice::from_ref(&entry)) else {
        panic!("the merge is beside a rewrite")
    };
    assert_eq!((r.out, r.back), (vec![4], vec![3]));
    {
        // The replaced head `2` was jj's rewrite of an operation `1`, which a command wrote on:
        // `4`, an op head beside the replacement `3`, is on `1`, which has the fingerprint of
        // `2`. It is no rewrite of `2`, and the replacement stays.
        let rewritten_from = Ops(vec![
            op(&[], 0, true),
            op(&[], 1, false),
            op(&[], 1, false),
            op(&[], 3, true),
            op(&[1], 4, false),
        ]);
        let from_entry = Replaced {
            head: 2,
            fingerprint: "1".into(),
            images: vec![3],
            by: vec![3],
        };
        assert!(matches!(
            look_conforms(&rewritten_from, &[4, 3], std::slice::from_ref(&from_entry)),
            Look::Nothing { .. }
        ));
        // But `jj op abandon`'s rewrite `1` of `2`, as an op head beside the replacement, is one.
        let Look::Retire(r) =
            look_conforms(&rewritten_from, &[1, 3], std::slice::from_ref(&from_entry))
        else {
            panic!("a rewrite beside the replacement is taken out")
        };
        assert_eq!(r.out, vec![3]);
    }
    // A rewrite known to the cache is none of jj's; nor is the replaced head itself, still an op
    // head, whatever its fingerprint.
    let still = Ops(vec![op(&[], 0, true), op(&[], 0, false), op(&[], 5, true)]);
    let own = Replaced {
        head: 1,
        fingerprint: "0".into(),
        images: vec![2],
        by: vec![2],
    };
    assert!(matches!(
        look_conforms(&still, &[1, 2], std::slice::from_ref(&own)),
        Look::Nothing { .. }
    ));
    let known = Ops(vec![op(&[], 0, true), op(&[], 0, true), op(&[], 5, true)]);
    let entry = Replaced {
        by: vec![2],
        ..entry
    };
    assert!(matches!(
        look_conforms(&known, &[1, 2], std::slice::from_ref(&entry)),
        Look::Nothing { .. }
    ));
}

/// What a move of `read` to `new` makes to watch, for any heads and images.
#[hegel::test(profile = "op-heads")]
fn entries_conformance(tc: TestCase) {
    let ops = tc.draw(ops());
    let read = some(&tc, &ops, 3);
    let mut new = some(&tc, &ops, 4);
    if !read.is_empty() && tc.draw(gs::booleans()) {
        new.push(read[0]);
    }
    new.dedup();
    let old: Vec<&u32> = read.iter().filter(|h| !new.contains(h)).collect();
    let mut from = HashMap::new();
    for head in &old {
        if tc.draw(gs::booleans()) {
            from.insert(**head, some(&tc, &ops, 2));
        }
    }
    let computed = entries(&old, &from, &new, &read, &ops).unwrap();
    let from_json: Vec<Value> = from
        .iter()
        .map(|(head, images)| json!({"head": head, "images": images}))
        .collect();
    let modelled = ask(&json!({
        "op": "opHeads", "call": "entries", "ops": ops.json(), "read": read, "new": new,
        "from": from_json,
    }));
    assert_eq!(
        json!({"ok": true, "entries": list_json(&computed)}),
        modelled,
        "{ops:?}, read {read:?}, new {new:?}, from {from:?}"
    );
}

/// What is watched after another move.
#[hegel::test(profile = "op-heads")]
fn compose_conformance(tc: TestCase) {
    let ops = tc.draw(ops());
    let watched = watch(&tc, &ops, &[]);
    let replaced = watch(&tc, &ops, &[]);
    let composed = compose(watched.clone(), replaced.clone());
    let modelled = ask(&json!({
        "op": "opHeads", "call": "compose", "watch": list_json(&watched),
        "replaced": list_json(&replaced),
    }));
    assert_eq!(
        json!({"ok": true, "watch": list_json(&composed)}),
        modelled,
        "{watched:?} and {replaced:?}"
    );
}

/// Whether the op heads are those musubi read.
#[hegel::test(profile = "op-heads")]
fn same_conformance(tc: TestCase) {
    let ids = || gs::vecs(gs::integers::<u32>().max_value(3)).max_size(4);
    let a = tc.draw(ids());
    let b = tc.draw(ids());
    let modelled = ask(&json!({"op": "opHeads", "call": "same", "a": a, "b": b}));
    assert_eq!(
        json!({"ok": true, "same": same(&a, &b)}),
        modelled,
        "{a:?} and {b:?}"
    );
}

/// A replaced head that was itself one of what an earlier entry put in takes that entry's place
/// there, and what is put in twice is put in once.
#[test]
fn compose_examples() {
    let entry = |head: u32, images: &[u32], by: &[u32]| Replaced {
        head,
        fingerprint: head.to_string(),
        images: images.to_vec(),
        by: by.to_vec(),
    };
    let watched = vec![entry(0, &[2], &[2, 3])];
    let replaced = vec![entry(2, &[4], &[3, 5])];
    let composed = compose(watched.clone(), replaced.clone());
    let modelled = ask(&json!({
        "op": "opHeads", "call": "compose", "watch": list_json(&watched),
        "replaced": list_json(&replaced),
    }));
    assert_eq!(json!({"ok": true, "watch": list_json(&composed)}), modelled);
    assert_eq!(composed[0], entry(0, &[4], &[3, 5]));
    assert_eq!(composed[1], replaced[0]);
}

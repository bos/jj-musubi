//! `heads::plan`, what musubi decides about the op heads it moves, against `OpHeads.lean`,
//! through the oracle (docs/internals/conformance.md, "Moving op heads"): when the op heads
//! are the same.

use hegel::TestCase;
use hegel::generators as gs;
use serde_json::json;

use super::heads::plan::same;
use crate::oracle::Oracle;

/// Whether the op heads are those musubi read.
#[hegel::test(profile = "op-heads")]
fn same_conformance(tc: TestCase) {
    let ids = || gs::vecs(gs::integers::<u32>().max_value(3)).max_size(4);
    let a = tc.draw(ids());
    let b = tc.draw(ids());
    // The request leaves the oracle as it found it.
    let modelled = Oracle::with(|oracle| {
        oracle.call(&json!({"op": "opHeads", "call": "same", "a": a, "b": b}))
    });
    assert_eq!(
        json!({"ok": true, "same": same(&a, &b)}),
        modelled,
        "{a:?} and {b:?}"
    );
}

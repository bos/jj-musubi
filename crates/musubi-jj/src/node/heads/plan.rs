//! What musubi decides about op heads it moves, with no files and no jj: the Lean model's
//! `OpHeads.lean`, which the conformance test in `heads_conformance.rs` checks it against
//! (docs/internals/conformance.md, "Moving op heads").

use std::collections::HashSet;
use std::hash::Hash;

/// Whether `a` and `b` are the same op heads, in any order: the check before a move, which
/// moves nothing unless the op heads are those musubi read.
pub(in crate::node) fn same<Id: Eq + Hash>(a: &[Id], b: &[Id]) -> bool {
    let a: HashSet<&Id> = a.iter().collect();
    let b: HashSet<&Id> = b.iter().collect();
    a == b
}

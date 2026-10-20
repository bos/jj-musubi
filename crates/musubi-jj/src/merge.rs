//! Three-way merges of named entries, exactly as jj merges a workspace's working copy.

use std::hash::Hash;

use jj_lib::merge::SameChange;
use jj_lib::merge::trivial_merge;

/// Merges one entry three-way, as jj merges a workspace's working-copy commit when it
/// merges concurrent operations: a trivial merge where there is one, then a removal on
/// either side, then `ours`. This is jj-lib's private `MutableRepo::merge_wc_commit`, built
/// the same way on jj's `trivial_merge`; the `workspace_merge_matches_jj` test checks that
/// the two agree.
pub fn merge_entry<'a, T: Eq + Hash>(
    ours: Option<&'a T>,
    base: Option<&'a T>,
    theirs: Option<&'a T>,
) -> Option<&'a T> {
    if let Some(resolved) = trivial_merge(&[ours, base, theirs], SameChange::Accept) {
        *resolved
    } else if ours.is_none() || theirs.is_none() {
        None
    } else {
        ours
    }
}

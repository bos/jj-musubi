//! Detect independent merges that perform the same rebase twice, apart from jj's own repeat
//! of a rebase after `jj op abandon`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;

use jj_lib::backend::CommitId;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;

use super::Reference;

#[derive(Clone)]
pub(super) struct MergeRewrite {
    pub(super) operation: OperationId,
    pub(super) new: CommitId,
    pub(super) predecessors: Vec<CommitId>,
}

/// Whether a change's alike commits come from the same rebase done twice, and by whom.
#[derive(Debug, PartialEq, Eq)]
pub enum RebaseTwice {
    No,
    /// jj's own merge of one of the merges' parents made the same alike pair: jj's known
    /// repeat of a rebase after `jj op abandon` (docs/internals/races.md, "Known jj
    /// limitations").
    ByJj,
    /// Two of the hive's merges did it, and jj's merge of neither's parents does.
    ByMerges,
}

/// The pairs of merges in `rewrites` that rewrote one commit into commits with the same
/// structural key.
pub(super) fn repeated_rebases(
    rewrites: &[MergeRewrite],
    keys: &HashMap<CommitId, u64>,
) -> Vec<(OperationId, OperationId)> {
    let mut made: HashMap<(CommitId, u64), Vec<&MergeRewrite>> = HashMap::new();
    let mut pairs = vec![];
    for rewrite in rewrites {
        for predecessor in &rewrite.predecessors {
            let previous = made
                .entry((predecessor.clone(), keys[&rewrite.new]))
                .or_default();
            for other in previous.iter() {
                if other.operation != rewrite.operation && other.new != rewrite.new {
                    pairs.push((other.operation.clone(), rewrite.operation.clone()));
                }
            }
            previous.push(rewrite);
        }
    }
    pairs
}

impl Reference {
    /// A commit's change id as the view's `change_id` template prints it, which names a change
    /// in `alike_changes` and in the `change` that `same_rebase_twice` is asked about: the two
    /// must agree for jj's alike pair to be found.
    fn change_name(&mut self, id: &CommitId) -> String {
        self.facts(id).change.reverse_hex()
    }

    /// The changes with two visible commits alike in `view` (by structural key), as jj's own
    /// merge made them: recorded for each merge the reference replays, so that a repeated
    /// rebase jj makes too isn't taken for the hive's.
    pub(super) fn alike_changes(&mut self, view: &View) -> BTreeSet<String> {
        let visible: Vec<CommitId> = self.visible(view).iter().cloned().collect();
        let keys = self.keys(&visible, &|_| true);
        let mut seen: BTreeMap<(String, u64), usize> = BTreeMap::new();
        for id in &visible {
            let change = self.change_name(id);
            *seen.entry((change, keys[id])).or_default() += 1;
        }
        seen.into_iter()
            .filter(|(_, n)| *n > 1)
            .map(|((change, _), _)| change)
            .collect()
    }

    /// Whether two of the hive's independent merges rewrote one commit of `change` alike: into
    /// commits with the same contents, change id and parents (by structural key). That is the
    /// same rebase done twice, by two merges of the same operations, which the hub's
    /// sequencing exists to prevent. Two commits of a change can also end up alike when jj
    /// rebases two different rewrites of it onto the same parents, or when a command and a
    /// merge each rebase it the same way, as a `jj rebase -r` of its parent and a merge with
    /// a concurrent abandon of that parent do; neither is it. jj's own merge can also rebase
    /// the original again after `jj op abandon`, with the first result already in its inputs
    /// (docs/internals/races.md, "Known jj limitations"): where jj's replay of either merge
    /// has the same alike pair, the repeat is jj's.
    pub fn same_rebase_twice(&mut self, change: &str) -> RebaseTwice {
        let ours: Vec<_> = self
            .rewrites
            .clone()
            .into_iter()
            .filter(|rewrite| self.change_name(&rewrite.new) == change)
            .collect();
        let ids: Vec<CommitId> = ours.iter().map(|rewrite| rewrite.new.clone()).collect();
        let keys = self.keys(&ids, &|_| true);
        let pairs = repeated_rebases(&ours, &keys);
        rebase_twice(&pairs, &self.jj_alike, change)
    }
}

/// Who did the repeated rebases `pairs` of `change`: jj, if for each pair jj's own merge of
/// either merge's parents made the same alike pair of commits of `change` (`jj_alike`), and
/// else the hive's merges.
fn rebase_twice(
    pairs: &[(OperationId, OperationId)],
    jj_alike: &HashMap<OperationId, BTreeSet<String>>,
    change: &str,
) -> RebaseTwice {
    let by_jj = |op: &OperationId| {
        jj_alike
            .get(op)
            .is_some_and(|changes| changes.contains(change))
    };
    if pairs.is_empty() {
        RebaseTwice::No
    } else if pairs.iter().all(|(a, b)| by_jj(a) || by_jj(b)) {
        RebaseTwice::ByJj
    } else {
        RebaseTwice::ByMerges
    }
}

/// A repeated rebase is jj's own, so recorded and not failed, exactly where jj's own merge of
/// either merge's parents made the same alike pair of the change; a duplicate that jj's merge
/// didn't make is the hive's. Merges 1 and 2 rewrite the commit 10 into alike commits, as do 3
/// and 4 the commit 11, and 5 rewrites it into a different one.
#[test]
fn a_repeated_rebase_is_jjs_only_where_jjs_own_merge_made_it() {
    let op = |n: u8| OperationId::new(vec![n]);
    let commit = |n: u8| CommitId::new(vec![n]);
    let rewrite = |operation: u8, new: u8, old: u8| MergeRewrite {
        operation: op(operation),
        new: commit(new),
        predecessors: vec![commit(old)],
    };
    // The structural key of each new commit: 21 and 22 are alike, and 23 is not.
    let keys: HashMap<CommitId, u64> =
        HashMap::from([(commit(21), 7), (commit(22), 7), (commit(23), 8)]);
    let repeated = |rewrites: &[MergeRewrite]| repeated_rebases(rewrites, &keys);
    let jj_alike = |ops: &[u8], change: &str| -> HashMap<OperationId, BTreeSet<String>> {
        ops.iter()
            .map(|n| (op(*n), BTreeSet::from([change.to_owned()])))
            .collect()
    };

    let twice = repeated(&[rewrite(1, 21, 10), rewrite(2, 22, 10)]);
    assert_eq!(twice, [(op(1), op(2))]);
    let different = repeated(&[rewrite(1, 21, 10), rewrite(5, 23, 10)]);
    assert_eq!(
        rebase_twice(&different, &jj_alike(&[], "c"), "c"),
        RebaseTwice::No
    );

    // jj's own merge of either merge's parents made the pair: jj's repeat.
    for ops in [&[1][..], &[2], &[1, 2]] {
        assert_eq!(
            rebase_twice(&twice, &jj_alike(ops, "c"), "c"),
            RebaseTwice::ByJj
        );
    }
    // A duplicate jj's merges didn't make is the hive's: jj made no pair, a pair of another
    // change, or a pair at merges outside this one.
    for alike in [
        jj_alike(&[], "c"),
        jj_alike(&[1, 2], "other"),
        jj_alike(&[3, 4], "c"),
    ] {
        assert_eq!(rebase_twice(&twice, &alike, "c"), RebaseTwice::ByMerges);
    }
    // Every repeat must be jj's: one it didn't make fails the change.
    let both = repeated(&[
        rewrite(1, 21, 10),
        rewrite(2, 22, 10),
        rewrite(3, 21, 11),
        rewrite(4, 22, 11),
    ]);
    assert_eq!(both, [(op(1), op(2)), (op(3), op(4))]);
    assert_eq!(
        rebase_twice(&both, &jj_alike(&[1, 4], "c"), "c"),
        RebaseTwice::ByJj
    );
    assert_eq!(
        rebase_twice(&both, &jj_alike(&[1], "c"), "c"),
        RebaseTwice::ByMerges
    );
}

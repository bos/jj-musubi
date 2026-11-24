//! Detect independent merges that perform the same rebase twice, apart from jj's own repeat
//! of a rebase after `jj op abandon`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;

use super::Reference;
use crate::identity::SourceKey;

#[derive(Clone)]
pub(super) struct MergeRewrite {
    pub(super) operation: OperationId,
    pub(super) new: CommitId,
    pub(super) predecessors: Vec<CommitId>,
    /// For each of `predecessors`, the operations the merge brought to it, by source key
    /// (`brought_to`), or `None` where that is unknown or not all users' commands.
    pub(super) brought: Vec<Option<Arc<BTreeSet<SourceKey>>>>,
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

/// Whether a user's `jj` command made an operation of a parent's history, as the world
/// recorded it (`World::record_commands`). Merges, and what musubi writes itself, such as a
/// forget, are not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Origin {
    Command,
    Other,
}

/// What a merge brought to each of `predecessors`, the commits it rewrote (`brought_to`):
/// all unknown where `jj op abandon` gave the merge other parents, since it rewrote for its
/// original ones.
pub(super) fn brought_by_merge(
    predecessors: &[CommitId],
    reparented: bool,
    shown: &[Arc<HashSet<CommitId>>],
    histories: &[HashMap<SourceKey, Origin>],
) -> Vec<Option<Arc<BTreeSet<SourceKey>>>> {
    predecessors
        .iter()
        .map(|old| {
            (!reparented)
                .then(|| brought_to(old, shown, histories))
                .flatten()
        })
        .collect()
}

/// The operations a merge brought to `commit`, which it rewrote: the history of the merge's
/// parents whose views (`shown`, one for each parent, as `histories` has each parent's
/// history, itself included) don't show the commit, less the history of those that do. What
/// the merge did to the commit beyond what the parents showing it have, it did for those
/// operations: for one that removed or rewrote an ancestor of the commit, as an abandon of
/// its parent does. The operation that made the commit is in the history of the parents
/// showing it, so never among them. Operations go by source key, which canonicalization and
/// reparenting keep, so that one operation published twice is still one, without the
/// operation ids an undo, restore or revert names, which each copy writes differently
/// (`SourceKey::without_op_ids`). `None` where every parent shows the commit, or none does,
/// or what is left is nothing, so that which operations the merge brought to it is unknown,
/// or where any of them is not a user's command, so that two merges' could be the same work
/// musubi did twice.
pub(super) fn brought_to(
    commit: &CommitId,
    shown: &[Arc<HashSet<CommitId>>],
    histories: &[HashMap<SourceKey, Origin>],
) -> Option<Arc<BTreeSet<SourceKey>>> {
    let (with, without): (Vec<usize>, Vec<usize>) =
        (0..shown.len()).partition(|&i| shown[i].contains(commit));
    let held: HashSet<&SourceKey> = with.iter().flat_map(|&i| histories[i].keys()).collect();
    let mut brought = BTreeSet::new();
    for (key, origin) in without.iter().flat_map(|&i| &histories[i]) {
        if !held.contains(key) {
            if *origin != Origin::Command {
                return None;
            }
            brought.insert(key.clone());
        }
    }
    (!with.is_empty() && !brought.is_empty()).then(|| Arc::new(brought))
}

/// Whether two merges that rewrote one commit brought it operations of which none is the
/// other's (`brought_to`): each rewrote it for users' commands of its own, as when one merges
/// a concurrent abandon of its parent and the other another machine's concurrent command that
/// also removes that parent, which jj's merge of the two lines rebases alike too. The same
/// removal merged into two lines that show the commit is in what both merges brought, as is
/// everything where two merges have the same parents, so those still count as the same
/// rebase twice; so does a pair where either's is unknown. What this can't see is the
/// operation that made the commit merged into two lines, since neither merge brought it: that
/// a node merges only what is its own to merge is Locality and MergeOwnership
/// (docs/internals/protocol.md, "Properties"), which `formal/Musubi/Safety.lean` proves of
/// the model and the protocol property tests check of the code after every step
/// (`crates/musubi-core/tests/support/world/properties.rs`).
fn brought_apart(
    a: Option<&Arc<BTreeSet<SourceKey>>>,
    b: Option<&Arc<BTreeSet<SourceKey>>>,
) -> bool {
    a.zip(b).is_some_and(|(a, b)| a.is_disjoint(b))
}

/// The pairs of merges in `rewrites` that rewrote one commit into commits with the same
/// structural key, bringing it operations in common (`brought_apart`).
pub(super) fn repeated_rebases(
    rewrites: &[MergeRewrite],
    keys: &HashMap<CommitId, u64>,
) -> Vec<(OperationId, OperationId)> {
    type Seen<'a> = (&'a MergeRewrite, Option<&'a Arc<BTreeSet<SourceKey>>>);
    let mut made: HashMap<(CommitId, u64), Vec<Seen<'_>>> = HashMap::new();
    let mut pairs = vec![];
    for rewrite in rewrites {
        for (i, predecessor) in rewrite.predecessors.iter().enumerate() {
            let brought = rewrite.brought.get(i).and_then(Option::as_ref);
            let previous = made
                .entry((predecessor.clone(), keys[&rewrite.new]))
                .or_default();
            for (other, other_brought) in previous.iter() {
                if other.operation != rewrite.operation
                    && other.new != rewrite.new
                    && !brought_apart(*other_brought, brought)
                {
                    pairs.push((other.operation.clone(), rewrite.operation.clone()));
                }
            }
            previous.push((rewrite, brought));
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
    /// commits with the same contents, change id and parents (by structural key), where what
    /// they brought to it isn't known to be users' commands of their own (`brought_apart`).
    /// That catches the same removal of an ancestor of the commit merged twice, and two merges
    /// of the same parents: the same rebase done twice, which the hub's sequencing exists to
    /// prevent. Two commits of a change can also end up alike when jj rebases two different
    /// rewrites of it onto the same parents, when a command and a merge each rebase it the
    /// same way, as a `jj rebase -r` of its parent and a merge with a concurrent abandon of
    /// that parent do, or when two merges each bring it a different user's command that
    /// removes its parent, as two machines' abandons of the parent do; none is it. jj's own
    /// merge can also rebase the original again after `jj op abandon`, with the first result
    /// already in its inputs (docs/internals/races.md, "Known jj limitations"): where jj's
    /// replay of either merge has the same alike pair, the repeat is jj's.
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
        brought: vec![None],
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

/// Two merges rewrote one commit alike for the same operation only if what each brought to it
/// has an operation in common. The hive's history: 1 made the commit 10 visible, and 2 and 3
/// are each a user's concurrent command beside 1 that removes 10's parent, as `jj abandon`
/// does, or a `jj squash` of a rewrite of it; 40 and 41 are each a forget musubi wrote that
/// does the same to a working-copy commit. Merge 5 merges 1 and 2, as does 4; 6 merges 1 and
/// 3; 7 merges 1 with a command 8 above 2; 9 merges 1 and 40, and 11 merges 1 and 41. Each
/// rebases 10 onto the same parent, into alike commits 21, 22 and 23.
#[test]
fn merges_rebase_one_commit_twice_only_for_an_operation_both_brought() {
    let op = |n: u8| SourceKey::from_template(&n.to_string());
    let merge = |n: u8| OperationId::new(vec![n]);
    let commit = |n: u8| CommitId::new(vec![n]);
    // Operations from 40 on are musubi's own.
    let ops = |ns: &[u8]| -> HashMap<SourceKey, Origin> {
        ns.iter()
            .map(|n| {
                (
                    op(*n),
                    if *n < 40 {
                        Origin::Command
                    } else {
                        Origin::Other
                    },
                )
            })
            .collect()
    };
    let shown = |ns: &[u8]| Arc::new(ns.iter().map(|n| commit(*n)).collect::<HashSet<_>>());
    // Each merge's parents: the one with 10, at 1, and the one without.
    let with_10 = shown(&[9, 10]);
    let without = shown(&[9]);
    let parents = [with_10.clone(), without.clone()];
    let brought = |other: &[u8]| brought_to(&commit(10), &parents, &[ops(&[0, 1]), ops(other)]);
    assert_eq!(*brought(&[0, 2]).unwrap(), BTreeSet::from([op(2)]));
    assert_eq!(
        *brought(&[0, 2, 8]).unwrap(),
        BTreeSet::from([op(2), op(8)])
    );
    // A parent whose history the other's holds brings nothing: what the merge did is unknown.
    assert_eq!(brought(&[0]), None);
    // Anything musubi wrote itself among what a merge brought leaves it unknown.
    assert_eq!(brought(&[0, 40]), None);
    assert_eq!(brought(&[0, 2, 40]), None);
    // Where both parents show the commit, or neither does, the merge brought nothing known.
    for parents in [
        [with_10.clone(), with_10.clone()],
        [without.clone(), without.clone()],
    ] {
        assert_eq!(
            brought_to(&commit(10), &parents, &[ops(&[0, 1]), ops(&[0, 2])]),
            None
        );
    }
    // A merge `jj op abandon` gave other parents brought nothing known to any commit.
    let histories = [ops(&[0, 1]), ops(&[0, 2])];
    let predecessors = [commit(10), commit(9)];
    assert_eq!(
        brought_by_merge(&predecessors, true, &parents, &histories),
        [None, None]
    );
    assert_eq!(
        brought_by_merge(&predecessors, false, &parents, &histories),
        [brought(&[0, 2]), None]
    );
    // An undo, restore or revert names an operation differently in each copy: one key.
    assert_eq!(
        SourceKey::from_template("1 2 restore to operation 0123abcd").without_op_ids(),
        SourceKey::from_template("1 2 restore to operation 4567ef89").without_op_ids()
    );

    let keys: HashMap<CommitId, u64> =
        HashMap::from([(commit(21), 7), (commit(22), 7), (commit(23), 7)]);
    let rewrite = |operation: u8, new: u8, brought| MergeRewrite {
        operation: merge(operation),
        new: commit(new),
        predecessors: vec![commit(10)],
        brought: vec![brought],
    };
    let pairs = |rewrites: &[MergeRewrite]| repeated_rebases(rewrites, &keys);
    // 5 and 6 brought 10 different commands: no repeat.
    assert!(
        pairs(&[
            rewrite(5, 21, brought(&[0, 2])),
            rewrite(6, 22, brought(&[0, 3]))
        ])
        .is_empty()
    );
    // 5 and 7 both brought 2, as 5 and 4, with the same parents, do: the same rebase twice.
    for (other, all) in [(7, &[0, 2, 8][..]), (4, &[0, 2])] {
        assert_eq!(
            pairs(&[
                rewrite(5, 21, brought(&[0, 2])),
                rewrite(other, 23, brought(all))
            ]),
            [(merge(5), merge(other))]
        );
    }
    // What a merge brought unknown, a repeat can't be ruled out: nor where 9 and 11 each
    // brought a forget of musubi's.
    assert_eq!(
        pairs(&[rewrite(5, 21, brought(&[0, 2])), rewrite(6, 22, None)]),
        [(merge(5), merge(6))]
    );
    assert_eq!(
        pairs(&[
            rewrite(9, 21, brought(&[0, 40])),
            rewrite(11, 22, brought(&[0, 41]))
        ]),
        [(merge(9), merge(11))]
    );
}

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
    /// The changes with two visible commits alike in `view` (by structural key), as jj's own
    /// merge made them: recorded for each merge the reference replays, so that a repeated
    /// rebase jj makes too isn't taken for the hive's.
    pub(super) fn alike_changes(&mut self, view: &View) -> BTreeSet<String> {
        let visible: Vec<CommitId> = self.visible(view).iter().cloned().collect();
        let keys = self.keys(&visible, &|_| true);
        let mut seen: BTreeMap<(String, u64), usize> = BTreeMap::new();
        for id in &visible {
            let change = self.facts(id).change.reverse_hex();
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
            .filter(|rewrite| self.facts(&rewrite.new).change.reverse_hex() == change)
            .collect();
        let ids: Vec<CommitId> = ours.iter().map(|rewrite| rewrite.new.clone()).collect();
        let keys = self.keys(&ids, &|_| true);
        let pairs = repeated_rebases(&ours, &keys);
        let by_jj = |op: &OperationId| {
            self.jj_alike
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
}

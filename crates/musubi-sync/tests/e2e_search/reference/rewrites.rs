//! Detect independent merges that perform the same rebase twice.
//!
//! A repeated native serial rebase is allowed only when an independent native replay
//! certifies its entire shared result and exact predecessor relation.

use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

use jj_lib::backend::CommitId;
use jj_lib::op_store;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::View;
use musubi_jj::op_id::CanonicalOp;

use super::Reference;
use super::comparison::Summary;
use super::replay::Replayed;

#[derive(Clone)]
pub(super) struct MergeRewrite {
    pub(super) operation: OperationId,
    pub(super) new: CommitId,
    pub(super) predecessors: Vec<CommitId>,
    /// Inputs of an independently replayed native merge that made this exact rewrite.
    /// A result already visible there was not made by an independent concurrent merge.
    pub(super) native_inputs: Arc<HashSet<CommitId>>,
}

/// Whether the native replay certifies this rewrite, including its complete shared result.
pub(super) fn native_rebase_matches<'a>(
    results: (&Summary, &Summary),
    key: u64,
    predecessors: &[CommitId],
    native: impl IntoIterator<Item = (u64, &'a [CommitId])>,
) -> bool {
    results.0 == results.1
        && native.into_iter().any(|(native_key, native_predecessors)| {
            native_key == key && native_predecessors == predecessors
        })
}

pub(super) fn repeated_rebase(rewrites: &[MergeRewrite], keys: &HashMap<CommitId, u64>) -> bool {
    let mut made: HashMap<(CommitId, u64), Vec<&MergeRewrite>> = HashMap::new();
    for rewrite in rewrites {
        for predecessor in &rewrite.predecessors {
            let previous = made
                .entry((predecessor.clone(), keys[&rewrite.new]))
                .or_default();
            if previous.iter().any(|other| {
                other.operation != rewrite.operation
                    && other.new != rewrite.new
                    && !rewrite.native_inputs.contains(&other.new)
                    && !other.native_inputs.contains(&rewrite.new)
            }) {
                return true;
            }
            previous.push(rewrite);
        }
    }
    false
}

impl Reference {
    /// Record inputs only when an independent native replay has the entire shared result
    /// and the exact predecessor relation. Neither ancestry, a retained view, nor an
    /// earlier result visible in a parent alone certifies a serial native rebase.
    pub(super) fn certify_serial_rebases(
        &mut self,
        id: &CanonicalOp,
        op: &op_store::Operation,
        replayed: &Replayed,
        parents: &[CanonicalOp],
        views: &HashMap<CanonicalOp, View>,
        results: (&Summary, &Summary),
    ) {
        let native = &replayed.op.store_operation().commit_predecessors;
        let new: Vec<_> = op
            .commit_predecessors
            .iter()
            .flatten()
            .chain(native.iter().flatten())
            .map(|(new, _)| new.clone())
            .collect();
        let keys = self.keys(&new, &|_| true);
        let mut inputs = HashSet::new();
        for parent in parents {
            inputs.extend(self.visible(&views[parent]).iter().cloned());
        }
        let inputs = Arc::new(inputs);
        for rewrite in self.rewrites.iter_mut().filter(|r| r.operation == id.0) {
            if native_rebase_matches(
                results,
                keys[&rewrite.new],
                &rewrite.predecessors,
                native
                    .iter()
                    .flatten()
                    .map(|(new, predecessors)| (keys[new], predecessors.as_slice())),
            ) {
                rewrite.native_inputs = inputs.clone();
            }
        }
    }

    /// Whether two of the hive's independent merges rewrote one commit of `change` alike: into
    /// commits with the same contents, change id and parents (by structural key). That is the
    /// same rebase done twice, by two merges of the same operations, which the hub's
    /// sequencing exists to prevent. Two commits of a change can also end up alike when jj
    /// rebases two different rewrites of it onto the same parents, or when a command and a
    /// merge each rebase it the same way, as a `jj rebase -r` of its parent and a merge with
    /// a concurrent abandon of that parent do; neither is it. A native merge can also rebase
    /// the original again after an operation abandon, with the first result already visible
    /// in its inputs. Only an independently replayed full result and predecessor relation
    /// certify that serial case; independent duplicate merges remain forbidden.
    pub fn same_rebase_twice(&mut self, change: &str) -> bool {
        let ours: Vec<_> = self
            .rewrites
            .clone()
            .into_iter()
            .filter(|rewrite| self.facts(&rewrite.new).change.reverse_hex() == change)
            .collect();
        let ids: Vec<CommitId> = ours.iter().map(|rewrite| rewrite.new.clone()).collect();
        let keys = self.keys(&ids, &|_| true);
        repeated_rebase(&ours, &keys)
    }
}

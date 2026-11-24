//! jj merge semantics, feasibility checks, and diagnosis of unmergeable local history.
//!
//! This module owns the remembered diagnosis across sync retries. It does not publish op
//! heads: the advancement module controls the publication and lock boundary.

use std::collections::HashSet;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;

use futures::TryStreamExt as _;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_walk;
use jj_lib::operation::Operation;
use jj_lib::repo::ReadonlyRepo;
use jj_lib::repo::Repo as _;
use jj_lib::repo::RepoLoader;
use pollster::FutureExt as _;

use super::super::NodeError;
use super::super::NodeRepo;
use super::super::catch_jj_panic;
use super::super::view::PerMachine;
use crate::op_attrs::OpAttrs;
use crate::op_id::CanonicalOp;
use crate::op_id::LocalOp;

#[derive(Default)]
pub(in crate::node) struct MergeDiagnosis(Mutex<UnmergeableMemo>);

impl MergeDiagnosis {
    pub(in crate::node) fn keep_from(&mut self, previous: &Self) {
        let previous = previous
            .0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        *self.0.lock().unwrap_or_else(PoisonError::into_inner) = previous;
    }

    pub(in crate::node) fn searches(&self) -> usize {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .searches
    }
}

#[derive(Clone, Default)]
struct UnmergeableMemo {
    last: Option<UnmergeableSearch>,
    /// The last op heads jj couldn't merge, and the one of them to revert, if found: they
    /// stay so until someone reverts one, and each search writes operations.
    last_heads: Option<(Vec<LocalOp>, Option<LocalOp>)>,
    searches: usize,
}

#[derive(Clone)]
struct UnmergeableSearch {
    heads: Vec<LocalOp>,
    theirs: CanonicalOp,
    culprit: Option<LocalOp>,
}

impl NodeRepo {
    /// The per-machine fields a realization starts from: its parent's, or for a merge, the
    /// parents' merged three-way as jj merges them, as a local merge of the same operations
    /// would.
    pub(super) fn inherited_per_machine(
        &self,
        parents: &[LocalOp],
    ) -> Result<Arc<PerMachine>, NodeError> {
        if let ([parent], Some((last, per_machine))) = (parents, self.realizing.last_realized())
            && parent == last
        {
            return Ok(per_machine.clone());
        }
        let (first, rest) = parents.split_first().expect("operations have parents");
        let first_op = self.loader.load_operation(&first.0).block_on()?;
        if rest.is_empty() {
            return Ok(Arc::new(fields_of(&first_op)?));
        }
        // jj's merge loads each parent's repository, and so its index, which for a join
        // operation, whose only ancestor is the root, means indexing all its commits anew: a
        // second or more for a large repository. Usually it isn't needed.
        if let Some(merged) = self.merged_trivially(&first_op, rest)? {
            debug_assert_eq!(*merged, *merged_by_jj(&self.loader, first_op, rest)?);
            return Ok(merged);
        }
        merged_by_jj(&self.loader, first_op, rest)
    }

    /// The per-machine fields of `first_op` and `rest` merged three-way, if at most one of
    /// them differs from its base, which the merge then takes: another machine's join
    /// operation's are its base's, the root's, as, usually, are those of other machines'
    /// operations. `None` where jj's merge must decide (`PerMachine::merged_trivially`), or
    /// where a merge has several bases or changes workspace names: jj's workspace cleanup
    /// can remove a Git HEAD record even when none of the per-machine fields changed.
    pub(super) fn merged_trivially(
        &self,
        first_op: &Operation,
        rest: &[LocalOp],
    ) -> Result<Option<Arc<PerMachine>>, NodeError> {
        let first_view = first_op.view().block_on()?;
        let mut merged = PerMachine::of(first_view.store_view());
        let mut ops = vec![first_op.clone()];
        for other in rest {
            let other_op = self.loader.load_operation(&other.0).block_on()?;
            // Several bases would need jj's merge of them, which costs what this saves.
            let Some(base) = single_base(&self.loader, &ops, &other_op)? else {
                return Ok(None);
            };
            let base_view = base.view().block_on()?;
            let other_view = other_op.view().block_on()?;
            if !first_view
                .store_view()
                .wc_commit_ids
                .keys()
                .eq(base_view.store_view().wc_commit_ids.keys())
                || !other_view
                    .store_view()
                    .wc_commit_ids
                    .keys()
                    .eq(base_view.store_view().wc_commit_ids.keys())
            {
                return Ok(None);
            }
            let (base, theirs) = (
                PerMachine::of(base_view.store_view()),
                PerMachine::of(other_view.store_view()),
            );
            match PerMachine::merged_trivially(&base, merged, theirs) {
                Some(next) => merged = next,
                None => return Ok(None),
            }
            ops.push(other_op);
        }
        Ok(Some(Arc::new(merged)))
    }

    /// The realization `head` merged with this machine's concurrent op heads `theirs`, as
    /// jj merges op heads on loading them, in order of their end times, into an operation
    /// written but not published.
    pub(super) fn merge_unpublished(
        &self,
        head: &LocalOp,
        theirs: &[Operation],
    ) -> Result<LocalOp, String> {
        let mut operations = theirs.to_vec();
        operations.push(
            self.loader
                .load_operation(&head.0)
                .block_on()
                .map_err(|err| format!("{err:#}"))?,
        );
        operations.sort_by_key(|op| op.metadata().time.end.timestamp);
        catch_jj_panic(|| {
            self.loader
                .merge_operations(operations, None, Some("reconcile divergent operations"), [])
                .block_on()
                .map(|(repo, _)| LocalOp(repo.op_id().clone()))
                .map_err(|err| format!("{err:#}"))
        })
    }

    /// Refuses to publish a realization that jj cannot merge with this machine's own
    /// concurrent operations, the op heads `heads`. Published, it would be merged by every `jj`
    /// command here, and each would fail, or for some jj bugs panic, until someone reverted an
    /// operation by hand. Unpublished, jj keeps working, and the error says which operations to
    /// revert. Returns the op heads the realization descends from, beyond its parents, which
    /// are not concurrent with it, as the previous head is after a catch-up;
    /// and those that are.
    pub(super) fn check_mergeable(
        &self,
        canonical: &CanonicalOp,
        realized: &LocalOp,
        heads: &[LocalOp],
    ) -> Result<(Vec<LocalOp>, Vec<Operation>), NodeError> {
        let realized_op = self.loader.load_operation(&realized.0).block_on()?;
        let mut heads = heads.to_vec();
        let others: Vec<LocalOp> = heads
            .iter()
            .filter(|head| *head != realized && !realized_op.parent_ids().contains(&head.0))
            .cloned()
            .collect();
        let mut theirs = vec![];
        let mut superseded = vec![];
        for head in others {
            let op = self.loader.load_operation(&head.0).block_on()?;
            // Nothing of its own that the realization lacks: an ancestor.
            let beyond = std::pin::pin!(op_walk::walk_ancestors_range(
                std::slice::from_ref(&op),
                std::slice::from_ref(&realized_op),
            ))
            .try_next()
            .block_on()?;
            match beyond {
                None => superseded.push(head),
                Some(_) => theirs.push(op),
            }
        }
        if theirs.is_empty() {
            return Ok((superseded, theirs));
        }
        // This machine's operations that the hive doesn't have: one of them conflicts.
        let roots = realized_op.parents().block_on()?;
        let ours: Vec<LocalOp> = op_walk::walk_ancestors_range(&theirs, &roots)
            .map_ok(|op| LocalOp(op.id().clone()))
            .try_collect()
            .block_on()?;
        let mut operations = theirs.clone();
        operations.push(realized_op.clone());
        if let Err(reason) = self.try_merge(operations) {
            // The same heads and the hive's same operation, as when the sync is retried,
            // give the same result. Failing to find it leaves the advice to list them.
            heads.sort();
            let mut memo = self
                .merge_diagnosis
                .0
                .lock()
                .unwrap_or_else(PoisonError::into_inner);
            let culprit = match &memo.last {
                Some(last) if last.heads == heads && last.theirs == *canonical => {
                    last.culprit.clone()
                }
                _ => {
                    memo.searches += 1;
                    // An error, as reading the store, is no answer to keep.
                    // Failing a single revert that will do, one that will help.
                    let culprit = self
                        .op_to_revert(&theirs, &ours, &realized_op)
                        .and_then(|found| match found {
                            Some(op) => Ok(Some(op)),
                            None => self.first_unmergeable(&ours, &realized_op),
                        })
                        .ok();
                    if let Some(culprit) = &culprit {
                        memo.last = Some(UnmergeableSearch {
                            heads,
                            theirs: canonical.clone(),
                            culprit: culprit.clone(),
                        });
                    }
                    culprit.flatten()
                }
            };
            drop(memo);
            return Err(self.unmergeable(&ours, culprit, reason));
        }
        Ok((superseded, theirs))
    }

    /// Whether jj can merge `operations` without failing or panicking. jj merges op heads in
    /// order of their end times, and the result can depend on the order, so this tries that
    /// order, and the reverse too: equal times sort either way.
    fn try_merge(&self, mut operations: Vec<Operation>) -> Result<(), String> {
        operations.sort_by_key(|op| op.metadata().time.end.timestamp);
        let reversed: Vec<_> = operations.iter().rev().cloned().collect();
        for order in [operations, reversed] {
            catch_jj_panic(|| {
                self.loader
                    .merge_operations(order, None, Some("reconcile divergent operations"), [])
                    .block_on()
                    .map(|_| ())
                    .map_err(|err| format!("{err:#}"))
            })?;
        }
        Ok(())
    }

    /// Of this machine's operations the hive doesn't have, `ours` (newest first), the newest
    /// whose revert lets jj merge the hive's operation `realized`: the one to revert. Each
    /// is reverted as `jj op revert` would, on top of this machine's op heads, `heads`,
    /// merged, into an operation written but not published (though it rebases immutable
    /// commits too, where `jj op revert` leaves them), and that merged with `realized`.
    /// Newest first, since reverting an operation whose result was rewritten since leaves
    /// it divergent, which can untie the loop where reverting the rewrite would be cleaner.
    /// Skips merges, which `jj op revert` refuses, operations already reverted, and those
    /// that leave the commit graph as it was, which can't make a loop. `None` if no single
    /// revert will do, as when several of this machine's operations each loop with the
    /// hive's.
    fn op_to_revert(
        &self,
        heads: &[Operation],
        ours: &[LocalOp],
        realized: &Operation,
    ) -> Result<Option<LocalOp>, NodeError> {
        // Where `jj op revert` starts: jj's merge of the op heads, in jj's order, as any
        // command loads them.
        let mut heads = heads.to_vec();
        heads.sort_by_key(|op| op.metadata().time.end.timestamp);
        let Ok(Ok(head)) = catch_jj_panic(|| {
            Ok(self
                .loader
                .merge_operations(heads, None, Some("reconcile divergent operations"), [])
                .block_on())
        }) else {
            return Ok(None);
        };
        let head = head.0;
        let mut ops = vec![];
        for id in ours {
            ops.push(self.loader.load_operation(&id.0).block_on()?);
        }
        let reverted = reverted_by(&ops);
        for op in &ops {
            if op.parent_ids().len() != 1 || reverted.contains(&op.id().hex()) {
                continue;
            }
            let parent = op.parents().block_on()?.remove(0);
            if op.view().block_on()?.heads() == parent.view().block_on()?.heads() {
                continue;
            }
            let Some(revert_op) = self.revert_on(&head, op, &parent)? else {
                continue;
            };
            if self.try_merge(vec![revert_op, realized.clone()]).is_ok() {
                return Ok(Some(LocalOp(op.id().clone())));
            }
        }
        Ok(None)
    }

    /// `op`, whose parent is `parent`, reverted as `jj op revert` would on top of `head`, into
    /// an operation written but not published (though it rebases immutable commits too, where
    /// `jj op revert` leaves them). `None` if jj fails or panics reverting it.
    fn revert_on(
        &self,
        head: &Arc<ReadonlyRepo>,
        op: &Operation,
        parent: &Operation,
    ) -> Result<Option<Operation>, NodeError> {
        let (at_op, at_parent) = (
            self.loader.load_at(op).block_on()?,
            self.loader.load_at(parent).block_on()?,
        );
        let revert_op = catch_jj_panic(|| {
            let mut tx = head.start_transaction();
            Ok(async {
                tx.repo_mut().merge(&at_op, &at_parent).await?;
                // `jj op revert` keeps git's refs as they are.
                let mut view = tx.repo().view().store_view().clone();
                view.git_refs = head.view().store_view().git_refs.clone();
                view.git_heads = head.view().store_view().git_heads.clone();
                tx.repo_mut().set_view(view);
                tx.repo_mut().rebase_descendants().await?;
                let reverted = tx
                    .write(format!("revert operation {}", op.id().hex()))
                    .await?;
                Ok::<_, NodeError>(reverted.leave_unpublished().operation().clone())
            }
            .block_on())
        });
        Ok(match revert_op {
            Ok(Ok(revert_op)) => Some(revert_op),
            _ => None,
        })
    }

    /// The error for op heads `heads` that jj can't merge, failing for `reason`: as when a
    /// `jj` command that loaded the repository before musubi realized the hive's operations
    /// commits a rebase beside them that loops with one of them (#172). Every `jj` command
    /// here then fails or panics, `jj op log` and a plain `jj op revert` included, so the
    /// error names the operation to revert at itself: the newest op head of this machine's
    /// own, not a realization, a merge or a checkpoint, whose revert, on top of it, jj can
    /// merge with the other heads. Failing one, it lists this machine's own op heads.
    pub(in crate::node) fn unmergeable_heads(
        &self,
        heads: &[LocalOp],
        reason: String,
    ) -> NodeError {
        let mut own = vec![];
        for head in heads {
            let Ok(op) = self.loader.load_operation(&head.0).block_on() else {
                continue;
            };
            let attrs = OpAttrs(&op.metadata().attributes);
            if op.parent_ids().len() == 1 && !attrs.has_original_parents() && !attrs.is_checkpoint()
            {
                own.push(op);
            }
        }
        own.sort_by(|a, b| {
            (b.metadata().time.end.timestamp, b.id())
                .cmp(&(a.metadata().time.end.timestamp, a.id()))
        });
        let ours: Vec<LocalOp> = own.iter().map(|op| LocalOp(op.id().clone())).collect();
        let mut sorted_heads = heads.to_vec();
        sorted_heads.sort();
        let memo = self
            .merge_diagnosis
            .0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .last_heads
            .clone();
        let culprit = match memo {
            Some((last, culprit)) if last == sorted_heads => culprit,
            _ => {
                let culprit = own.iter().find_map(|op| self.revert_merges(heads, op));
                let mut memo = self
                    .merge_diagnosis
                    .0
                    .lock()
                    .unwrap_or_else(PoisonError::into_inner);
                memo.searches += 1;
                memo.last_heads = Some((sorted_heads, culprit.clone()));
                culprit
            }
        };
        let revert = |id: &LocalOp| {
            let short = &id.0.hex()[..12];
            format!("`jj --at-op {short} op revert {short}`")
        };
        let advice = match (&culprit, ours.is_empty()) {
            (Some(op), _) => format!(
                "To go on, revert this machine's operation {} with {}. That undoes only what it \
                 did, and what other machines did stays; musubi then catches up",
                self.describe(op),
                revert(op)
            ),
            (None, false) => {
                let listed: Vec<String> = ours.iter().map(|op| self.describe(op)).collect();
                format!(
                    "To go on, revert this machine's own operations among the heads one at a \
                     time, newest first ({}), with `jj --at-op <id> op revert <id>`, until \
                     `jj status` works again",
                    listed.join(", ")
                )
            }
            (None, true) => "None of the heads is an operation of this machine's own to revert, \
                             which is a bug: please report it with this message"
                .to_owned(),
        };
        NodeError::UnmergeableHeads {
            ours,
            culprit,
            advice,
            reason,
        }
    }

    /// `op`, one of the op heads `heads`, if reverting it on top of itself, as
    /// `jj --at-op <op> op revert <op>` does, lets jj merge the result with the other heads.
    fn revert_merges(&self, heads: &[LocalOp], op: &Operation) -> Option<LocalOp> {
        let mut operations = heads
            .iter()
            .filter(|head| head.0 != *op.id())
            .map(|head| self.loader.load_operation(&head.0).block_on())
            .collect::<Result<Vec<_>, _>>()
            .ok()?;
        let parent = op.parents().block_on().ok()?.remove(0);
        let at_op = self.loader.load_at(op).block_on().ok()?;
        operations.push(self.revert_on(&at_op, op, &parent).ok()??);
        self.try_merge(operations)
            .is_ok()
            .then(|| LocalOp(op.id().clone()))
    }

    /// An operation's short id and description, as an error names it.
    fn describe(&self, id: &LocalOp) -> String {
        let description = self
            .loader
            .load_operation(&id.0)
            .block_on()
            .map(|op| op.metadata().description.clone())
            .unwrap_or_default();
        format!("{} ({description})", &id.0.hex()[..12])
    }

    /// Of this machine's operations the hive doesn't have, `ours` (newest first), the oldest
    /// whose own change jj panics merging with the hive's operation `realized`: one to revert
    /// first where no single revert will do. Each operation's change, from its parent, is
    /// merged with `realized` alone, both ways round, since the result can depend on which
    /// side the merge starts from, in a transaction never committed (though the rebased
    /// commits are written). Merged whole instead, every operation after the one to revert
    /// would fail too, carrying its change, though reverting them wouldn't help. Skips
    /// merges, which `jj op revert` refuses, and operations already reverted. `None` if no
    /// change panics alone, as when the loop needs several of them.
    fn first_unmergeable(
        &self,
        ours: &[LocalOp],
        realized: &Operation,
    ) -> Result<Option<LocalOp>, NodeError> {
        let mut ops = vec![];
        for id in ours.iter().rev() {
            ops.push(self.loader.load_operation(&id.0).block_on()?);
        }
        let reverted = reverted_by(&ops);
        let at_realized = self.loader.load_at(realized).block_on()?;
        for op in &ops {
            if op.parent_ids().len() != 1 || reverted.contains(&op.id().hex()) {
                continue;
            }
            let parent = op.parents().block_on()?.remove(0);
            let at_op = self.loader.load_at(op).block_on()?;
            // A panic is jj failing on a loop. An error doesn't say which operation to
            // revert: from the parent, this machine's earlier work looks abandoned on the
            // hive's side, which can itself fail, as for a merge commit on the root. `None`
            // for an error, which passes over the operation: only a loop panics.
            let panics = |repo: &Arc<ReadonlyRepo>, other: &Operation| {
                let merged = catch_jj_panic(|| {
                    let mut tx = repo.start_transaction();
                    Ok(async {
                        tx.merge_operation(&parent, other).await?;
                        tx.repo_mut().rebase_descendants().await?;
                        Ok::<_, NodeError>(())
                    }
                    .block_on())
                });
                match merged {
                    Ok(Ok(())) => Some(false),
                    Ok(Err(_)) => None,
                    Err(_) => Some(true),
                }
            };
            let panicked = match panics(&at_op, realized) {
                Some(false) => panics(&at_realized, op),
                other => other,
            };
            if panicked == Some(true) {
                return Ok(Some(LocalOp(op.id().clone())));
            }
        }
        Ok(None)
    }

    /// The error for operations of this machine's, `ours` (newest first), that jj can't
    /// merge with the hive's, `culprit` being the one to revert if known.
    pub(in crate::node) fn unmergeable(
        &self,
        ours: &[LocalOp],
        culprit: Option<LocalOp>,
        reason: String,
    ) -> NodeError {
        const SHOWN: usize = 5;
        let describe = |id: &LocalOp| self.describe(id);
        let advice = match &culprit {
            Some(op) => format!(
                "To go on, revert this machine's operation {} with `jj op revert {}`: \
                 musubi then catches up, or names another to revert",
                describe(op),
                &op.0.hex()[..12]
            ),
            None => {
                let mut listed: Vec<String> = ours.iter().take(SHOWN).map(describe).collect();
                if ours.len() > SHOWN {
                    listed.push(format!("and {} older", ours.len() - SHOWN));
                }
                format!(
                    "To go on, revert this machine's operation that conflicts with them, one \
                     of those the hive doesn't have yet (newest first: {}), with \
                     `jj op revert <id>`; musubi then catches up",
                    listed.join(", ")
                )
            }
        };
        NodeError::Unmergeable {
            ours: ours.to_vec(),
            culprit,
            advice,
            reason,
        }
    }
}

/// The operations that those of `ops` that `jj op revert` wrote reverted, by hex id: it
/// describes what it writes so.
fn reverted_by(ops: &[Operation]) -> HashSet<String> {
    ops.iter()
        .filter_map(|op| op.metadata().description.strip_prefix("revert operation "))
        .map(str::to_owned)
        .collect()
}

/// The per-machine fields of a local operation's view.
pub(super) fn fields_of(op: &Operation) -> Result<PerMachine, NodeError> {
    Ok(PerMachine::of(op.view().block_on()?.store_view()))
}

/// The per-machine fields of `first_op` and `rest` merged three-way by jj.
pub(in crate::node) fn merged_by_jj(
    loader: &RepoLoader,
    first_op: Operation,
    rest: &[LocalOp],
) -> Result<Arc<PerMachine>, NodeError> {
    let repo = loader.load_at(&first_op).block_on()?;
    let mut tx = repo.start_transaction();
    let mut merged = vec![first_op];
    for other in rest {
        let other_op = loader.load_operation(&other.0).block_on()?;
        let base = merge_base(loader, &merged, &other_op)?;
        tx.merge_operation(&base, &other_op).block_on()?;
        merged.push(other_op);
    }
    Ok(Arc::new(PerMachine::of(tx.repo().view().store_view())))
}

/// The closest common ancestor of `ops` and `other`, or the root if they have none; `None`
/// if they have several.
fn single_base(
    loader: &RepoLoader,
    ops: &[Operation],
    other: &Operation,
) -> Result<Option<Operation>, NodeError> {
    let mut bases = op_walk::closest_common_ancestors(ops.to_vec(), [other.clone()]).block_on()?;
    Ok(match bases.len() {
        0 => Some(loader.root_operation().block_on()),
        1 => Some(bases.remove(0)),
        _ => None,
    })
}

/// The base a merge of `ops` with `other` merges three-way against, as jj's
/// `merge_operations` has it: their closest common ancestor, or where there are several,
/// as in a criss-cross merge, those merged first, recursively, into an operation that is
/// written but not published. Against the first of them instead, a merged record can be a
/// conflict that matches neither `.git` nor jj's merge, which the export can't correct and
/// the next import merges into the bookmark (`firstBase_reverts` in
/// formal/Musubi/Refs.lean).
fn merge_base(
    loader: &RepoLoader,
    ops: &[Operation],
    other: &Operation,
) -> Result<Operation, NodeError> {
    let mut bases = op_walk::closest_common_ancestors(ops.to_vec(), [other.clone()]).block_on()?;
    match bases.len() {
        0 => return Ok(loader.root_operation().block_on()),
        1 => return Ok(bases.remove(0)),
        _ => {}
    }
    let first = bases[0].clone();
    // jj's merge rebases descendants, which can panic, as in `merge_heads`; jj's own merge
    // of these operations would too. Then the first base, as musubi had before.
    match catch_jj_panic(|| Ok(loader.merge_operations(bases, None, None, []).block_on())) {
        Ok(merged) => Ok(merged?.0.operation().clone()),
        Err(reason) => {
            tracing::warn!("merging the bases of a criss-cross merge: {reason}");
            Ok(first)
        }
    }
}

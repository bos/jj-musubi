//! Moving op heads that musubi read earlier (docs/internals/design.md, "Moving op heads").
//!
//! Every jj command but two publishes its operation under jj's op-heads lock, in place of the
//! op heads it loaded. `jj op abandon` and `jj op integrate` take no lock: one reads the op
//! heads, writes for a while, then puts its rewrite in place of each head it read. So musubi
//! replaces op heads only under that lock, and only while they are still those it read; and
//! it remembers what it took out, so that a `jj op abandon` that read the op heads before
//! musubi replaced them, and wrote after, is noticed, and musubi's replacement taken out again.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::op_heads_store::OpHeadsStoreLock;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;
use super::join::fingerprint;

use crate::op_id::LocalOp;

pub(super) mod plan;

pub(super) use plan::Replaced;
use plan::same;

/// Where a test runs something of its own in the next move of op heads that musubi read
/// earlier ([`NodeRepo::race_head_move`]).
#[doc(hidden)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeadRace {
    /// Once the move is worked out, before jj's op-heads lock is taken: as a `jj` command
    /// that finishes meanwhile. Where the caller holds the lock already, as publication
    /// cleanup does, only a command that takes no lock can run here.
    Unlocked,
    /// Holding jj's op-heads lock, the op heads checked, before they move: as `jj op
    /// abandon`. Only a command that takes no lock can run here: any other waits forever.
    Locked,
}

/// What tests run in the next move of op heads, and where.
pub(super) type HeadRaces = std::sync::Mutex<Vec<(HeadRace, Box<dyn FnOnce() + Send>)>>;

/// jj's op-heads lock, as this handle holds it: taken once however many of musubi's head moves
/// nest under it, since jj's lock is a file lock, which the same process taking again waits
/// for forever.
pub(super) struct HeadsLock<'a> {
    _lock: Option<Box<dyn OpHeadsStoreLock + 'a>>,
    held: Option<Arc<AtomicBool>>,
}

impl Drop for HeadsLock<'_> {
    fn drop(&mut self) {
        if let Some(held) = &self.held {
            held.store(false, Ordering::SeqCst);
        }
    }
}

/// The operations musubi reads of this repository.
struct RepoGraph<'a>(&'a NodeRepo);

impl plan::Graph<LocalOp> for RepoGraph<'_> {
    type Error = NodeError;

    fn read(&self, id: &LocalOp) -> Result<plan::Node<LocalOp>, NodeError> {
        let op = self.0.loader.op_store().read_operation(&id.0).block_on()?;
        Ok(plan::Node {
            parents: LocalOp::parents_of(&op),
            fingerprint: fingerprint(&op),
        })
    }

    fn known(&self, id: &LocalOp) -> bool {
        self.0.canonical_of(id).is_some() || self.0.joins.before.contains(id)
    }
}

impl NodeRepo {
    /// Takes jj's op-heads lock in `store`, this repository's, unless this handle holds it
    /// already. No jj command publishes an operation or merges op heads while it is held.
    pub(super) fn lock_heads<'a>(
        &self,
        store: &'a dyn OpHeadsStore,
    ) -> Result<HeadsLock<'a>, NodeError> {
        if self.heads_locked.load(Ordering::SeqCst) {
            return Ok(HeadsLock {
                _lock: None,
                held: None,
            });
        }
        let lock = store.lock().block_on()?;
        self.heads_locked.store(true, Ordering::SeqCst);
        Ok(HeadsLock {
            _lock: Some(lock),
            held: Some(self.heads_locked.clone()),
        })
    }

    /// Makes `new` the op heads in place of `read`, the op heads as read earlier, under jj's
    /// op-heads lock, if they are still exactly those; `from` says what each of `read` became,
    /// where it became anything but itself. The new heads go in before the old come out, the
    /// last with them: a crash in between leaves extra heads, which jj merges, rather than
    /// losing any. Unless `remove`, the old ones stay, as a crash in jj's update leaves them.
    ///
    /// Returns whether the op heads are as it left them. They aren't where they changed since
    /// they were read, as a jj command changes them, when it moves nothing; or where a `jj op
    /// abandon` rewrote one of those it took out while it moved them, when it takes out again
    /// what it put in ([`Self::retire_overtaken`]). The caller then works out the move again
    /// from the op heads as they are now.
    pub(super) fn replace_heads(
        &self,
        read: &[LocalOp],
        from: &HashMap<LocalOp, Vec<LocalOp>>,
        new: &[LocalOp],
        remove: bool,
    ) -> Result<bool, NodeError> {
        let Some((last, rest)) = new.split_last() else {
            return Ok(same(&self.local_heads()?, read));
        };
        let old: Vec<&LocalOp> = read.iter().filter(|h| !new.contains(h)).collect();
        let replaced = plan::entries(&old, from, new, read, &RepoGraph(self))?;
        self.race(HeadRace::Unlocked);
        let store = self.loader.op_heads_store().clone();
        let _lock = self.lock_heads(&*store)?;
        if !same(&self.local_heads()?, read) {
            return Ok(false);
        }
        self.race(HeadRace::Locked);
        for head in rest {
            store.update_op_heads(&[], &head.0).block_on()?;
        }
        if !remove {
            store.update_op_heads(&[], &last.0).block_on()?;
            return Ok(true);
        }
        let old: Vec<OperationId> = old.iter().map(|h| h.0.clone()).collect();
        store.update_op_heads(&old, &last.0).block_on()?;
        self.records.watch_replaced(replaced);
        // `jj op abandon` may have read the op heads before this took them out, and put its
        // rewrite of one beside those this put in meanwhile.
        if same(&self.local_heads()?, new) {
            return Ok(true);
        }
        let out = self.retire_overtaken()?;
        Ok(!new.iter().any(|op| out.contains(op)))
    }

    /// Takes out the op heads musubi put in place of one that `jj op abandon` rewrote since: one
    /// that read the op heads before musubi replaced them and wrote its rewrite after, as it
    /// takes no lock. That rewrite is then an op head beside musubi's replacement, the two
    /// sharing nothing above what the abandon rewrote from; merged, they would bring back what it
    /// dropped. Taken out, the op heads are as the abandon left them, to notice it in as in any
    /// other. Of a merge or realization taken out, the op heads it was on that are none of what
    /// musubi put in place of a rewritten head go back: the rewrites of an op head the abandon
    /// left as it was, or another machine's work. Returns what it took out.
    ///
    /// jj's rewrite of an operation keeps all of it but its parents, so it is an op head with the
    /// replaced head's [`fingerprint`] and another id, unknown to the translation cache. It is
    /// the op head itself: a `jj` command that loads the repository then finds two op heads, and
    /// merges them before writing anything on them. One run `--at-op` at the rewrite, or another
    /// `jj op abandon`, which rewrites both, races as it would with any command on one machine
    /// ("Known jj limitations" in races.md). Below an op head, an operation with that fingerprint
    /// may instead be what the replaced head was rewritten from, by an earlier `jj op abandon`,
    /// as a `jj` command that loaded the repository before that abandon writes on: that command
    /// is no rewrite of the replaced head, and musubi's replacement stays.
    ///
    /// It works that out without jj's op-heads lock, which every jj command waits for, and
    /// takes the lock only to act, if the op heads are still those it read.
    pub(super) fn retire_overtaken(&self) -> Result<Vec<LocalOp>, NodeError> {
        if !self.records.watching_replaced() {
            return Ok(vec![]);
        }
        let store = self.loader.op_heads_store().clone();
        loop {
            let Some(retiring) = self.retiring()? else {
                return Ok(vec![]);
            };
            let _lock = self.lock_heads(&*store)?;
            if !same(&self.local_heads()?, &retiring.heads) {
                continue;
            }
            let plan::Retiring {
                heads,
                out,
                back,
                kept,
                rewritten,
            } = retiring;
            tracing::info!(
                "jj op abandon rewrote {rewritten} operation heads while musubi replaced them"
            );
            for op in &back {
                store.update_op_heads(&[], &op.0).block_on()?;
            }
            let stay = heads
                .iter()
                .find(|head| !out.contains(head))
                .expect("an op head musubi didn't put in");
            // Put in again, to take the others out with it: `update_op_heads` adds before it
            // removes, and a head already there stays.
            let ids: Vec<OperationId> = out.iter().map(|op| op.0.clone()).collect();
            store.update_op_heads(&ids, &stay.0).block_on()?;
            self.records.keep_replaced(kept);
            return Ok(out);
        }
    }

    /// What [`Self::retire_overtaken`] does with the op heads as they are now, if anything,
    /// forgetting what it watches whose replacements are no longer op heads.
    fn retiring(&self) -> Result<Option<plan::Retiring<LocalOp>>, NodeError> {
        let heads = self.local_heads()?;
        match plan::look(&heads, self.records.replaced(), &RepoGraph(self))? {
            plan::Look::Nothing { kept } => {
                self.records.keep_replaced(kept);
                Ok(None)
            }
            plan::Look::Retire(retiring) => Ok(Some(retiring)),
        }
    }

    /// For tests of races: runs `run` in the next move of op heads that musubi read earlier,
    /// at `at`, as if another process ran it then. It runs once.
    #[doc(hidden)]
    pub fn race_head_move(&self, at: HeadRace, run: impl FnOnce() + Send + 'static) {
        self.head_races
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push((at, Box::new(run)));
    }

    /// Runs what a test said to run at `at`.
    fn race(&self, at: HeadRace) {
        let run: Vec<_> = {
            let mut races = self
                .head_races
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            let (now, later) = std::mem::take(&mut *races)
                .into_iter()
                .partition(|(when, _)| *when == at);
            *races = later;
            now
        };
        for (_, run) in run {
            run();
        }
    }
}

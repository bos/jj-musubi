//! Moving op heads that musubi read earlier (docs/internals/design.md, "Moving op heads").
//!
//! Every jj command but two publishes its operation under jj's op-heads lock, in place of the
//! op heads it loaded. `jj op abandon` and `jj op integrate` take no lock: one reads the op
//! heads, writes for a while, then puts its rewrite in place of each head it read. So musubi
//! replaces op heads only under that lock, and only while they are still those it read, and
//! moves nothing otherwise: no operation a jj command wrote is lost.

use std::sync::Arc;
use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;

use jj_lib::op_heads_store::OpHeadsStore;
use jj_lib::op_heads_store::OpHeadsStoreLock;
use jj_lib::op_store::OperationId;
use pollster::FutureExt as _;

use super::NodeError;
use super::NodeRepo;

use crate::op_id::LocalOp;

pub(super) mod plan;

use plan::same;

/// What tests run in the next move of op heads.
pub(super) type HeadRaces = std::sync::Mutex<Vec<Box<dyn FnOnce() + Send>>>;

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
    /// op-heads lock, if they are still exactly those. The new heads go in before the old come
    /// out, the last with them: a crash in between leaves extra heads, which jj merges, rather
    /// than losing any. Unless `remove`, the old ones stay, as a crash in jj's update leaves
    /// them.
    ///
    /// Returns whether it moved them. It moves nothing where the op heads changed since they
    /// were read, as a jj command changes them, or a `jj op abandon` or `jj op integrate`,
    /// which takes no lock; the caller then works out the move again from the op heads as they
    /// are now.
    pub(super) fn replace_heads(
        &self,
        read: &[LocalOp],
        new: &[LocalOp],
        remove: bool,
    ) -> Result<bool, NodeError> {
        let Some((last, rest)) = new.split_last() else {
            return Ok(same(&self.local_heads()?, read));
        };
        let old: Vec<&LocalOp> = read.iter().filter(|h| !new.contains(h)).collect();
        self.race();
        let store = self.loader.op_heads_store().clone();
        let _lock = self.lock_heads(&*store)?;
        if !same(&self.local_heads()?, read) {
            return Ok(false);
        }
        for head in rest {
            store.update_op_heads(&[], &head.0).block_on()?;
        }
        if !remove {
            store.update_op_heads(&[], &last.0).block_on()?;
            return Ok(true);
        }
        let old: Vec<OperationId> = old.iter().map(|h| h.0.clone()).collect();
        store.update_op_heads(&old, &last.0).block_on()?;
        Ok(true)
    }

    /// For tests of races: runs `run` in the next move of op heads that musubi read earlier,
    /// or in the next advance to what it fetched, once the move is worked out and before jj's
    /// op-heads lock is taken, as if another process ran it then: as a `jj` command that
    /// finishes meanwhile. It runs once. Where the caller holds the lock already, as publication
    /// cleanup does, only a command that takes no lock can run here.
    #[doc(hidden)]
    pub fn race_head_move(&self, run: impl FnOnce() + Send + 'static) {
        self.head_races
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .push(Box::new(run));
    }

    /// Runs what a test said to run in a move of op heads.
    pub(super) fn race(&self) {
        let run = std::mem::take(
            &mut *self
                .head_races
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner),
        );
        for run in run {
            run();
        }
    }
}

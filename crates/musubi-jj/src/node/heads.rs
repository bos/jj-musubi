//! Moving op heads that musubi read earlier (docs/internals/design.md, "Moving op heads").
//!
//! Every jj command but two publishes its operation under jj's op-heads lock, in place of the
//! op heads it loaded. `jj op abandon` and `jj op integrate` take no lock: one reads the op
//! heads, writes for a while, then puts its rewrite in place of each head it read. So musubi
//! replaces op heads only under that lock, and only while they are still those it read; and
//! it remembers what it took out, so that a `jj op abandon` that read the op heads before
//! musubi replaced them, and wrote after, is noticed, and musubi's replacement taken out again.

use std::collections::HashMap;
use std::collections::HashSet;
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

/// An op head musubi took out, with what it put in its place. Kept while one of those is still
/// an op head, since until then a `jj op abandon` that read the op heads before can still put
/// its rewrite of this one beside them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Replaced {
    /// The op head as it was.
    pub(super) head: LocalOp,
    /// Its content but for its parents ([`fingerprint`]), which jj's rewrite of it keeps.
    pub(super) fingerprint: String,
    /// What musubi rewrote it to, op heads or not.
    pub(super) images: Vec<LocalOp>,
    /// The op heads musubi put in its place: those of `images`, and what it put in on them,
    /// as a merge of them or a realization on one.
    pub(super) by: Vec<LocalOp>,
}

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

/// What [`NodeRepo::retire_overtaken`] takes out and puts back, worked out from the op heads
/// `heads`.
struct Retiring {
    heads: Vec<LocalOp>,
    out: Vec<LocalOp>,
    back: Vec<LocalOp>,
    /// The watch as it is once they move.
    kept: Vec<Replaced>,
    /// How many op heads jj rewrote.
    rewritten: usize,
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
        let replaced = self.replaced_by(&old, from, new, read)?;
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

    /// What `new` puts in place of each of `old`, of the op heads `read`, as `from` rewrote
    /// them: its images among `new`, and what else of `new` is on them.
    fn replaced_by(
        &self,
        old: &[&LocalOp],
        from: &HashMap<LocalOp, Vec<LocalOp>>,
        new: &[LocalOp],
        read: &[LocalOp],
    ) -> Result<Vec<Replaced>, NodeError> {
        let store = self.loader.op_store();
        let mut parents = HashMap::new();
        for op in new.iter().filter(|op| !read.contains(op)) {
            let read = store.read_operation(&op.0).block_on()?;
            parents.insert(op, LocalOp::parents_of(&read));
        }
        let mut replaced = vec![];
        for head in old {
            let images = from.get(*head).cloned().unwrap_or_default();
            let by: Vec<LocalOp> = parents
                .iter()
                .filter(|(op, on)| images.contains(op) || on.iter().any(|p| images.contains(p)))
                .map(|(op, _)| (*op).clone())
                .collect();
            if by.is_empty() {
                continue;
            }
            let op = store.read_operation(&head.0).block_on()?;
            replaced.push(Replaced {
                head: (*head).clone(),
                fingerprint: fingerprint(&op),
                images,
                by,
            });
        }
        Ok(replaced)
    }

    /// Takes out the op heads musubi put in place of one that `jj op abandon` rewrote since:
    /// one that read the op heads before musubi replaced them and wrote its rewrite after, as
    /// it takes no lock. That rewrite, or a `jj` command on it, is then an op head beside
    /// musubi's replacement, the two sharing nothing above what the abandon rewrote from;
    /// merged, they would bring back what it dropped. Taken out, the op heads are as the
    /// abandon left them, to notice it in as in any other. Of a merge or realization taken out,
    /// the op heads it was on that are none of what musubi put in place of a rewritten head go
    /// back: the rewrites of an op head the abandon left as it was, or another machine's work.
    /// Returns what it took out.
    ///
    /// jj's rewrite of an operation keeps all of it but its parents, so it is an operation
    /// with the replaced head's [`fingerprint`] and another id, reached from an op head that
    /// isn't one musubi put in, without passing an operation the translation cache has. An
    /// operation that rewrote the head, in another `jj op abandon` before it, looks the same,
    /// but only a `jj` command that loaded the repository before that abandon writes on it,
    /// in a race jj doesn't resolve either ("Known jj limitations" in races.md).
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
            let Retiring {
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
    fn retiring(&self) -> Result<Option<Retiring>, NodeError> {
        let heads = self.local_heads()?;
        let mut watched = self.records.replaced();
        // Gone, once nothing musubi put in its place is an op head: jj's rewrite of it, now,
        // would be beside a jj command's, as it would be on one machine.
        watched.retain(|replaced| replaced.by.iter().any(|op| heads.contains(op)));
        let put: HashSet<&LocalOp> = watched.iter().flat_map(|r| &r.by).collect();
        let beside: Vec<&LocalOp> = heads.iter().filter(|h| !put.contains(h)).collect();
        let rewritten = if beside.is_empty() {
            HashSet::new()
        } else {
            self.rewritten(&watched, &beside, &put)?
        };
        if rewritten.is_empty() {
            self.records.keep_replaced(watched);
            return Ok(None);
        }
        let (stale, mut kept): (Vec<Replaced>, Vec<Replaced>) = watched
            .into_iter()
            .partition(|replaced| rewritten.contains(&replaced.head));
        let stale_images: HashSet<&LocalOp> = stale.iter().flat_map(|r| &r.images).collect();
        let stale_by: HashSet<&LocalOp> = stale.iter().flat_map(|r| &r.by).collect();
        let out: Vec<LocalOp> = heads
            .iter()
            .filter(|head| stale_by.contains(head))
            .cloned()
            .collect();
        // What a merge or realization taken out was on, but for the rewrites of a head jj
        // rewrote and what is on them.
        let store = self.loader.op_store();
        let mut back: Vec<LocalOp> = vec![];
        for op in out.iter().filter(|op| !stale_images.contains(op)) {
            let read = store.read_operation(&op.0).block_on()?;
            for parent in LocalOp::parents_of(&read) {
                if stale_images.contains(&parent)
                    || stale_by.contains(&parent)
                    || heads.contains(&parent)
                    || back.contains(&parent)
                {
                    continue;
                }
                let on = store.read_operation(&parent.0).block_on()?;
                if LocalOp::parents_of(&on)
                    .iter()
                    .all(|p| !stale_images.contains(p))
                {
                    back.push(parent);
                }
            }
        }
        for replaced in &mut kept {
            replaced.by.retain(|op| !out.contains(op));
            replaced.by.extend(
                back.iter()
                    .filter(|op| replaced.images.contains(op))
                    .cloned(),
            );
        }
        Ok(Some(Retiring {
            heads,
            out,
            back,
            kept,
            rewritten: stale.len(),
        }))
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

    /// The heads among `watched` that jj rewrote, as the history below `beside`, the op heads
    /// musubi didn't put in (`put`), has them.
    fn rewritten(
        &self,
        watched: &[Replaced],
        beside: &[&LocalOp],
        put: &HashSet<&LocalOp>,
    ) -> Result<HashSet<LocalOp>, NodeError> {
        let mut found = HashSet::new();
        let mut stack: Vec<LocalOp> = beside.iter().map(|h| (*h).clone()).collect();
        let mut seen = HashSet::new();
        while let Some(id) = stack.pop() {
            if found.len() == watched.len() {
                break;
            }
            if !seen.insert(id.clone())
                || put.contains(&id)
                || self.canonical_of(&id).is_some()
                || self.joins.before.contains(&id)
            {
                continue;
            }
            let op = self.loader.op_store().read_operation(&id.0).block_on()?;
            let print = fingerprint(&op);
            for replaced in watched {
                if replaced.fingerprint == print && replaced.head != id {
                    found.insert(replaced.head.clone());
                }
            }
            stack.extend(LocalOp::parents_of(&op));
        }
        Ok(found)
    }
}

/// Whether `a` and `b` are the same op heads, in any order.
fn same(a: &[LocalOp], b: &[LocalOp]) -> bool {
    let a: HashSet<&LocalOp> = a.iter().collect();
    let b: HashSet<&LocalOp> = b.iter().collect();
    a == b
}

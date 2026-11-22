//! Daemon and network actions: full and partial syncs, delivery, restarts, rollback and
//! crashes. Source evidence is captured around each effect; supported refusals pass through
//! the recovery policy rather than weakening a property's expected result.

use std::fs;

use jj_lib::object_id::ObjectId as _;
use musubi_core::message::Head;
use musubi_core::message::HeadKind;
use musubi_core::message::Reply;
use musubi_core::message::Request;
use musubi_core::node::Step;
use musubi_sync::Attachment;
use musubi_sync::OpId;

use super::World;

impl World {
    /// A node's first policy step merges its op heads if there are several (`NodeCore::step`).
    /// Before a sync, they are all this machine's own concurrent operations (from `--at-op`),
    /// so the merge is this machine's work, and the ledger records it as such; this takes
    /// that first step through the same code, and records it. Later merges, with operations
    /// from the hub, are musubi's and are not recorded.
    pub fn merge_local_heads(&mut self, m: usize) {
        if self.op_heads(m).len() < 2 {
            return;
        }
        let before = self.seen(m);
        if let Err(err) = self.fx.node(m).merge_heads() {
            self.fail(&format!(
                "merging {}'s op heads failed: {err}",
                self.machine(m)
            ));
        }
        let after = self.seen(m);
        let what = format!("{}: merge own op heads before sync", self.machine(m));
        self.ledger.record(m, &what, &before, &after, false);
        self.observe_operation_sources(m);
    }

    /// Lets node `m` poll the hub and run its policy until idle.
    pub fn sync(&mut self, m: usize) {
        self.record(format!("{}: sync", self.machine(m)));
        self.sync_counted(m);
    }

    /// Syncs node `m` until idle and returns how many steps it took.
    pub fn sync_counted(&mut self, m: usize) -> usize {
        crate::coverage::interrupt_races();
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.merge_local_heads(m);
        let forgotten = self.forgotten_working_copies(m);
        let steps = loop {
            let input = self.git_record_input(m);
            let result = self.fx.hive.sync(m);
            self.finish_git_record_input(m, input);
            match result {
                Ok(steps) => break steps,
                Err(err) => self.recover(m, "sync", &err),
            }
        };
        self.note_forgotten_rebase(m, forgotten);
        self.record_merges(m);
        steps
    }

    /// Lets node `m` poll the hub and take at most `steps` policy steps, delivering every
    /// request but losing the reply to request number `lose`: progress that stops partway,
    /// possibly after an upload but before the push.
    pub fn sync_partial(&mut self, m: usize, steps: usize, lose: Option<usize>) {
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.record(format!(
            "{}: sync {steps} step(s){}",
            self.machine(m),
            lose.map(|d| format!(", losing reply {d}"))
                .unwrap_or_default()
        ));
        self.merge_local_heads(m);
        // Progress stops here either way: a partial sync that pauses has nothing to retry.
        if let Err(err) = self.try_sync_partial(m, steps, lose, None) {
            self.recover(m, "partial sync", &err);
        }
        self.record_merges(m);
    }

    /// Lets node `m` sync until it has realized `count` operations, or has nothing more to
    /// realize, and stops there, with what it realized perhaps still being written.
    pub fn sync_realizing(&mut self, m: usize, count: usize) {
        self.observe_operation_sources(m);
        self.touched.insert(m);
        self.record(format!(
            "{}: sync until {count} operation(s) realized",
            self.machine(m)
        ));
        self.merge_local_heads(m);
        if let Err(err) = self.try_sync_partial(m, usize::MAX, None, Some(count)) {
            self.recover(m, "partial sync", &err);
        }
        self.record_merges(m);
    }

    pub(super) fn try_sync_partial(
        &mut self,
        m: usize,
        steps: usize,
        lose: Option<usize>,
        realizing: Option<usize>,
    ) -> anyhow::Result<()> {
        let input = self.git_record_input(m);
        let result = self.try_sync_partial_inner(m, steps, lose, realizing);
        self.finish_git_record_input(m, input);
        result
    }

    fn try_sync_partial_inner(
        &mut self,
        m: usize,
        steps: usize,
        lose: Option<usize>,
        realizing: Option<usize>,
    ) -> anyhow::Result<()> {
        crate::coverage::interrupt_races();
        let mut sent = 0;
        let mut deliver = |world: &mut Self, request| {
            let lost = lose == Some(sent);
            sent += 1;
            world.deliver(m, request, lost)
        };
        // Polled first, as the daemon does (`Driver::sync`).
        let poll = {
            let member = &mut self.fx.hive.members[m];
            member.adapter.poll(&member.core)?
        };
        deliver(self, poll)?;
        self.fx.hive.members[m].adapter.before_sync()?;
        let mut realized = 0;
        for _ in 0..steps {
            let member = &mut self.fx.hive.members[m];
            match member.core.step(&mut member.adapter)? {
                Step::Idle => break,
                Step::Send(requests) => {
                    for request in requests {
                        deliver(self, request)?;
                    }
                }
                Step::Realized(_) => {
                    realized += 1;
                    if realizing == Some(realized) {
                        break;
                    }
                }
                // Advancing finishes writing what was realized.
                Step::Advanced(_) if realizing.is_some() => break,
                Step::Merged | Step::Advanced(_) => {}
            }
        }
        Ok(())
    }

    /// Delivers a request to the hub, and its reply back (unless lost), then any new head to
    /// every node, as `Hive` does.
    fn deliver(
        &mut self,
        m: usize,
        request: Request<OpId, Attachment>,
        lost: bool,
    ) -> anyhow::Result<()> {
        let hive = &mut self.fx.hive;
        let handled = hive.handle(request)?;
        if !lost {
            let member = &mut hive.members[m];
            member
                .core
                .handle_reply(&mut member.adapter, handled.reply)?;
        }
        if let Some(Head { seq, head }) = handled.publish {
            for member in &mut hive.members {
                let notify = Reply::Head {
                    kind: HeadKind::Notify,
                    seq,
                    head: head.clone(),
                };
                member.core.handle(&mut member.adapter, notify)?;
            }
        }
        Ok(())
    }

    /// Forgets node `m`'s volatile protocol state.
    pub fn restart(&mut self, m: usize) {
        self.record(format!("{}: restart", self.machine(m)));
        self.fx.hive.restart(m);
    }

    /// Crashes the hub, which reopens its store.
    pub fn restart_hub(&mut self) {
        self.record("hub: restart".to_owned());
        if let Err(err) = self.fx.hive.restart_hub() {
            self.fail(&format!("restarting the hub: {err:#}"));
        }
    }

    /// Whether a power cut can send the hub back: it accepted a head.
    pub fn hub_can_go_back(&self) -> bool {
        self.hub_seq() > 0
    }

    pub fn hub_seq(&self) -> u64 {
        self.fx.hive.hub.store().head().0
    }

    /// Has the hub lose its last `lost` heads, but not its root, as a power cut can make
    /// it, and restarts it.
    pub fn hub_goes_back(&mut self, lost: usize) {
        self.record(format!("hub: goes back {lost}"));
        let seq = self.hub_seq().saturating_sub(lost as u64);
        if let Err(err) = self.fx.hive.hub_goes_back(seq) {
            self.fail(&format!("restarting the hub: {err:#}"));
        }
    }

    /// Makes the hive again, empty, as a hub does whose store is corrupt.
    pub fn remake_hub(&mut self) {
        self.record("hub: made again".to_owned());
        if let Err(err) = self.fx.hive.remake_hub() {
            self.fail(&format!("making the hive again: {err:#}"));
        }
    }

    /// Crashes node `m`'s daemon: it reopens the repository, losing every in-memory cache,
    /// and with `lose_cache` also the on-disk translation cache. The realizations it was
    /// still writing stay unrecorded, and those `stopped` picks, by bit, lose their operation
    /// files, as if it crashed between a view and its operation. Returns how many it was
    /// writing.
    pub fn crash(&mut self, m: usize, lose_cache: bool, stopped: u64) -> usize {
        self.observe_native_origins(m);
        let in_flight = self.fx.hive.members[m]
            .adapter
            .repo_mut()
            .crash_before_settling();
        let stopped: Vec<_> = in_flight
            .iter()
            .enumerate()
            .filter(|(i, _)| (stopped >> (i % 64)) & 1 == 1)
            .map(|(_, local)| local)
            .collect();
        self.record(format!(
            "{}: crash{}{}",
            self.machine(m),
            if in_flight.is_empty() {
                String::new()
            } else {
                format!(
                    ", writing {} operations, {} stopped before their files",
                    in_flight.len(),
                    stopped.len()
                )
            },
            if lose_cache {
                ", losing the translation cache"
            } else {
                ""
            }
        ));
        let repo = self.fx.repo(m);
        for local in stopped {
            let path = repo
                .repo_path()
                .join("op_store/operations")
                .join(local.0.hex());
            if path.exists() {
                fs::remove_file(path).unwrap();
            }
        }
        if lose_cache {
            let path = repo.repo_path().join("musubi/translation");
            if path.exists() {
                fs::remove_file(path).unwrap();
            }
        }
        self.fx.reopen(m);
        self.touched.insert(m);
        in_flight.len()
    }
}

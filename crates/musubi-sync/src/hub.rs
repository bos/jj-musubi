//! The core's `HubStorage` over a hub store.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;
use std::time::Instant;

use anyhow::bail;
use jj_lib::backend::CommitId;
use musubi_core::hub::HubStorage;
use musubi_core::message::Head;
use musubi_core::message::OpEntry;
use musubi_core::message::RecordState;
use musubi_hub::store::Contracted;
use musubi_hub::store::HubStore;
use musubi_jj::canonical::CanonicalError;
use musubi_jj::objects::Backend;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::presence::Presence;
use musubi_jj::records::HubOp;

use crate::Attachment;
use crate::OpId;
use crate::open_bundle_dir;
use crate::short;
use crate::temp_bundle;

/// How long the hub waits, before pruning its records, for a machine joining the hive after it
/// last heard from it: a machine joining says what it took with its first fetch, which realizes
/// the hive's history, and may then be away that long, asleep, say, before its first push lands.
/// One away longer, which the hub prunes without, can't take the records it pruned, and stops
/// syncing for good.
pub const JOINING_LIFETIME: Duration = Duration::from_secs(24 * 3600);

/// How long the hub prunes nothing after it opens a hive's store, as after a restart or once it
/// has made the hive again: it no longer knows which machines were joining, and one that is
/// online says what it took within minutes of the hub coming back. A machine joining that is
/// offline then, and away for longer, can be stranded.
pub const WAIT_AFTER_OPENING: Duration = Duration::from_secs(3600);

pub struct HubAdapter {
    store: HubStore,
    tmp: PathBuf,
    /// The history with a supersede's drops dropped too, as a push asks about it: the same
    /// for each of its questions, and for taking it.
    contracted: RefCell<Option<Contracted>>,
    /// What the hub knows of the hive's machines, in memory only.
    machines: Machines,
}

/// What the hub knows of a hive's machines, which it keeps only in memory: what each last said
/// it took, and when, which are joining, and when it started remembering. Opening the hive's
/// store again in the same process, as after a panic, keeps it ([`HubAdapter::into_machines`]).
pub struct Machines {
    /// What each machine last said it took, and when.
    reports: HashMap<String, (RecordState, Instant)>,
    /// The machines whose `musubi join` chose this hive, and that aren't present at its head
    /// yet, as they are once their first push lands, with when the hub last heard from each:
    /// the join, or what it last said it took. Among them is a copy that left, and that the
    /// history knows, joining again.
    joining: HashMap<String, Instant>,
    /// When the hub opened the hive's store, and started remembering: a machine joining may
    /// have said what it took to the hub as it was before, which kept that only in memory.
    opened: Instant,
    /// How far tests have moved the hub's clock on ([`HubAdapter::age`]).
    aged: Duration,
}

impl Machines {
    fn retire_joins<Op: Clone + Ord>(&mut self, presence: &Presence<Op>, now: Instant) {
        self.joining.retain(|machine, heard| {
            !presence.is_present(machine) && now.duration_since(*heard) < JOINING_LIFETIME
        });
    }

    fn waits_after_opening(&self, now: Instant) -> bool {
        now.duration_since(self.opened) < WAIT_AFTER_OPENING
    }

    fn waited_for<Op: Clone + Ord>(
        &mut self,
        presence: &Presence<Op>,
        now: Instant,
    ) -> BTreeSet<String> {
        // A forgotten copy's reports count only while it is explicitly joining again.
        let joining = &self.joining;
        self.reports.retain(|machine, (_, when)| {
            presence.is_present(machine)
                || joining.contains_key(machine)
                || (!presence.known().contains(machine)
                    && now.duration_since(*when) < JOINING_LIFETIME)
        });
        let mut waited: BTreeSet<String> = presence.copies().map(str::to_owned).collect();
        waited.extend(self.reports.keys().cloned());
        waited
    }

    fn report(&mut self, machine: &str, records: &RecordState, now: Instant) {
        if let Some(heard) = self.joining.get_mut(machine) {
            *heard = now;
        }
        match self.reports.get_mut(machine) {
            Some((taken, when)) if taken == records => *when = now,
            _ => {
                self.reports
                    .insert(machine.to_owned(), (records.clone(), now));
            }
        }
    }
}

impl HubAdapter {
    pub fn init(dir: &Path, backend: Backend) -> anyhow::Result<Self> {
        Self::new(HubStore::init(dir, backend)?, dir)
    }

    pub fn open(dir: &Path) -> anyhow::Result<Self> {
        Self::new(HubStore::open(dir)?, dir)
    }

    /// Serves the hive's store, knowing nothing yet of what any machine took.
    pub fn new(store: HubStore, dir: &Path) -> anyhow::Result<Self> {
        let tmp = dir.join("tmp");
        open_bundle_dir(&tmp)?;
        Ok(Self {
            store,
            tmp,
            contracted: RefCell::new(None),
            machines: Machines {
                reports: HashMap::new(),
                joining: HashMap::new(),
                opened: Instant::now(),
                aged: Duration::ZERO,
            },
        })
    }

    /// What the hub knows of the hive's machines, for the hub that serves its store next in
    /// this process ([`Self::recall`]).
    pub fn into_machines(self) -> Machines {
        self.machines
    }

    /// Takes up what the hub that served the hive's store earlier in this process knew of its
    /// machines: nothing a machine has said since then is lost.
    pub fn recall(&mut self, machines: Machines) {
        self.machines = machines;
    }

    /// Has the hub wait, before pruning, for `machine`, which asked it to join the hive
    /// (`musubi_hub::hub_dir::HubDir::joined`), until its first push lands, or until it has
    /// heard nothing from it for [`JOINING_LIFETIME`].
    pub fn joining(&mut self, machine: &str) {
        let now = self.now();
        self.machines.joining.insert(machine.to_owned(), now);
    }

    /// Makes it as if `elapsed` had passed, for tests that would otherwise wait out how long
    /// the hub waits for a machine joining ([`JOINING_LIFETIME`], [`WAIT_AFTER_OPENING`]).
    pub fn age(&mut self, elapsed: Duration) {
        self.machines.aged += elapsed;
    }

    fn now(&self) -> Instant {
        Instant::now() + self.machines.aged
    }

    /// How many machines the hub remembers having said what they took, and how many it knows
    /// to be joining.
    #[cfg(test)]
    pub(crate) fn remembered(&self) -> (usize, usize) {
        (self.machines.reports.len(), self.machines.joining.len())
    }

    /// Runs `f` on the history with `dropped` dropped too, worked out once for them.
    fn with_contracted<T>(
        &self,
        dropped: &[OpId],
        f: impl FnOnce(&Contracted) -> anyhow::Result<T>,
    ) -> anyhow::Result<T> {
        let mut cached = self.contracted.borrow_mut();
        let wanted: BTreeSet<&OpId> = dropped
            .iter()
            .filter(|op| !self.store.is_superseded(op))
            .collect();
        // For the history as of the head now: another push may have moved it since.
        let fresh = cached.as_ref().is_none_or(|contracted| {
            contracted.head != *self.store.head().1
                || contracted.dropped.iter().collect::<BTreeSet<_>>() != wanted
        });
        if fresh {
            let dropped: Vec<HubOp> = dropped
                .iter()
                .map(|op| HubOp(CanonicalOp(op.clone())))
                .collect();
            *cached = Some(self.store.contract(&dropped)?);
        }
        f(cached.as_ref().expect("contracted above"))
    }

    pub fn store(&self) -> &HubStore {
        &self.store
    }

    /// Prunes the hub's records once every copy the hive hasn't forgotten has said it took
    /// them all (`musubi_core::hub::prune`): every copy present at the head; every machine
    /// joining ([`Self::joining`]) that has said what it took, as its first fetch, straight
    /// after the join, does, until the hub has heard nothing from it for [`JOINING_LIFETIME`];
    /// and every machine the history doesn't know that has said what it took in that time, as
    /// one joining does before the hub accepts its first push. It prunes
    /// nothing for [`WAIT_AFTER_OPENING`] after opening the store, as after a restart: a machine
    /// joining may have said so to the hub before. Returns how many it has pruned, if it pruned
    /// any now.
    pub fn prune(&mut self) -> anyhow::Result<Option<u64>> {
        let now = self.now();
        // Before anything else, so that no join outlives the machine's first push: the machine
        // is then waited for as present, and once the hive forgets it, and its daemon goes on
        // saying what it took, its join mustn't keep the hub waiting.
        if !self.machines.joining.is_empty() {
            let presence = self.store.presence()?;
            self.machines.retire_joins(presence.as_ref(), now);
        }
        if self.machines.waits_after_opening(now) {
            return Ok(None);
        }
        let records = HubStorage::records(self);
        // Nothing to prune, or no machine has taken it all yet, as after the push that took
        // a record, which renamed the history: the walk for presence can wait.
        if self.store.records().is_empty()
            || !self
                .machines
                .reports
                .values()
                .any(|(taken, _)| *taken == records)
        {
            return Ok(None);
        }
        let presence = self.store.presence()?;
        let waited = self.machines.waited_for(presence.as_ref(), now);
        let pruned = musubi_core::hub::prune(self, &waited)?;
        if let Some(count) = pruned {
            tracing::info!("pruned the first {count} records, which every machine has taken");
        }
        Ok(pruned)
    }
}

/// The state of `count` records whose digest is `digest`.
fn record_state(count: usize, digest: &musubi_jj::records::RecordDigest) -> RecordState {
    RecordState {
        count: count as u64,
        digest: digest.bytes().to_vec(),
    }
}

impl HubStorage for HubAdapter {
    type Op = OpId;
    type Attachment = Attachment;
    type Error = anyhow::Error;

    fn head(&self) -> Head<OpId> {
        let (seq, head) = self.store.head();
        Head {
            seq,
            head: head.clone(),
        }
    }

    fn set_head(&mut self, seq: u64, head: &OpId, dropped: &[OpId]) -> anyhow::Result<()> {
        let contracted = if dropped.is_empty() {
            self.contracted.take();
            None
        } else {
            self.with_contracted(dropped, |_| Ok(()))?;
            self.contracted.take()
        };
        Ok(self.store.set_head(seq, head, contracted)?)
    }

    fn records(&self) -> RecordState {
        let count = self.store.record_count();
        record_state(
            count,
            self.store.digest(count).expect("a digest per prefix"),
        )
    }

    fn pruned(&self) -> RecordState {
        let count = self.store.pruned();
        record_state(count, self.store.digest(count).expect("the pruned digest"))
    }

    fn records_since(&self, records: &RecordState) -> anyhow::Result<(u64, Vec<Vec<OpId>>)> {
        let pruned = self.store.pruned();
        let from = usize::try_from(records.count)
            .ok()
            .filter(|&count| {
                self.store.digest(count).map(|digest| digest.bytes()) == Some(&records.digest[..])
            })
            .unwrap_or(pruned);
        let records = self.store.records()[from - pruned..]
            .iter()
            .map(|record| record.ops().iter().map(|op| op.0.0.clone()).collect())
            .collect();
        Ok((from as u64, records))
    }

    fn report(&mut self, machine: &str, records: &RecordState) {
        let now = self.now();
        self.machines.report(machine, records, now);
    }

    fn reported(&self, machine: &str) -> Option<RecordState> {
        self.machines
            .reports
            .get(machine)
            .map(|(taken, _)| taken.clone())
    }

    fn prune(&mut self, count: u64) -> anyhow::Result<()> {
        // All of them at once: only then is nothing left to replay on opening.
        anyhow::ensure!(
            count == self.store.record_count() as u64,
            "the hub prunes all its records at once, not {count} of {}",
            self.store.record_count()
        );
        self.contracted.take();
        Ok(self.store.prune()?)
    }

    fn is_dropped(&self, op: &OpId, dropped: &[OpId]) -> anyhow::Result<bool> {
        Ok(self.store.is_superseded(op) || dropped.contains(op))
    }

    fn store_ops(&mut self, ops: &[OpId], attachment: &Attachment) -> anyhow::Result<()> {
        let imported = match self
            .store
            .canonical()
            .import_operations(attachment.bundle_path()?)
        {
            Ok(imported) => imported,
            // Views sent as deltas against views this hub lacks, by a node that doesn't yet
            // know the hub went back or made the hive again, which its push expects at a head
            // the hub lacks: the push stores no more, so it can't be accepted, and its answer
            // gives the node the hub's head.
            Err(err @ CanonicalError::MissingDeltaBase { .. }) => {
                tracing::info!("not storing a push's operations: {err}");
                return Ok(());
            }
            Err(err) => return Err(err.into()),
        };
        let imported: BTreeSet<&OpId> = imported.iter().map(|(id, _)| &id.0).collect();
        if let Some(missing) = ops.iter().find(|op| !imported.contains(op)) {
            bail!("bundle lacks announced operation {missing:?}");
        }
        Ok(())
    }

    fn store_objects(&mut self, _: &[OpId], attachment: &Attachment) -> anyhow::Result<()> {
        // No connectivity check here: the operations may not have arrived yet. `Cas` checks
        // the whole closure before anything can refer to these objects.
        self.store
            .object_store()
            .import(attachment.bundle_path()?, &[], &[])?;
        Ok(())
    }

    fn ops_since(
        &self,
        head: &OpId,
        base: &OpId,
    ) -> anyhow::Result<(Vec<OpEntry<OpId>>, Attachment)> {
        self.ops_with_records(head, base, &[])
    }

    fn ops_with_records(
        &self,
        head: &OpId,
        base: &OpId,
        records: &[Vec<OpId>],
    ) -> anyhow::Result<(Vec<OpEntry<OpId>>, Attachment)> {
        let ids = self.store.ops_since(head, base)?;
        if ids.is_empty() && records.is_empty() {
            return Ok((vec![], Attachment::None));
        }
        let canonical = self.store.canonical();
        let mut entries = Vec::with_capacity(ids.len());
        let ids: Vec<CanonicalOp> = ids.into_iter().map(CanonicalOp).collect();
        for id in &ids {
            entries.push(OpEntry {
                id: id.0.clone(),
                parents: canonical.parents(id)?.into_iter().map(|op| op.0).collect(),
            });
        }
        let bundle = temp_bundle(&self.tmp)?;
        let record_ops: Vec<CanonicalOp> =
            records.iter().flatten().cloned().map(CanonicalOp).collect();
        canonical.export_operations_with_records(&ids, &record_ops, &bundle)?;
        Ok((entries, Attachment::bundle(bundle)))
    }

    fn objects_for(
        &self,
        for_ops: &[OpId],
        base: &OpId,
        haves: &Attachment,
    ) -> anyhow::Result<Attachment> {
        let stored: Vec<OpId> = for_ops
            .iter()
            .filter(|op| {
                self.store
                    .canonical()
                    .has_operation(&CanonicalOp((*op).clone()))
            })
            .cloned()
            .collect();
        let wants = self.store.required_commits(&stored)?;
        if wants.is_empty() {
            return Ok(Attachment::None);
        }
        let wants: Vec<CommitId> = wants.into_iter().collect();
        let objects = self.store.object_store();
        let absent = objects.missing(&wants)?;
        let present: Vec<CommitId> = wants.into_iter().filter(|c| !absent.contains(c)).collect();
        // The node has `closure(base)`, and what it says it has.
        let mut haves: BTreeSet<CommitId> = haves.haves().iter().cloned().collect();
        if self
            .store
            .canonical()
            .has_operation(&CanonicalOp(base.clone()))
        {
            haves.extend(self.store.required_commits(std::slice::from_ref(base))?);
        }
        let haves: Vec<CommitId> = haves.into_iter().collect();
        let bundle = temp_bundle(&self.tmp)?;
        objects.export(&present, &haves, &bundle)?;
        Ok(Attachment::bundle(bundle))
    }

    fn is_closed(&self, op: &OpId, dropped: &[OpId]) -> anyhow::Result<bool> {
        let missing = if dropped.is_empty() {
            self.store.missing_closure(op)?
        } else {
            self.with_contracted(dropped, |contracted| {
                Ok(self.store.missing_closure_with(op, Some(contracted))?)
            })?
        };
        if !missing.is_empty() {
            // The node hears only that the push can't be taken (`Incomplete`).
            let shown: Vec<&str> = missing.iter().take(5).map(String::as_str).collect();
            tracing::warn!(
                "a push of {} can't be taken: {} missing, abandoned or repeated, among them {}",
                short(op),
                missing.len(),
                shown.join(", ")
            );
        }
        Ok(missing.is_empty())
    }

    fn descends(&self, ancestor: &OpId, op: &OpId, dropped: &[OpId]) -> anyhow::Result<bool> {
        if !dropped.is_empty() {
            // `ancestor`, as the history names it with `dropped` dropped too: what it is
            // then, every operation of which `op` must descend from.
            let images =
                self.with_contracted(dropped, |contracted| Ok(contracted.image(ancestor)))?;
            let canonical = self.store.canonical();
            let op = CanonicalOp(op.clone());
            for image in &images {
                if !canonical.is_ancestor_of(&CanonicalOp(image.clone()), &op)? {
                    return Ok(false);
                }
            }
            return Ok(!images.is_empty());
        }
        if ancestor == self.store.head().1 {
            return Ok(self.store.descends_from_head(op)?);
        }
        let canonical = self.store.canonical();
        if *ancestor == canonical.root_operation_id().0 {
            return Ok(true);
        }
        let ancestry = canonical.ancestors_until(&[CanonicalOp(op.clone())], |_| false)?;
        Ok(ancestry.contains(&CanonicalOp(ancestor.clone())))
    }
}

#[cfg(test)]
mod tests {
    use musubi_jj::presence::Kind;

    use super::*;

    fn machines(opened: Instant) -> Machines {
        Machines {
            reports: HashMap::new(),
            joining: HashMap::new(),
            opened,
            aged: Duration::ZERO,
        }
    }

    fn records(count: u64) -> RecordState {
        RecordState {
            count,
            digest: vec![count as u8],
        }
    }

    /// The native examples retain successful join/rejoin and a stranded copy's refusal.
    /// This table pins the restart grace and expiry policy without making repositories.
    #[test]
    fn pruning_waits_for_recent_joins_and_restart_grace() {
        let start = Instant::now();
        let tick = Duration::from_nanos(1);
        let hour = Duration::from_secs(3600);
        let day = Duration::from_secs(24 * 3600);
        for (elapsed, waiting) in [(hour - tick, true), (hour, false), (hour + tick, false)] {
            let state = machines(start);
            assert_eq!(state.waits_after_opening(start + elapsed), waiting);
        }

        // Restart loses reports and explicit joins; a fresh opening starts a new grace.
        let restarted = machines(start + day);
        assert!(restarted.reports.is_empty() && restarted.joining.is_empty());
        assert!(restarted.waits_after_opening(start + day + hour - tick));
        assert!(!restarted.waits_after_opening(start + day + hour));

        for (known, present, rejoining, protected) in [
            (false, false, false, true), // A new copy's first fetch has reported.
            (true, false, true, true),   // A forgotten copy explicitly joins again.
            (true, false, false, false), // A forgotten daemon's reports don't count.
            (true, true, false, true),   // A present copy never expires.
            (true, true, true, true),    // Its first push retires the explicit join.
        ] {
            let mut presence = Presence::<usize>::default();
            if known {
                presence = presence.apply(
                    &1,
                    &Kind {
                        work: Some("gamma".to_owned()),
                        ..Kind::default()
                    },
                );
            }
            if known && !present {
                presence = presence.apply(
                    &2,
                    &Kind {
                        forgets: ["gamma".to_owned()].into(),
                        ..Kind::default()
                    },
                );
            }
            // Even without a report, every present copy must be waited for.
            let mut unreported = machines(start);
            assert_eq!(
                unreported.waited_for(&presence, start).contains("gamma"),
                present
            );
            for (elapsed, recent) in [
                (23 * hour, true),
                (day - tick, true),
                (day, false),
                (25 * hour, false),
            ] {
                let now = start + elapsed;
                let mut state = machines(start);
                if rejoining {
                    state.joining.insert("gamma".to_owned(), start);
                }
                state.report("gamma", &records(0), start);
                state.retire_joins(&presence, now);
                let waited = state.waited_for(&presence, now);
                let expected = protected && (present || recent);
                assert_eq!(
                    waited.contains("gamma"),
                    expected,
                    "{known}, {present}, {rejoining}, {elapsed:?}"
                );
                assert_eq!(state.reports.contains_key("gamma"), expected);
                assert_eq!(
                    state.joining.contains_key("gamma"),
                    rejoining && !present && recent
                );
            }
        }

        // Reporting unchanged records refreshes the day from the last fetch, including
        // an explicit rejoin of a known, absent copy. A new report also replaces its value.
        let absent = Presence::<usize>::default().apply(
            &1,
            &Kind {
                forgets: ["gamma".to_owned()].into(),
                ..Kind::default()
            },
        );
        let mut state = machines(start);
        state.joining.insert("gamma".to_owned(), start);
        state.report("gamma", &records(0), start);
        let halfway = start + day / 2;
        state.report("gamma", &records(0), halfway);
        let renewed = halfway + day - tick;
        state.retire_joins(&absent, renewed);
        assert!(state.waited_for(&absent, renewed).contains("gamma"));
        state.report("gamma", &records(1), renewed);
        assert_eq!(state.reports["gamma"], (records(1), renewed));
        let expired = renewed + day;
        state.retire_joins(&absent, expired);
        assert!(state.waited_for(&absent, expired).is_empty());
    }
}

//! The core's `HubStorage` over a hub store.

use std::cell::RefCell;
use std::collections::BTreeSet;
use std::path::Path;
use std::path::PathBuf;

use anyhow::bail;
use jj_lib::backend::CommitId;
use musubi_core::hub::HubStorage;
use musubi_core::message::OpEntry;
use musubi_core::message::RecordState;
use musubi_hub::store::Contracted;
use musubi_hub::store::HubStore;
use musubi_jj::canonical::CanonicalError;
use musubi_jj::objects::Backend;
use musubi_jj::op_id::CanonicalOp;
use musubi_jj::records::HubOp;

use crate::Attachment;
use crate::OpId;
use crate::open_bundle_dir;
use crate::short;
use crate::temp_bundle;

pub struct HubAdapter {
    store: HubStore,
    tmp: PathBuf,
    /// The history with a supersede's drops dropped too, as a push asks about it: the same
    /// for each of its questions, and for taking it.
    contracted: RefCell<Option<Contracted>>,
}

impl HubAdapter {
    pub fn init(dir: &Path, backend: Backend) -> anyhow::Result<Self> {
        Self::new(HubStore::init(dir, backend)?, dir)
    }

    pub fn open(dir: &Path) -> anyhow::Result<Self> {
        Self::new(HubStore::open(dir)?, dir)
    }

    pub fn new(store: HubStore, dir: &Path) -> anyhow::Result<Self> {
        let tmp = dir.join("tmp");
        open_bundle_dir(&tmp)?;
        Ok(Self {
            store,
            tmp,
            contracted: RefCell::new(None),
        })
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
}

impl HubStorage for HubAdapter {
    type Op = OpId;
    type Attachment = Attachment;
    type Error = anyhow::Error;

    fn head(&self) -> (u64, OpId) {
        let (seq, head) = self.store.head();
        (seq, head.clone())
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
        let count = self.store.records().len();
        RecordState {
            count: count as u64,
            digest: self
                .store
                .digest(count)
                .expect("a digest per prefix")
                .bytes()
                .to_vec(),
        }
    }

    fn records_since(&self, records: &RecordState) -> anyhow::Result<(u64, Vec<Vec<OpId>>)> {
        let all = self.store.records();
        let from = usize::try_from(records.count)
            .ok()
            .filter(|&count| {
                self.store.digest(count).map(|digest| digest.bytes()) == Some(&records.digest[..])
            })
            .unwrap_or(0);
        let records = all[from..]
            .iter()
            .map(|record| record.ops().iter().map(|op| op.0.0.clone()).collect())
            .collect();
        Ok((from as u64, records))
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
        let ids = self.store.ops_since(head, base)?;
        if ids.is_empty() {
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
        canonical.export_operations(&ids, &bundle)?;
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
            // The node hears only that something is missing (`Incomplete`).
            let shown: Vec<&str> = missing.iter().take(5).map(String::as_str).collect();
            tracing::warn!(
                "a push of {} can't be closed: {} missing, among them {}",
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

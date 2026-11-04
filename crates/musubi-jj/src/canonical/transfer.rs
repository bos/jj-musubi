//! Exporting canonical histories and admitting incoming bundles in bounded batches.

use std::collections::HashMap;
use std::collections::HashSet;
use std::path::Path;
#[cfg(test)]
use std::sync::PoisonError;

use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::ViewId;

use super::CanonicalError;
use super::CanonicalStore;
use super::is_root_view;
use super::validate::Admitted;
use super::validate::admit;
use super::validate::encoded_view_commits;
use super::validate::encoded_view_id;
use super::validate::names_decoded_commits;
use super::validate::normal_view;
use super::validate::view_commit_ids;
use crate::objects::ObjectError;
use crate::objects::bundle;
use crate::objects::bundle::BundleWriter;
use crate::objects::bundle::Record;
use crate::op_id::CanonicalOp;

/// `work` done on each of `items`, by as many workers as are worth it, each numbered and
/// given a share in order, with the results in order. A panic in a worker is passed on as it
/// is: jj-lib and jj-core panic on some malformed views.
fn in_parallel<T: Sync, R: Send>(items: &[T], work: impl Fn(usize, &T) -> R + Sync) -> Vec<R> {
    let workers = std::thread::available_parallelism()
        .map_or(1, |n| n.get())
        .min(MAX_WORKERS)
        .min(items.len().div_ceil(MIN_PER_WORKER))
        .max(1);
    if workers == 1 {
        return items.iter().map(|item| work(0, item)).collect();
    }
    let share = items.len().div_ceil(workers);
    let work = &work;
    std::thread::scope(|scope| {
        let workers: Vec<_> = items
            .chunks(share)
            .enumerate()
            .map(|(worker, items)| {
                scope.spawn(move || {
                    items
                        .iter()
                        .map(|item| work(worker, item))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|worker| {
                worker
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect()
    })
}

/// How many views an import verifies, in parallel, before appending them: few in tests and
/// fuzzing, so that they cross batches.
const IMPORT_BATCH: usize = if cfg!(any(test, fuzzing)) { 2 } else { 512 };

/// How many records, of operations and views, an import takes in before appending them.
const IMPORT_ITEMS: usize = 4096;

/// How many bytes of views and operations an import takes in before appending them, so
/// that a bundle of many large views is taken in a part at a time. A single view may still
/// be as large as a record may be.
const IMPORT_BYTES: usize = 64 << 20;

/// The most workers an import verifies views with.
const MAX_WORKERS: usize = 16;

/// The fewest views worth a worker of their own.
const MIN_PER_WORKER: usize = 16;

/// A view an import is to store, with the delta it came as, if any, and its base.
struct Pending {
    id: ViewId,
    contents: Vec<u8>,
    delta: Option<Delta>,
}

/// A delta a view came as, with its base, and the bytes of the base it was applied to.
struct Delta {
    base: ViewId,
    bytes: Vec<u8>,
    applied_to: Applied,
}

/// The bytes of its base a delta was applied to.
enum Applied {
    /// The store's: in normal form.
    Stored,
    /// Those of the view at this index in [`Batch::views`], as received.
    Batch(usize),
    /// Those of a view received in an earlier batch, as received.
    Earlier,
}

enum Item {
    /// The view at this index in [`Batch::views`].
    View(usize),
    Operation(OperationId, Vec<u8>),
}

/// What an import has taken in, in the order the bundle had it, and not yet stored.
#[derive(Default)]
struct Batch {
    items: Vec<Item>,
    views: Vec<Pending>,
    /// Each view's index in `views`.
    by_id: HashMap<ViewId, usize>,
    /// What the views and operations take, roughly.
    bytes: usize,
}

impl Batch {
    fn push_view(&mut self, id: ViewId, contents: Vec<u8>, delta: Option<Delta>) {
        self.bytes += contents.len() + delta.as_ref().map_or(0, |delta| delta.bytes.len());
        self.by_id.insert(id.clone(), self.views.len());
        self.items.push(Item::View(self.views.len()));
        self.views.push(Pending {
            id,
            contents,
            delta,
        });
    }

    /// A view taken in, as received.
    fn view(&self, id: &ViewId) -> Option<&[u8]> {
        self.by_id
            .get(id)
            .map(|&i| self.views[i].contents.as_slice())
    }

    /// Whether to store what it holds before taking in more.
    fn full(&self) -> bool {
        self.views.len() >= IMPORT_BATCH
            || self.items.len() >= IMPORT_ITEMS
            || self.bytes >= IMPORT_BYTES
    }
}

/// An operation [`CanonicalStore::import_operations`] took in, with its parents if it stored
/// it, or `None` if it was stored already.
pub type Imported = (CanonicalOp, Option<Vec<CanonicalOp>>);

impl CanonicalStore {
    /// Writes `ops` and their views to a bundle, compressed, in the given order, which must
    /// put ancestors first (as [`Self::ancestors_until`] does).
    ///
    /// The reader must have the parents of `ops` that are not among them, as it does when
    /// `ops` is `anc*(head) \ anc*(base)` and it has `base`. Then it has every parent's view
    /// by the time it reads an operation, so a view a parent has is not sent at all, and
    /// any other view goes as a delta against the first parent's: consecutive views
    /// usually differ in a few bookmarks, however large they are. A delta is between the two
    /// views' normal forms (see `normal_view_bytes`), as the reader assumes when it
    /// takes the view one delta made as the base of the next.
    pub fn export_operations(&self, ops: &[CanonicalOp], out: &Path) -> Result<(), CanonicalError> {
        let mut writer = BundleWriter::create(out)?;
        writer.begin_compressed()?;
        let mut sent = HashSet::new();
        // The views of the operations written so far, which are usually the next ones'
        // parents.
        let mut views: HashMap<CanonicalOp, ViewId> = HashMap::new();
        // The last view a delta went to, in normal form: usually the next delta's base.
        let mut last: Option<(ViewId, Vec<u8>)> = None;
        for id in ops {
            let encoded = self.operation_bytes(id)?;
            let view_id = encoded_view_id(&encoded)
                .ok_or_else(|| CanonicalError::MalformedOperation(id.0.hex()))?;
            let view_id = ViewId::from_bytes(view_id);
            let mut parent_views = vec![];
            for parent in self.parents(id)? {
                parent_views.push(match views.get(&parent) {
                    Some(view) => view.clone(),
                    None => self.read_operation(&parent)?.view_id,
                });
            }
            let view = &view_id;
            if !is_root_view(view) && !parent_views.contains(view) && sent.insert(view.clone()) {
                let base = parent_views.first().filter(|base| !is_root_view(base));
                let stored = match base {
                    Some(base) => self
                        .shared
                        .log
                        .stored_delta_against(view, base)
                        .map_err(self.shared.log_err())?,
                    None => None,
                };
                match base {
                    // Stored against the base the reader has: sent as it is.
                    Some(base) if stored.is_some() => {
                        let delta = stored.expect("matched");
                        writer.view_delta_made(view.as_bytes(), base.as_bytes(), &delta)?;
                        last = None;
                    }
                    Some(base) => {
                        let base_bytes = match last.take() {
                            Some((last_id, bytes)) if last_id == *base => bytes,
                            _ => self.normal_view_bytes(base)?,
                        };
                        let view_bytes = self.normal_view_bytes(view)?;
                        writer.view_delta(
                            view.as_bytes(),
                            base.as_bytes(),
                            &base_bytes,
                            &view_bytes,
                        )?;
                        last = Some((view.clone(), view_bytes));
                    }
                    None => writer.view(view.as_bytes(), &self.view_bytes(view)?)?,
                }
            }
            writer.operation(id.0.as_bytes(), &encoded)?;
            views.insert(id.clone(), view_id);
        }
        Ok(writer.finish()?)
    }

    /// Exports operations with the canonical bodies needed to rename record names later.
    /// The extra bodies are metadata, including their parents and views; receivers must
    /// not stage or realize them merely because they occur in the bundle.
    pub fn export_operations_with_records(
        &self,
        ops: &[CanonicalOp],
        record_ops: &[CanonicalOp],
        out: &Path,
    ) -> Result<(), CanonicalError> {
        if record_ops.is_empty() {
            return self.export_operations(ops, out);
        }
        let mut exported = self.record_operations(record_ops)?;
        let mut seen: HashSet<CanonicalOp> = exported.iter().cloned().collect();
        exported.extend(ops.iter().filter(|op| seen.insert((*op).clone())).cloned());
        self.export_operations(&exported, out)
    }

    /// The complete operation ancestry of record names, parents first. Unlike
    /// `ancestors_until`, missing bodies or views are errors: a record holder must be able
    /// to rename every name after a later rollback, without realizing its old history.
    pub fn record_operations(
        &self,
        record_ops: &[CanonicalOp],
    ) -> Result<Vec<CanonicalOp>, CanonicalError> {
        let ops = self.ancestors_until(record_ops, |_| false)?;
        for id in record_ops.iter().chain(&ops) {
            let op = self.read_operation(id)?;
            if !self.has_view(&op.view_id) {
                self.read_view(&op.view_id)?;
            }
            for parent in &op.parents {
                self.read_operation(&CanonicalOp(parent.clone()))?;
            }
        }
        Ok(ops)
    }

    /// Verifies and stores the views and operations of a bundle written by
    /// [`Self::export_operations`]. Returns the operations in bundle order, each with its
    /// parents if this stored it, or `None` if it was stored already.
    pub fn import_operations(&self, bundle_path: &Path) -> Result<Vec<Imported>, CanonicalError> {
        let mut ops = vec![];
        let mut batch = Batch::default();
        // The last view a delta made, in normal form (see `normal_view_bytes`): usually the
        // next delta's base, since consecutive operations' views go as deltas against each
        // other.
        let mut last: Option<(ViewId, Vec<u8>)> = None;
        bundle::read(bundle_path, |record| {
            match record {
                Record::View { id, contents } => {
                    let id = ViewId::new(id);
                    if !self.has_view(&id) && batch.view(&id).is_none() {
                        batch.push_view(id, contents, None);
                    }
                }
                Record::ViewDelta { id, base, delta } => {
                    let (id, base) = (ViewId::new(id), ViewId::new(base));
                    if !self.has_view(&id) && batch.view(&id).is_none() {
                        let in_batch = batch.by_id.get(&base).copied();
                        let (base_contents, applied_to) = match last.take() {
                            Some((last_id, bytes)) if last_id == base => {
                                (bytes, in_batch.map_or(Applied::Earlier, Applied::Batch))
                            }
                            _ => match in_batch {
                                Some(at) => (batch.views[at].contents.clone(), Applied::Batch(at)),
                                None if self.has_view(&base) => {
                                    (self.normal_view_bytes(&base)?, Applied::Stored)
                                }
                                None => {
                                    return Err(CanonicalError::MissingDeltaBase {
                                        view: id.hex(),
                                        base: base.hex(),
                                    });
                                }
                            },
                        };
                        let contents = bundle::apply_view_delta(&base_contents, &delta)?;
                        last = Some((id.clone(), contents.clone()));
                        let delta = Delta {
                            base,
                            bytes: delta,
                            applied_to,
                        };
                        batch.push_view(id, contents, Some(delta));
                    }
                }
                Record::Operation { id, contents } => {
                    batch.bytes += contents.len();
                    batch
                        .items
                        .push(Item::Operation(OperationId::new(id), contents));
                }
                _ => {
                    return Err(ObjectError::MalformedBundle(
                        "unexpected record in an operation bundle".to_owned(),
                    )
                    .into());
                }
            }
            if batch.full() {
                self.store_batch(std::mem::take(&mut batch), &mut ops)?;
            }
            Ok(())
        })?;
        self.store_batch(batch, &mut ops)?;
        Ok(ops)
    }

    /// Verifies the views and operations of `batch`, the views in parallel, then appends
    /// them all, in order, under one lock. Adds the operations to `ops`, as
    /// [`Self::import_operations`] returns them.
    fn store_batch(&self, batch: Batch, ops: &mut Vec<Imported>) -> Result<(), CanonicalError> {
        let normal = self.verify_views(&batch.views)?;
        // Which views came in normal form.
        let normal_form: Vec<bool> = batch
            .views
            .iter()
            .zip(&normal)
            .map(|(view, normal)| view.contents == *normal)
            .collect();
        // The operations to store, each once: not those stored already.
        let mut seen = HashSet::new();
        let new: Vec<(usize, &OperationId, &[u8])> = batch
            .items
            .iter()
            .enumerate()
            .filter_map(|(at, item)| match item {
                Item::Operation(id, bytes) => Some((at, id, bytes.as_slice())),
                Item::View(_) => None,
            })
            .filter(|(_, id, _)| {
                !self.has_operation(&CanonicalOp((*id).clone())) && seen.insert((*id).clone())
            })
            .collect();
        let verified = in_parallel(&new, |_, (_, id, bytes)| self.verify_operation(id, bytes));
        let mut stored: Vec<Option<Vec<OperationId>>> = vec![None; batch.items.len()];
        for ((at, _, _), parents) in new.iter().zip(verified) {
            stored[*at] = Some(parents?);
        }
        #[cfg(test)]
        if let Some(meanwhile) = self
            .meanwhile
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .take()
        {
            meanwhile();
        }
        self.shared
            .log
            .append(|appender| {
                // Which views this append wrote, with the bytes this batch has for them.
                let mut written = vec![false; batch.views.len()];
                for (item, parents) in batch.items.iter().zip(&stored) {
                    match item {
                        Item::View(index) => {
                            let Pending {
                                id,
                                contents,
                                delta,
                            } = &batch.views[*index];
                            let normal = &normal[*index];
                            // The delta made the bytes received from those of its base it was
                            // applied to. Stored, it makes, from the bytes the log holds for the
                            // base, the view's: so only if both are what the log holds. For a
                            // base in this batch, the log holds its bytes only if they were in
                            // normal form and this append wrote them: another process may have
                            // appended it first, in bytes of its own.
                            let in_normal_form = |at: usize| normal_form[at] && written[at];
                            let delta = delta
                                .as_ref()
                                .filter(|delta| {
                                    normal == contents
                                        && match delta.applied_to {
                                            Applied::Stored => true,
                                            Applied::Batch(at) => in_normal_form(at),
                                            Applied::Earlier => false,
                                        }
                                })
                                .map(|delta| (&delta.base, delta.bytes.as_slice()));
                            written[*index] = appender.view(id, normal, delta)?;
                        }
                        Item::Operation(id, bytes) => {
                            if parents.is_some() {
                                appender.operation(id, bytes)?;
                            }
                        }
                    }
                }
                Ok(())
            })
            .map_err(self.shared.log_err())?;
        for (item, parents) in batch.items.into_iter().zip(stored) {
            if let Item::Operation(id, _) = item {
                let parents = parents.map(|parents| parents.into_iter().map(CanonicalOp).collect());
                ops.push((CanonicalOp(id), parents));
            }
        }
        Ok(())
    }

    /// Checks each view, decoded, against its id, as [`Self::import_view`] does, and returns
    /// its normal form. Decoding takes most of an import's time, so workers share it, each
    /// with a scratch store of its own.
    fn verify_views(&self, views: &[Pending]) -> Result<Vec<Vec<u8>>, CanonicalError> {
        self.shared
            .views
            .with_workers(|| in_parallel(views, |worker, view| self.verify_view(worker, view)))
            .into_iter()
            .collect()
    }

    fn verify_view(&self, worker: usize, view: &Pending) -> Result<Vec<u8>, CanonicalError> {
        let Pending { id, contents, .. } = view;
        let normal =
            normal_view(contents).ok_or_else(|| CanonicalError::MalformedView(id.hex()))?;
        let decoded = self.shared.views.decode_in(worker, id, &normal)?;
        admit(Admitted {
            kind: "view",
            malformed: CanonicalError::MalformedView,
            expected: id.hex(),
            actual: ViewId::new(blake2b_hash(&decoded).to_vec()).hex(),
            names_its_commits: names_decoded_commits(
                &normal,
                encoded_view_commits,
                view_commit_ids(&decoded),
            ),
        })?;
        Ok(normal)
    }

    /// A stored view in normal form (see `normal_view`), which is how the store holds
    /// it.
    fn normal_view_bytes(&self, id: &ViewId) -> Result<Vec<u8>, CanonicalError> {
        self.view_bytes(id)
    }
}

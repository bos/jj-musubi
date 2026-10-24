//! The canonical op store: replicated operations, written by this jj-lib.
//!
//! Canonical ids are ordinary jj operation and view ids, and the operations and views are
//! encoded as jj's simple op store encodes them, but they are kept in one log (see
//! `canonical/log.rs`): operations as encoded, and views as deltas. Operations and views
//! received from peers are verified by decoding and re-hashing before they enter the
//! store; this works because every canonical one was written by the same pinned jj-lib, so
//! decoding and re-hashing round-trips exactly.

mod codec;
mod log;

use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;

use async_trait::async_trait;
use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::HexPrefix;
use jj_lib::object_id::ObjectId as _;
use jj_lib::object_id::PrefixResolution;
use jj_lib::op_store::OpStore;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::OpStoreResult;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RemoteRef;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use pollster::FutureExt as _;
use thiserror::Error;

use self::codec::ViewCodec;
use self::log::Log;
use crate::objects::ObjectError;
use crate::objects::bundle;
use crate::objects::bundle::BundleWriter;
use crate::objects::bundle::Record;
use crate::protobuf::next_field;

#[derive(Debug, Error)]
pub enum CanonicalError {
    #[error(transparent)]
    Bundle(#[from] ObjectError),
    #[error(transparent)]
    OpStore(#[from] OpStoreError),
    #[error("I/O error on {path}")]
    Io { path: PathBuf, source: io::Error },
    #[error("received {kind} {expected} hashes to {actual}")]
    HashMismatch {
        kind: &'static str,
        expected: String,
        actual: String,
    },
    #[error("received view {view} as a delta against view {base}, which is not stored")]
    MissingDeltaBase { view: String, base: String },
    #[error("view {0} is malformed")]
    MalformedView(String),
    #[error("operation {0} is malformed")]
    MalformedOperation(String),
}

impl CanonicalError {
    /// Whether this error, reading a stored operation or view, says that it couldn't be
    /// read, as when the process is out of file descriptors, rather than that what was read
    /// is wrong: an I/O error other than the file being missing or short.
    pub fn unreadable(&self) -> bool {
        let mut source: Option<&(dyn std::error::Error + 'static)> = Some(self);
        while let Some(err) = source {
            if let Some(err) = err.downcast_ref::<io::Error>() {
                return !matches!(
                    err.kind(),
                    io::ErrorKind::NotFound
                        | io::ErrorKind::UnexpectedEof
                        | io::ErrorKind::InvalidData
                );
            }
            source = err.source();
        }
        false
    }
}

/// What an operation or view arriving in a bundle turned out to be, once decoded.
struct Admitted {
    kind: &'static str,
    /// The error for one whose encoding names other commits than its decoding does.
    malformed: fn(String) -> CanonicalError,
    expected: String,
    actual: String,
    /// Whether its encoding names exactly the commits its decoding does.
    names_its_commits: bool,
}

/// `work` done on each of `items`, by as many workers as are worth it, each numbered and
/// given a share in order, with the results in order. A panic in a worker is passed on as it
/// is: jj-lib panics on some malformed views.
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

/// How many views an import verifies, in parallel, before appending them: few in tests, so
/// that they cross batches.
const IMPORT_BATCH: usize = if cfg!(test) { 2 } else { 512 };

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

/// Whether an operation or view is what it says it is, and may be stored.
fn admit(checked: Admitted) -> Result<(), CanonicalError> {
    let Admitted {
        kind,
        malformed,
        expected,
        actual,
        names_its_commits,
    } = checked;
    if expected != actual {
        Err(CanonicalError::HashMismatch {
            kind,
            expected,
            actual,
        })
    } else if !names_its_commits {
        Err(malformed(expected))
    } else {
        Ok(())
    }
}

fn io_err(path: &Path) -> impl FnOnce(io::Error) -> CanonicalError + '_ {
    move |source| CanonicalError::Io {
        path: path.to_owned(),
        source,
    }
}

/// An operation [`CanonicalStore::import_operations`] took in, with its parents if it stored
/// it, or `None` if it was stored already.
pub type Imported = (OperationId, Option<Vec<OperationId>>);

pub struct CanonicalStore {
    shared: Arc<Shared>,
    /// Generation numbers of stored operations (the root 0, otherwise one more than the
    /// largest parent's), which bound ancestry searches. A stored operation never changes,
    /// so neither does its entry.
    generations: Mutex<HashMap<OperationId, u64>>,
    /// In tests, what another process does between an import's checking a batch and its
    /// appending it.
    #[cfg(test)]
    meanwhile: Mutex<Option<Box<dyn FnOnce() + Send>>>,
}

/// The store as jj's [`OpStore`], for jj's walks over operations.
#[derive(Debug)]
struct Shared {
    path: PathBuf,
    root_commit_id: CommitId,
    root_operation_id: OperationId,
    root_view_id: ViewId,
    log: Log,
    views: ViewCodec,
}

impl Shared {
    fn log_err(&self) -> impl FnOnce(io::Error) -> CanonicalError + '_ {
        io_err(&self.path)
    }

    fn not_found(kind: &str, hex: String) -> OpStoreError {
        OpStoreError::ObjectNotFound {
            object_type: kind.to_owned(),
            hash: hex,
            source: None,
        }
    }

    fn read_error(
        kind: &str,
        hex: String,
        source: impl Into<Box<dyn std::error::Error + Send + Sync>>,
    ) -> OpStoreError {
        OpStoreError::ReadObject {
            object_type: kind.to_owned(),
            hash: hex,
            source: source.into(),
        }
    }

    fn operation_bytes(&self, id: &OperationId) -> Result<Vec<u8>, CanonicalError> {
        self.log
            .operation(id)
            .map_err(self.log_err())?
            .ok_or_else(|| Self::not_found("operation", id.hex()).into())
    }

    fn view_bytes(&self, id: &ViewId) -> Result<Vec<u8>, CanonicalError> {
        self.log
            .view(id)
            .map_err(self.log_err())?
            .ok_or_else(|| Self::not_found("view", id.hex()).into())
    }

    fn read_operation(&self, id: &OperationId) -> Result<Operation, CanonicalError> {
        if *id == self.root_operation_id {
            return Ok(Operation::make_root(self.root_view_id.clone()));
        }
        let bytes = self.operation_bytes(id)?;
        let op = codec::decode_operation(&bytes, &self.root_operation_id)
            .map_err(|err| Self::read_error("operation", id.hex(), err))?;
        // A stored operation was checked as it arrived; this checks the decoding, which is
        // musubi's rather than jj's.
        let actual = OperationId::new(blake2b_hash(&op).to_vec());
        if actual != *id {
            return Err(CanonicalError::HashMismatch {
                kind: "operation",
                expected: id.hex(),
                actual: actual.hex(),
            });
        }
        Ok(op)
    }

    /// An operation's parents, as jj decodes them, read from its encoding: a walk over the
    /// history needs only those, and decoding and hashing the whole operation at every step
    /// would take most of its time. Every stored operation was checked as it arrived.
    fn parents(&self, id: &OperationId) -> Result<Vec<OperationId>, CanonicalError> {
        if *id == self.root_operation_id {
            return Ok(vec![]);
        }
        let bytes = self.operation_bytes(id)?;
        let mut parents = vec![];
        each_field(&bytes, |number, payload| {
            if number == 2 {
                (payload.len() == log::ID_LEN).then_some(())?;
                parents.push(OperationId::from_bytes(payload));
            }
            Some(())
        })
        .ok_or_else(|| CanonicalError::MalformedOperation(id.hex()))?;
        // As jj reads an operation from before it had a root operation.
        if parents.is_empty() {
            parents.push(self.root_operation_id.clone());
        }
        Ok(parents)
    }

    fn read_view(&self, id: &ViewId) -> Result<View, CanonicalError> {
        if *id == self.root_view_id {
            return Ok(View::make_root(self.root_commit_id.clone()));
        }
        Ok(self.views.decode(id, &self.view_bytes(id)?)?)
    }

    fn write_operation(&self, op: &Operation) -> Result<OperationId, CanonicalError> {
        let id = OperationId::new(blake2b_hash(op).to_vec());
        self.log
            .append_operation(&id, &codec::encode_operation(op))
            .map_err(self.log_err())?;
        Ok(id)
    }

    fn write_view(&self, view: &View) -> Result<ViewId, CanonicalError> {
        let (id, encoded) = self.views.encode(view)?;
        let normal =
            normal_view(&encoded).ok_or_else(|| CanonicalError::MalformedView(id.hex()))?;
        self.log.append_view(&id, &normal).map_err(self.log_err())?;
        Ok(id)
    }
}

/// An error from the store, as jj's [`OpStore`] reports one.
fn op_store_error(err: CanonicalError) -> OpStoreError {
    match err {
        CanonicalError::OpStore(err) => err,
        err => OpStoreError::Other(err.into()),
    }
}

#[async_trait]
impl OpStore for Shared {
    fn name(&self) -> &'static str {
        "musubi_canonical"
    }

    fn root_operation_id(&self) -> &OperationId {
        &self.root_operation_id
    }

    async fn read_view(&self, id: &ViewId) -> OpStoreResult<View> {
        Self::read_view(self, id).map_err(op_store_error)
    }

    async fn write_view(&self, contents: &View) -> OpStoreResult<ViewId> {
        Self::write_view(self, contents).map_err(op_store_error)
    }

    async fn read_operation(&self, id: &OperationId) -> OpStoreResult<Operation> {
        Self::read_operation(self, id).map_err(op_store_error)
    }

    async fn write_operation(&self, contents: &Operation) -> OpStoreResult<OperationId> {
        Self::write_operation(self, contents).map_err(op_store_error)
    }

    async fn resolve_operation_id_prefix(
        &self,
        prefix: &HexPrefix,
    ) -> OpStoreResult<PrefixResolution<OperationId>> {
        self.log
            .resolve_prefix(prefix, &self.root_operation_id)
            .map_err(|err| OpStoreError::Other(err.into()))
    }

    async fn gc(&self, _: &[OperationId], _: std::time::SystemTime) -> OpStoreResult<()> {
        Err(OpStoreError::Other(
            "the canonical store keeps every operation".into(),
        ))
    }
}

impl CanonicalStore {
    /// Opens the store at `path`, creating it if needed. `root_commit_id` is the backend's
    /// root commit, which the root view refers to.
    pub fn open(path: &Path, root_commit_id: CommitId) -> Result<Self, CanonicalError> {
        let log = Log::open(path).map_err(io_err(path))?;
        let views = ViewCodec::new(path, root_commit_id.clone()).map_err(io_err(path))?;
        let shared = Shared {
            path: path.join("log"),
            root_commit_id,
            root_operation_id: OperationId::from_bytes(&[0; log::ID_LEN]),
            root_view_id: ViewId::from_bytes(&[0; log::ID_LEN]),
            log,
            views,
        };
        Ok(Self {
            shared: Arc::new(shared),
            generations: Mutex::new(HashMap::new()),
            #[cfg(test)]
            meanwhile: Mutex::new(None),
        })
    }

    /// The closest common ancestors of two sets of stored operations, as jj computes them
    /// for merges.
    pub fn closest_common_ancestors(
        &self,
        left: &[OperationId],
        right: &[OperationId],
    ) -> Result<Vec<OperationId>, CanonicalError> {
        let to_ops =
            |ids: &[OperationId]| -> Result<Vec<jj_lib::operation::Operation>, CanonicalError> {
                ids.iter()
                    .map(|id| {
                        let store: Arc<dyn OpStore> = self.shared.clone();
                        Ok(jj_lib::operation::Operation::new(
                            store,
                            id.clone(),
                            self.read_operation(id)?,
                        ))
                    })
                    .collect()
            };
        let ancestors =
            jj_lib::op_walk::closest_common_ancestors(to_ops(left)?, to_ops(right)?).block_on()?;
        Ok(ancestors.into_iter().map(|op| op.id().clone()).collect())
    }

    pub fn root_operation_id(&self) -> &OperationId {
        &self.shared.root_operation_id
    }

    pub fn read_operation(&self, id: &OperationId) -> Result<Operation, CanonicalError> {
        self.shared.read_operation(id)
    }

    pub fn read_view(&self, id: &ViewId) -> Result<View, CanonicalError> {
        self.shared.read_view(id)
    }

    /// The parents of a stored operation, without reading the rest of it.
    pub fn parents(&self, id: &OperationId) -> Result<Vec<OperationId>, CanonicalError> {
        self.shared.parents(id)
    }

    /// The view of the operation `id`.
    pub fn read_operation_view(&self, id: &OperationId) -> Result<View, CanonicalError> {
        self.read_view(&self.read_operation(id)?.view_id)
    }

    pub fn write_operation(&self, op: &Operation) -> Result<OperationId, CanonicalError> {
        self.shared.write_operation(op)
    }

    pub fn write_view(&self, view: &View) -> Result<ViewId, CanonicalError> {
        self.shared.write_view(view)
    }

    /// Resolves a hex prefix of a canonical operation id.
    pub fn resolve_prefix(&self, prefix: &str) -> Result<Option<OperationId>, CanonicalError> {
        let Some(prefix) = HexPrefix::try_from_hex(prefix) else {
            return Ok(None);
        };
        let resolved = self
            .shared
            .log
            .resolve_prefix(&prefix, self.root_operation_id())
            .map_err(self.shared.log_err())?;
        match resolved {
            PrefixResolution::SingleMatch(id) => Ok(Some(id)),
            _ => Ok(None),
        }
    }

    /// Whether any operation but the root is stored.
    pub fn has_operations(&self) -> Result<bool, CanonicalError> {
        Ok(!self.operation_ids()?.is_empty())
    }

    /// Every stored operation except the root, in no particular order.
    pub fn operation_ids(&self) -> Result<Vec<OperationId>, CanonicalError> {
        self.shared
            .log
            .operation_ids()
            .map_err(self.shared.log_err())
    }

    /// What isn't what its id says it is, as a power cut can leave it: a stored operation
    /// or view that doesn't read back as what it hashes to, or a view not in normal form,
    /// and anything after the last whole record, which a scan doesn't read. Fails, rather
    /// than count something torn, if it can't be read for some other reason, as when the
    /// process is out of file descriptors.
    pub fn torn(&self) -> Result<Vec<String>, CanonicalError> {
        let mut torn = vec![];
        for id in self.operation_ids()? {
            let read = self.read_operation(&id).map(|op| blake2b_hash(&op));
            judge(&mut torn, "operation", &id.hex(), id.as_bytes(), read)?;
        }
        let views = self.shared.log.view_ids().map_err(self.shared.log_err())?;
        for id in views {
            let read = self.read_view(&id).map(|view| blake2b_hash(&view));
            judge(&mut torn, "view", &id.hex(), id.as_bytes(), read)?;
            // Deltas sent on, and those stored as they came, are against the normal form.
            if let Ok(bytes) = self.view_bytes(&id)
                && normal_view(&bytes).is_none_or(|normal| normal != bytes)
            {
                torn.push(format!("view {} isn't in normal form", id.hex()));
            }
        }
        let unread = self.shared.log.unread().map_err(self.shared.log_err())?;
        if unread > 0 {
            torn.push(format!("{unread} bytes after the last whole record"));
        }
        Ok(torn)
    }

    pub fn has_operation(&self, id: &OperationId) -> bool {
        id == self.root_operation_id() || self.shared.log.has_operation(id).unwrap_or(false)
    }

    pub fn has_view(&self, id: &ViewId) -> bool {
        is_root_view(id) || self.shared.log.has_view(id).unwrap_or(false)
    }

    /// The encoded operation, as sent to peers. Not defined for the root operation, which
    /// every store has implicitly.
    pub fn operation_bytes(&self, id: &OperationId) -> Result<Vec<u8>, CanonicalError> {
        self.shared.operation_bytes(id)
    }

    /// The encoded view, in normal form (see `normal_view`). Not defined for the root
    /// view, which every store has implicitly.
    pub fn view_bytes(&self, id: &ViewId) -> Result<Vec<u8>, CanonicalError> {
        self.shared.view_bytes(id)
    }

    /// Every commit the stored operations `ops` require but the backend's root commit, which
    /// no store contains: those their views refer to, and the predecessors they record.
    ///
    /// They are read from the operations' and views' encodings (see `encoded_view_commits`),
    /// not from jj's [`View`]s, whose maps take far longer to build and free than the ids
    /// take to find: a fetch reads the view of every operation it sends, and a view names
    /// every bookmark and tag. An id of the wrong length, which jj would take for a commit
    /// that cannot exist, makes the operation or view malformed.
    pub fn required_commits(
        &self,
        ops: &[OperationId],
    ) -> Result<BTreeSet<CommitId>, CanonicalError> {
        let len = self.shared.root_commit_id.as_bytes().len();
        let mut named: HashSet<Vec<u8>> = HashSet::new();
        let mut found = |id: &[u8]| {
            (id.len() == len).then(|| {
                if !named.contains(id) {
                    named.insert(id.to_vec());
                }
            })
        };
        for id in ops {
            if id == self.root_operation_id() {
                continue;
            }
            let op = self.operation_bytes(id)?;
            let malformed = || CanonicalError::MalformedOperation(id.hex());
            let view_id = ViewId::new(encoded_view_id(&op).ok_or_else(malformed)?.to_vec());
            encoded_op_commits(&op, &mut found).ok_or_else(malformed)?;
            // The root view's file is implicit, like the root operation's, and it refers
            // only to the root commit.
            if is_root_view(&view_id) {
                continue;
            }
            let view = self.view_bytes(&view_id)?;
            encoded_view_commits(&view, &mut found)
                .ok_or_else(|| CanonicalError::MalformedView(view_id.hex()))?;
        }
        named.remove(self.shared.root_commit_id.as_bytes());
        Ok(named.into_iter().map(CommitId::new).collect())
    }

    /// Verifies and stores an operation received from a peer. The operation's view must
    /// already be stored, so that a stored operation is always readable.
    pub fn import_operation(&self, id: &OperationId, bytes: &[u8]) -> Result<(), CanonicalError> {
        self.import_operation_parents(id, bytes)?;
        Ok(())
    }

    /// [`Self::import_operation`], returning the parents of an operation it stored, which
    /// verifying it decoded, or `None` if the operation was stored already.
    fn import_operation_parents(
        &self,
        id: &OperationId,
        bytes: &[u8],
    ) -> Result<Option<Vec<OperationId>>, CanonicalError> {
        if self.has_operation(id) {
            return Ok(None);
        }
        let parents = self.verify_operation(id, bytes)?;
        self.shared
            .log
            .append_operation(id, bytes)
            .map_err(self.shared.log_err())?;
        Ok(Some(parents))
    }

    /// Checks an operation, decoded, against its id, and returns its parents.
    fn verify_operation(
        &self,
        id: &OperationId,
        bytes: &[u8],
    ) -> Result<Vec<OperationId>, CanonicalError> {
        let op = codec::decode_operation(bytes, self.root_operation_id())
            .map_err(|err| Shared::read_error("operation", id.hex(), err))?;
        admit(Admitted {
            kind: "operation",
            malformed: CanonicalError::MalformedOperation,
            expected: id.hex(),
            actual: OperationId::new(blake2b_hash(&op).to_vec()).hex(),
            names_its_commits: names_decoded_commits(bytes, encoded_op_commits, op_commit_ids(&op)),
        })?;
        Ok(op.parents)
    }

    /// Verifies and stores a view received from a peer, in normal form (see
    /// `normal_view`). It is the normal form that is decoded and checked, since that is
    /// what the store will hold.
    pub fn import_view(&self, id: &ViewId, bytes: &[u8]) -> Result<(), CanonicalError> {
        if self.has_view(id) {
            return Ok(());
        }
        let normal = normal_view(bytes).ok_or_else(|| CanonicalError::MalformedView(id.hex()))?;
        let view = self.shared.views.decode(id, &normal)?;
        admit(Admitted {
            kind: "view",
            malformed: CanonicalError::MalformedView,
            expected: id.hex(),
            actual: ViewId::new(blake2b_hash(&view).to_vec()).hex(),
            names_its_commits: names_decoded_commits(
                &normal,
                encoded_view_commits,
                view_commit_ids(&view),
            ),
        })?;
        self.shared
            .log
            .append_view(id, &normal)
            .map_err(self.shared.log_err())
    }

    /// Whether `ancestor` is in `anc*(heads)`.
    pub fn is_ancestor(
        &self,
        ancestor: &OperationId,
        heads: &[OperationId],
    ) -> Result<bool, CanonicalError> {
        let mut seen: HashSet<OperationId> = HashSet::new();
        let mut stack = heads.to_vec();
        while let Some(id) = stack.pop() {
            if id == *ancestor {
                return Ok(true);
            }
            if id == *self.root_operation_id() || !seen.insert(id.clone()) {
                continue;
            }
            stack.extend(self.parents(&id)?);
        }
        Ok(false)
    }

    /// The generation of stored operation `id`: the root's is 0, and any other's one more than
    /// its largest parent's. The first call reads the whole history below `id`.
    pub fn generation(&self, id: &OperationId) -> Result<u64, CanonicalError> {
        let mut generations = self
            .generations
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        let mut stack = vec![id.clone()];
        while let Some(op) = stack.last().cloned() {
            if generations.contains_key(&op) {
                stack.pop();
                continue;
            }
            if op == *self.root_operation_id() {
                generations.insert(op, 0);
                stack.pop();
                continue;
            }
            let parents = self.parents(&op)?;
            let missing: Vec<OperationId> = parents
                .iter()
                .filter(|p| !generations.contains_key(*p))
                .cloned()
                .collect();
            if missing.is_empty() {
                let generation = parents.iter().map(|p| generations[p]).max().unwrap_or(0) + 1;
                generations.insert(op, generation);
                stack.pop();
            } else {
                stack.extend(missing);
            }
        }
        Ok(generations[id])
    }

    /// Records the generation of `id`, whose `parents` have theirs recorded, as a walk that
    /// reads it anyway can, so that [`Self::generation`] needn't read it again.
    pub fn note_generation(&self, id: &OperationId, parents: &[OperationId]) {
        let mut generations = self
            .generations
            .lock()
            .unwrap_or_else(PoisonError::into_inner);
        if generations.contains_key(id) {
            return;
        }
        let root = self.root_operation_id();
        let parent_generations: Option<Vec<u64>> = parents
            .iter()
            .map(|p| {
                if p == root {
                    Some(0)
                } else {
                    generations.get(p).copied()
                }
            })
            .collect();
        if let Some(parent_generations) = parent_generations {
            let generation = parent_generations.into_iter().max().unwrap_or(0) + 1;
            generations.insert(id.clone(), generation);
        }
    }

    /// Whether `ancestor` is in `anc*(op)`, both stored. Operations whose generation is no
    /// higher than `ancestor`'s cannot lead to it, so the search never enters them.
    pub fn is_ancestor_of(
        &self,
        ancestor: &OperationId,
        op: &OperationId,
    ) -> Result<bool, CanonicalError> {
        if ancestor == op {
            return Ok(true);
        }
        let target = self.generation(ancestor)?;
        let mut seen = HashSet::new();
        let mut stack = vec![op.clone()];
        while let Some(id) = stack.pop() {
            if id == *ancestor {
                return Ok(true);
            }
            if !seen.insert(id.clone()) || self.generation(&id)? <= target {
                continue;
            }
            stack.extend(self.parents(&id)?);
        }
        Ok(false)
    }

    /// The operations in `anc*(heads)` that `stop` rejects, ancestors before descendants.
    /// The walk does not enter operations that `stop` accepts, nor the root, nor operations
    /// this store lacks.
    pub fn ancestors_until(
        &self,
        heads: &[OperationId],
        stop: impl Fn(&OperationId) -> bool,
    ) -> Result<Vec<OperationId>, CanonicalError> {
        let mut order = vec![];
        let mut done: HashSet<OperationId> = HashSet::new();
        // (operation, whether its parents have been pushed)
        let mut stack: Vec<(OperationId, bool)> =
            heads.iter().map(|h| (h.clone(), false)).collect();
        while let Some((id, expanded)) = stack.pop() {
            if done.contains(&id) {
                continue;
            }
            if expanded {
                done.insert(id.clone());
                order.push(id);
                continue;
            }
            if id == *self.root_operation_id() || stop(&id) || !self.has_operation(&id) {
                done.insert(id);
                continue;
            }
            let parents = self.parents(&id)?;
            stack.push((id, true));
            stack.extend(
                parents
                    .into_iter()
                    .filter(|p| !done.contains(p))
                    .map(|p| (p, false)),
            );
        }
        Ok(order)
    }

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
    pub fn export_operations(&self, ops: &[OperationId], out: &Path) -> Result<(), CanonicalError> {
        let mut writer = BundleWriter::create(out)?;
        writer.begin_compressed()?;
        let mut sent = HashSet::new();
        // The views of the operations written so far, which are usually the next ones'
        // parents.
        let mut views: HashMap<OperationId, ViewId> = HashMap::new();
        // The last view a delta went to, in normal form: usually the next delta's base.
        let mut last: Option<(ViewId, Vec<u8>)> = None;
        for id in ops {
            let encoded = self.operation_bytes(id)?;
            let view_id = encoded_view_id(&encoded)
                .ok_or_else(|| CanonicalError::MalformedOperation(id.hex()))?;
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
            writer.operation(id.as_bytes(), &encoded)?;
            views.insert(id.clone(), view_id);
        }
        Ok(writer.finish()?)
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
            .filter(|(_, id, _)| !self.has_operation(id) && seen.insert((*id).clone()))
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
                ops.push((id, parents));
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

/// A view's bytes as a function of its content alone, which view deltas are between, and
/// which the store holds. jj encodes `head_ids`, a set, and `wc_commit_ids`, a map, in
/// hash order, so two stores can be given different bytes for one view. Sorting the
/// top-level fields, and the entries of those two among them, leaves nothing to chance,
/// without decoding the view. The result is a valid encoding of the same view, for any
/// encoding this jj-lib writes. `None` if `encoded` isn't a protobuf message.
fn normal_view(encoded: &[u8]) -> Option<Vec<u8>> {
    /// `head_ids` and `wc_commit_ids`.
    const UNORDERED: [u32; 2] = [1, 8];
    let mut fields = top_level_fields(encoded)?;
    // Stable, so other repeated fields keep their order.
    fields.sort_by(|(number, bytes), (other_number, other_bytes)| {
        number.cmp(other_number).then_with(|| {
            if UNORDERED.contains(number) {
                bytes.cmp(other_bytes)
            } else {
                std::cmp::Ordering::Equal
            }
        })
    });
    let mut normal = Vec::with_capacity(encoded.len());
    for (_, bytes) in fields {
        normal.extend_from_slice(bytes);
    }
    Some(normal)
}

/// Adds the stored `kind` named `name` to `torn` if `read`, its hash once read, isn't
/// `id`; fails if it couldn't be read at all.
fn judge<H: AsRef<[u8]>>(
    torn: &mut Vec<String>,
    kind: &str,
    name: &str,
    id: &[u8],
    read: Result<H, CanonicalError>,
) -> Result<(), CanonicalError> {
    match read {
        Ok(hash) if hash.as_ref() == id => {}
        Ok(_) => torn.push(format!("{kind} {name} is something else")),
        Err(err) if err.unreadable() => return Err(err),
        Err(err) => torn.push(format!("{kind} {name}: {err}")),
    }
    Ok(())
}

/// Whether `id` is the root view's, whose file every store has implicitly.
fn is_root_view(id: &ViewId) -> bool {
    id.as_bytes().iter().all(|&b| b == 0)
}

/// Calls `each` with the number and payload of every length-delimited field of an encoded
/// message, in order; fields of other wire types hold no id or message. `None` if the
/// message, or `each`, finds it malformed.
fn each_field<'a>(
    mut bytes: &'a [u8],
    mut each: impl FnMut(u32, &'a [u8]) -> Option<()>,
) -> Option<()> {
    while !bytes.is_empty() {
        let (key, payload) = next_field(&mut bytes)?;
        if key & 7 == 2 {
            each(u32::try_from(key >> 3).ok()?, payload)?;
        }
    }
    Some(())
}

/// The last field `number` of an encoded message, which is what prost decodes a singular
/// field as, if there is one.
fn last_field(bytes: &[u8], number: u32) -> Option<Option<&[u8]>> {
    let mut last = None;
    each_field(bytes, |n, payload| {
        if n == number {
            last = Some(payload);
        }
        Some(())
    })?;
    Some(last)
}

/// An encoded operation's view id.
fn encoded_view_id(op: &[u8]) -> Option<&[u8]> {
    last_field(op, 1)?
}

/// Where [`encoded_op_commits`] and [`encoded_view_commits`] report each id they find,
/// which ends the walk by returning `None`.
type Found<'a, 'f> = dyn FnMut(&'a [u8]) -> Option<()> + 'f;

fn id<'a>(bytes: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    found(bytes)
}

/// A singular id field of the message `bytes`, which prost decodes as empty when absent,
/// and jj then takes for a commit.
fn required_id<'a>(bytes: &'a [u8], number: u32, found: &mut Found<'a, '_>) -> Option<()> {
    id(last_field(bytes, number)?.unwrap_or_default(), found)
}

/// In the message `bytes`, each field `number`, through `each`.
fn field<'a>(
    bytes: &'a [u8],
    number: u32,
    found: &mut Found<'a, '_>,
    each: fn(&'a [u8], &mut Found<'a, '_>) -> Option<()>,
) -> Option<()> {
    each_field(bytes, |n, payload| {
        if n == number {
            each(payload, found)?;
        }
        Some(())
    })
}

/// `RefConflict.Term` and `RefTargetTerm`: an id, if present.
fn term<'a>(bytes: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    field(bytes, 1, found, id)
}

/// `RefTarget`: an id (legacy), a `RefConflictLegacy` of ids, or a `RefConflict` of terms,
/// its removes and adds alike.
fn target<'a>(bytes: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    each_field(bytes, |number, payload| match number {
        1 => id(payload, found),
        2 => each_field(payload, |number, payload| match number {
            1 | 2 => id(payload, found),
            _ => Some(()),
        }),
        3 => each_field(payload, |number, payload| match number {
            1 | 2 => term(payload, found),
            _ => Some(()),
        }),
        _ => Some(()),
    })
}

/// Calls `found` with every commit id an encoded operation holds: its recorded predecessors
/// (`CommitPredecessors`), with the fields this jj-lib's `simple_op_store.proto` gives them.
/// An id is reported as jj decodes it, so an absent one that jj decodes as empty is reported
/// empty, for the caller to refuse.
fn encoded_op_commits<'a>(op: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    each_field(op, |number, payload| match number {
        4 => {
            required_id(payload, 1, found)?;
            field(payload, 2, found, id)
        }
        _ => Some(()),
    })
}

/// [`encoded_op_commits`] for an encoded view, with legacy fields included: every commit
/// that jj's decoding of it refers to, and none it doesn't in what this jj-lib writes (see
/// the test `encoded_commits_are_referenced_commits`).
fn encoded_view_commits<'a>(view: &'a [u8], found: &mut Found<'a, '_>) -> Option<()> {
    each_field(view, |number, payload| match number {
        // `head_ids`.
        1 => id(payload, found),
        // The legacy `wc_commit_id` and `git_head_legacy`, which jj reads only if not empty.
        2 | 7 if !payload.is_empty() => id(payload, found),
        // `wc_commit_ids`, a map entry with the id as its value.
        8 => required_id(payload, 2, found),
        // `Bookmark`: its local target, and its `RemoteBookmark`s' (legacy).
        5 => each_field(payload, |number, payload| match number {
            2 => target(payload, found),
            3 => field(payload, 2, found, target),
            _ => Some(()),
        }),
        // `Tag`, and `GitHead`.
        6 | 13 => field(payload, 2, found, target),
        // `RemoteView`: its bookmarks' and tags' `RemoteRef`s, each with its terms.
        11 => each_field(payload, |number, payload| match number {
            2 | 3 => field(payload, 2, found, term),
            _ => Some(()),
        }),
        // `GitRef`: a target, or without one its id (legacy).
        3 => match last_field(payload, 3)? {
            Some(_) => field(payload, 3, found, target),
            None => required_id(payload, 2, found),
        },
        // The legacy `git_head`.
        9 => target(payload, found),
        _ => Some(()),
    })
}

/// Every commit a view refers to, as jj decodes it. It is taken apart field by field, so that
/// a jj-lib with more of them fails to build here, and whoever upgrades it checks
/// [`encoded_view_commits`] against the new schema.
fn view_commit_ids(view: &View) -> impl Iterator<Item = &CommitId> {
    let View {
        head_ids,
        local_bookmarks,
        local_tags,
        remote_views,
        git_refs,
        git_heads,
        wc_commit_ids,
    } = view;
    let remote_targets = remote_views
        .values()
        .flat_map(|RemoteView { bookmarks, tags }| {
            bookmarks
                .values()
                .chain(tags.values())
                .map(|RemoteRef { target, state: _ }| target)
        });
    let targets = local_bookmarks
        .values()
        .chain(local_tags.values())
        .chain(git_refs.values())
        .chain(git_heads.values())
        .chain(remote_targets);
    head_ids
        .iter()
        .chain(targets.flat_map(|target| target.iter().flatten()))
        .chain(wc_commit_ids.values())
}

/// [`view_commit_ids`] for an operation: its recorded predecessors.
fn op_commit_ids(op: &Operation) -> impl Iterator<Item = &CommitId> {
    let Operation {
        view_id: _,
        parents: _,
        metadata: _,
        commit_predecessors,
    } = op;
    commit_predecessors
        .iter()
        .flatten()
        .flat_map(|(commit, predecessors)| std::iter::once(commit).chain(predecessors))
}

/// Whether `encoded`, walked by `walk`, names exactly the commits that jj's decoding of it
/// refers to, as everything this jj-lib encodes does. Reading stored views' and operations'
/// commits from their encodings (see [`CanonicalStore::required_commits`]) relies on it, so
/// nothing else is stored: a peer's encoding that jj reads differently, such as one with a
/// legacy field contradicting its replacement, would otherwise stand for the view's id.
fn names_decoded_commits<'a, 'b>(
    encoded: &'a [u8],
    walk: fn(&'a [u8], &mut Found<'a, '_>) -> Option<()>,
    decoded: impl Iterator<Item = &'b CommitId>,
) -> bool {
    let mut named = vec![];
    if walk(encoded, &mut |id| {
        named.push(id);
        Some(())
    })
    .is_none()
    {
        return false;
    }
    let mut decoded: Vec<&[u8]> = decoded.map(|id| id.as_bytes()).collect();
    for ids in [&mut named, &mut decoded] {
        ids.sort_unstable();
        ids.dedup();
    }
    named == decoded
}

/// The top-level fields of a protobuf message, each with its number and its encoding,
/// key included, in order.
fn top_level_fields(mut bytes: &[u8]) -> Option<Vec<(u32, &[u8])>> {
    let mut fields = vec![];
    while !bytes.is_empty() {
        let start = bytes;
        let (key, _) = next_field(&mut bytes)?;
        let number = u32::try_from(key >> 3).ok()?;
        fields.push((number, &start[..start.len() - bytes.len()]));
    }
    Some(fields)
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::collections::BTreeMap;

    use std::fs;

    use hegel::TestCase;
    use hegel::generators as gs;
    use jj_lib::merge::Merge;
    use jj_lib::op_store::RefTarget;
    use jj_lib::op_store::RemoteRefState;
    use prost::Message as _;

    use super::*;

    /// What the walker must find: every commit that jj's decoding of an operation and its
    /// view refers to.
    fn referenced_commits(op: &Operation, view: &View) -> BTreeSet<CommitId> {
        view_commit_ids(view)
            .chain(op_commit_ids(op))
            .cloned()
            .collect()
    }

    fn commit(i: u8) -> CommitId {
        CommitId::from_bytes(&[i; 20])
    }

    /// Every field jj writes commits to.
    #[test]
    fn encoded_commits_are_referenced_commits() {
        let dir = tempfile::tempdir().unwrap();
        let root_commit = commit(0);
        let store = CanonicalStore::open(dir.path(), root_commit.clone()).unwrap();
        let conflict = |i: u8| Merge::from_vec(vec![Some(commit(i)), Some(commit(i + 1)), None]);
        let tracked = |target| RemoteRef {
            target,
            state: RemoteRefState::Tracked,
        };
        let mut view = View::make_root(root_commit.clone());
        view.head_ids.extend([commit(1), commit(2)]);
        view.local_bookmarks = BTreeMap::from([
            ("main".into(), RefTarget::normal(commit(3))),
            ("split".into(), conflict(4)),
        ]);
        view.local_tags = BTreeMap::from([("v1".into(), RefTarget::normal(commit(6)))]);
        view.remote_views = BTreeMap::from([(
            "origin".into(),
            RemoteView {
                bookmarks: BTreeMap::from([
                    ("main".into(), tracked(RefTarget::normal(commit(7)))),
                    ("split".into(), tracked(conflict(8))),
                ]),
                tags: BTreeMap::from([("v1".into(), tracked(RefTarget::normal(commit(10))))]),
            },
        )]);
        view.git_refs = BTreeMap::from([("refs/heads/main".into(), RefTarget::normal(commit(11)))]);
        // Not the default workspace's, which jj also writes to the legacy `git_head`.
        view.git_heads = BTreeMap::from([("other".into(), RefTarget::normal(commit(12)))]);
        view.wc_commit_ids =
            BTreeMap::from([("default".into(), commit(13)), ("other".into(), commit(14))]);
        let view_id = store.write_view(&view).unwrap();
        let mut op = operation(store.root_operation_id(), view_id);
        op.commit_predecessors = Some(BTreeMap::from([(commit(15), vec![commit(16), commit(17)])]));
        let op_id = store.write_operation(&op).unwrap();

        let mut expected = referenced_commits(&op, &view);
        assert_eq!(expected.len(), 18);
        expected.remove(&root_commit);
        assert_eq!(store.required_commits(&[op_id]).unwrap(), expected);
    }

    /// What a power cut can leave in the store is torn: a record cut short, or garbled. A
    /// scan stops there, so what comes before it still reads, `torn` reports the rest, and
    /// the next write cuts it off.
    #[test]
    fn torn_records_are_found() {
        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), commit(0)).unwrap();
        let view_id = store.write_view(&view_with_heads(1)).unwrap();
        let op = operation(store.root_operation_id(), view_id.clone());
        let op_id = store.write_operation(&op).unwrap();
        assert_eq!(store.torn().unwrap(), Vec::<String>::new());
        let log = dir.path().join("log");
        let len = fs::metadata(&log).unwrap().len();
        fs::OpenOptions::new()
            .write(true)
            .open(&log)
            .unwrap()
            .set_len(len - 1)
            .unwrap();

        let store = CanonicalStore::open(dir.path(), commit(0)).unwrap();
        assert!(!store.has_operation(&op_id));
        assert_eq!(store.read_view(&view_id).unwrap(), view_with_heads(1));
        let torn = store.torn().unwrap();
        assert_eq!(torn.len(), 1, "{torn:?}");
        assert!(
            torn[0].ends_with("bytes after the last whole record"),
            "{torn:?}"
        );
        assert_eq!(store.write_operation(&op).unwrap(), op_id);
        assert_eq!(store.torn().unwrap(), Vec::<String>::new());
        assert_eq!(store.read_operation(&op_id).unwrap(), op);
    }

    /// Stores a view encoded by hand, as a peer could send it.
    fn import_encoded(
        store: &CanonicalStore,
        view: &jj_lib::protos::simple_op_store::View,
    ) -> ViewId {
        let bytes = view.encode_to_vec();
        // A view's id hashes jj's decoding of it, which the store reports for a wrong one.
        let id = match store.import_view(&ViewId::new(vec![1; 64]), &bytes) {
            Err(CanonicalError::HashMismatch { actual, .. }) => {
                ViewId::try_from_hex(&actual).unwrap()
            }
            other => panic!("{other:?}"),
        };
        store.import_view(&id, &bytes).unwrap();
        id
    }

    /// The fields older jj-libs wrote commits to, which jj still reads, and those that
    /// jj-lib writes only along with another field holding the same commits.
    #[test]
    #[allow(deprecated)]
    fn encoded_commits_include_legacy_fields() {
        use jj_lib::protos::simple_op_store as proto;

        let dir = tempfile::tempdir().unwrap();
        let store = CanonicalStore::open(dir.path(), commit(0)).unwrap();
        let id = |i: u8| vec![i; 20];
        let target = |i: u8| {
            Some(proto::RefTarget {
                value: Some(proto::ref_target::Value::CommitId(id(i))),
            })
        };
        let legacy = proto::View {
            head_ids: vec![id(1)],
            wc_commit_id: id(2),
            bookmarks: vec![proto::Bookmark {
                name: "main".into(),
                local_target: Some(proto::RefTarget {
                    value: Some(proto::ref_target::Value::ConflictLegacy(
                        proto::RefConflictLegacy {
                            removes: vec![id(3)],
                            adds: vec![id(4), id(5)],
                        },
                    )),
                }),
                remote_bookmarks: vec![proto::RemoteBookmark {
                    remote_name: "origin".into(),
                    target: target(6),
                    state: Some(proto::RemoteRefState::Tracked as i32),
                }],
            }],
            git_refs: vec![proto::GitRef {
                name: "refs/tags/v1".into(),
                commit_id: id(7),
                target: None,
            }],
            git_head_legacy: id(8),
            ..Default::default()
        };
        // Remote bookmarks only in `remote_views`, and the git head only in `git_head`.
        let alone = proto::View {
            head_ids: vec![id(1)],
            remote_views: vec![proto::RemoteView {
                name: "origin".into(),
                bookmarks: vec![proto::RemoteRef {
                    name: "main".into(),
                    target_terms: vec![proto::RefTargetTerm { value: Some(id(9)) }],
                    state: proto::RemoteRefState::Tracked as i32,
                }],
                tags: vec![],
            }],
            git_head: target(10),
            has_git_refs_migrated_to_remote_tags: true,
            ..Default::default()
        };
        for (view, commits) in [(legacy, 8), (alone, 3)] {
            let view_id = import_encoded(&store, &view);
            let op = operation(store.root_operation_id(), view_id.clone());
            let op_id = store.write_operation(&op).unwrap();
            let expected = referenced_commits(&op, &store.read_view(&view_id).unwrap());
            assert_eq!(expected.len(), commits);
            assert_eq!(store.required_commits(&[op_id]).unwrap(), expected);
        }
    }

    /// An id jj would take for a commit, but that no commit has, makes a view malformed:
    /// empty, as an absent one decodes to, or too short.
    #[test]
    fn impossible_commits_are_refused() {
        use jj_lib::protos::simple_op_store as proto;

        let dir = tempfile::tempdir().unwrap();
        let store = CanonicalStore::open(dir.path(), commit(0)).unwrap();
        let views = [
            proto::View {
                head_ids: vec![vec![]],
                ..Default::default()
            },
            proto::View {
                head_ids: vec![vec![1; 4]],
                ..Default::default()
            },
            proto::View {
                head_ids: vec![vec![1; 20]],
                wc_commit_ids: [("default".to_owned(), vec![])].into(),
                ..Default::default()
            },
            #[allow(deprecated)]
            proto::View {
                head_ids: vec![vec![1; 20]],
                git_refs: vec![proto::GitRef {
                    name: "refs/heads/main".into(),
                    commit_id: vec![],
                    target: None,
                }],
                ..Default::default()
            },
        ];
        for view in &views {
            let view_id = import_encoded(&store, view);
            let op_id = store
                .write_operation(&operation(store.root_operation_id(), view_id.clone()))
                .unwrap();
            assert!(
                matches!(
                    store.required_commits(&[op_id]),
                    Err(CanonicalError::MalformedView(ref hex)) if *hex == view_id.hex()
                ),
                "{view:?}"
            );
        }
        // A predecessor without an id, which prost leaves out and jj decodes as empty.
        let view_id = store.write_view(&view_with_heads(1)).unwrap();
        let mut op = operation(store.root_operation_id(), view_id);
        op.commit_predecessors = Some(BTreeMap::from([(CommitId::new(vec![]), vec![])]));
        let op_id = store.write_operation(&op).unwrap();
        assert!(matches!(
            store.required_commits(std::slice::from_ref(&op_id)),
            Err(CanonicalError::MalformedOperation(ref hex)) if *hex == op_id.hex()
        ));
    }

    /// An encoding that names commits jj doesn't read from it is refused, though it decodes
    /// to the view or operation its id stands for.
    #[test]
    #[allow(deprecated)]
    fn encodings_jj_reads_differently_are_refused() {
        use jj_lib::protos::simple_op_store as proto;

        let dir = tempfile::tempdir().unwrap();
        let store = CanonicalStore::open(dir.path(), commit(0)).unwrap();
        // jj reads `git_heads`, and ignores the legacy `git_head_legacy` beside it.
        let target = proto::RefTarget {
            value: Some(proto::ref_target::Value::CommitId(vec![1; 20])),
        };
        let view = proto::View {
            head_ids: vec![vec![1; 20]],
            git_heads: vec![proto::GitHead {
                name: "default".into(),
                target: Some(target),
            }],
            git_head_legacy: vec![2; 20],
            has_git_refs_migrated_to_remote_tags: true,
            ..Default::default()
        }
        .encode_to_vec();
        let view_id = match store.import_view(&ViewId::new(vec![1; 64]), &view) {
            Err(CanonicalError::HashMismatch { actual, .. }) => {
                ViewId::try_from_hex(&actual).unwrap()
            }
            other => panic!("{other:?}"),
        };
        assert!(matches!(
            store.import_view(&view_id, &view),
            Err(CanonicalError::MalformedView(_))
        ));
        assert!(!store.has_view(&view_id));

        // jj ignores predecessors unless the operation says it stores them.
        let view_id = store.write_view(&view_with_heads(1)).unwrap();
        let op = proto::Operation {
            view_id: view_id.to_bytes(),
            parents: vec![store.root_operation_id().to_bytes()],
            metadata: Some(Default::default()),
            commit_predecessors: vec![proto::CommitPredecessors {
                commit_id: vec![3; 20],
                predecessor_ids: vec![],
            }],
            stores_commit_predecessors: false,
        }
        .encode_to_vec();
        let op_id = match store.import_operation(&OperationId::new(vec![1; 64]), &op) {
            Err(CanonicalError::HashMismatch { actual, .. }) => {
                OperationId::try_from_hex(&actual).unwrap()
            }
            other => panic!("{other:?}"),
        };
        assert!(matches!(
            store.import_operation(&op_id, &op),
            Err(CanonicalError::MalformedOperation(_))
        ));
        assert!(!store.has_operation(&op_id));
    }

    /// Parents read from an operation's encoding are those jj decodes: a merge's in order,
    /// and the root for an operation that has none, as from before jj had a root operation.
    #[test]
    fn parents_are_read_as_jj_decodes_them() {
        use jj_lib::protos::simple_op_store as proto;

        let dir = musubi_testutil::tempdir();
        let store = CanonicalStore::open(dir.path(), commit(0)).unwrap();
        let root = store.root_operation_id().clone();
        let view_id = store.write_view(&view_with_heads(1)).unwrap();
        let a = store
            .write_operation(&operation(&root, view_id.clone()))
            .unwrap();
        let b = store
            .write_operation(&operation(&a, view_id.clone()))
            .unwrap();
        let mut merge = operation(&b, view_id.clone());
        merge.parents.push(a.clone());
        let merge = store.write_operation(&merge).unwrap();
        let orphan = proto::Operation {
            view_id: view_id.to_bytes(),
            metadata: Some(Default::default()),
            ..Default::default()
        }
        .encode_to_vec();
        let orphan_id = match store.import_operation(&OperationId::new(vec![1; 64]), &orphan) {
            Err(CanonicalError::HashMismatch { actual, .. }) => {
                OperationId::try_from_hex(&actual).unwrap()
            }
            other => panic!("{other:?}"),
        };
        store.import_operation(&orphan_id, &orphan).unwrap();
        for id in [&root, &a, &b, &merge, &orphan_id] {
            assert_eq!(
                store.parents(id).unwrap(),
                store.read_operation(id).unwrap().parents
            );
        }
        assert_eq!(store.parents(&merge).unwrap(), [b, a]);
        assert_eq!(store.parents(&orphan_id).unwrap(), [root]);
    }

    /// A delta made against bytes of its base other than the store's normal form, which a
    /// peer can send, is stored anew rather than as it came: stored, it would rebuild from
    /// the normal form into something else, under an id it was checked against.
    #[test]
    fn a_delta_against_another_encoding_of_its_base_is_made_again() {
        let dir = musubi_testutil::tempdir();
        let root_commit = CommitId::from_bytes(&[0; 20]);
        let sender = CanonicalStore::open(&dir.path().join("sender"), root_commit.clone()).unwrap();
        let root = sender.root_operation_id().clone();
        let base_view = sender.write_view(&view_with_heads(30)).unwrap();
        let base = sender
            .write_operation(&operation(&root, base_view.clone()))
            .unwrap();
        let view = view_with_heads(31);
        let child_view = sender.write_view(&view).unwrap();
        let child = sender
            .write_operation(&operation(&base, child_view.clone()))
            .unwrap();

        // The base, its heads in the opposite order, and a delta against those bytes.
        let normal = sender.view_bytes(&base_view).unwrap();
        let mut proto = jj_lib::protos::simple_op_store::View::decode(&*normal).unwrap();
        proto.head_ids.reverse();
        let reordered = proto.encode_to_vec();
        assert_ne!(reordered, normal);
        let delta =
            bundle::view_delta(&reordered, &sender.view_bytes(&child_view).unwrap()).unwrap();
        let bundle_file = tempfile::NamedTempFile::new_in(dir.path()).unwrap();
        let mut writer = BundleWriter::create(bundle_file.path()).unwrap();
        writer.view(base_view.as_bytes(), &reordered).unwrap();
        writer
            .operation(base.as_bytes(), &sender.operation_bytes(&base).unwrap())
            .unwrap();
        writer
            .view_delta_made(child_view.as_bytes(), base_view.as_bytes(), &delta)
            .unwrap();
        writer
            .operation(child.as_bytes(), &sender.operation_bytes(&child).unwrap())
            .unwrap();
        writer.finish().unwrap();

        let receiver_dir = dir.path().join("receiver");
        let receiver = CanonicalStore::open(&receiver_dir, root_commit.clone()).unwrap();
        receiver.import_operations(bundle_file.path()).unwrap();
        drop(receiver);
        // Opened again, with nothing rebuilt yet.
        let receiver = CanonicalStore::open(&receiver_dir, root_commit).unwrap();
        assert_eq!(receiver.read_view(&child_view).unwrap(), view);
        assert_eq!(receiver.torn().unwrap(), Vec::<String>::new());
    }

    /// Bundles a peer could send: each view in one of three encodings that decode to it (the
    /// sender's normal form; its heads reversed; and with an unknown field after them, which
    /// is in normal form but isn't the sender's), whole, or as a delta made against any encoding of any view before
    /// it; some sent twice; across bundles imported in turn by two stores sharing a log, as
    /// the daemon and a command do, with batches small enough to cross. Whatever an import
    /// makes of each, refusing it or not, everything stored reads back, from the log opened
    /// afresh, as what its id says. And a bundle as musubi makes one, in the sender's normal
    /// form with deltas against the view before, is taken whole.
    #[hegel::test(test_cases = 200)]
    fn imports_store_only_what_reads_back_as_its_id(tc: TestCase) {
        use jj_lib::protos::simple_op_store as proto;

        let dir = musubi_testutil::tempdir();
        let root_commit = commit(0);
        let sender = CanonicalStore::open(&dir.path().join("sender"), root_commit.clone()).unwrap();
        let count = tc.draw(gs::integers::<usize>().min_value(1).max_value(10));
        // Each view's id and the sender's bytes for it, and the operation it is the view of.
        let mut views: Vec<(ViewId, Vec<u8>)> = vec![];
        let mut ops: Vec<OperationId> = vec![];
        let mut parent = sender.root_operation_id().clone();
        for _ in 0..count {
            let heads = tc.draw(gs::integers::<u8>().min_value(1).max_value(12));
            let first = tc.draw(gs::integers::<u8>().min_value(1).max_value(8));
            let mut view = View::make_root(root_commit.clone());
            view.head_ids = (first..first + heads).map(commit).collect();
            let view_id = sender.write_view(&view).unwrap();
            let op = sender
                .write_operation(&operation(&parent, view_id.clone()))
                .unwrap();
            views.push((view_id.clone(), sender.view_bytes(&view_id).unwrap()));
            ops.push(op.clone());
            parent = op;
        }
        let encode = |jj: &[u8], how: u8| -> Vec<u8> {
            match how {
                0 => jj.to_vec(),
                1 => {
                    let mut view = proto::View::decode(jj).unwrap();
                    view.head_ids.reverse();
                    view.encode_to_vec()
                }
                // A length-delimited field 99, which jj's schema doesn't have.
                _ => [jj, &[0x9a, 0x06, 0x01, 0x00]].concat(),
            }
        };
        let honest = tc.draw(gs::booleans());
        let receiver_dir = dir.path().join("receiver");
        let receivers = [
            CanonicalStore::open(&receiver_dir, root_commit.clone()).unwrap(),
            CanonicalStore::open(&receiver_dir, root_commit.clone()).unwrap(),
        ];
        // The encoding each view went in first: a delta against it makes the view again, so
        // that the receiver takes it in, where a delta against another fails its check.
        let mut sent = vec![0; count];
        let mut next = 0;
        while next < count {
            let size = tc
                .draw(gs::integers::<usize>().min_value(1).max_value(count - next))
                .min(count - next);
            let path = dir.path().join(format!("bundle-{next}"));
            let mut writer = BundleWriter::create(&path).unwrap();
            for i in next..next + size {
                let (view_id, jj) = &views[i];
                let times = if honest {
                    1
                } else {
                    tc.draw(gs::integers::<u8>().min_value(1).max_value(2))
                };
                for time in 0..times {
                    let how = if honest {
                        0
                    } else {
                        tc.draw(gs::integers::<u8>().max_value(2))
                    };
                    if time == 0 {
                        sent[i] = how;
                    }
                    let contents = encode(jj, how);
                    // Honest: a delta against the view before, as an export makes one.
                    let base = match (i, tc.draw(gs::integers::<u8>().max_value(3))) {
                        (0, _) => None,
                        _ if honest => Some((i - 1, 0)),
                        // Mostly against the view before, as bundles are, in the encoding
                        // it went in, across batches and within them.
                        (_, 0) => Some((i - 1, sent[i - 1])),
                        (_, 1) => {
                            let at = tc.draw(gs::integers::<usize>().max_value(i - 1));
                            Some((at, sent[at]))
                        }
                        (_, 2) => Some((
                            tc.draw(gs::integers::<usize>().max_value(i - 1)),
                            tc.draw(gs::integers::<u8>().max_value(2)),
                        )),
                        _ => None,
                    };
                    match base {
                        Some((at, base_how)) if views[at].0 != *view_id => {
                            let (base_id, base_jj) = &views[at];
                            let delta =
                                bundle::view_delta(&encode(base_jj, base_how), &contents).unwrap();
                            writer
                                .view_delta_made(view_id.as_bytes(), base_id.as_bytes(), &delta)
                                .unwrap();
                        }
                        _ => writer.view(view_id.as_bytes(), &contents).unwrap(),
                    }
                }
                writer
                    .operation(ops[i].as_bytes(), &sender.operation_bytes(&ops[i]).unwrap())
                    .unwrap();
            }
            writer.finish().unwrap();
            let receiver = &receivers[tc.draw(gs::integers::<usize>().max_value(1))];
            let imported = receiver.import_operations(&path);
            if honest {
                imported.unwrap();
            }
            let fresh = CanonicalStore::open(&receiver_dir, root_commit.clone()).unwrap();
            assert_eq!(fresh.torn().unwrap(), Vec::<String>::new());
            next += size;
        }
        if honest {
            let fresh = CanonicalStore::open(&receiver_dir, root_commit).unwrap();
            for ((view_id, _), op) in views.iter().zip(&ops) {
                assert_eq!(
                    blake2b_hash(&fresh.read_view(view_id).unwrap()).as_slice(),
                    view_id.as_bytes()
                );
                assert!(fresh.has_operation(op));
            }
        }
    }

    /// Another process can append a view that an import has checked, but not yet appended,
    /// in other bytes, which the log then keeps. A delta in the import made against the
    /// import's bytes for it is then made again, not stored as it came against bytes the log
    /// doesn't hold.
    #[test]
    fn a_delta_whose_base_another_process_appends_first_is_made_again() {
        let dir = musubi_testutil::tempdir();
        let root_commit = CommitId::from_bytes(&[0; 20]);
        let sender = CanonicalStore::open(&dir.path().join("sender"), root_commit.clone()).unwrap();
        let root = sender.root_operation_id().clone();
        let base_view = sender.write_view(&view_with_heads(30)).unwrap();
        let base = sender
            .write_operation(&operation(&root, base_view.clone()))
            .unwrap();
        let view = view_with_heads(31);
        let child_view = sender.write_view(&view).unwrap();
        let child = sender
            .write_operation(&operation(&base, child_view.clone()))
            .unwrap();
        let normal = sender.view_bytes(&base_view).unwrap();
        // The base in other bytes, in normal form too: an unknown field after the rest.
        let other = [normal.as_slice(), &[0x9a, 0x06, 0x01, 0x00]].concat();
        assert_eq!(normal_view(&other).as_deref(), Some(other.as_slice()));
        let delta = bundle::view_delta(&other, &sender.view_bytes(&child_view).unwrap()).unwrap();
        let bundle_file = tempfile::NamedTempFile::new_in(dir.path()).unwrap();
        let mut writer = BundleWriter::create(bundle_file.path()).unwrap();
        writer.view(base_view.as_bytes(), &other).unwrap();
        writer
            .operation(base.as_bytes(), &sender.operation_bytes(&base).unwrap())
            .unwrap();
        writer
            .view_delta_made(child_view.as_bytes(), base_view.as_bytes(), &delta)
            .unwrap();
        writer
            .operation(child.as_bytes(), &sender.operation_bytes(&child).unwrap())
            .unwrap();
        writer.finish().unwrap();

        let receiver_dir = dir.path().join("receiver");
        let receiver = CanonicalStore::open(&receiver_dir, root_commit.clone()).unwrap();
        let elsewhere = CanonicalStore::open(&receiver_dir, root_commit.clone()).unwrap();
        let (id, bytes) = (base_view.clone(), normal.clone());
        *receiver.meanwhile.lock().unwrap() = Some(Box::new(move || {
            elsewhere.import_view(&id, &bytes).unwrap();
        }));
        receiver.import_operations(bundle_file.path()).unwrap();
        drop(receiver);
        let fresh = CanonicalStore::open(&receiver_dir, root_commit).unwrap();
        assert_eq!(fresh.view_bytes(&base_view).unwrap(), normal);
        assert_eq!(fresh.read_view(&child_view).unwrap(), view);
        assert_eq!(fresh.torn().unwrap(), Vec::<String>::new());
    }

    fn view_with_heads(heads: u8) -> View {
        let mut view = View::make_root(CommitId::from_bytes(&[0; 20]));
        view.head_ids = (1..=heads)
            .map(|i| CommitId::from_bytes(&[i; 20]))
            .collect();
        view
    }

    fn operation(parent: &OperationId, view_id: ViewId) -> Operation {
        let mut op = Operation::make_root(view_id);
        op.parents = vec![parent.clone()];
        op
    }

    /// jj writes a set in hash order, so two stores can hold different bytes for the same
    /// view. A view sent as a delta against it still arrives intact.
    #[test]
    fn delta_survives_differently_encoded_base() {
        let dir = tempfile::tempdir().unwrap();
        let root_commit = CommitId::from_bytes(&[0; 20]);
        let sender = CanonicalStore::open(&dir.path().join("sender"), root_commit.clone()).unwrap();
        let receiver = CanonicalStore::open(&dir.path().join("receiver"), root_commit).unwrap();
        let root = sender.root_operation_id().clone();

        let base_view = sender.write_view(&view_with_heads(30)).unwrap();
        let base = sender
            .write_operation(&operation(&root, base_view.clone()))
            .unwrap();
        let view = view_with_heads(31);
        let child_view = sender.write_view(&view).unwrap();
        let child = sender
            .write_operation(&operation(&base, child_view.clone()))
            .unwrap();

        // The receiver has the base, with its heads in the opposite order.
        let bytes = sender.view_bytes(&base_view).unwrap();
        let mut proto = jj_lib::protos::simple_op_store::View::decode(&*bytes).unwrap();
        proto.head_ids.reverse();
        let reordered = proto.encode_to_vec();
        assert_ne!(reordered, bytes);
        receiver.import_view(&base_view, &reordered).unwrap();
        receiver
            .import_operation(&base, &sender.operation_bytes(&base).unwrap())
            .unwrap();

        let bundle = tempfile::NamedTempFile::new().unwrap();
        sender
            .export_operations(std::slice::from_ref(&child), bundle.path())
            .unwrap();
        assert_eq!(
            receiver.import_operations(bundle.path()).unwrap(),
            [(child, Some(vec![base]))]
        );
        assert_eq!(receiver.read_view(&child_view).unwrap(), view);
    }
}

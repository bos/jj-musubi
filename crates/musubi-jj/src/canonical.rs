//! The canonical op store: replicated operations, written by this jj-lib.
//!
//! Canonical ids are ordinary jj operation and view ids, and the operations and views are
//! encoded as jj's simple op store encodes them, but they are kept in one log (see
//! `canonical/log.rs`): operations as encoded, and views as deltas. Operations and views
//! received from peers are verified by decoding and re-hashing before they enter the
//! store; this works because every canonical one was written by the same pinned jj-lib, so
//! decoding and re-hashing round-trips exactly.
//!
//! Opening, reading, and walking the store live here. `transfer` exchanges histories in
//! bundles; `validate` normalizes their bytes and checks their meaning against jj's decoding.

mod codec;
mod contract;
mod log;
pub(crate) mod namespace;
mod origin;
mod presence;
mod transfer;
mod validate;

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
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use pollster::FutureExt as _;
use thiserror::Error;

use self::codec::ViewCodec;
pub use self::contract::Contraction;
pub use self::contract::current;
use self::log::Log;
pub use self::presence::PresenceMemo;
pub use self::presence::Work;
pub use self::presence::merge as merge_presence;
pub use self::transfer::Imported;
use self::validate::Admitted;
use self::validate::admit;
use self::validate::each_field;
use self::validate::encoded_op_commits;
use self::validate::encoded_view_commits;
use self::validate::encoded_view_id;
use self::validate::names_decoded_commits;
use self::validate::normal_view;
use self::validate::op_commit_ids;
use self::validate::view_commit_ids;
use crate::objects::ObjectError;
use crate::op_id::CanonicalOp;

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

fn io_err(path: &Path) -> impl FnOnce(io::Error) -> CanonicalError + '_ {
    move |source| CanonicalError::Io {
        path: path.to_owned(),
        source,
    }
}

pub struct CanonicalStore {
    shared: Arc<Shared>,
    /// Generation numbers of stored operations (the root 0, otherwise one more than the
    /// largest parent's), which bound ancestry searches. A stored operation never changes,
    /// so neither does its entry.
    generations: Mutex<HashMap<CanonicalOp, u64>>,
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
    root_operation_id: CanonicalOp,
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
        if *id == self.root_operation_id.0 {
            return Ok(Operation::make_root(self.root_view_id.clone()));
        }
        let bytes = self.operation_bytes(id)?;
        let op = codec::decode_operation(&bytes, &self.root_operation_id.0)
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
        if *id == self.root_operation_id.0 {
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
            parents.push(self.root_operation_id.0.clone());
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
        self.write_original(&origin::fresh(op))
    }

    /// Writes immutable content already prepared by fresh creation or contraction.
    fn write_original(&self, op: &Operation) -> Result<OperationId, CanonicalError> {
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
        &self.root_operation_id.0
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
            .resolve_prefix(prefix, &self.root_operation_id.0)
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
            root_operation_id: CanonicalOp(OperationId::from_bytes(&[0; log::ID_LEN])),
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
        left: &[CanonicalOp],
        right: &[CanonicalOp],
    ) -> Result<Vec<CanonicalOp>, CanonicalError> {
        let to_ops =
            |ids: &[CanonicalOp]| -> Result<Vec<jj_lib::operation::Operation>, CanonicalError> {
                ids.iter().map(|id| self.load_operation(id)).collect()
            };
        let ancestors =
            jj_lib::op_walk::closest_common_ancestors(to_ops(left)?, to_ops(right)?).block_on()?;
        Ok(ancestors
            .into_iter()
            .map(|op| CanonicalOp(op.id().clone()))
            .collect())
    }

    pub fn root_operation_id(&self) -> &CanonicalOp {
        &self.shared.root_operation_id
    }

    pub fn read_operation(&self, id: &CanonicalOp) -> Result<Operation, CanonicalError> {
        self.shared.read_operation(&id.0)
    }

    /// The immutable identity before contraction, recomputed from original parent material.
    pub fn original_id(&self, id: &CanonicalOp) -> Result<OperationId, CanonicalError> {
        Ok(self.read_operation_and_original(id)?.1)
    }

    /// Read once when a caller needs both the operation and its original identity.
    pub fn read_operation_and_original(
        &self,
        id: &CanonicalOp,
    ) -> Result<(Operation, OperationId), CanonicalError> {
        let op = self.read_operation(id)?;
        if id == self.root_operation_id() {
            return Ok((op, id.0.clone()));
        }
        let original = origin::identity(&op)?;
        Ok((op, original))
    }

    /// A stored operation as jj's walks over operations take it.
    pub fn load_operation(
        &self,
        id: &CanonicalOp,
    ) -> Result<jj_lib::operation::Operation, CanonicalError> {
        let store: Arc<dyn OpStore> = self.shared.clone();
        Ok(jj_lib::operation::Operation::new(
            store,
            id.0.clone(),
            self.read_operation(id)?,
        ))
    }

    pub fn read_view(&self, id: &ViewId) -> Result<View, CanonicalError> {
        self.shared.read_view(id)
    }

    /// The parents of a stored operation, without reading the rest of it.
    pub fn parents(&self, id: &CanonicalOp) -> Result<Vec<CanonicalOp>, CanonicalError> {
        Ok(self
            .shared
            .parents(&id.0)?
            .into_iter()
            .map(CanonicalOp)
            .collect())
    }

    /// The view of the operation `id`.
    pub fn read_operation_view(&self, id: &CanonicalOp) -> Result<View, CanonicalError> {
        self.read_view(&self.read_operation(id)?.view_id)
    }

    pub fn write_operation(&self, op: &Operation) -> Result<CanonicalOp, CanonicalError> {
        Ok(CanonicalOp(self.shared.write_operation(op)?))
    }

    pub fn write_view(&self, view: &View) -> Result<ViewId, CanonicalError> {
        self.shared.write_view(view)
    }

    /// The id [`Self::write_operation`] gives `op`, without storing it.
    pub fn operation_id(op: &Operation) -> CanonicalOp {
        CanonicalOp(OperationId::new(blake2b_hash(&origin::fresh(op)).to_vec()))
    }

    /// The id [`Self::write_view`] gives `view`, without storing it.
    pub fn view_id(&self, view: &View) -> Result<ViewId, CanonicalError> {
        Ok(self.shared.views.encode(view)?.0)
    }

    /// Resolves a hex prefix of a canonical operation id.
    pub fn resolve_prefix(&self, prefix: &str) -> Result<Option<CanonicalOp>, CanonicalError> {
        let Some(prefix) = HexPrefix::try_from_hex(prefix) else {
            return Ok(None);
        };
        let resolved = self
            .shared
            .log
            .resolve_prefix(&prefix, &self.root_operation_id().0)
            .map_err(self.shared.log_err())?;
        match resolved {
            PrefixResolution::SingleMatch(id) => Ok(Some(CanonicalOp(id))),
            _ => Ok(None),
        }
    }

    /// Whether any operation but the root is stored.
    pub fn has_operations(&self) -> Result<bool, CanonicalError> {
        Ok(!self.operation_ids()?.is_empty())
    }

    /// Every stored operation except the root, in no particular order.
    pub fn operation_ids(&self) -> Result<Vec<CanonicalOp>, CanonicalError> {
        let ids = self
            .shared
            .log
            .operation_ids()
            .map_err(self.shared.log_err())?;
        Ok(ids.into_iter().map(CanonicalOp).collect())
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
            judge(&mut torn, "operation", &id.0.hex(), id.0.as_bytes(), read)?;
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

    pub fn has_operation(&self, id: &CanonicalOp) -> bool {
        id == self.root_operation_id() || self.shared.log.has_operation(&id.0).unwrap_or(false)
    }

    pub fn has_view(&self, id: &ViewId) -> bool {
        is_root_view(id) || self.shared.log.has_view(id).unwrap_or(false)
    }

    /// The encoded operation, as sent to peers. Not defined for the root operation, which
    /// every store has implicitly.
    pub fn operation_bytes(&self, id: &CanonicalOp) -> Result<Vec<u8>, CanonicalError> {
        self.shared.operation_bytes(&id.0)
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
        ops: &[CanonicalOp],
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
            let malformed = || CanonicalError::MalformedOperation(id.0.hex());
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
    pub fn import_operation(&self, id: &CanonicalOp, bytes: &[u8]) -> Result<(), CanonicalError> {
        self.import_operation_parents(&id.0, bytes)?;
        Ok(())
    }

    /// [`Self::import_operation`], returning the parents of an operation it stored, which
    /// verifying it decoded, or `None` if the operation was stored already.
    fn import_operation_parents(
        &self,
        id: &OperationId,
        bytes: &[u8],
    ) -> Result<Option<Vec<OperationId>>, CanonicalError> {
        if self.has_operation(&CanonicalOp(id.clone())) {
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
        let op = codec::decode_operation(bytes, &self.root_operation_id().0)
            .map_err(|err| Shared::read_error("operation", id.hex(), err))?;
        admit(Admitted {
            kind: "operation",
            malformed: CanonicalError::MalformedOperation,
            expected: id.hex(),
            actual: OperationId::new(blake2b_hash(&op).to_vec()).hex(),
            names_its_commits: names_decoded_commits(bytes, encoded_op_commits, op_commit_ids(&op)),
        })?;
        origin::identity(&op)?;
        presence::check_stamp(&op).map_err(|_| CanonicalError::MalformedOperation(id.hex()))?;
        namespace::Namespace::read(&op.metadata)?;
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
        ancestor: &CanonicalOp,
        heads: &[CanonicalOp],
    ) -> Result<bool, CanonicalError> {
        let mut seen: HashSet<CanonicalOp> = HashSet::new();
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
    pub fn generation(&self, id: &CanonicalOp) -> Result<u64, CanonicalError> {
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
            let missing: Vec<CanonicalOp> = parents
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
    pub fn note_generation(&self, id: &CanonicalOp, parents: &[CanonicalOp]) {
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
        ancestor: &CanonicalOp,
        op: &CanonicalOp,
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
        heads: &[CanonicalOp],
        stop: impl Fn(&CanonicalOp) -> bool,
    ) -> Result<Vec<CanonicalOp>, CanonicalError> {
        let mut order = vec![];
        let mut done: HashSet<CanonicalOp> = HashSet::new();
        // (operation, whether its parents have been pushed)
        let mut stack: Vec<(CanonicalOp, bool)> =
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

    use jj_lib::op_store::RemoteRef;
    use jj_lib::op_store::RemoteView;

    use super::*;
    use crate::objects::bundle;
    use crate::objects::bundle::BundleWriter;

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
        assert_eq!(store.read_operation(&op_id).unwrap(), origin::fresh(&op));
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
            Err(CanonicalError::MalformedOperation(ref hex)) if *hex == op_id.0.hex()
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
            parents: vec![store.root_operation_id().0.to_bytes()],
            metadata: Some(Default::default()),
            commit_predecessors: vec![proto::CommitPredecessors {
                commit_id: vec![3; 20],
                predecessor_ids: vec![],
            }],
            stores_commit_predecessors: false,
        }
        .encode_to_vec();
        let op_id = match store.import_operation(&CanonicalOp(OperationId::new(vec![1; 64])), &op) {
            Err(CanonicalError::HashMismatch { actual, .. }) => {
                CanonicalOp(OperationId::try_from_hex(&actual).unwrap())
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
        merge.parents.push(a.0.clone());
        let merge = store.write_operation(&merge).unwrap();
        let orphan = proto::Operation {
            view_id: view_id.to_bytes(),
            metadata: Some(proto::OperationMetadata {
                attributes: vec![(origin::ORIGINAL_PARENTS.to_owned(), root.0.hex())]
                    .into_iter()
                    .collect(),
                ..Default::default()
            }),
            ..Default::default()
        }
        .encode_to_vec();
        let orphan_id =
            match store.import_operation(&CanonicalOp(OperationId::new(vec![1; 64])), &orphan) {
                Err(CanonicalError::HashMismatch { actual, .. }) => {
                    CanonicalOp(OperationId::try_from_hex(&actual).unwrap())
                }
                other => panic!("{other:?}"),
            };
        store.import_operation(&orphan_id, &orphan).unwrap();
        for id in [&root, &a, &b, &merge, &orphan_id] {
            assert_eq!(
                store.parents(id).unwrap(),
                CanonicalOp::parents_of(&store.read_operation(id).unwrap())
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
            .operation(base.0.as_bytes(), &sender.operation_bytes(&base).unwrap())
            .unwrap();
        writer
            .view_delta_made(child_view.as_bytes(), base_view.as_bytes(), &delta)
            .unwrap();
        writer
            .operation(child.0.as_bytes(), &sender.operation_bytes(&child).unwrap())
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
        let mut ops: Vec<CanonicalOp> = vec![];
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
                    .operation(
                        ops[i].0.as_bytes(),
                        &sender.operation_bytes(&ops[i]).unwrap(),
                    )
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
            .operation(base.0.as_bytes(), &sender.operation_bytes(&base).unwrap())
            .unwrap();
        writer
            .view_delta_made(child_view.as_bytes(), base_view.as_bytes(), &delta)
            .unwrap();
        writer
            .operation(child.0.as_bytes(), &sender.operation_bytes(&child).unwrap())
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

    fn operation(parent: &CanonicalOp, view_id: ViewId) -> Operation {
        let mut op = Operation::make_root(view_id);
        op.parents = vec![parent.0.clone()];
        op
    }

    #[test]
    fn record_metadata_arrives_without_current_operations_or_parent_views() {
        let dir = musubi_testutil::tempdir();
        let root_commit = CommitId::from_bytes(&[0; 20]);
        let sender = CanonicalStore::open(&dir.path().join("sender"), root_commit.clone()).unwrap();
        let root = sender.root_operation_id().clone();
        let parent_view = sender.write_view(&view_with_heads(30)).unwrap();
        let parent = sender
            .write_operation(&operation(&root, parent_view.clone()))
            .unwrap();
        let dropped_view = sender.write_view(&view_with_heads(31)).unwrap();
        let dropped = sender
            .write_operation(&operation(&parent, dropped_view.clone()))
            .unwrap();
        let bundle = tempfile::NamedTempFile::new_in(dir.path()).unwrap();
        // The normal history delta may be empty, or share an ancestor with the metadata.
        for (i, normal) in [vec![], vec![parent.clone()]].into_iter().enumerate() {
            let receiver = CanonicalStore::open(
                &dir.path().join(format!("receiver-{i}")),
                root_commit.clone(),
            )
            .unwrap();
            sender
                .export_operations_with_records(
                    &normal,
                    std::slice::from_ref(&dropped),
                    bundle.path(),
                )
                .unwrap();
            let imported = receiver.import_operations(bundle.path()).unwrap();
            assert_eq!(
                imported.iter().map(|(id, _)| id).collect::<Vec<_>>(),
                [&parent, &dropped]
            );
            assert_eq!(
                receiver
                    .record_operations(std::slice::from_ref(&dropped))
                    .unwrap(),
                [parent.clone(), dropped.clone()]
            );
            assert_eq!(
                receiver.read_view(&parent_view).unwrap(),
                view_with_heads(30)
            );
            assert_eq!(
                receiver.read_view(&dropped_view).unwrap(),
                view_with_heads(31)
            );
        }
        let absent = CanonicalOp(OperationId::from_bytes(&[99; 64]));
        assert!(
            sender
                .export_operations_with_records(&[], &[absent], bundle.path())
                .is_err()
        );
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

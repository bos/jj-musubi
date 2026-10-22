//! The canonical op store: replicated operations, written by this jj-lib.
//!
//! It is an ordinary jj `SimpleOpStore` in its own directory, so canonical ids are ordinary
//! jj operation and view ids. Files received from peers are verified by decoding and
//! re-hashing before they enter the store; this works because every canonical file was
//! written by the same pinned jj-lib, so decoding and re-hashing round-trips exactly.

use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

use std::collections::HashMap;
use std::collections::HashSet;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::git::REMOTE_NAME_FOR_LOCAL_GIT_REPO;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OpStore as _;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RootOperationData;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;
use prost::Message as _;
use thiserror::Error;

use crate::objects::ObjectError;
use crate::objects::bundle;
use crate::objects::bundle::BundleWriter;
use crate::objects::bundle::Record;

fn boxed(err: CanonicalError) -> ObjectError {
    ObjectError::Nested(Box::new(err))
}

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
    path: PathBuf,
    store: Arc<SimpleOpStore>,
    incoming: SimpleOpStore,
}

impl CanonicalStore {
    /// Opens the store at `path`, creating it if needed. `root_commit_id` is the backend's
    /// root commit, which the root view refers to.
    pub fn open(path: &Path, root_commit_id: CommitId) -> Result<Self, CanonicalError> {
        let incoming_path = path.join("incoming");
        for dir in [
            "operations",
            "views",
            "incoming/operations",
            "incoming/views",
        ] {
            let dir = path.join(dir);
            fs::create_dir_all(&dir).map_err(io_err(&dir))?;
        }
        let root_data = || RootOperationData {
            root_commit_id: root_commit_id.clone(),
        };
        Ok(Self {
            path: path.to_owned(),
            store: Arc::new(SimpleOpStore::load(path, root_data())),
            incoming: SimpleOpStore::load(&incoming_path, root_data()),
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
                        let store: Arc<dyn jj_lib::op_store::OpStore> = self.store.clone();
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
        self.store.root_operation_id()
    }

    pub fn read_operation(&self, id: &OperationId) -> Result<Operation, CanonicalError> {
        Ok(self.store.read_operation(id).block_on()?)
    }

    pub fn read_view(&self, id: &ViewId) -> Result<View, CanonicalError> {
        Ok(self.store.read_view(id).block_on()?)
    }

    pub fn write_operation(&self, op: &Operation) -> Result<OperationId, CanonicalError> {
        Ok(self.store.write_operation(op).block_on()?)
    }

    pub fn write_view(&self, view: &View) -> Result<ViewId, CanonicalError> {
        Ok(self.store.write_view(view).block_on()?)
    }

    /// Resolves a hex prefix of a canonical operation id.
    pub fn resolve_prefix(&self, prefix: &str) -> Result<Option<OperationId>, CanonicalError> {
        let Some(prefix) = jj_lib::object_id::HexPrefix::try_from_hex(prefix) else {
            return Ok(None);
        };
        match self.store.resolve_operation_id_prefix(&prefix).block_on()? {
            jj_lib::object_id::PrefixResolution::SingleMatch(id) => Ok(Some(id)),
            _ => Ok(None),
        }
    }

    /// Every stored operation except the root, in no particular order.
    pub fn operation_ids(&self) -> Result<Vec<OperationId>, CanonicalError> {
        let dir = self.path.join("operations");
        let entries = fs::read_dir(&dir).map_err(io_err(&dir))?;
        let mut ids = vec![];
        for entry in entries {
            let entry = entry.map_err(io_err(&dir))?;
            if let Some(id) = entry
                .file_name()
                .to_str()
                .and_then(OperationId::try_from_hex)
            {
                ids.push(id);
            }
        }
        Ok(ids)
    }

    pub fn has_operation(&self, id: &OperationId) -> bool {
        id == self.root_operation_id() || self.op_path(id).exists()
    }

    pub fn has_view(&self, id: &ViewId) -> bool {
        id.as_bytes().iter().all(|&b| b == 0) || self.view_path(id).exists()
    }

    /// The encoded operation, as sent to peers. Not defined for the root operation, which
    /// every store has implicitly.
    pub fn operation_bytes(&self, id: &OperationId) -> Result<Vec<u8>, CanonicalError> {
        let path = self.op_path(id);
        fs::read(&path).map_err(io_err(&path))
    }

    pub fn view_bytes(&self, id: &ViewId) -> Result<Vec<u8>, CanonicalError> {
        let path = self.view_path(id);
        fs::read(&path).map_err(io_err(&path))
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
        let staged = self.path.join("incoming/operations").join(id.hex());
        fs::write(&staged, bytes).map_err(io_err(&staged))?;
        let result = self.incoming.read_operation(id).block_on();
        let op = match result {
            Ok(op) => op,
            Err(err) => {
                fs::remove_file(&staged).ok();
                return Err(err.into());
            }
        };
        let actual = OperationId::new(blake2b_hash(&op).to_vec());
        self.admit(
            &staged,
            &self.op_path(id),
            "operation",
            id.hex(),
            actual.hex(),
        )?;
        Ok(Some(op.parents))
    }

    pub fn import_view(&self, id: &ViewId, bytes: &[u8]) -> Result<(), CanonicalError> {
        if self.has_view(id) {
            return Ok(());
        }
        let staged = self.path.join("incoming/views").join(id.hex());
        fs::write(&staged, bytes).map_err(io_err(&staged))?;
        let view = match self.incoming.read_view(id).block_on() {
            Ok(view) => view,
            Err(err) => {
                fs::remove_file(&staged).ok();
                return Err(err.into());
            }
        };
        let actual = ViewId::new(blake2b_hash(&view).to_vec());
        self.admit(&staged, &self.view_path(id), "view", id.hex(), actual.hex())
    }

    fn admit(
        &self,
        staged: &Path,
        dest: &Path,
        kind: &'static str,
        expected: String,
        actual: String,
    ) -> Result<(), CanonicalError> {
        if expected != actual {
            fs::remove_file(staged).ok();
            return Err(CanonicalError::HashMismatch {
                kind,
                expected,
                actual,
            });
        }
        fs::rename(staged, dest).map_err(io_err(dest))
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
            stack.extend(self.read_operation(&id)?.parents);
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
            let parents = self.read_operation(&id)?.parents;
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
        let is_root_view = |id: &ViewId| id.as_bytes().iter().all(|&b| b == 0);
        let mut writer = BundleWriter::create(out)?;
        writer.begin_compressed()?;
        let mut sent = HashSet::new();
        // The views of the operations written so far, which are usually the next ones'
        // parents.
        let mut views: HashMap<OperationId, ViewId> = HashMap::new();
        // The last view a delta went to, in normal form: usually the next delta's base.
        let mut last: Option<(ViewId, Vec<u8>)> = None;
        for id in ops {
            let op = self.read_operation(id)?;
            let mut parent_views = vec![];
            for parent in &op.parents {
                parent_views.push(match views.get(parent) {
                    Some(view) => view.clone(),
                    None => self.read_operation(parent)?.view_id,
                });
            }
            let view = &op.view_id;
            if !is_root_view(view) && !parent_views.contains(view) && sent.insert(view.clone()) {
                match parent_views.first().filter(|base| !is_root_view(base)) {
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
            writer.operation(id.as_bytes(), &self.operation_bytes(id)?)?;
            views.insert(id.clone(), op.view_id);
        }
        Ok(writer.finish()?)
    }

    /// Verifies and stores the views and operations of a bundle written by
    /// [`Self::export_operations`]. Returns the operations in bundle order, each with its
    /// parents if this stored it, or `None` if it was stored already.
    pub fn import_operations(&self, bundle_path: &Path) -> Result<Vec<Imported>, CanonicalError> {
        let mut ops = vec![];
        // The last view a delta made, in normal form (see `normal_view_bytes`): usually the
        // next delta's base, since consecutive operations' views go as deltas against each
        // other.
        let mut last: Option<(ViewId, Vec<u8>)> = None;
        bundle::read(bundle_path, |record| {
            match record {
                Record::View { id, contents } => {
                    self.import_view(&ViewId::new(id), &contents)
                        .map_err(boxed)?;
                }
                Record::ViewDelta { id, base, delta } => {
                    let (id, base) = (ViewId::new(id), ViewId::new(base));
                    if !self.has_view(&id) {
                        let base = match last.take() {
                            Some((last_id, bytes)) if last_id == base => bytes,
                            _ if !self.has_view(&base) => {
                                return Err(boxed(CanonicalError::MissingDeltaBase {
                                    view: id.hex(),
                                    base: base.hex(),
                                }));
                            }
                            _ => self.normal_view_bytes(&base).map_err(boxed)?,
                        };
                        let contents = bundle::apply_view_delta(&base, &delta)?;
                        self.import_view(&id, &contents).map_err(boxed)?;
                        last = Some((id, contents));
                    }
                }
                Record::Operation { id, contents } => {
                    let id = OperationId::new(id);
                    let parents = self
                        .import_operation_parents(&id, &contents)
                        .map_err(boxed)?;
                    ops.push((id, parents));
                }
                _ => {
                    return Err(ObjectError::MalformedBundle(
                        "unexpected record in an operation bundle".to_owned(),
                    ));
                }
            }
            Ok(())
        })
        .map_err(|err| match err {
            ObjectError::Nested(inner) => *inner.downcast::<CanonicalError>().expect("boxed by us"),
            other => CanonicalError::Bundle(other),
        })?;
        Ok(ops)
    }

    /// A stored view's bytes as a function of its content alone, which view deltas are
    /// between. jj encodes `head_ids`, a set, and `wc_commit_ids`, a map, in hash order,
    /// and rewrites a view's file whenever it writes the same view again, so two stores
    /// can hold different bytes for one view, and the store's own can change. Re-encoding
    /// drops anything this jj-lib does not know, and sorting the entries of those two
    /// fields leaves nothing to chance. The result is a valid encoding of the same view.
    fn normal_view_bytes(&self, id: &ViewId) -> Result<Vec<u8>, CanonicalError> {
        /// `head_ids` and `wc_commit_ids`.
        const UNORDERED: [u32; 2] = [1, 8];
        let malformed = || CanonicalError::MalformedView(id.hex());
        let encoded = jj_lib::protos::simple_op_store::View::decode(&*self.view_bytes(id)?)
            .map_err(|_| malformed())?
            .encode_to_vec();
        let mut fields = top_level_fields(&encoded).ok_or_else(malformed)?;
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
        Ok(fields
            .into_iter()
            .flat_map(|(_, bytes)| bytes)
            .copied()
            .collect())
    }

    fn op_path(&self, id: &OperationId) -> PathBuf {
        self.path.join("operations").join(id.hex())
    }

    fn view_path(&self, id: &ViewId) -> PathBuf {
        self.path.join("views").join(id.hex())
    }
}

/// The top-level fields of a protobuf message, each with its number and its encoding,
/// key included, in order.
fn top_level_fields(mut bytes: &[u8]) -> Option<Vec<(u32, &[u8])>> {
    fn varint(bytes: &mut &[u8]) -> Option<u64> {
        let mut value = 0;
        for shift in (0..64).step_by(7) {
            let (&byte, rest) = bytes.split_first()?;
            *bytes = rest;
            value |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Some(value);
            }
        }
        None
    }
    let mut fields = vec![];
    while !bytes.is_empty() {
        let start = bytes;
        let key = varint(&mut bytes)?;
        let len = match key & 7 {
            0 => {
                varint(&mut bytes)?;
                0
            }
            1 => 8,
            2 => usize::try_from(varint(&mut bytes)?).ok()?,
            5 => 4,
            _ => return None,
        };
        bytes = bytes.get(len..)?;
        let number = u32::try_from(key >> 3).ok()?;
        fields.push((number, &start[..start.len() - bytes.len()]));
    }
    Some(fields)
}

/// Removes this machine's records of its own `.git` from a view: `git_refs`, the `git`
/// pseudo-remote, and each workspace's git HEAD. (Workspaces themselves are handled in
/// `NodeRepo`, which replaces them with machine-qualified entries.)
pub fn strip_git_records(view: &mut View) {
    view.git_refs.clear();
    view.remote_views.remove(REMOTE_NAME_FOR_LOCAL_GIT_REPO);
    view.git_heads.clear();
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use super::*;

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

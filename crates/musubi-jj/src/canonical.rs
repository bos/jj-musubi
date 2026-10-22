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

use std::collections::BTreeSet;
use std::collections::HashMap;
use std::collections::HashSet;

use jj_lib::backend::CommitId;
use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OpStore as _;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::RemoteRef;
use jj_lib::op_store::RemoteView;
use jj_lib::op_store::RootOperationData;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;
use thiserror::Error;

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
    root_commit_id: CommitId,
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
            root_commit_id: root_commit_id.clone(),
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

    /// The view of the operation `id`.
    pub fn read_operation_view(&self, id: &OperationId) -> Result<View, CanonicalError> {
        self.read_view(&self.read_operation(id)?.view_id)
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
        is_root_view(id) || self.view_path(id).exists()
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
        let len = self.root_commit_id.as_bytes().len();
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
        named.remove(self.root_commit_id.as_bytes());
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
        if actual == *id && !names_decoded_commits(bytes, encoded_op_commits, op_commit_ids(&op)) {
            fs::remove_file(&staged).ok();
            return Err(CanonicalError::MalformedOperation(id.hex()));
        }
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
        if actual == *id
            && !names_decoded_commits(bytes, encoded_view_commits, view_commit_ids(&view))
        {
            fs::remove_file(&staged).ok();
            return Err(CanonicalError::MalformedView(id.hex()));
        }
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
                    self.import_view(&ViewId::new(id), &contents)?;
                }
                Record::ViewDelta { id, base, delta } => {
                    let (id, base) = (ViewId::new(id), ViewId::new(base));
                    if !self.has_view(&id) {
                        let base = match last.take() {
                            Some((last_id, bytes)) if last_id == base => bytes,
                            _ if !self.has_view(&base) => {
                                return Err(CanonicalError::MissingDeltaBase {
                                    view: id.hex(),
                                    base: base.hex(),
                                });
                            }
                            _ => self.normal_view_bytes(&base)?,
                        };
                        let contents = bundle::apply_view_delta(&base, &delta)?;
                        self.import_view(&id, &contents)?;
                        last = Some((id, contents));
                    }
                }
                Record::Operation { id, contents } => {
                    let id = OperationId::new(id);
                    let parents = self.import_operation_parents(&id, &contents)?;
                    ops.push((id, parents));
                }
                _ => {
                    return Err(ObjectError::MalformedBundle(
                        "unexpected record in an operation bundle".to_owned(),
                    )
                    .into());
                }
            }
            Ok(())
        })?;
        Ok(ops)
    }

    /// A stored view's bytes as a function of its content alone, which view deltas are
    /// between. A store's bytes for a view are this jj-lib's encoding of it, as written where
    /// the view was made or in the normal form a delta rebuilt it in, but jj encodes
    /// `head_ids`, a set, and `wc_commit_ids`, a map, in hash order, and rewrites a view's
    /// file whenever it writes the same view again: two stores can hold different bytes for
    /// one view, and the store's own can change. Sorting the top-level fields, and the
    /// entries of those two among them, leaves nothing to chance, without decoding the view.
    /// The result is a valid encoding of the same view. (Bytes from a peer that jj-lib did
    /// not write may normalize differently; then a delta against them fails on arrival.)
    fn normal_view_bytes(&self, id: &ViewId) -> Result<Vec<u8>, CanonicalError> {
        /// `head_ids` and `wc_commit_ids`.
        const UNORDERED: [u32; 2] = [1, 8];
        let malformed = || CanonicalError::MalformedView(id.hex());
        let encoded = self.view_bytes(id)?;
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
        let mut normal = Vec::with_capacity(encoded.len());
        for (_, bytes) in fields {
            normal.extend_from_slice(bytes);
        }
        Ok(normal)
    }

    fn op_path(&self, id: &OperationId) -> PathBuf {
        self.path.join("operations").join(id.hex())
    }

    fn view_path(&self, id: &ViewId) -> PathBuf {
        self.path.join("views").join(id.hex())
    }
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

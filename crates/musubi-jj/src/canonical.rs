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
}

fn io_err(path: &Path) -> impl FnOnce(io::Error) -> CanonicalError + '_ {
    move |source| CanonicalError::Io {
        path: path.to_owned(),
        source,
    }
}

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
        if self.has_operation(id) {
            return Ok(());
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
        )
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

    /// Writes `ops` and their views to a bundle, in the given order, which should put
    /// ancestors first (as [`Self::ancestors_until`] does).
    pub fn export_operations(&self, ops: &[OperationId], out: &Path) -> Result<(), CanonicalError> {
        let mut writer = BundleWriter::create(out)?;
        let mut views = HashSet::new();
        for id in ops {
            let op = self.read_operation(id)?;
            if views.insert(op.view_id.clone()) && !op.view_id.as_bytes().iter().all(|&b| b == 0) {
                writer.view(op.view_id.as_bytes(), &self.view_bytes(&op.view_id)?)?;
            }
            writer.operation(id.as_bytes(), &self.operation_bytes(id)?)?;
        }
        Ok(writer.finish()?)
    }

    /// Verifies and stores the views and operations of a bundle written by
    /// [`Self::export_operations`]. Returns the operation ids, in bundle order.
    pub fn import_operations(
        &self,
        bundle_path: &Path,
    ) -> Result<Vec<OperationId>, CanonicalError> {
        let mut ops = vec![];
        bundle::read(bundle_path, |record| {
            match record {
                Record::View { id, contents } => {
                    self.import_view(&ViewId::new(id), &contents)
                        .map_err(boxed)?;
                }
                Record::Operation { id, contents } => {
                    let id = OperationId::new(id);
                    self.import_operation(&id, &contents).map_err(boxed)?;
                    ops.push(id);
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

    fn op_path(&self, id: &OperationId) -> PathBuf {
        self.path.join("operations").join(id.hex())
    }

    fn view_path(&self, id: &ViewId) -> PathBuf {
        self.path.join("views").join(id.hex())
    }
}

/// Removes this machine's records of its own `.git` from a view: `git_refs`, the `git`
/// pseudo-remote, and each workspace's git HEAD. (Workspaces themselves are handled in
/// `NodeRepo`, which replaces them with machine-qualified entries.)
pub fn strip_git_records(view: &mut View) {
    view.git_refs.clear();
    view.remote_views.remove(REMOTE_NAME_FOR_LOCAL_GIT_REPO);
    view.git_heads.clear();
}

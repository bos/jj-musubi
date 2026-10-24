//! Encoding and decoding canonical operations and views as jj's simple op store does.
//!
//! Operations are decoded here, as this jj-lib's `simple_op_store` decodes them: they are
//! read at every step of a walk over the history, and their schema is small. A decoding
//! that strayed from jj's would show at once, since every read checks that the operation
//! hashes to its id. Views, whose schema is large and has legacy fields, go through jj's own
//! code instead, by way of a scratch op store: their bytes are written to a file there for
//! jj to read, or jj writes them there to be read back.

use std::collections::BTreeMap;
use std::fs;
use std::io;
use std::path::Path;
use std::sync::Mutex;
use std::sync::PoisonError;

use jj_lib::backend::CommitId;
use jj_lib::backend::MillisSinceEpoch;
use jj_lib::backend::Timestamp;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::OpStore as _;
use jj_lib::op_store::OpStoreError;
use jj_lib::op_store::Operation;
use jj_lib::op_store::OperationId;
use jj_lib::op_store::OperationMetadata;
use jj_lib::op_store::RootOperationData;
use jj_lib::op_store::TimestampRange;
use jj_lib::op_store::View;
use jj_lib::op_store::ViewId;
use jj_lib::protos::simple_op_store as proto;
use jj_lib::simple_op_store::SimpleOpStore;
use pollster::FutureExt as _;
use prost::Message as _;

use super::log::ID_LEN;

/// Why an encoded operation doesn't decode, as jj's decoding would refuse it.
#[derive(Debug, thiserror::Error)]
pub enum DecodeError {
    #[error(transparent)]
    Prost(#[from] prost::DecodeError),
    #[error("invalid hash length (expected {ID_LEN} bytes, got {0} bytes)")]
    IdLength(usize),
}

/// Decodes an operation as this jj-lib's `SimpleOpStore::read_operation` does: an operation
/// without parents, from before jj had a root operation, has the root as its parent.
pub fn decode_operation(bytes: &[u8], root: &OperationId) -> Result<Operation, DecodeError> {
    let proto::Operation {
        view_id,
        parents,
        metadata,
        commit_predecessors,
        stores_commit_predecessors,
    } = proto::Operation::decode(bytes)?;
    let id = |bytes: Vec<u8>| {
        if bytes.len() == ID_LEN {
            Ok(bytes)
        } else {
            Err(DecodeError::IdLength(bytes.len()))
        }
    };
    let mut parents: Vec<OperationId> = parents
        .into_iter()
        .map(|parent| id(parent).map(OperationId::new))
        .collect::<Result<_, _>>()?;
    if parents.is_empty() {
        parents.push(root.clone());
    }
    let proto::OperationMetadata {
        start_time,
        end_time,
        description,
        hostname,
        username,
        is_snapshot,
        workspace_name,
        attributes,
    } = metadata.unwrap_or_default();
    let timestamp = |t: Option<proto::Timestamp>| {
        let proto::Timestamp {
            millis_since_epoch,
            tz_offset,
        } = t.unwrap_or_default();
        Timestamp {
            timestamp: MillisSinceEpoch(millis_since_epoch),
            tz_offset,
        }
    };
    let metadata = OperationMetadata {
        time: TimestampRange {
            start: timestamp(start_time),
            end: timestamp(end_time),
        },
        description,
        hostname,
        username,
        is_snapshot,
        workspace_name: workspace_name.map(Into::into),
        attributes: attributes.into_iter().collect(),
    };
    let commit_predecessors = stores_commit_predecessors.then(|| {
        commit_predecessors
            .into_iter()
            .map(|entry| {
                let proto::CommitPredecessors {
                    commit_id,
                    predecessor_ids,
                } = entry;
                let predecessors = predecessor_ids.into_iter().map(CommitId::new).collect();
                (CommitId::new(commit_id), predecessors)
            })
            .collect::<BTreeMap<_, _>>()
    });
    Ok(Operation {
        view_id: ViewId::new(id(view_id)?),
        parents,
        metadata,
        commit_predecessors,
    })
}

/// Encodes an operation as this jj-lib's `SimpleOpStore::write_operation` does. It is taken
/// apart field by field, so that a jj-lib with more fields fails to build here, and whoever
/// upgrades it brings this up to date.
pub fn encode_operation(op: &Operation) -> Vec<u8> {
    let Operation {
        view_id,
        parents,
        metadata,
        commit_predecessors,
    } = op;
    let OperationMetadata {
        time: TimestampRange { start, end },
        description,
        hostname,
        username,
        is_snapshot,
        workspace_name,
        attributes,
    } = metadata;
    let timestamp = |t: &Timestamp| proto::Timestamp {
        millis_since_epoch: t.timestamp.0,
        tz_offset: t.tz_offset,
    };
    let metadata = proto::OperationMetadata {
        start_time: Some(timestamp(start)),
        end_time: Some(timestamp(end)),
        description: description.clone(),
        hostname: hostname.clone(),
        username: username.clone(),
        is_snapshot: *is_snapshot,
        workspace_name: workspace_name.clone().map(Into::into),
        attributes: attributes
            .iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect(),
    };
    let (commit_predecessors, stores_commit_predecessors) = match commit_predecessors {
        Some(map) => (
            map.iter()
                .map(|(commit, predecessors)| proto::CommitPredecessors {
                    commit_id: commit.to_bytes(),
                    predecessor_ids: predecessors.iter().map(|id| id.to_bytes()).collect(),
                })
                .collect(),
            true,
        ),
        None => (vec![], false),
    };
    proto::Operation {
        view_id: view_id.to_bytes(),
        parents: parents.iter().map(|id| id.to_bytes()).collect(),
        metadata: Some(metadata),
        commit_predecessors,
        stores_commit_predecessors,
    }
    .encode_to_vec()
}

/// Views encoded and decoded by jj, through a scratch op store of its own.
#[derive(Debug)]
pub struct ViewCodec {
    dir: tempfile::TempDir,
    store: SimpleOpStore,
    /// One view at a time: jj names its file by the view's id.
    busy: Mutex<()>,
}

impl ViewCodec {
    /// A codec with its scratch store in a new directory under `parent`, where it removes
    /// any a process that crashed left behind more than a day ago.
    pub fn new(parent: &Path, root_commit_id: CommitId) -> io::Result<Self> {
        remove_stale_scratch(parent);
        let dir = tempfile::Builder::new()
            .prefix("scratch-")
            .tempdir_in(parent)?;
        let store = SimpleOpStore::load(dir.path(), RootOperationData { root_commit_id });
        Ok(Self {
            dir,
            store,
            busy: Mutex::new(()),
        })
    }

    fn views_dir(&self) -> io::Result<std::path::PathBuf> {
        let views = self.dir.path().join("views");
        // Made again if something cleaned it away.
        fs::create_dir_all(&views)?;
        Ok(views)
    }

    /// Decodes `bytes` as jj decodes the view it stores as `id`.
    pub fn decode(&self, id: &ViewId, bytes: &[u8]) -> Result<View, OpStoreError> {
        let _busy = self.busy.lock().unwrap_or_else(PoisonError::into_inner);
        let path = self.views_dir().map_err(write_error)?.join(id.hex());
        fs::write(&path, bytes).map_err(write_error)?;
        let view = self.store.read_view(id).block_on();
        fs::remove_file(&path).ok();
        view
    }

    /// Encodes a view as jj writes it, with its id.
    pub fn encode(&self, view: &View) -> Result<(ViewId, Vec<u8>), OpStoreError> {
        let _busy = self.busy.lock().unwrap_or_else(PoisonError::into_inner);
        let views = self.views_dir().map_err(write_error)?;
        let id = self.store.write_view(view).block_on()?;
        let path = views.join(id.hex());
        let bytes = fs::read(&path).map_err(write_error);
        fs::remove_file(&path).ok();
        Ok((id, bytes?))
    }
}

/// Removes scratch directories in `parent` unused for a day: whose `views`, where every
/// view is written and removed, hasn't changed, or which have none. One in use that another
/// process removes anyway makes its `views` again (see [`ViewCodec::views_dir`]).
fn remove_stale_scratch(parent: &Path) {
    let Ok(entries) = fs::read_dir(parent) else {
        return;
    };
    let age = |path: &Path| {
        fs::metadata(path)
            .and_then(|meta| meta.modified())
            .ok()
            .and_then(|modified| modified.elapsed().ok())
    };
    for entry in entries.flatten() {
        if !entry.file_name().to_string_lossy().starts_with("scratch-") {
            continue;
        }
        let used = age(&entry.path().join("views")).or_else(|| age(&entry.path()));
        if used.is_some_and(|age| age > std::time::Duration::from_secs(24 * 60 * 60)) {
            fs::remove_dir_all(entry.path()).ok();
        }
    }
}

fn write_error(err: io::Error) -> OpStoreError {
    OpStoreError::WriteObject {
        object_type: "view",
        source: Box::new(err),
    }
}

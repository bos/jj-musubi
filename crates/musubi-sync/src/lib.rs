//! The protocol core (`musubi-core`) bound to real jj repositories (`musubi-jj`) and hub
//! storage (`musubi-hub`).
//!
//! Internal to jj-musubi, with no stable API.
//!
//! - [`node::NodeAdapter`] implements the core's `LocalRepo` over a jj repository.
//! - [`hub::HubAdapter`] implements the core's `HubStorage` over a hub store.
//! - [`hive::Hive`] runs a hub and nodes in one process with direct delivery, for tests.
//!
//! Attachments are local bundle files here; transports carry them as chunked blobs.

use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use std::time::SystemTime;

use jj_lib::backend::CommitId;

pub mod blobs;
pub mod driver;
pub mod hive;
pub mod hub;
pub mod node;
pub mod remote;
pub mod server;
pub mod service;
pub mod wire;

pub type OpId = jj_lib::op_store::OperationId;

/// An abbreviated id, for logs. Ids from the wire are not checked for length.
pub(crate) fn short(op: &OpId) -> String {
    use jj_lib::object_id::ObjectId as _;
    let hex = op.hex();
    hex.get(..12).unwrap_or(&hex).to_owned()
}

/// Content accompanying a protocol message.
#[derive(Clone, Debug, Default)]
pub enum Attachment {
    #[default]
    None,
    /// A bundle file (see `musubi_jj::objects::bundle`), deleted once nothing refers to it.
    Bundle(Arc<tempfile::TempPath>),
    /// A bundle file owned by someone else, such as a blob store.
    File(PathBuf),
    /// Commits the requester has, with everything reachable from them.
    Haves(Vec<CommitId>),
}

impl Attachment {
    pub fn bundle(path: tempfile::TempPath) -> Self {
        Self::Bundle(Arc::new(path))
    }

    pub fn bundle_path(&self) -> anyhow::Result<&Path> {
        match self {
            Self::Bundle(path) => Ok(path),
            Self::File(path) => Ok(path),
            other => anyhow::bail!("expected a bundle, got {other:?}"),
        }
    }

    pub fn haves(&self) -> &[CommitId] {
        match self {
            Self::Haves(haves) => haves,
            _ => &[],
        }
    }
}

/// How old a temporary bundle must be for whoever opens its directory to take it for one a
/// process left there when it was killed: none is in use for so long.
const ABANDONED_BUNDLE_AGE: Duration = Duration::from_secs(24 * 3600);

/// Creates `dir`, for temporary bundles, if need be, and removes any a process left there
/// when it was killed: only dropping its [`tempfile::TempPath`] deletes a bundle.
pub(crate) fn open_bundle_dir(dir: &Path) -> io::Result<()> {
    fs::create_dir_all(dir)?;
    blobs::sweep_dir(dir, SystemTime::now() - ABANDONED_BUNDLE_AGE);
    Ok(())
}

/// A fresh temporary file in `dir` for building a bundle.
pub(crate) fn temp_bundle(dir: &Path) -> anyhow::Result<tempfile::TempPath> {
    Ok(tempfile::NamedTempFile::new_in(dir)?.into_temp_path())
}

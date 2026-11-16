//! A copy's persisted sync status and the synchronized snapshot shared with control requests.
//!
//! The worker records changes through `SharedStatus`, which keeps the memory update and the
//! best-effort file write under one lock. Foreground syncs use the same status format directly.

use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::SystemTime;

use musubi_sync::node::history_lost;
use serde::Deserialize;
use serde::Serialize;

use crate::control::Synced;
use crate::repo::Located;

/// A repository's replication state, written after every sync attempt, by the daemon or by
/// `musubi sync` without one.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Status {
    pub last_attempt: Option<u64>,
    pub last_success: Option<u64>,
    pub known_seq: Option<u64>,
    pub known_head: Option<String>,
    pub error: Option<String>,
    /// Whether the error is one that syncing again can't get past, as after `jj op abandon`.
    #[serde(default)]
    pub paused: bool,
    /// Outgoing snapshot content needs a decision; receiving continues normally.
    #[serde(default)]
    pub publication_held: bool,
}

impl Status {
    pub fn path(repo_path: &Path) -> PathBuf {
        repo_path.join("musubi/status.json")
    }

    pub fn load(repo_path: &Path) -> Option<Self> {
        serde_json::from_slice(&fs::read(Self::path(repo_path)).ok()?).ok()
    }

    /// Records a sync: its error, if it failed, and the hive's head as it left the node
    /// knowing it.
    pub(super) fn synced(&mut self, error: Option<&anyhow::Error>, known: &Synced) {
        self.last_attempt = Some(now());
        if error.is_none() {
            self.last_success = self.last_attempt;
        }
        self.set_error(error);
        self.known_seq = Some(known.seq);
        self.known_head = Some(known.head.clone());
    }

    /// Records an attempt that failed before it could sync, as to reach the hub.
    pub(super) fn failed(&mut self, error: &anyhow::Error) {
        self.last_attempt = Some(now());
        self.set_error(Some(error));
    }

    fn set_error(&mut self, error: Option<&anyhow::Error>) {
        self.error = error.map(|err| format!("{err:#}"));
        self.paused = error.is_some_and(history_lost);
        self.publication_held = error.is_some_and(publication_held);
    }

    /// Overwrites the status in place: it changes at every sync attempt, and ext4 writes out
    /// at once a file truncated to nothing, or renamed over another. A reader that comes
    /// while it is written may find no status.
    pub(super) fn save(&self, repo_path: &Path) {
        let Ok(json) = serde_json::to_vec_pretty(self) else {
            return;
        };
        let write = || -> std::io::Result<()> {
            let mut file = fs::OpenOptions::new()
                .write(true)
                .create(true)
                .truncate(false)
                .open(Self::path(repo_path))?;
            file.write_all(&json)?;
            file.set_len(json.len() as u64)
        };
        write().ok();
    }
}

pub(super) fn publication_held(error: &anyhow::Error) -> bool {
    error
        .chain()
        .any(|cause| cause.is::<musubi_jj::node::PublicationHeld>())
}

pub fn now() -> u64 {
    SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// A worker's status, readable by the server without exposing its locking or file updates.
#[derive(Clone)]
pub(super) struct SharedStatus(Arc<Mutex<Status>>);

impl SharedStatus {
    pub(super) fn new(status: Status) -> Self {
        Self(Arc::new(Mutex::new(status)))
    }

    pub(super) fn snapshot(&self) -> Status {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }

    pub(super) fn succeeded_since(&self, started: u64) -> bool {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .last_success
            .is_some_and(|time| time >= started)
    }

    pub(super) fn publication_held(&self) -> bool {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .publication_held
    }

    /// Records in memory and, if this is still the copy being served, in its status file.
    pub(super) fn record(&self, copy: Option<&Located>, change: impl FnOnce(&mut Status)) {
        let mut status = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        change(&mut status);
        if let Some(located) = copy {
            status.save(&located.repo_path);
        }
    }
}

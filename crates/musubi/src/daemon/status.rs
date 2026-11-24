//! A copy's persisted sync status and the synchronized snapshot shared with control requests.
//!
//! The worker records changes through `SharedStatus`, which keeps the memory update and the
//! best-effort file write under one lock. Foreground syncs use the same status format directly.

use std::collections::BTreeMap;
use std::fs;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::PoisonError;
use std::time::SystemTime;

use musubi_hub::hub_dir::Pause;
use musubi_sync::node::history_lost;
use musubi_sync::remote::HivePaused;
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
    /// `paused` in the file, as earlier releases wrote it, before hives could be paused.
    #[serde(default, rename = "paused")]
    pub history_lost: bool,
    /// Who paused the hive, and when, if the error is that it is paused (`musubi pause`).
    #[serde(default)]
    pub hive_paused: Option<Pause>,
    /// Outgoing snapshot content needs a decision; receiving continues normally.
    #[serde(default)]
    pub publication_held: bool,
    /// Whether the error is that a `musubi resume` here stopped partway.
    #[serde(default)]
    pub reset_unfinished: bool,
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
        self.history_lost = error.is_some_and(history_lost);
        self.hive_paused = error.and_then(HivePaused::of);
        self.publication_held = error.is_some_and(publication_held);
        self.reset_unfinished = error.is_some_and(crate::reset::unfinished);
    }

    /// Forgets a pause the last attempt found, and the error it failed with, once the hub has
    /// answered a request of a sync since, which it doesn't while the hive is paused. Returns
    /// whether there was one.
    pub(super) fn pause_lifted(&mut self) -> bool {
        let lifted = self.hive_paused.take().is_some();
        if lifted {
            self.error = None;
        }
        lifted
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
pub(super) struct SharedStatus(Arc<Mutex<WorkerStatus>>);

struct WorkerStatus {
    sync: Status,
    snapshot_issues: BTreeMap<String, String>,
}

impl SharedStatus {
    pub(super) fn new(status: Status) -> Self {
        Self(Arc::new(Mutex::new(WorkerStatus {
            sync: status,
            snapshot_issues: BTreeMap::new(),
        })))
    }

    pub(super) fn snapshot(&self) -> Status {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .sync
            .clone()
    }

    pub(super) fn snapshot_issues(&self) -> BTreeMap<String, String> {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .snapshot_issues
            .clone()
    }

    pub(super) fn set_snapshot_issues(&self, issues: BTreeMap<String, String>) {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .snapshot_issues = issues;
    }

    pub(super) fn succeeded_since(&self, started: u64) -> bool {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .sync
            .last_success
            .is_some_and(|time| time >= started)
    }

    pub(super) fn hive_paused(&self) -> bool {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .sync
            .hive_paused
            .is_some()
    }

    /// Records, in memory and in `copy`'s status file, that the hub has answered a request of
    /// the sync under way, so that `musubi status` stops saying the hive is paused while the
    /// sync brings in what the hive did meanwhile, rather than until it ends.
    pub(super) fn answered(&self, copy: &Located) {
        let mut status = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        if status.sync.pause_lifted() {
            status.sync.save(&copy.repo_path);
        }
    }

    pub(super) fn publication_held(&self) -> bool {
        self.0
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .sync
            .publication_held
    }

    /// Records in memory and, if this is still the copy being served, in its status file.
    pub(super) fn record(&self, copy: Option<&Located>, change: impl FnOnce(&mut Status)) {
        let mut status = self.0.lock().unwrap_or_else(PoisonError::into_inner);
        change(&mut status.sync);
        if let Some(located) = copy {
            status.sync.save(&located.repo_path);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The hub answering a sync's request forgets a pause the last attempt found, with its
    /// error, in memory and in the status file, which `musubi status` reads without a daemon;
    /// with no pause remembered, it changes and writes nothing. Keeping the error, or not
    /// saving, fails it.
    #[test]
    fn an_answer_forgets_a_remembered_pause() {
        let dir = musubi_testutil::tempdir();
        let copy = Located {
            workspace_root: dir.path().to_owned(),
            repo_path: dir.path().join("repo"),
        };
        fs::create_dir_all(copy.repo_path.join("musubi")).unwrap();
        let pause = Pause {
            by: "alpha".to_owned(),
            at: 0,
        };
        let mut paused = Status::default();
        paused.failed(&HivePaused(pause).into());
        assert!(paused.hive_paused.is_some() && paused.error.is_some());
        let shared = SharedStatus::new(paused);
        shared.answered(&copy);
        let saved = Status::load(&copy.repo_path).expect("saved");
        for status in [shared.snapshot(), saved] {
            assert_eq!((status.hive_paused, status.error), (None, None));
        }

        fs::remove_file(Status::path(&copy.repo_path)).unwrap();
        let mut failing = Status::default();
        failing.failed(&anyhow::anyhow!("the hub is out of reach"));
        let shared = SharedStatus::new(failing);
        shared.answered(&copy);
        assert_eq!(
            shared.snapshot().error.as_deref(),
            Some("the hub is out of reach")
        );
        assert!(Status::load(&copy.repo_path).is_none());
    }
}

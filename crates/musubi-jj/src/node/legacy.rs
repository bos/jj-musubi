//! What earlier releases kept in a copy's `musubi` directory to replicate `jj op abandon`.
//!
//! musubi no longer passes an abandon on, so nothing reads these files, and a copy that holds
//! them removes them when it opens the repository. They record how a copy renamed the hive's
//! history when it took the hub's records, which no machine takes now: the hub's names for
//! operations are the names that are left, and the hive's heads already carry them.

use std::fs;
use std::io::ErrorKind;
use std::path::Path;

use super::NodeError;

/// What the earlier releases called the files they kept the hive's records, this copy's
/// renamings of its history, the hub's renamings and the originals' fingerprints in.
const FILES: [&str; 4] = ["records.json", "superseded", "hub-renamings", "originals"];

/// Removes the files earlier releases kept to replicate `jj op abandon`, unless they record
/// drops this copy hadn't published. Returns whether they do, in which case they stay, so that
/// every later open finds them again: such a copy lost history the hive has, and stops syncing
/// as any other does (`NodeRepo::refuse_legacy_drops`).
///
/// Compatibility until 2027-02-21: remove this, `NodeRepo::refuse_legacy_drops`, its call and
/// the test `drops_recorded_before_upgrading_stop_that_copy`, and the guide's and the
/// changelog's mention of them. A release before 0.48 recorded drops in `records.json` on
/// `jj op abandon`, and published them on the next sync.
pub(super) fn remove_records(musubi_dir: &Path) -> Result<bool, NodeError> {
    let io = |path: &Path, source| NodeError::Io {
        path: path.to_owned(),
        source,
    };
    let records = musubi_dir.join(FILES[0]);
    match fs::read(&records) {
        Ok(bytes) => {
            if has_pending_drops(&bytes) {
                return Ok(true);
            }
        }
        Err(err) if err.kind() == ErrorKind::NotFound => {}
        Err(err) => return Err(io(&records, err)),
    }
    for name in FILES {
        let path = musubi_dir.join(name);
        match fs::remove_file(&path) {
            Ok(()) => {}
            Err(err) if err.kind() == ErrorKind::NotFound => {}
            Err(err) => return Err(io(&path, err)),
        }
    }
    Ok(false)
}

/// Whether `records.json`, as an earlier release wrote it, lists drops not yet published, or
/// records it was taking, whose move of the op heads wasn't done: such a copy's history is
/// named half one way and half another. A file this can't read says none: it was torn, and
/// nothing it says is worth stopping for.
fn has_pending_drops(bytes: &[u8]) -> bool {
    let Ok(records) = serde_json::from_slice::<serde_json::Value>(bytes) else {
        return false;
    };
    let filled = |value: Option<&serde_json::Value>| {
        value
            .and_then(serde_json::Value::as_array)
            .is_some_and(|items| !items.is_empty())
    };
    let moving = records
        .get("realign")
        .is_some_and(|realign| filled(realign.get("from")) || filled(realign.get("to")));
    filled(records.get("pending")) || filled(records.get("custody")) || moving
}

impl super::NodeRepo {
    /// Fails if an earlier release left drops recorded here that it hadn't published: this
    /// copy lost history the hive has, so it stops syncing, publishing nothing.
    ///
    /// Compatibility until 2027-02-21: see `remove_records`.
    pub fn refuse_legacy_drops(&self) -> Result<(), NodeError> {
        if self.legacy_drops {
            Err(NodeError::UnreachableHistory)
        } else {
            Ok(())
        }
    }
}

/// What development builds after 0.47 called the file of the machine keys a repository had
/// left hives under, which no release reads.
pub(super) const RETIRED_KEYS: &str = "retired-keys.json";

impl super::NodeRepo {
    /// Fails if a development build after 0.47 took this repository out of a hive, and maybe
    /// joined one again under another key: what it recorded to tell its operations under each
    /// key apart this build doesn't read, so this repository can't sync, join or leave until it starts
    /// over without the history it shared (`musubi join --fresh`), which removes the file
    /// (`SHARED_HISTORY`).
    ///
    /// Compatibility until 2027-02-25: remove this, `NodeError::RetiredKeys`, their calls,
    /// `RETIRED_KEYS` in `SHARED_HISTORY`, and the test
    /// `a_repository_a_development_build_rejoined_under_a_new_key_starts_over`. No release
    /// wrote the file, so no guide or changelog mentions it.
    pub fn refuse_retired_keys(repo_path: &Path) -> Result<(), NodeError> {
        if repo_path.join("musubi").join(RETIRED_KEYS).exists() {
            Err(NodeError::RetiredKeys)
        } else {
            Ok(())
        }
    }
}

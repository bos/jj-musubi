//! A hive's store over its life on disk, past what joins and pushes do to it: made again
//! when a power cut leaves it corrupt, set aside under `removed/` when the hive is made again
//! or removed, and deleted or emptied after their retention period. A removed hive's
//! directory stays under `removed/`, emptied, as its tombstone.

use std::collections::BTreeSet;
use std::fs;
use std::io::BufRead as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::Context as _;
use uuid::Uuid;

use super::HIVE_FILE;
use super::HiveId;
use super::HiveInfo;
use super::HubDir;
use super::Refusal;
use super::refusal;
use crate::store;
use crate::store::HubStore;
use crate::store::StoreError;

/// How long a hive's corrupt store, set aside when the hive was made again, stays once the
/// new one has accepted a head, and a removed hive's store stays: long enough for someone
/// curious to look at it.
pub(super) const SET_ASIDE_LIFETIME: Duration = Duration::from_secs(24 * 3600);

/// A store set aside under `removed/`: a hive's corrupt store, set aside when the hive was
/// made again, or a removed hive's.
pub(super) struct SetAside {
    id: HiveId,
    path: PathBuf,
    /// When it was set aside, in seconds since the epoch.
    stamp: u64,
}

impl HubDir {
    /// Makes hive `id`, whose store `why` found corrupt, again: empty, for its machines to
    /// fill, under its name and with the index joins match it by. The hive goes back to its
    /// root, and machines that knew its later heads follow it (docs/internals/protocol.md,
    /// "Network and failures").
    ///
    /// Its store goes under `removed/` until a day after the new one has accepted a head,
    /// and a new one takes its place, made whole beside it first, so that a failure leaves
    /// the hive as it was, to be made again next time, and a crash between the two renames
    /// leaves it for the hub to finish as it next starts.
    pub fn remake(&mut self, id: &HiveId, why: &StoreError) -> anyhow::Result<()> {
        let hive = self.hive(id)?;
        let removed = self.dir.join("removed");
        fs::create_dir_all(&removed)?;
        let stamp = now();
        let aside = removed.join(format!("{id}-{stamp}.corrupt"));
        let staging = remade(&self.dir, id);
        if staging.exists() {
            fs::remove_dir_all(&staging)?;
        }
        HubStore::init(&staging, hive.meta.backend)?;
        // Linked, not written again: a file new to the disk is what a power cut empties, and
        // a hive whose own file won't parse stops the hub starting.
        fs::hard_link(hive.dir.join(HIVE_FILE), staging.join(HIVE_FILE))?;
        hive.index.save(&staging)?;
        fs::rename(&hive.dir, &aside)?;
        if let Err(err) = fs::rename(&staging, &hive.dir) {
            fs::rename(&aside, &hive.dir).ok();
            return Err(err.into());
        }
        tracing::warn!(
            "hive {} ({id}) is made again, empty, for its machines to fill ({why}); the old \
             store is in {}, until a day from now once they have",
            hive.meta.name,
            aside.display()
        );
        self.corrupt.push(SetAside {
            id: id.clone(),
            path: aside,
            stamp,
        });
        Ok(())
    }

    /// Deletes each corrupt store [`Self::remake`] set aside a day after it did, once the hive
    /// made again has accepted a head, so that its machines have filled it, or is gone; and
    /// empties each removed hive's store a day after it was removed, keeping its directory
    /// as the hive's tombstone. In the background: a store can be large, and the caller holds
    /// the hub. One cut short is still a tombstone, and is emptied as the hub next starts.
    pub(super) fn sweep(&mut self) {
        let now = now();
        self.unemptied.retain(|SetAside { id, path, stamp }| {
            if now.saturating_sub(*stamp) < SET_ASIDE_LIFETIME.as_secs() {
                return true;
            }
            let (id, path) = (id.clone(), path.clone());
            std::thread::spawn(move || match empty_dir(&path) {
                Ok(()) => tracing::info!("emptied removed hive {id}'s store"),
                Err(err) => tracing::warn!("emptying {}: {err}", path.display()),
            });
            false
        });
        let hives = &self.hives;
        self.corrupt.retain(|SetAside { id, path, stamp }| {
            if now.saturating_sub(*stamp) < SET_ASIDE_LIFETIME.as_secs() {
                return true;
            }
            // Accepted a head: a line after the root's.
            let replaced = hives.get(id).is_none_or(|hive| {
                fs::File::open(hive.dir.join("heads"))
                    .is_ok_and(|heads| std::io::BufReader::new(heads).lines().nth(1).is_some())
            });
            if replaced {
                let (id, path) = (id.clone(), path.clone());
                std::thread::spawn(move || match delete_dir(&path) {
                    Ok(()) => tracing::info!("deleted hive {id}'s corrupt store"),
                    Err(err) => tracing::warn!("deleting {}: {err}", path.display()),
                });
            }
            !replaced
        });
    }

    /// Whether `musubi hub remove` removed the hive with this id.
    pub fn is_removed(&self, id: &HiveId) -> bool {
        self.removed.contains(id)
    }

    /// Takes a hive out of the hub, keeping its store under `removed/`. The caller has
    /// stopped serving it.
    pub fn remove(&mut self, id: &HiveId) -> Result<(HiveInfo, RemovedStore), Refusal> {
        let info = self.info(id).ok_or_else(|| format!("no hive {id}"))?;
        let removed = self.dir.join("removed");
        fs::create_dir_all(&removed).map_err(refusal)?;
        let stamp = now();
        let hive = &self.hives[id];
        let path = removed.join(format!("{id}-{stamp}"));
        fs::rename(&hive.dir, &path).map_err(refusal)?;
        self.hives.remove(id);
        self.removed.insert(id.clone());
        self.unemptied.push(SetAside {
            id: id.clone(),
            path: path.clone(),
            stamp,
        });
        Ok((
            info,
            RemovedStore {
                id: id.clone(),
                path,
            },
        ))
    }
}

/// A removed hive's store, which can be emptied without holding the hub directory lock.
pub struct RemovedStore {
    id: HiveId,
    path: PathBuf,
}

impl RemovedStore {
    /// Empties the store and deletes any corrupt stores set aside for the same hive.
    /// The empty directory remains the hive's tombstone.
    pub fn purge(self) -> anyhow::Result<()> {
        let removed = self.path.parent().expect("store under removed/");
        let entries =
            fs::read_dir(removed).with_context(|| format!("reading {}", removed.display()))?;
        for entry in entries {
            let entry = entry.with_context(|| format!("reading {}", removed.display()))?;
            let name = entry.file_name();
            if name
                .to_str()
                .and_then(aside_name)
                .is_some_and(|(id, _, corrupt)| corrupt && id == self.id.as_str())
            {
                delete_dir(&entry.path())
                    .with_context(|| format!("deleting {}", entry.path().display()))?;
            }
        }
        empty_dir(&self.path).with_context(|| format!("emptying {}", self.path.display()))
    }
}

/// A hive's store, or why it is corrupt.
pub enum Opened {
    Whole(Box<HubStore>),
    /// Corrupt, and to be made again.
    Damaged(StoreError),
}

/// Opens the store in `dir`: one that won't open because it is corrupt is damaged. Fails if
/// it won't open for some other reason, as when the hub is out of file descriptors.
pub fn open_whole(dir: &Path) -> anyhow::Result<Opened> {
    match HubStore::open(dir) {
        Ok(store) => Ok(Opened::Whole(Box::new(store))),
        Err(err) if store::is_corrupt(&err) => Ok(Opened::Damaged(err)),
        Err(err) => Err(err.into()),
    }
}

/// Where [`HubDir::remake`] makes hive `id` of the hub in `hub_dir` again: not a hive's
/// name, which is its id.
pub(super) fn remade(hub_dir: &Path, id: &HiveId) -> PathBuf {
    hub_dir.join(format!(".{id}.remade"))
}

/// Finishes what [`HubDir::remake`] began in the hub in `dir` before a crash: puts a hive made
/// again in place of the store it renamed away, and deletes one it never got as far as.
pub(super) fn finish_remakes(dir: &Path) -> anyhow::Result<()> {
    for entry in fs::read_dir(dir)?.flatten() {
        let name = entry.file_name();
        let Some(id) = name
            .to_str()
            .and_then(|name| name.strip_prefix('.')?.strip_suffix(".remade"))
        else {
            continue;
        };
        let hive_dir = dir.join(id);
        if hive_dir.exists() {
            fs::remove_dir_all(entry.path())?;
        } else {
            fs::rename(entry.path(), hive_dir)?;
        }
    }
    Ok(())
}

/// Now, in seconds since the epoch.
pub(super) fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// What is under `removed/` in a hub.
#[derive(Default)]
pub(super) struct SetAsides {
    pub(super) corrupt: Vec<SetAside>,
    pub(super) removed: BTreeSet<HiveId>,
    pub(super) unemptied: Vec<SetAside>,
}

/// The stores set aside under `removed/` in the hub in `dir`: corrupt ones, `<id>-<time>`
/// with `.corrupt` after it, of hives the hub may still have, and removed hives'.
pub(super) fn set_aside(dir: &Path) -> SetAsides {
    let mut found = SetAsides::default();
    let Ok(entries) = fs::read_dir(dir.join("removed")) else {
        return found;
    };
    for entry in entries.flatten() {
        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };
        let Some((id, stamp, corrupt)) = aside_name(&name) else {
            continue;
        };
        let aside = SetAside {
            id: HiveId::from(id.to_owned()),
            path: entry.path(),
            stamp,
        };
        if corrupt {
            found.corrupt.push(aside);
        } else {
            found.removed.insert(aside.id.clone());
            if fs::read_dir(&aside.path).is_ok_and(|mut entries| entries.next().is_some()) {
                found.unemptied.push(aside);
            }
        }
    }
    found
}

/// Reads the hive id, time and whether the store was set aside as corrupt.
fn aside_name(name: &str) -> Option<(&str, u64, bool)> {
    let (stem, corrupt) = match name.strip_suffix(".corrupt") {
        Some(stem) => (stem, true),
        None => (name, false),
    };
    let (id, stamp) = stem.rsplit_once('-')?;
    Uuid::parse_str(id).ok()?;
    Some((id, stamp.parse().ok()?, corrupt))
}

/// A sweep and an explicit purge can both delete a corrupt store.
fn delete_dir(path: &Path) -> std::io::Result<()> {
    match fs::remove_dir_all(path) {
        Err(err) if err.kind() == std::io::ErrorKind::NotFound && !path.try_exists()? => Ok(()),
        result => result,
    }
}

/// Deletes everything in `dir`, leaving it empty.
fn empty_dir(dir: &Path) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            fs::remove_dir_all(entry.path())?;
        } else {
            fs::remove_file(entry.path())?;
        }
    }
    Ok(())
}

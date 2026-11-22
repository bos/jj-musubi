//! A hive's store over its life on disk, past what joins and pushes do to it: made again
//! when a power cut leaves it corrupt, set aside under `removed/` when the hive is made again
//! or removed, and deleted or emptied a day later. A removed hive's directory stays under
//! `removed/`, emptied, as its tombstone. A hive reset from one of its copies (`musubi resume`)
//! is made again under a new id, and its old store emptied at once, but for what its tombstone
//! needs.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io::BufRead as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;

use jj_lib::object_id::ObjectId as _;
use serde::Deserialize;
use serde::Serialize;
use uuid::Uuid;

use super::HIVE_FILE;
use super::HiveId;
use super::HiveIndex;
use super::HiveInfo;
use super::HiveMeta;
use super::HubDir;
use super::JoinChoice;
use super::JoinRequest;
use super::PAUSED_FILE;
use super::Refusal;
use super::Reset;
use super::ResetOutcome;
use super::names;
use super::no_record;
use super::refusal;
use crate::store;
use crate::store::HubStore;
use crate::store::StoreError;

/// How long a hive's corrupt store, set aside when the hive was made again, stays once the
/// new one has accepted a head, and a removed hive's store stays: long enough for someone
/// curious to look at it.
pub(super) const SET_ASIDE_LIFETIME: Duration = Duration::from_secs(24 * 3600);

/// How a refused reset ends where the hive has work the copy hasn't received, which `musubi
/// resume` gives a hint for.
pub const LACKS_WORK: &str = "that this copy hasn't received";

/// The file in a reset hive's tombstone saying what it was reset to ([`Tombstone`]).
const RESET_FILE: &str = "reset";

/// What a reset hive's tombstone keeps of it: its `hive.toml`, for its name and settings, and
/// this, in its `reset` file.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(super) struct Tombstone {
    /// The hive it was made again as; none if a power cut lost the file that said.
    to: Option<HiveId>,
    by: String,
    key: String,
    at: u64,
    /// The old hive's name, from its `hive.toml`, not in the file.
    #[serde(skip)]
    name: String,
}

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
        // A pause is the hub's to forget, though it's kept where it can be.
        if hive.paused.is_some() {
            fs::hard_link(hive.dir.join(PAUSED_FILE), staging.join(PAUSED_FILE)).ok();
        }
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
                std::thread::spawn(move || match fs::remove_dir_all(&path) {
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

    /// What the hub answers for hive `id`, if `musubi resume` reset it: the new hive's name,
    /// as it is now, and who reset it, and when.
    pub fn reset_of(&self, id: &HiveId) -> Option<Reset> {
        let tombstone = self.reset.get(id)?;
        let name = tombstone
            .to
            .as_ref()
            .and_then(|to| self.hives.get(to))
            .map_or_else(|| tombstone.name.clone(), |hive| hive.meta.name.clone());
        Some(Reset {
            hive: id.clone(),
            name,
            by: tombstone.by.clone(),
            key: tombstone.key.clone(),
            at: tombstone.at,
        })
    }

    /// Makes hive `id` again from the copy `request` comes from alone, as
    /// [`JoinChoice::Reset`] asks: a new hive with its name, settings and index, for the copy
    /// to join; its old store is emptied at once, in the background, leaving a tombstone that
    /// answers [`Self::reset_of`]. Refused unless the hive is paused and, unless forced, its
    /// head is the one the copy last fetched. A copy asking for a hive reset already gets the
    /// reset, unless it is the copy that reset it, asking again after missing the answer,
    /// which joins the new hive, made again if a crash lost it. The caller has stopped
    /// serving hive `id`.
    pub fn reset(&mut self, request: &JoinRequest) -> Result<ResetOutcome, Refusal> {
        let JoinChoice::Reset { id, base, force } = &request.choice else {
            return Err("not a reset".to_owned());
        };
        if let Some(tombstone) = self.reset.get(id).cloned() {
            if tombstone.key != request.machine {
                return Ok(ResetOutcome::Reset(self.reset_of(id).expect("found above")));
            }
            let to = self.finish_reset(id, &tombstone)?;
            let mut joined = self.joined(request, &to, false, "reset".to_owned())?;
            joined.created = true;
            return Ok(ResetOutcome::Joined(joined));
        }
        let removed = self.is_removed(id);
        let hive = self.hives.get(id).ok_or_else(|| no_record(removed))?;
        if hive.paused.is_none() {
            return Err(format!(
                "hive {} isn't paused; `musubi pause` stops it syncing, for you to clean up a \
                 copy and reset the hive from it",
                hive.meta.name
            ));
        }
        let (meta, dir) = (hive.meta.clone(), hive.dir.clone());
        if !force && let Some(lacking) = self.lacking(id, base, &request.machine)? {
            return Err(format!("hive {} has work{lacking} {LACKS_WORK}", meta.name));
        }
        let tombstone = Tombstone {
            to: Some(HiveId::from(Uuid::new_v4())),
            by: musubi_jj::workspaces::machine_name(&request.machine).to_owned(),
            key: request.machine.clone(),
            at: now(),
            name: meta.name.clone(),
        };
        let removed = self.dir.join("removed");
        fs::create_dir_all(&removed).map_err(refusal)?;
        let text = toml::to_string(&tombstone).map_err(refusal)?;
        fs::write(dir.join(RESET_FILE), text).map_err(refusal)?;
        // The hive is reset once its store is renamed: what follows, a crash can leave undone
        // for its copy to finish by asking again.
        let path = removed.join(format!("{id}-{}.reset", tombstone.at));
        fs::rename(&dir, &path).map_err(refusal)?;
        self.hives.remove(id);
        self.reset.insert(id.clone(), tombstone.clone());
        empty_in_background(id.clone(), path);
        // And a store a power cut left corrupt, which it set aside a day ago at most.
        let (corrupt, kept) = std::mem::take(&mut self.corrupt)
            .into_iter()
            .partition(|aside| aside.id == *id);
        self.corrupt = kept;
        for SetAside { path, .. } in corrupt {
            std::thread::spawn(move || {
                if let Err(err) = fs::remove_dir_all(&path) {
                    tracing::warn!("deleting {}: {err}", path.display());
                }
            });
        }
        let to = tombstone.to.clone().expect("made above");
        // Its index fills from what this copy's first push brings, as a new hive's does.
        self.create_with(&to, meta, HiveIndex::default())
            .map_err(refusal)?;
        let mut joined = self.joined(request, &to, false, "reset".to_owned())?;
        joined.created = true;
        Ok(ResetOutcome::Joined(joined))
    }

    /// The hive hive `id`'s tombstone says it was reset to, made again, empty, under the name
    /// its tombstone keeps, if a crash lost it before it was made.
    fn finish_reset(&mut self, id: &HiveId, tombstone: &Tombstone) -> Result<HiveId, Refusal> {
        let lost = || "the hub lost what this hive was reset to; `musubi clone` makes a new copy";
        let to = tombstone.to.clone().ok_or_else(|| lost().to_owned())?;
        if self.hives.contains_key(&to) {
            return Ok(to);
        }
        let path = self
            .reset_path(id)
            .ok_or_else(|| lost().to_owned())?
            .join(HIVE_FILE);
        let mut meta: HiveMeta = fs::read_to_string(&path)
            .ok()
            .and_then(|text| toml::from_str(&text).ok())
            .ok_or_else(|| lost().to_owned())?;
        meta.name = names::choose_name(std::slice::from_ref(&meta.name), |name| {
            self.name_taken(name)
        });
        // Whatever a crash left of making it, which isn't a hive yet.
        let dir = self.dir.join(to.as_str());
        if dir.exists() {
            fs::remove_dir_all(&dir).map_err(refusal)?;
        }
        self.create_with(&to, meta, HiveIndex::default())
            .map_err(refusal)?;
        Ok(to)
    }

    /// Where hive `id`'s reset tombstone is.
    fn reset_path(&self, id: &HiveId) -> Option<PathBuf> {
        let tombstone = self.reset.get(id)?;
        Some(
            self.dir
                .join("removed")
                .join(format!("{id}-{}.reset", tombstone.at)),
        )
    }

    /// The machines whose work hive `id`'s head has and the operation `base`, a hex id, does
    /// not, but for `machine`, as ` from beta and gamma`, or nothing if it can't tell which;
    /// `None` if there are none, as when the head is `base`, or only `machine`'s own work is
    /// past it, as after the reply to its last push was lost.
    fn lacking(
        &mut self,
        id: &HiveId,
        base: &str,
        machine: &str,
    ) -> Result<Option<String>, Refusal> {
        let store = self.open_store(id).map_err(refusal)?;
        let head = store.head().1.clone();
        if head.hex() == base {
            return Ok(None);
        }
        let base = jj_lib::op_store::OperationId::try_from_hex(base)
            .filter(|base| store.is_accepted(base));
        let Some(base) = base else {
            return Ok(Some(String::new()));
        };
        let mut names = BTreeSet::new();
        for op in store.ops_since(&head, &base).map_err(refusal)? {
            let op = store
                .canonical()
                .read_operation(&musubi_jj::op_id::CanonicalOp(op))
                .map_err(refusal)?;
            if let Some(key) = musubi_jj::presence::Kind::of(&op.metadata)
                .work
                .filter(|key| key != machine)
            {
                names.insert(musubi_jj::workspaces::machine_name(&key).to_owned());
            }
        }
        let names: Vec<String> = names.into_iter().collect();
        Ok(match names.as_slice() {
            [] => None,
            [one] => Some(format!(" from {one}")),
            [init @ .., last] => Some(format!(" from {} and {last}", init.join(", "))),
        })
    }

    /// Takes a hive out of the hub, keeping its store under `removed/`. The caller has
    /// stopped serving it.
    pub fn remove(&mut self, id: &HiveId) -> Result<HiveInfo, Refusal> {
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
            path,
            stamp,
        });
        Ok(info)
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
    pub(super) reset: BTreeMap<HiveId, Tombstone>,
}

/// The stores set aside under `removed/` in the hub in `dir`: corrupt ones, `<id>-<time>`
/// with `.corrupt` after it, of hives the hub may still have, removed hives', and reset
/// hives', with `.reset` after it, whose stores are emptied now if a crash left them whole.
pub(super) fn set_aside(dir: &Path) -> SetAsides {
    let mut found = SetAsides::default();
    let Ok(entries) = fs::read_dir(dir.join("removed")) else {
        return found;
    };
    for entry in entries.flatten() {
        let Ok(name) = entry.file_name().into_string() else {
            continue;
        };
        let (stem, kind) = if let Some(stem) = name.strip_suffix(".corrupt") {
            (stem, Kind::Corrupt)
        } else if let Some(stem) = name.strip_suffix(".reset") {
            (stem, Kind::Reset)
        } else {
            (name.as_str(), Kind::Removed)
        };
        let Some((id, stamp)) = stem.rsplit_once('-') else {
            continue;
        };
        let (Ok(stamp), Ok(_)) = (stamp.parse(), Uuid::parse_str(id)) else {
            continue;
        };
        let aside = SetAside {
            id: HiveId::from(id.to_owned()),
            path: entry.path(),
            stamp,
        };
        if kind == Kind::Reset {
            found.reset.insert(aside.id.clone(), read_tombstone(&aside));
            if fs::read_dir(&aside.path).is_ok_and(|entries| {
                entries
                    .flatten()
                    .any(|entry| !KEPT.iter().any(|kept| entry.file_name() == *kept))
            }) {
                empty_in_background(aside.id, aside.path);
            }
        } else if kind == Kind::Corrupt {
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

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Corrupt,
    Removed,
    Reset,
}

/// What a reset hive's tombstone keeps: its settings and what it was reset to.
const KEPT: [&str; 2] = [HIVE_FILE, RESET_FILE];

/// What reset hive `aside`'s tombstone says, as far as a power cut left it.
fn read_tombstone(aside: &SetAside) -> Tombstone {
    let read = |file| fs::read_to_string(aside.path.join(file)).ok();
    let mut tombstone = read(RESET_FILE)
        .and_then(|text| toml::from_str(&text).ok())
        .unwrap_or_else(|| Tombstone {
            to: None,
            by: "another machine".to_owned(),
            key: String::new(),
            at: aside.stamp,
            name: String::new(),
        });
    tombstone.name = read(HIVE_FILE)
        .and_then(|text| toml::from_str::<HiveMeta>(&text).ok())
        .map_or_else(|| aside.id.to_string(), |meta| meta.name);
    tombstone
}

/// Empties reset hive `id`'s old store, at `path`, but for what its tombstone keeps, in the
/// background: a store can be large, and the caller holds the hub.
fn empty_in_background(id: HiveId, path: PathBuf) {
    std::thread::spawn(move || match empty_dir_except(&path, &KEPT) {
        Ok(()) => tracing::info!("deleted reset hive {id}'s old store"),
        Err(err) => tracing::warn!("deleting {}: {err}", path.display()),
    });
}

/// Deletes everything in `dir`, leaving it empty.
fn empty_dir(dir: &Path) -> std::io::Result<()> {
    empty_dir_except(dir, &[])
}

/// Deletes everything in `dir` but the files named `kept`.
fn empty_dir_except(dir: &Path, kept: &[&str]) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        if kept.iter().any(|kept| entry.file_name() == *kept) {
            continue;
        }
        if entry.file_type()?.is_dir() {
            fs::remove_dir_all(entry.path())?;
        } else {
            fs::remove_file(entry.path())?;
        }
    }
    Ok(())
}

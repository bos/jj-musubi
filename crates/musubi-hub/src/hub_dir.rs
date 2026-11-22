//! A hub's directory: one subdirectory per hive, named by the hive's id, each holding a hub
//! store (see [`crate::store`]), the hive's `hive.toml` (its name and backend), and its
//! index (see [`crate::index`]), and while it is paused, its `paused` file. Removed and reset
//! hives move to `removed/`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;
use std::time::Instant;

use jj_lib::backend::CommitId;
use musubi_jj::files;
use musubi_jj::objects::Backend;
use musubi_jj::remote_url::RemoteBinding;
use musubi_jj::workspaces;
use serde::Deserialize;
use serde::Serialize;
use uuid::Uuid;

use crate::index::HiveIndex;
use crate::matching;
use crate::matching::Candidate;
use crate::matching::Decision;
use crate::matching::Joiner;
use crate::names;
use crate::names::RemoteUrl;
use crate::store;
use crate::store::HubStore;

mod bindings;
mod lifecycle;

pub use lifecycle::LACKS_WORK;
pub use lifecycle::Opened;
use lifecycle::SetAside;
use lifecycle::SetAsides;
use lifecycle::Tombstone;
use lifecycle::finish_remakes;
pub use lifecycle::open_whole;
use lifecycle::set_aside;

const HIVE_FILE: &str = "hive.toml";
/// Who paused a hive, and when ([`Pause`]), while it is paused.
const PAUSED_FILE: &str = "paused";

/// A hive's internal identity, distinct from a human-supplied name or prefix: a UUID in its
/// usual form, as the hub makes them, though one a repository asks for may be anything.
/// Encoded as the bare string, wherever it is serialized, and shown as one in debug output,
/// as messages that print a reply with `{:?}` showed it when it was a `String`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct HiveId(String);

impl HiveId {
    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn into_string(self) -> String {
        self.0
    }
}

impl From<String> for HiveId {
    fn from(id: String) -> Self {
        Self(id)
    }
}

impl From<Uuid> for HiveId {
    fn from(id: Uuid) -> Self {
        Self(id.hyphenated().to_string())
    }
}

impl std::fmt::Debug for HiveId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl std::fmt::Display for HiveId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

/// A hive's `hive.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct HiveMeta {
    name: String,
    backend: Backend,
    remote_bindings: BTreeMap<String, RemoteBinding>,
    clone_config: BTreeMap<String, String>,
}

/// Which hive a joining repository asks for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum JoinChoice {
    /// The one that matches it (`musubi join`).
    Match,
    /// This one, by name, name prefix, or id.
    Hive(String),
    /// A new one (`musubi create`), with this name if given, else one from the repository's
    /// remote or directory.
    Create(Option<String>),
    /// The one with this id, which the joining repository was part of (`musubi join` in a
    /// repository whose hive the hub lacks): the hive made again, empty, under its id, unless
    /// it was removed. Under this name, if no hive has it, as `Create` with the name would
    /// make it; otherwise as `Create` without one would, refused if the repository belongs in
    /// another hive here. A hive with this id that the hub has is joined.
    Remake { id: HiveId, name: Option<String> },
    /// The hive with this id made again from the joining repository alone, under a new id,
    /// with its name and settings (`musubi resume`): it must be paused, and unless `force`,
    /// its head must be `base`, the hex id of the operation the repository last fetched, so
    /// that the repository has all its work. The old hive's store goes at once, and its id
    /// answers [`Reset`] from then on.
    Reset {
        id: HiveId,
        base: String,
        force: bool,
    },
}

/// What a joining repository tells the hub.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinRequest {
    pub choice: JoinChoice,
    pub backend: Backend,
    /// Defaults recorded only when creating a hive, for filling missing clone config.
    pub clone_config: BTreeMap<String, String>,
    /// Names and URLs of its remotes: a remote's name once for each of its URLs, as git
    /// expands it and as written.
    pub remotes: Vec<(String, String)>,
    /// Effective fetch and push identities, checked independently of discovery hints.
    pub remote_bindings: BTreeMap<String, RemoteBinding>,
    /// The name of the repository's directory, to name a hive after when it has no
    /// remotes.
    pub dir_name: String,
    /// Hex ids of its commits whose parent is the root commit.
    pub roots: Vec<String>,
    /// Hex ids of the commits its remote bookmarks point to.
    pub remote_targets: Vec<String>,
    /// The joining machine's key.
    pub machine: String,
    /// The ids of the hives whose history the repository carries, as its join operations
    /// name them: a join is refused if any was reset since ([`HubDir::reset_among`]), since
    /// it would bring back the history the reset removed.
    pub carried: Vec<String>,
}

/// A hive, as `musubi list` shows it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveInfo {
    pub id: HiveId,
    pub name: String,
    pub backend: Backend,
    /// One-time defaults from the copy that created the hive, as TOML values.
    pub clone_config: BTreeMap<String, String>,
    pub urls: Vec<String>,
    /// Names of the machines with workspaces in the hive.
    pub machines: Vec<String>,
    /// Who paused the hive, and when, while it is paused.
    pub paused: Option<Pause>,
}

/// A hive paused by `musubi pause`: while it is, the hub answers its requests with this, so
/// that nothing syncs, until `musubi pause --cancel`. Kept in the hive's `paused` file, which
/// isn't synced to disk: a hub that loses it is simply not paused, and nothing changed while
/// it was.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Pause {
    /// The name of the machine that paused it, as its copy's record has it.
    pub by: String,
    /// When, by the hub's clock, in seconds since the epoch.
    pub at: u64,
}

/// A hive made again from one of its copies (`musubi resume`), as the hub answers for its old
/// id from then on: so that the other copies, which have the history the reset removed, stop
/// syncing, and never bring that history back.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Reset {
    /// The id of the hive that was reset, which the hub answers this for.
    pub hive: HiveId,
    /// The new hive's name, as the hub has it now.
    pub name: String,
    /// The name of the machine whose copy the hive was made again from.
    pub by: String,
    /// That copy's machine key, which tells it that the reset is its own.
    pub key: String,
    /// When, by the hub's clock, in seconds since the epoch.
    pub at: u64,
}

/// What a [`JoinChoice::Reset`] comes to.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResetOutcome {
    /// The hive made again, for the copy that asked to join, or for the copy that made it
    /// asking again, after it missed the answer.
    Joined(Joined),
    /// Another copy reset the hive already.
    Reset(Reset),
}

/// Why a join was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JoinRefused {
    /// For the user, as a message.
    Refused(Refusal),
    /// A hive it would bring the old history of was reset: for the hub to answer as for a reset.
    Reset(Reset),
}

/// The outcome of a join.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Joined {
    pub hive: HiveInfo,
    pub created: bool,
    /// Why this hive, for telling the user: `matched remote origin`, say.
    pub reason: String,
    /// The keys of the copies present at the hive's head, and of those joining it: a copy
    /// whose history came from another hive forgets the others it knows
    /// (docs/internals/copies.md, R8).
    pub present: Vec<String>,
}

/// How long the hub counts what a joining repository brings as the hive's before the
/// repository has pushed it: long enough for its first sync to start.
const PENDING_LIFETIME: Duration = Duration::from_secs(120);

struct Hive {
    dir: PathBuf,
    meta: HiveMeta,
    index: HiveIndex,
    /// Whether `index` holds what its file doesn't, because saving it failed: the next push
    /// saves it again, though it brings nothing new.
    unsaved: bool,
    /// Joins whose first push the hive hasn't accepted yet.
    pending: Vec<Pending>,
    paused: Option<Pause>,
}

/// What a joining repository said it brings, so that another copy of it joining meanwhile
/// finds the same hive. It is forgotten once the joining machine's first push is accepted,
/// which puts what it really brought in the index, or after a while if it never comes.
struct Pending {
    machine: String,
    urls: Vec<String>,
    roots: BTreeSet<String>,
    until: Instant,
}

pub struct HubDir {
    dir: PathBuf,
    hives: BTreeMap<HiveId, Hive>,
    pending_lifetime: Duration,
    /// Corrupt stores set aside under `removed/` and not deleted yet (see
    /// [`Self::sweep`]).
    corrupt: Vec<SetAside>,
    /// The ids of hives `musubi hub remove` removed: each has a directory under `removed/`,
    /// kept for good, empty once a day has passed, as a tombstone.
    removed: BTreeSet<HiveId>,
    /// The removed hives' stores not emptied yet.
    unemptied: Vec<SetAside>,
    /// The ids of hives `musubi resume` made again under new ids: each has a directory under
    /// `removed/`, kept for good, holding only what [`Tombstone`] needs.
    reset: BTreeMap<HiveId, Tombstone>,
}

/// Errors that are the requester's to fix, worded for them.
pub type Refusal = String;

fn refusal(err: impl std::fmt::Display) -> Refusal {
    format!("{err:#}")
}

impl HubDir {
    /// Opens the hub directory `dir`, which must exist, rebuilding any missing index.
    pub fn open(dir: &Path) -> anyhow::Result<Self> {
        finish_remakes(dir)?;
        let mut hives = BTreeMap::new();
        let mut unindexed = vec![];
        for entry in fs::read_dir(dir)? {
            let entry = entry?;
            let Some(id) = entry
                .file_name()
                .to_str()
                .filter(|name| Uuid::parse_str(name).is_ok())
                .map(|name| HiveId::from(name.to_owned()))
            else {
                continue;
            };
            let hive_dir = entry.path();
            let meta_path = hive_dir.join(HIVE_FILE);
            let Ok(text) = fs::read_to_string(&meta_path) else {
                continue;
            };
            let meta: HiveMeta = toml::from_str(&text)
                .map_err(|err| anyhow::anyhow!("{}: {err}", meta_path.display()))?;
            let index = HiveIndex::load(&hive_dir).unwrap_or_else(|| {
                unindexed.push(id.clone());
                HiveIndex::default()
            });
            // One that won't parse, as a power cut can leave it, is no pause.
            let paused = fs::read_to_string(hive_dir.join(PAUSED_FILE))
                .ok()
                .and_then(|text| toml::from_str(&text).ok());
            hives.insert(
                id,
                Hive {
                    dir: hive_dir,
                    meta,
                    index,
                    unsaved: false,
                    pending: vec![],
                    paused,
                },
            );
        }
        let SetAsides {
            corrupt,
            removed,
            unemptied,
            reset,
        } = set_aside(dir);
        let mut hubs = Self {
            dir: dir.to_owned(),
            hives,
            pending_lifetime: PENDING_LIFETIME,
            corrupt,
            removed,
            unemptied,
            reset,
        };
        for id in unindexed {
            let index = HiveIndex::rebuild(&hubs.open_store(&id)?)?;
            let hive = hubs.hives.get_mut(&id).expect("listed above");
            index.save(&hive.dir)?;
            hive.index = index;
        }
        hubs.sweep();
        Ok(hubs)
    }

    /// Opens hive `id`'s store, making the hive again first if a power cut left it corrupt
    /// ([`open_whole`]).
    pub fn open_store(&mut self, id: &HiveId) -> anyhow::Result<HubStore> {
        let dir = self.hive(id)?.dir.clone();
        match open_whole(&dir)? {
            Opened::Whole(store) => Ok(*store),
            Opened::Damaged(why) => {
                self.remake(id, &why)?;
                Ok(HubStore::open(&dir)?)
            }
        }
    }

    fn hive(&self, id: &HiveId) -> anyhow::Result<&Hive> {
        self.hives
            .get(id)
            .ok_or_else(|| anyhow::anyhow!("no hive {id}"))
    }

    /// How long a join counts for matching before its first push, for tests.
    #[cfg(test)]
    fn with_pending_lifetime(mut self, lifetime: Duration) -> Self {
        self.pending_lifetime = lifetime;
        self
    }

    pub fn len(&self) -> usize {
        self.hives.len()
    }

    pub fn is_empty(&self) -> bool {
        self.hives.is_empty()
    }

    /// The store directory of the hive with this id.
    pub fn hive_dir(&self, id: &HiveId) -> Option<&Path> {
        self.hives.get(id).map(|hive| hive.dir.as_path())
    }

    /// Creates an empty hive.
    pub fn create(&mut self, name: &str, backend: Backend) -> anyhow::Result<HiveId> {
        self.check_new_name(name).map_err(anyhow::Error::msg)?;
        let id = HiveId::from(Uuid::new_v4());
        self.create_as(&id, name, backend)?;
        Ok(id)
    }

    /// Creates an empty hive with id `id`, a UUID in its usual form, and `name`, which must be
    /// valid.
    fn create_as(&mut self, id: &HiveId, name: &str, backend: Backend) -> anyhow::Result<()> {
        let meta = HiveMeta {
            name: name.to_owned(),
            backend,
            remote_bindings: BTreeMap::new(),
            clone_config: BTreeMap::new(),
        };
        self.create_with(id, meta, HiveIndex::default())
    }

    /// Creates an empty hive with id `id`, a UUID in its usual form, and `meta`, whose name
    /// must be valid, and with `index` for joins to match it by.
    fn create_with(&mut self, id: &HiveId, meta: HiveMeta, index: HiveIndex) -> anyhow::Result<()> {
        names::check_name(&meta.name).map_err(anyhow::Error::msg)?;
        let dir = self.dir.join(id.as_str());
        HubStore::init(&dir, meta.backend)?;
        write_meta(&dir, &meta)?;
        index.save(&dir)?;
        self.hives.insert(
            id.clone(),
            Hive {
                dir,
                meta,
                index,
                unsaved: false,
                pending: vec![],
                paused: None,
            },
        );
        Ok(())
    }

    fn name_taken(&self, name: &str) -> bool {
        self.hives.values().any(|hive| hive.meta.name == name)
    }

    /// Whether `name` will do for a hive about to be given it: valid, and no hive's yet.
    fn check_new_name(&self, name: &str) -> Result<(), Refusal> {
        names::check_name(name)?;
        if self.name_taken(name) {
            return Err(format!("there is already a hive named {name}"));
        }
        Ok(())
    }

    /// The id of the hive `name` names: its name, its id, or a prefix of exactly one
    /// hive's name (or else id).
    pub fn resolve(&self, name: &str) -> Result<HiveId, Refusal> {
        // A prefix of every name.
        names::check_name_given(name)?;
        if let Some(id) = self.exact_id(name) {
            return Ok(id);
        }
        let by_name = |hive: &Hive, _: &str| hive.meta.name.starts_with(name);
        let by_id = |_: &Hive, id: &str| id.starts_with(name);
        for matches in [&by_name as &dyn Fn(&Hive, &str) -> bool, &by_id] {
            let found: Vec<(&HiveId, &Hive)> = self
                .hives
                .iter()
                .filter(|(id, hive)| matches(hive, id.as_str()))
                .collect();
            match found.as_slice() {
                [] => {}
                [(id, _)] => return Ok((*id).clone()),
                several => {
                    let mut names: Vec<&str> =
                        several.iter().map(|(_, h)| h.meta.name.as_str()).collect();
                    names.sort_unstable();
                    return Err(format!("{name} could be any of {}", names.join(", ")));
                }
            }
        }
        Err(format!("this hub has no hive named {name}"))
    }

    /// The id of the hive whose name or id is exactly `name`, for removing it, which a
    /// prefix is too easily mistaken for.
    pub fn resolve_exact(&self, name: &str) -> Result<HiveId, Refusal> {
        names::check_name_given(name)?;
        self.exact_id(name)
            .ok_or_else(|| format!("this hub has no hive named {name}"))
    }

    /// Exact names take precedence over ids, in both kinds of lookup.
    fn exact_id(&self, name: &str) -> Option<HiveId> {
        if let Some((id, _)) = self.hives.iter().find(|(_, h)| h.meta.name == name) {
            return Some(id.clone());
        }
        let id = HiveId::from(name.to_owned());
        self.hives.contains_key(&id).then_some(id)
    }

    pub fn info(&self, id: &HiveId) -> Option<HiveInfo> {
        let hive = self.hives.get(id)?;
        Some(HiveInfo {
            id: id.clone(),
            name: hive.meta.name.clone(),
            backend: hive.meta.backend,
            clone_config: hive.meta.clone_config.clone(),
            urls: hive.index.urls.iter().cloned().collect(),
            machines: display_names(&hive.index.machines),
            paused: hive.paused.clone(),
        })
    }

    /// Who paused hive `id`, and when, if it is paused.
    pub fn paused(&self, id: &HiveId) -> Option<&Pause> {
        self.hives.get(id)?.paused.as_ref()
    }

    /// Pauses hive `id` for machine `by`, unless it is paused already. Returns the hive as it
    /// is now, and how it was paused before, if it was.
    pub fn pause(&mut self, id: &HiveId, by: &str) -> Result<(HiveInfo, Option<Pause>), Refusal> {
        let removed = self.is_removed(id);
        let hive = self.hives.get_mut(id).ok_or_else(|| no_record(removed))?;
        let before = hive.paused.clone();
        if before.is_none() {
            let pause = Pause {
                by: by.to_owned(),
                at: lifecycle::now(),
            };
            let text = toml::to_string(&pause).map_err(refusal)?;
            files::replace(&hive.dir.join(PAUSED_FILE), text.as_bytes()).map_err(refusal)?;
            hive.paused = Some(pause);
        }
        Ok((self.info(id).expect("found above"), before))
    }

    /// Lifts hive `id`'s pause, if it is paused. Returns the hive as it is now, and how it was
    /// paused, if it was.
    pub fn unpause(&mut self, id: &HiveId) -> Result<(HiveInfo, Option<Pause>), Refusal> {
        let removed = self.is_removed(id);
        let hive = self.hives.get_mut(id).ok_or_else(|| no_record(removed))?;
        if hive.paused.is_some() {
            match fs::remove_file(hive.dir.join(PAUSED_FILE)) {
                Err(err) if err.kind() != std::io::ErrorKind::NotFound => {
                    return Err(refusal(err));
                }
                _ => {}
            }
        }
        let before = hive.paused.take();
        Ok((self.info(id).expect("found above"), before))
    }

    /// The keys of the machines with workspaces in hive `id`'s head.
    pub fn machine_keys(&self, id: &HiveId) -> Option<&BTreeSet<String>> {
        Some(&self.hives.get(id)?.index.machines)
    }

    pub fn list(&self) -> Vec<HiveInfo> {
        let mut hives: Vec<HiveInfo> = self.hives.keys().filter_map(|id| self.info(id)).collect();
        hives.sort_by(|a, b| a.name.cmp(&b.name));
        hives
    }

    /// Renames the hive `name` names, as [`Self::resolve`] finds it, `to`. Returns the name it
    /// had, and the hive as it is now.
    pub fn rename(&mut self, name: &str, to: &str) -> Result<(String, HiveInfo), Refusal> {
        let id = self.resolve(name)?;
        let from = self.hives[&id].meta.name.clone();
        if from != to {
            self.check_new_name(to)?;
            let hive = self.hives.get_mut(&id).expect("resolved");
            let mut meta = hive.meta.clone();
            meta.name = to.to_owned();
            write_meta(&hive.dir, &meta).map_err(refusal)?;
            hive.meta = meta;
        }
        Ok((from, self.info(&id).expect("resolved")))
    }

    /// Adds what newly accepted operations brought to a hive's index, and forgets the
    /// pending joins of machines that are now in it.
    pub fn update_index(&mut self, id: &HiveId, index: HiveIndex) -> anyhow::Result<()> {
        let Some(hive) = self.hives.get_mut(id) else {
            return Ok(());
        };
        hive.pending
            .retain(|pending| !index.machines.contains(&pending.machine));
        let mut changed = hive.unsaved || hive.index.machines != index.machines;
        for url in index.urls {
            changed |= hive.index.urls.insert(url);
        }
        for (name, bindings) in index.remote_bindings {
            let known = hive.index.remote_bindings.entry(name).or_default();
            for binding in bindings {
                changed |= known.insert(binding);
            }
        }
        for root in index.roots {
            changed |= hive.index.roots.insert(root);
        }
        hive.index.machines = index.machines;
        // Most heads bring nothing new. Saving anyway would replace the index at every push,
        // and ext4 writes out a file that replaces another at once.
        if changed {
            hive.unsaved = true;
            hive.index.save(&hive.dir)?;
            hive.unsaved = false;
        }
        self.sweep();
        Ok(())
    }

    /// Whether hive `hive` shares a root with the joining repository, or will once its
    /// pending joins push.
    fn shares_root(hive: &Hive, request: &JoinRequest) -> bool {
        let pending_roots = hive.pending.iter().flat_map(|pending| &pending.roots);
        hive.meta.backend == request.backend
            && hive
                .index
                .roots
                .iter()
                .chain(pending_roots)
                .any(|root| request.roots.contains(root))
    }

    /// The stores to look in for what `request`'s remotes point at: those of the hives
    /// [`Self::join_probed`] can't otherwise tell are related. Looking opens each store, so it is
    /// done with [`Probe::run`], without the hub.
    pub fn probe(&self, request: &JoinRequest) -> Probe {
        let targets: Vec<CommitId> = request
            .remote_targets
            .iter()
            .filter_map(CommitId::try_from_hex)
            .collect();
        let hives = if targets.is_empty() {
            vec![]
        } else {
            // By the index's roots alone: a pending join's may lapse before
            // [`Self::join_probed`], leaving the hive unprobed.
            self.hives
                .iter()
                .filter(|(_, hive)| {
                    hive.meta.backend == request.backend
                        && !hive
                            .index
                            .roots
                            .iter()
                            .any(|root| request.roots.contains(root))
                })
                .map(|(id, hive)| (id.clone(), hive.dir.clone()))
                .collect()
        };
        Probe {
            backend: request.backend,
            targets,
            hives,
        }
    }

    /// Every hive, as a candidate for `request` to join: whether it shares history with the
    /// joining repository, or will once its pending joins push, and the repositories its
    /// remotes name. A hive `probed` lacks, as one made since, has none of the remotes'
    /// commits.
    fn candidates(
        &self,
        request: &JoinRequest,
        probed: &Probed,
    ) -> Result<Vec<Candidate>, Refusal> {
        let mut candidates = vec![];
        for (id, hive) in &self.hives {
            let related = Self::shares_root(hive, request)
                || match probed.0.get(id) {
                    Some(Ok(found)) => *found,
                    Some(Err(err)) => return Err(err.clone()),
                    None => false,
                };
            let pending_urls = hive.pending.iter().flat_map(|pending| &pending.urls);
            candidates.push(Candidate {
                id: id.clone(),
                name: hive.meta.name.clone(),
                related,
                url_keys: hive
                    .index
                    .urls
                    .iter()
                    .chain(pending_urls)
                    .filter_map(|url| RemoteUrl::parse(url))
                    .map(|url| url.key())
                    .collect(),
            });
        }
        Ok(candidates)
    }

    /// A hive reset since (`musubi resume`) that `request` would bring the old history of
    /// into whichever hive it joins: one its history carries, or the one it asks to make
    /// again, unless [`Self::finishing_reset`]. A reset is for [`Self::reset`] to answer.
    pub fn reset_among(&self, request: &JoinRequest) -> Option<Reset> {
        let remake = match &request.choice {
            JoinChoice::Reset { .. } => return None,
            JoinChoice::Remake { .. } if self.finishing_reset(request) => None,
            JoinChoice::Remake { id, .. } => Some(id.clone()),
            _ => None,
        };
        request
            .carried
            .iter()
            .map(|id| HiveId::from(id.clone()))
            .chain(remake)
            .find_map(|id| self.reset_of(&id))
    }

    /// Whether `request` asks to make again a hive the joining copy reset itself, from a
    /// repository whose history no longer carries it: a copy that a crash stopped partway
    /// through `musubi resume`, after it had forgotten the old hive, which a remake (`musubi
    /// join --original`) joins to the new hive, as [`Self::reset`] would.
    pub fn finishing_reset(&self, request: &JoinRequest) -> bool {
        let JoinChoice::Remake { id, .. } = &request.choice else {
            return false;
        };
        self.reset_of(id)
            .is_some_and(|reset| reset.key == request.machine)
            && !request.carried.iter().any(|hive| hive == id.as_str())
    }

    /// Decides which hive a repository joins, or creates one if asked to, or makes one
    /// again ([`JoinChoice::Remake`]). See [`crate::matching`].
    #[cfg(test)]
    fn join(&mut self, request: &JoinRequest) -> Result<Joined, Refusal> {
        let probed = self.probe(request).run();
        self.join_probed(request, &probed)
            .map_err(|refused| match refused {
                JoinRefused::Refused(message) => message,
                JoinRefused::Reset(reset) => format!("hive {} was reset", reset.name),
            })
    }

    /// Decides which hive a repository joins, as the test-only `join` does, with what
    /// [`Self::probe`] found in the hives' stores. It looks for a reset again
    /// ([`Self::reset_among`]), since one can land between the caller's look and the lock this
    /// runs under, after the probe.
    pub fn join_probed(
        &mut self,
        request: &JoinRequest,
        probed: &Probed,
    ) -> Result<Joined, JoinRefused> {
        if let Some(reset) = self.reset_among(request) {
            return Err(JoinRefused::Reset(reset));
        }
        self.join_decided(request, probed)
            .map_err(JoinRefused::Refused)
    }

    fn join_decided(&mut self, request: &JoinRequest, probed: &Probed) -> Result<Joined, Refusal> {
        if let Some((name, _)) = request.remotes.iter().find(|(name, _)| {
            request
                .remote_bindings
                .get(name)
                .is_none_or(|binding| binding.fetch.is_none())
        }) {
            return Err(format!(
                "the join request omitted the fetch destination for remote {name}"
            ));
        }
        let backend = request.backend;
        let now = Instant::now();
        for hive in self.hives.values_mut() {
            hive.pending.retain(|pending| pending.until > now);
        }
        let intent = self.intent(&request.choice)?;
        let decision = self.decide(request, probed, &intent)?;
        let (id, created, reason) = match (intent, decision) {
            // A lost hive is made again, unless it has no name of its own here and the
            // repository belongs in a hive the hub has: one made again by hand meanwhile, say.
            (Intent::Remake { .. }, Decision::Join { id, reason }) => {
                let name = &self.hives[&id].meta.name;
                return Err(format!(
                    "the hub lacks this repository's hive, but it belongs in hive {name} \
                     ({reason}): `musubi leave --force`, then `musubi join`, joins that"
                ));
            }
            (Intent::Remake { .. }, Decision::Ambiguous(_)) => {
                return Err(
                    "the hub lacks this repository's hive, but it belongs in several \
                            the hub has: `musubi leave --force`, then `musubi join --hive <name>`, \
                            joins one (`musubi list` shows them)"
                        .to_owned(),
                );
            }
            (Intent::Remake { .. }, Decision::Refuse(message)) if request.roots.is_empty() => {
                return Err(message);
            }
            (Intent::Remake { id, name, .. }, Decision::Refuse(_) | Decision::Create) => {
                // A name an earlier release gave it may not be valid now.
                let former = name.filter(|name| names::check_name(name).is_ok());
                let mut names: Vec<String> = former.into_iter().cloned().collect();
                names.extend(names::name_candidates(&request.remotes, &request.dir_name));
                let name = names::choose_name(&names, |name| self.name_taken(name));
                self.create_as(id, &name, backend).map_err(refusal)?;
                (id.clone(), true, "made again".to_owned())
            }
            (_, Decision::Refuse(message) | Decision::Ambiguous(message)) => return Err(message),
            (_, Decision::Join { id, reason }) => (id, false, reason),
            (Intent::Create(Some(name)), Decision::Create) => {
                let id = self.create(name, backend).map_err(refusal)?;
                (id, true, "new".to_owned())
            }
            (_, Decision::Create) => {
                let name = names::choose_name(
                    &names::name_candidates(&request.remotes, &request.dir_name),
                    |name| self.name_taken(name),
                );
                let id = self.create(&name, backend).map_err(refusal)?;
                (id, true, "new".to_owned())
            }
        };
        self.joined(request, &id, created, reason)
    }

    /// What `choice` comes to among the hives here, or why it is refused.
    fn intent<'a>(&self, choice: &'a JoinChoice) -> Result<Intent<'a>, Refusal> {
        Ok(match choice {
            JoinChoice::Match => Intent::Match,
            JoinChoice::Hive(name) => Intent::Hive(self.resolve(name)?),
            JoinChoice::Create(name) => {
                if let Some(name) = name {
                    self.check_new_name(name)?;
                }
                Intent::Create(name.as_ref())
            }
            // `HubDir::reset`'s, not a join's.
            JoinChoice::Reset { .. } => return Err("a reset isn't a join".to_owned()),
            JoinChoice::Remake { id, name } => {
                if self.hives.contains_key(id) {
                    return Ok(Intent::Rejoin(id));
                }
                if let Some(reset) = self.reset_of(id) {
                    return Err(format!(
                        "this repository's hive was reset to remove history this repository \
                         has; `musubi clone {} <dir>` makes a new copy",
                        reset.name
                    ));
                }
                if self.is_removed(id) {
                    return Err(
                        "this repository's hive was removed from this hub; `musubi leave`, \
                                then `musubi create`, starts a new one"
                            .to_owned(),
                    );
                }
                // Only an id in the form the hub makes them names a directory here.
                if Uuid::parse_str(id.as_str()).map(HiveId::from).as_ref() != Ok(id) {
                    return Err(format!("{id:?} is not a hive id"));
                }
                // A hive made again under a name no hive here has is made as `musubi create
                // <name>` would make it, though the repository matches another: as the one it
                // was made beside on purpose, say. Under another name, it is made as an
                // unnamed create would be, and refused if it belongs in a hive here, as one
                // made by hand meanwhile.
                let named = name
                    .as_ref()
                    .is_some_and(|name| names::check_name(name).is_ok() && !self.name_taken(name));
                Intent::Remake {
                    id,
                    name: name.as_ref(),
                    named,
                }
            }
        })
    }

    /// Which hive `request`, asking for `intent`, joins, as [`matching::decide`] decides.
    fn decide(
        &self,
        request: &JoinRequest,
        probed: &Probed,
        intent: &Intent<'_>,
    ) -> Result<Decision, Refusal> {
        let (chosen, create, named) = match intent {
            // Joined as before, without looking for another hive.
            Intent::Rejoin(id) => {
                return Ok(Decision::Join {
                    id: (*id).clone(),
                    reason: "as before".to_owned(),
                });
            }
            Intent::Match => (None, false, false),
            Intent::Hive(id) => (Some(id.clone()), false, false),
            Intent::Create(name) => (None, true, name.is_some()),
            Intent::Remake { named, .. } => (None, *named, *named),
        };
        let candidates = self.candidates(request, probed)?;
        let joiner = Joiner {
            has_commits: !request.roots.is_empty(),
            chosen,
            create,
            named,
            remotes: request
                .remotes
                .iter()
                .filter_map(|(name, url)| Some((name.clone(), RemoteUrl::parse(url)?.key())))
                .collect(),
        };
        let decision = matching::decide(&joiner, &candidates);
        // A copy with the other hash shares no commit with the hive it belongs in, so nothing
        // matches it: say why, rather than that nothing shares its history.
        if let Decision::Refuse(_) = decision
            && joiner.has_commits
            && !matches!(intent, Intent::Remake { .. })
            && candidates.iter().all(|candidate| !candidate.related)
            && let Some(refusal) = self.other_backend(request, &joiner, &candidates)
        {
            return Ok(Decision::Refuse(refusal));
        }
        Ok(decision)
    }

    /// Why `request` can't join the hive it asked for, or the one its remotes name, if that
    /// hive has another backend.
    fn other_backend(
        &self,
        request: &JoinRequest,
        joiner: &Joiner,
        candidates: &[Candidate],
    ) -> Option<Refusal> {
        candidates
            .iter()
            .filter(|candidate| match &joiner.chosen {
                Some(id) => *id == candidate.id,
                None => joiner
                    .remotes
                    .iter()
                    .any(|(_, key)| candidate.url_keys.contains(key)),
            })
            .find_map(|candidate| backend_refusal(request, &self.hives[&candidate.id].meta))
    }

    /// Records that `request` joins hive `id`, which counts what it brings as the hive's
    /// until it pushes, and says so.
    fn joined(
        &mut self,
        request: &JoinRequest,
        id: &HiveId,
        created: bool,
        reason: String,
    ) -> Result<Joined, Refusal> {
        self.check_unpaused(id)?;
        if let Some(refusal) = backend_refusal(request, &self.hives[id].meta) {
            return Err(refusal);
        }
        self.reserve_remote_bindings(
            id,
            &request.remote_bindings,
            created.then_some(&request.clone_config),
        )?;
        let now = Instant::now();
        let hive = self.hives.get_mut(id).expect("chosen or created");
        hive.pending.push(Pending {
            machine: request.machine.clone(),
            urls: request.remotes.iter().map(|(_, url)| url.clone()).collect(),
            roots: request.roots.iter().cloned().collect(),
            until: now + self.pending_lifetime,
        });
        let mut info = self.info(id).expect("chosen or created");
        let hive = &self.hives[id];
        let mut machines = hive.index.machines.clone();
        machines.extend(hive.pending.iter().map(|pending| pending.machine.clone()));
        let present = machines.iter().cloned().collect();
        machines.insert(request.machine.clone());
        info.machines = display_names(&machines);
        Ok(Joined {
            hive: info,
            created,
            reason,
            present,
        })
    }

    /// Refuses a copy joining hive `id`, or cloned from it, while it is paused: it couldn't
    /// sync.
    fn check_unpaused(&self, id: &HiveId) -> Result<(), Refusal> {
        match &self.hives[id] {
            Hive {
                meta,
                paused: Some(pause),
                ..
            } => Err(format!(
                "hive {} is paused (by {}); it can be joined once `musubi pause --cancel` or \
                 `musubi resume` is run in one of its copies",
                meta.name, pause.by
            )),
            _ => Ok(()),
        }
    }

    /// Checks and reserves inherited Git names before a clone creates any directory.
    pub fn prepare_clone(
        &mut self,
        id: &HiveId,
        backend: Backend,
        incoming: &BTreeMap<String, RemoteBinding>,
    ) -> Result<HiveInfo, Refusal> {
        let hive = self.hives.get(id).ok_or_else(|| format!("no hive {id}"))?;
        self.check_unpaused(id)?;
        if hive.meta.backend != backend {
            return Err(
                "the hive changed backend during clone; run `musubi clone` again".to_owned(),
            );
        }
        self.reserve_remote_bindings(id, incoming, None)?;
        Ok(self.info(id).expect("checked by id"))
    }

    fn reserve_remote_bindings(
        &mut self,
        id: &HiveId,
        incoming: &BTreeMap<String, RemoteBinding>,
        clone_config: Option<&BTreeMap<String, String>>,
    ) -> Result<(), Refusal> {
        let bindings = self.checked_bindings(id, incoming)?;
        let hive = self.hives.get_mut(id).expect("chosen or created");
        // Approval reserves names even if its first sync is delayed beyond pending expiry.
        let mut meta = hive.meta.clone();
        meta.remote_bindings = bindings;
        if let Some(config) = clone_config {
            meta.clone_config = config.clone();
        }
        if hive.meta != meta {
            write_meta(&hive.dir, &meta).map_err(refusal)?;
            hive.meta = meta;
        }
        Ok(())
    }

    /// Checks immutable name bindings and the accepted evidence before join or clone.
    pub fn check_remote_consistency(&self, id: &HiveId) -> Result<(), Refusal> {
        self.checked_bindings(id, &BTreeMap::new()).map(|_| ())
    }

    /// Hive `id`'s remote bindings with `incoming` added ([`bindings::checked`]).
    fn checked_bindings(
        &self,
        id: &HiveId,
        incoming: &BTreeMap<String, RemoteBinding>,
    ) -> Result<BTreeMap<String, RemoteBinding>, Refusal> {
        let hive = &self.hives[id];
        bindings::checked(
            &hive.meta.name,
            &hive.meta.remote_bindings,
            &hive.index.remote_bindings,
            incoming,
        )
    }
}

/// Machines' names, as `musubi list` shows them: told apart by their keys where they are
/// alike.
fn display_names(keys: &BTreeSet<String>) -> Vec<String> {
    workspaces::display_names(keys, |_| false)
        .into_values()
        .collect()
}

/// What a join request's [`JoinChoice`] comes to among the hub's hives, once checked: the
/// hive it asked for found, a new name found free, a lost hive's id found to be one.
enum Intent<'a> {
    /// The hive that matches the repository.
    Match,
    /// The hive asked for.
    Hive(HiveId),
    /// A new hive, under this name, if the request gave one.
    Create(Option<&'a String>),
    /// A lost hive the hub has, made again since: joined as before.
    Rejoin(&'a HiveId),
    /// A lost hive made again under its id, which no hive has, with the name it had, if any.
    /// It is `named` when that name will do for a new hive here, which makes it as `musubi
    /// create <name>` would.
    Remake {
        id: &'a HiveId,
        name: Option<&'a String>,
        named: bool,
    },
}

/// The hives' stores a join looks in, from [`HubDir::probe`].
pub struct Probe {
    backend: Backend,
    targets: Vec<CommitId>,
    hives: Vec<(HiveId, PathBuf)>,
}

/// Whether each probed hive's store has any of the commits a joining repository's remotes
/// point at, or why it couldn't tell.
pub struct Probed(BTreeMap<HiveId, Result<bool, Refusal>>);

impl Probe {
    /// Looks in each store. A store removed meanwhile can't be looked in, but nor can its
    /// hive be joined, so [`HubDir::join_probed`] never sees the error.
    pub fn run(self) -> Probed {
        Probed(
            self.hives
                .into_iter()
                .map(|(id, dir)| {
                    let found = has_any(self.backend, &dir, &self.targets).map_err(refusal);
                    (id, found)
                })
                .collect(),
        )
    }
}

/// Whether the hive's store in `dir` has any of `commits`.
fn has_any(backend: Backend, dir: &Path, commits: &[CommitId]) -> anyhow::Result<bool> {
    if commits.is_empty() {
        return Ok(false);
    }
    let missing = store::object_store(backend, dir).missing(commits)?;
    Ok(missing.len() < commits.len())
}

/// Why `request` can't join `hive`, if their backends differ: commits a git repository names
/// with one hash are different commits under the other, and git can't convert a repository.
fn backend_refusal(request: &JoinRequest, hive: &HiveMeta) -> Option<Refusal> {
    if hive.backend == request.backend {
        return None;
    }
    let name = &hive.name;
    let kind = |backend: Backend| match backend {
        Backend::Git(_) => "git",
        Backend::Simple => "simple",
    };
    let differs = match (request.backend, hive.backend) {
        (Backend::Git(ours), Backend::Git(theirs)) => {
            format!(
                "this repository's git names objects with {ours}, but hive {name}'s with {theirs}"
            )
        }
        (ours, theirs) => format!(
            "this repository uses jj's {} backend, but hive {name} uses its {} backend",
            kind(ours),
            kind(theirs)
        ),
    };
    Some(format!(
        "{differs}, so it can't join it; `musubi clone {name} <dir>` makes a copy that can"
    ))
}

/// Why a request about a hive by its id, from one of its copies, finds no such hive here.
fn no_record(removed: bool) -> Refusal {
    if removed {
        "this repository's hive was removed from the hub".to_owned()
    } else {
        "the hub has no record of this repository's hive".to_owned()
    }
}

fn write_meta(dir: &Path, meta: &HiveMeta) -> anyhow::Result<()> {
    files::replace(&dir.join(HIVE_FILE), toml::to_string(meta)?.as_bytes())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::lifecycle::SET_ASIDE_LIFETIME;
    use super::lifecycle::now;
    use super::lifecycle::remade;
    use musubi_jj::objects::GitHash;

    use super::*;

    fn request(machine: &str, url: &str) -> JoinRequest {
        JoinRequest {
            backend: Backend::GIT,
            clone_config: BTreeMap::new(),
            remote_bindings: [(
                "origin".to_owned(),
                RemoteBinding {
                    fetch: RemoteUrl::parse(url).map(|url| url.key()),
                    push: RemoteUrl::parse(url)
                        .map(|url| url.key())
                        .into_iter()
                        .collect(),
                },
            )]
            .into(),
            remotes: vec![("origin".to_owned(), url.to_owned())],
            dir_name: "project".to_owned(),
            roots: vec!["11".repeat(20)],
            machine: format!("{machine}#00000000"),
            choice: JoinChoice::Match,
            remote_targets: vec![],
            carried: vec![],
        }
    }

    fn creating(request: JoinRequest) -> JoinRequest {
        JoinRequest {
            choice: JoinChoice::Create(None),
            ..request
        }
    }

    /// Clone resolves a user-supplied name once, then checks that exact hive by id.
    #[test]
    fn clone_preflight_keeps_the_resolved_hive() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let alpha = hubs.create("alpha", Backend::GIT).unwrap();
        let other = hubs.create(alpha.as_str(), Backend::GIT).unwrap();
        assert_ne!(alpha, other);
        assert_eq!(hubs.resolve(alpha.as_str()).unwrap(), other);
        let resolved = hubs.resolve("alpha").unwrap();
        let prepared = hubs
            .prepare_clone(&resolved, Backend::GIT, &BTreeMap::new())
            .unwrap();
        assert_eq!(prepared.id, alpha, "clone switched to a different hive");
        let missing = HiveId::from(Uuid::new_v4());
        hubs.create(missing.as_str(), Backend::GIT).unwrap();
        assert!(
            hubs.prepare_clone(&missing, Backend::GIT, &BTreeMap::new())
                .is_err()
        );
    }

    /// A pause outlives the hub restarting, keeps who paused first, and refuses joins and
    /// clones until it is lifted; a pause file a power cut emptied is no pause.
    #[test]
    fn a_pause_lasts_until_lifted() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let joined = hubs
            .join(&creating(request("alpha", "https://example.com/one")))
            .unwrap();
        let id = joined.hive.id;
        // As its first push records, for a join after the hub restarts to match.
        let index = HiveIndex {
            roots: ["11".repeat(20)].into(),
            ..HiveIndex::default()
        };
        hubs.update_index(&id, index).unwrap();
        let (info, before) = hubs.pause(&id, "alpha").unwrap();
        assert_eq!(before, None);
        let pause = info.paused.expect("paused");
        assert_eq!(pause.by, "alpha");
        let (_, before) = hubs.pause(&id, "beta").unwrap();
        assert_eq!(before.as_ref(), Some(&pause));
        let mut hubs = HubDir::open(dir.path()).unwrap();
        assert_eq!(hubs.paused(&id), Some(&pause));
        let joining = JoinRequest {
            choice: JoinChoice::Hive(id.as_str().to_owned()),
            ..request("beta", "https://example.com/one")
        };
        let err = hubs.join(&joining).unwrap_err();
        assert!(err.contains("is paused (by alpha)"), "{err}");
        let err = hubs
            .prepare_clone(&id, Backend::GIT, &BTreeMap::new())
            .unwrap_err();
        assert!(err.contains("is paused (by alpha)"), "{err}");
        let (info, before) = hubs.unpause(&id).unwrap();
        assert_eq!((info.paused, before), (None, Some(pause)));
        assert_eq!(HubDir::open(dir.path()).unwrap().paused(&id), None);
        hubs.join(&request("beta", "https://example.com/one"))
            .unwrap();
        hubs.pause(&id, "alpha").unwrap();
        fs::write(dir.path().join(id.as_str()).join(PAUSED_FILE), "").unwrap();
        assert_eq!(HubDir::open(dir.path()).unwrap().paused(&id), None);
        let missing = HiveId::from(Uuid::new_v4());
        assert!(
            hubs.pause(&missing, "alpha")
                .unwrap_err()
                .contains("no record")
        );
    }

    /// `musubi resume` makes a paused hive again under a new id, with its name and settings,
    /// unpaused, for the copy that asked to join, unless the head isn't the one it last
    /// fetched; the old id answers the reset from then on, to other copies, and stays refused
    /// to a remake, or a join that carries its history, across restarts. The copy that reset
    /// it, asking again after missing the answer, joins the new hive, made again if a crash
    /// lost it. The old store is emptied at once, but for its tombstone, which a power cut that
    /// tore it leaves still a reset.
    #[test]
    fn a_reset_hive_starts_again_under_a_new_id() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let named = JoinRequest {
            choice: JoinChoice::Create(Some("project".to_owned())),
            clone_config: [("user.name".to_owned(), "\"A\"".to_owned())].into(),
            ..request("alpha", "https://example.com/a")
        };
        let id = hubs.join(&named).unwrap().hive.id;
        let root = jj_lib::object_id::ObjectId::hex(hubs.open_store(&id).unwrap().head().1);
        let resetting = |base: &str, force: bool| JoinRequest {
            choice: JoinChoice::Reset {
                id: id.clone(),
                base: base.to_owned(),
                force,
            },
            ..request("alpha", "https://example.com/a")
        };
        let err = hubs.reset(&resetting(&root, false)).unwrap_err();
        assert!(err.contains("isn't paused"), "{err}");
        hubs.pause(&id, "alpha").unwrap();
        let err = hubs.reset(&resetting(&"ab".repeat(32), false)).unwrap_err();
        assert!(
            err.contains("has work that this copy hasn't received"),
            "{err}"
        );
        let ResetOutcome::Joined(joined) = hubs.reset(&resetting(&"ab".repeat(32), true)).unwrap()
        else {
            panic!("not reset");
        };
        let new = joined.hive.id.clone();
        assert_ne!(new, id);
        assert!(joined.created);
        assert_eq!(joined.hive.name, "project");
        assert_eq!(joined.hive.paused, None);
        assert_eq!(joined.hive.clone_config, named.clone_config);
        assert!(!dir.path().join(id.as_str()).exists());
        let reset = hubs.reset_of(&id).unwrap();
        assert_eq!(
            (reset.name.as_str(), reset.by.as_str(), reset.key.as_str()),
            ("project", "alpha", "alpha#00000000")
        );
        // Emptied in the background, but for the tombstone.
        let tombstone = fs::read_dir(dir.path().join("removed"))
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        let deadline = Instant::now() + Duration::from_secs(10);
        let left = || {
            let mut names: Vec<String> = fs::read_dir(&tombstone)
                .unwrap()
                .map(|entry| entry.unwrap().file_name().into_string().unwrap())
                .collect();
            names.sort();
            names
        };
        while left().len() > 2 && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(left(), ["hive.toml", "reset"]);

        let beta = JoinRequest {
            choice: JoinChoice::Reset {
                id: id.clone(),
                base: root.clone(),
                force: false,
            },
            ..request("beta", "https://example.com/a")
        };
        assert_eq!(
            hubs.reset(&beta).unwrap(),
            ResetOutcome::Reset(reset.clone())
        );
        let remake = JoinRequest {
            choice: JoinChoice::Remake {
                id: id.clone(),
                name: Some("project".to_owned()),
            },
            ..request("beta", "https://example.com/a")
        };
        let err = hubs.join(&remake).unwrap_err();
        assert!(err.contains("was reset"), "{err}");
        // Nor does a join that carries its history, into any hive.
        assert_eq!(hubs.reset_among(&remake), Some(reset.clone()));
        let carrying = JoinRequest {
            carried: vec![id.as_str().to_owned()],
            ..request("beta", "https://example.com/a")
        };
        assert_eq!(hubs.reset_among(&carrying), Some(reset.clone()));
        // join_probed looks again, for a reset that landed after the caller's look.
        let probed = hubs.probe(&carrying).run();
        assert_eq!(
            hubs.join_probed(&carrying, &probed).unwrap_err(),
            JoinRefused::Reset(reset.clone())
        );
        assert_eq!(
            hubs.reset_among(&request("beta", "https://example.com/a")),
            None
        );
        // Unless it is the copy that reset it, which no longer carries it.
        let own = JoinRequest {
            choice: remake.choice.clone(),
            ..request("alpha", "https://example.com/a")
        };
        assert!(hubs.finishing_reset(&own) && hubs.reset_among(&own).is_none());
        let still = JoinRequest {
            carried: vec![id.as_str().to_owned()],
            ..own.clone()
        };
        assert!(!hubs.finishing_reset(&still) && hubs.reset_among(&still).is_some());
        let again = |hubs: &mut HubDir| match hubs.reset(&resetting(&root, false)).unwrap() {
            ResetOutcome::Joined(joined) => joined.hive.id,
            ResetOutcome::Reset(_) => panic!("its own reset refused"),
        };
        assert_eq!(again(&mut hubs), new);

        // A crash before the new hive was made, then the hub restarting.
        fs::remove_dir_all(dir.path().join(new.as_str())).unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        assert_eq!(hubs.reset_of(&id), Some(reset.clone()));
        assert_eq!(again(&mut hubs), new);
        assert_eq!(hubs.info(&new).unwrap().name, "project");
        assert!(hubs.join(&remake).is_err());

        fs::write(tombstone.join("reset"), "").unwrap();
        let hubs = HubDir::open(dir.path()).unwrap();
        let torn = hubs.reset_of(&id).unwrap();
        assert_eq!(
            (torn.name.as_str(), torn.by.as_str()),
            ("project", "another machine")
        );
    }

    /// A name is reserved on approval, survives pending expiry and restart, and cannot
    /// be overridden by an explicit hive choice or an existing copy's rejoin.
    #[test]
    fn remote_bindings_are_checked_before_joining() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path())
            .unwrap()
            .with_pending_lifetime(Duration::ZERO);
        let binding = |target: &str| RemoteBinding {
            fetch: Some(target.to_owned()),
            push: [target.to_owned()].into(),
        };
        let mut first = creating(request("alpha", "https://example.com/one"));
        first
            .clone_config
            .insert("user.name".to_owned(), "\"Creator\"".to_owned());
        first
            .remote_bindings
            .insert("origin".to_owned(), binding("example.com/one"));
        let joined = hubs.join(&first).unwrap();
        let id = joined.hive.id;
        assert!(
            hubs.prepare_clone(&id, Backend::GIT, &first.remote_bindings)
                .is_ok()
        );
        let mut conflicting = first.remote_bindings.clone();
        conflicting
            .get_mut("origin")
            .unwrap()
            .push
            .insert("example.com/fork".to_owned());
        assert!(hubs.prepare_clone(&id, Backend::GIT, &conflicting).is_err());
        // The first push records common history independently of the approval's names.
        hubs.update_index(
            &id,
            HiveIndex {
                roots: first.roots.iter().cloned().collect(),
                ..HiveIndex::default()
            },
        )
        .unwrap();
        drop(hubs);
        let mut hubs = HubDir::open(dir.path()).unwrap();
        for choice in [
            JoinChoice::Hive(id.to_string()),
            JoinChoice::Remake {
                id: id.clone(),
                name: None,
            },
        ] {
            let mut second = request("beta", "https://example.com/one");
            second.choice = choice;
            second
                .remote_bindings
                .insert("origin".to_owned(), binding("example.com/two"));
            second
                .remote_bindings
                .insert("extra".to_owned(), binding("example.com/extra"));
            let err = hubs.join(&second).unwrap_err();
            assert!(err.contains("origin"), "{err}");
            assert!(hubs.hives[&id].pending.is_empty());
            assert!(!hubs.hives[&id].meta.remote_bindings.contains_key("extra"));
        }
        // Push destinations are checked too, even when the fetch destination agrees.
        let mut second = request("beta", "https://example.com/one");
        second.choice = JoinChoice::Hive(id.to_string());
        let mut pushes_elsewhere = binding("example.com/one");
        pushes_elsewhere.push.insert("example.com/fork".to_owned());
        second
            .remote_bindings
            .insert("origin".to_owned(), pushes_elsewhere);
        assert!(hubs.join(&second).is_err());
        second
            .clone_config
            .insert("user.name".to_owned(), "\"Joining User\"".to_owned());
        second.remote_bindings.clear();
        second.remotes.clear();
        assert!(
            hubs.join(&second).is_ok(),
            "a missing remote makes no claim"
        );
        assert_eq!(hubs.info(&id).unwrap().clone_config, first.clone_config);
    }

    /// A second copy joining before the first has pushed finds the first's hive, but only
    /// for a while: a join that never pushes stops counting.
    #[test]
    fn pending_joins_count_until_they_expire_or_push() {
        for (lifetime, joins_the_same) in [(PENDING_LIFETIME, true), (Duration::ZERO, false)] {
            let dir = tempfile::tempdir().unwrap();
            let mut hubs = HubDir::open(dir.path())
                .unwrap()
                .with_pending_lifetime(lifetime);
            let url = "https://example.com/team/project";
            let first = hubs.join(&creating(request("alpha", url))).unwrap();
            assert!(first.created);
            match hubs.join(&request("beta", url)) {
                Ok(second) => {
                    assert!(joins_the_same, "{lifetime:?}");
                    assert_eq!(second.hive.id, first.hive.id);
                }
                Err(message) => assert!(!joins_the_same, "{lifetime:?}: {message}"),
            }
        }
        // An accepted push from the joining machine replaces its pending join.
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let first = hubs
            .join(&creating(request("alpha", "https://example.com/a")))
            .unwrap();
        let id = first.hive.id;
        assert_eq!(hubs.hives[&id].pending.len(), 1);
        let pushed = HiveIndex {
            remote_bindings: BTreeMap::new(),
            machines: BTreeSet::from(["alpha#00000000".to_owned()]),
            ..HiveIndex::default()
        };
        hubs.update_index(&id, pushed).unwrap();
        assert!(hubs.hives[&id].pending.is_empty());
    }

    /// A join looks in the hives' stores without the hub held, so hives come and go
    /// meanwhile: one removed is no candidate, and one made since has none of the joining
    /// repository's commits.
    #[test]
    fn hives_come_and_go_while_a_join_looks_in_their_stores() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let gone = hubs.create("gone", Backend::GIT).unwrap();
        let kept = hubs.create("kept", Backend::GIT).unwrap();
        let joining = JoinRequest {
            remote_targets: vec!["22".repeat(20)],
            ..creating(request("alpha", "https://example.com/a"))
        };
        let probe = hubs.probe(&joining);
        hubs.remove(&gone).unwrap();
        let made = hubs.create("made", Backend::GIT).unwrap();
        let probed = probe.run();
        assert_eq!(probed.0.get(&kept), Some(&Ok(false)));
        assert!(probed.0.contains_key(&gone));
        assert!(!probed.0.contains_key(&made));
        let joined = hubs.join_probed(&joining, &probed).unwrap();
        assert!(joined.created);
        assert!(![gone, kept, made].contains(&joined.hive.id));
    }

    /// A hive is never named what no hive can be: a new one made without a name gets a valid
    /// one from the repository's directory, and so does a hive made again under a name an
    /// earlier release gave it that isn't valid now.
    #[test]
    fn default_names_are_valid_names() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let unnamed = |dir_name: &str, choice: JoinChoice| JoinRequest {
            choice,
            dir_name: dir_name.to_owned(),
            remotes: vec![],
            remote_bindings: BTreeMap::new(),
            ..request("alpha", "https://example.com/a")
        };
        let joined = hubs
            .join(&unnamed("My Project", JoinChoice::Create(None)))
            .unwrap();
        assert_eq!(joined.hive.name, "My-Project");
        let remake = JoinChoice::Remake {
            id: HiveId::from(Uuid::new_v4()),
            name: Some("Old Name".to_owned()),
        };
        let mut other = unnamed("Other Project", remake);
        other.roots = vec!["22".repeat(20)];
        let joined = hubs.join(&other).unwrap();
        assert!(joined.created);
        assert_eq!(joined.hive.name, "Other-Project");
        let err = hubs
            .create_as(&HiveId::from(Uuid::new_v4()), "My Project", Backend::GIT)
            .unwrap_err();
        assert_eq!(
            err.to_string(),
            r#"a hive name can't contain spaces: "My Project""#
        );
    }

    /// A hive is renamed by a prefix of its name, saying the name it had; and no empty name
    /// names one, though every name starts with it.
    #[test]
    fn hives_are_renamed_by_prefix_but_not_by_nothing() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        hubs.create("alpha", Backend::GIT).unwrap();
        let (from, info) = hubs.rename("alp", "beta").unwrap();
        assert_eq!((from.as_str(), info.name.as_str()), ("alpha", "beta"));
        let (from, info) = hubs.rename("be", "beta").unwrap();
        assert_eq!((from.as_str(), info.name.as_str()), ("beta", "beta"));
        let empty = "a hive name can't be empty".to_owned();
        assert_eq!(hubs.resolve("").unwrap_err(), empty);
        assert_eq!(hubs.resolve_exact("").unwrap_err(), empty);
        assert_eq!(hubs.rename("", "gamma").unwrap_err(), empty);
        let beta = hubs.resolve("beta").unwrap();
        assert_eq!(hubs.info(&beta).unwrap().name, "beta");
    }

    /// A hive created with a name has it, and no second hive can be created with it.
    #[test]
    fn a_new_hive_takes_the_name_asked_for() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let named = |name: &str, url: &str| JoinRequest {
            choice: JoinChoice::Create(Some(name.to_owned())),
            ..request("alpha", url)
        };
        let joined = hubs.join(&named("work", "https://example.com/a")).unwrap();
        assert!(joined.created);
        assert_eq!(joined.hive.name, "work");
        let err = hubs
            .join(&named("work", "https://example.com/b"))
            .unwrap_err();
        assert!(err.contains("already a hive named work"), "{err}");
    }

    /// A hive keeps the hash its first copy names objects with, across a restart and in its
    /// store's git, and refuses a copy with the other one, whether its remote matches or it
    /// names the hive, saying why: their commits can't be the same.
    #[test]
    fn a_hive_keeps_its_first_copys_hash() {
        let dir = tempfile::tempdir().unwrap();
        let sha256 = Backend::Git(GitHash::Sha256);
        let url = "https://example.com/a";
        let refusal = "this repository's git names objects with SHA-1, but hive a's with \
                       SHA-256, so it can't join it; `musubi clone a <dir>` makes a copy that can";
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let joined = hubs
            .join(&creating(JoinRequest {
                backend: sha256,
                ..request("alpha", url)
            }))
            .unwrap();
        assert_eq!(hubs.join(&request("beta", url)).unwrap_err(), refusal);
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let id = joined.hive.id;
        assert_eq!(hubs.info(&id).unwrap().backend, sha256);
        let store = hubs.open_store(&id).unwrap();
        assert_eq!(store.backend(), sha256);
        let format = std::process::Command::new("git")
            .arg("--git-dir")
            .arg(dir.path().join(id.as_str()).join("git"))
            .args(["rev-parse", "--show-object-format"])
            .output()
            .unwrap();
        assert_eq!(String::from_utf8_lossy(&format.stdout).trim(), "sha256");
        let named = JoinRequest {
            choice: JoinChoice::Hive("a".to_owned()),
            ..request("beta", url)
        };
        assert_eq!(hubs.join(&named).unwrap_err(), refusal);
    }

    /// Machines of one name, which their keys tell apart, are listed apart, and a joining
    /// machine is listed as it will be once it has pushed.
    #[test]
    fn machines_of_one_name_are_told_apart() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let url = "https://example.com/a";
        let id = hubs.join(&creating(request("mac", url))).unwrap().hive.id;
        let pushed = HiveIndex {
            remote_bindings: BTreeMap::new(),
            machines: BTreeSet::from(["mac#00000000".to_owned(), "mac#11111111".to_owned()]),
            roots: BTreeSet::from(["11".repeat(20)]),
            ..HiveIndex::default()
        };
        hubs.update_index(&id, pushed).unwrap();
        assert_eq!(hubs.info(&id).unwrap().machines, ["mac-0000", "mac-1111"]);
        let third = JoinRequest {
            choice: JoinChoice::Hive(id.to_string()),
            machine: "mac#22222222".to_owned(),
            ..request("mac", url)
        };
        let joined = hubs.join(&third).unwrap();
        assert_eq!(joined.hive.machines, ["mac-0000", "mac-1111", "mac-2222"]);
    }

    /// A push whose index the hub couldn't save has it saved by the next, though that push
    /// brings nothing new, so a hub that restarts still finds the hive by it.
    #[test]
    fn a_failed_index_save_is_retried_at_the_next_push() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let id = hubs
            .join(&creating(request("alpha", "https://example.com/a")))
            .unwrap()
            .hive
            .id;
        let pushed = HiveIndex {
            remote_bindings: BTreeMap::new(),
            machines: BTreeSet::from(["alpha#00000000".to_owned()]),
            roots: BTreeSet::from(["11".repeat(20)]),
            urls: BTreeSet::from(["https://example.com/a".to_owned()]),
        };
        // A directory in the file's place makes the save fail, as a full disk would.
        let file = dir.path().join(id.as_str()).join("index.json");
        fs::remove_file(&file).unwrap();
        fs::create_dir(&file).unwrap();
        hubs.update_index(&id, pushed.clone()).unwrap_err();
        fs::remove_dir(&file).unwrap();
        hubs.update_index(&id, pushed.clone()).unwrap();
        assert_eq!(HiveIndex::load(&dir.path().join(id.as_str())), Some(pushed));
    }

    /// A hive whose store is corrupt is made again, empty, from what the hub knows of it,
    /// though what is corrupt is the store's own record of its backend.
    #[test]
    fn a_hive_is_made_again_whatever_is_corrupt() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let id = hubs
            .join(&creating(request("alpha", "https://example.com/a")))
            .unwrap()
            .hive
            .id;
        let hive_dir = dir.path().join(id.as_str());
        fs::write(hive_dir.join("backend"), b"").unwrap();
        let Err(err) = HubStore::open(&hive_dir) else {
            panic!("opened a store with no backend");
        };
        assert!(store::is_corrupt(&err), "{err}");
        hubs.remake(&id, &err).unwrap();
        let store = HubStore::open(&hive_dir).unwrap();
        assert_eq!(store.backend(), Backend::GIT);
        assert_eq!(store.head().0, 0);
        assert_eq!(hubs.info(&id).unwrap().name, "a");
    }

    /// A hive whose `heads` log a 0.47 hub wrote with records, of `jj op abandon` it passed
    /// on, is made again, empty, when the hub opens its store: its machines fill it.
    ///
    /// Compatibility until 2027-02-21: remove with `StoreError::RecordsLog`.
    #[test]
    fn a_hive_with_records_is_made_again() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let id = hubs
            .join(&creating(request("alpha", "https://example.com/a")))
            .unwrap()
            .hive
            .id;
        let heads = dir.path().join(id.as_str()).join("heads");
        let log = fs::read_to_string(&heads).unwrap();
        let root = log.split(' ').nth(1).unwrap().trim();
        fs::write(&heads, format!("{log}1 {root} {}\n", "ab".repeat(64))).unwrap();
        let store = hubs.open_store(&id).unwrap();
        assert_eq!(store.head().0, 0);
        assert_eq!(fs::read_to_string(&heads).unwrap().lines().count(), 1);
    }

    /// A hive whose store is corrupt and whose index needs rebuilding no longer keeps the
    /// hub from starting: it is made again as the hub starts.
    #[test]
    fn a_corrupt_hive_is_made_again_as_the_hub_starts() {
        let dir = tempfile::tempdir().unwrap();
        let id = HubDir::open(dir.path())
            .unwrap()
            .join(&creating(request("alpha", "https://example.com/a")))
            .unwrap()
            .hive
            .id;
        let hive_dir = dir.path().join(id.as_str());
        fs::remove_file(hive_dir.join("index.json")).unwrap();
        let mut heads = fs::read(hive_dir.join("heads")).unwrap();
        heads.extend_from_slice(b"1 0123");
        fs::write(hive_dir.join("heads"), heads).unwrap();
        let hubs = HubDir::open(dir.path()).unwrap();
        assert_eq!(hubs.info(&id).unwrap().name, "a");
        assert_eq!(HubStore::open(&hive_dir).unwrap().head().0, 0);
        assert_eq!(set_aside(dir.path()).corrupt.len(), 1);
    }

    /// A remake a crash interrupted between its renames is finished as the hub starts, and
    /// one interrupted before them is undone.
    #[test]
    fn remakes_a_crash_interrupted_are_finished() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let mut join = |name: &str| {
            hubs.join(&creating(request(
                name,
                &format!("https://example.com/{name}"),
            )))
            .unwrap()
            .hive
            .id
        };
        let (renamed, begun) = (join("alpha"), join("beta"));
        fs::rename(
            dir.path().join(renamed.as_str()),
            remade(dir.path(), &renamed),
        )
        .unwrap();
        fs::create_dir(remade(dir.path(), &begun)).unwrap();
        let hubs = HubDir::open(dir.path()).unwrap();
        for id in [&renamed, &begun] {
            assert!(hubs.info(id).is_some(), "lost {id}");
            assert!(!remade(dir.path(), id).exists());
        }
    }

    /// A store set aside as corrupt goes a day after it was, once the hive made again has
    /// accepted a head: not while the hive is still empty, nor sooner.
    #[test]
    fn corrupt_stores_go_a_day_after_they_are_replaced() {
        let dir = tempfile::tempdir().unwrap();
        let id = HubDir::open(dir.path())
            .unwrap()
            .join(&creating(request("alpha", "https://example.com/a")))
            .unwrap()
            .hive
            .id;
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        let aside = |age: u64| {
            dir.path()
                .join("removed")
                .join(format!("{id}-{}.corrupt", now - age))
        };
        let (new, old) = (aside(60), aside(SET_ASIDE_LIFETIME.as_secs() + 60));
        for aside in [&new, &old] {
            fs::create_dir_all(aside).unwrap();
        }
        // As a hub started since finds them.
        let mut hubs = HubDir::open(dir.path()).unwrap();
        assert!(
            new.exists() && old.exists(),
            "swept before the hive was filled"
        );
        let heads = dir.path().join(id.as_str()).join("heads");
        let filled = format!(
            "{}1 {}\n",
            fs::read_to_string(&heads).unwrap(),
            "ab".repeat(64)
        );
        fs::write(&heads, filled).unwrap();
        hubs.sweep();
        // Deleted in the background.
        let deadline = Instant::now() + Duration::from_secs(10);
        while old.exists() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(new.exists(), "swept within a day");
        assert!(!old.exists(), "kept a day after the hive was filled");
    }

    /// A removed hive leaves a tombstone, which a hub started since knows, apart from a
    /// corrupt store set aside, whose hive is still there; its store is emptied a day after,
    /// and the tombstone stays. Removing takes a whole name or id, not a prefix.
    #[test]
    fn a_removed_hive_leaves_a_tombstone() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let named = JoinRequest {
            choice: JoinChoice::Create(Some("project".to_owned())),
            ..request("alpha", "https://example.com/a")
        };
        let id = hubs.join(&named).unwrap().hive.id;
        assert!(hubs.resolve_exact("proj").is_err(), "removed by a prefix");
        assert_eq!(hubs.resolve_exact("project").unwrap(), id);
        assert_eq!(hubs.resolve_exact(id.as_str()).unwrap(), id);
        hubs.remove(&id).unwrap();
        assert!(hubs.is_removed(&id));
        let removed = dir.path().join("removed");
        let tombstone = fs::read_dir(&removed)
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
            .path();
        // A day later, as a hub started then finds it, with a corrupt store beside it.
        let day_ago = now() - SET_ASIDE_LIFETIME.as_secs() - 60;
        let old = removed.join(format!("{id}-{day_ago}"));
        fs::rename(&tombstone, &old).unwrap();
        let other = Uuid::new_v4();
        fs::create_dir_all(removed.join(format!("{other}-{day_ago}.corrupt"))).unwrap();
        let hubs = HubDir::open(dir.path()).unwrap();
        assert!(hubs.is_removed(&id));
        assert!(!hubs.is_removed(&HiveId::from(other)));
        // Emptied in the background.
        let deadline = Instant::now() + Duration::from_secs(10);
        let empty = || fs::read_dir(&old).unwrap().next().is_none();
        while !empty() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(empty(), "kept the store a day after the hive was removed");
    }

    /// Hives made apart on purpose, from copies of one repository, by name, are each made
    /// again under its own name once the hub has lost them, though the copies match both.
    #[test]
    fn hives_made_apart_are_made_again_apart() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let mut made = vec![];
        for (machine, name) in [("alpha", "proj"), ("beta", "proj-exp")] {
            let named = JoinRequest {
                choice: JoinChoice::Create(Some(name.to_owned())),
                ..request(machine, "https://example.com/proj")
            };
            let joined = hubs.join(&named).unwrap();
            made.push((machine, joined.hive.id, joined.hive.name));
        }
        // A new hub, in place of the one lost.
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        for (machine, id, name) in made {
            let remake = JoinRequest {
                choice: JoinChoice::Remake {
                    id: id.clone(),
                    name: Some(name.clone()),
                },
                ..request(machine, "https://example.com/proj")
            };
            let joined = hubs.join(&remake).unwrap();
            assert!(joined.created);
            assert_eq!((joined.hive.id, joined.hive.name), (id, name));
        }
    }

    /// A repository that was part of a hive the hub has lost makes it again, under its id
    /// and name; but not a removed hive, nor one it belongs beside when the hub has its name or
    /// it has none; and joins it if it's there.
    #[test]
    fn a_lost_hive_is_made_again_by_joining() {
        let dir = musubi_testutil::tempdir();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let remake_as = |id: &str, name: Option<&str>| JoinRequest {
            choice: JoinChoice::Remake {
                id: HiveId::from(id.to_owned()),
                name: name.map(str::to_owned),
            },
            ..request("alpha", "https://example.com/a")
        };
        let remake = |id: &str, name: &str| remake_as(id, Some(name));
        let lost = HiveId::from(Uuid::new_v4());
        let joined = hubs.join(&remake(lost.as_str(), "mine")).unwrap();
        assert!(joined.created);
        assert_eq!(
            (joined.hive.id.as_str(), joined.hive.name.as_str()),
            (lost.as_str(), "mine")
        );
        // Made again already: joined.
        let joined = hubs.join(&remake(lost.as_str(), "mine")).unwrap();
        assert!(!joined.created);
        // Another lost hive of the same repository, under the name of this one, or none,
        // belongs beside it: refused.
        for name in [Some("mine"), None] {
            let err = hubs
                .join(&remake_as(&Uuid::new_v4().to_string(), name))
                .unwrap_err();
            assert!(err.contains("belongs in hive mine"), "{err}");
            // `musubi leave` alone would fail to tell the hive the hub lacks.
            assert!(err.contains("`musubi leave --force`"), "{err}");
        }
        hubs.remove(&lost).unwrap();
        let err = hubs.join(&remake(lost.as_str(), "mine")).unwrap_err();
        assert!(err.contains("removed"), "{err}");
        let err = hubs.join(&remake("../elsewhere", "mine")).unwrap_err();
        assert!(err.contains("not a hive id"), "{err}");
    }
}

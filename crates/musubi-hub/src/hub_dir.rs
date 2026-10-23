//! A hub's directory: one subdirectory per hive, named by the hive's id, each holding a hub
//! store (see [`crate::store`]), the hive's `hive.toml` (its name and backend), and its
//! index (see [`crate::index`]). Removed hives move to `removed/`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::io::BufRead as _;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;
use std::time::Instant;

use jj_lib::backend::CommitId;
use musubi_jj::files;
use musubi_jj::objects::Backend;
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

const HIVE_FILE: &str = "hive.toml";

/// A hive's `hive.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct HiveMeta {
    name: String,
    backend: Backend,
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
}

/// What a joining repository tells the hub.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinRequest {
    pub choice: JoinChoice,
    pub backend: Backend,
    /// Names and URLs of its remotes: a remote's name once for each of its URLs, as git
    /// expands it and as written.
    pub remotes: Vec<(String, String)>,
    /// The name of the repository's directory, to name a hive after when it has no
    /// remotes.
    pub dir_name: String,
    /// Hex ids of its commits whose parent is the root commit.
    pub roots: Vec<String>,
    /// Hex ids of the commits its remote bookmarks point to.
    pub remote_targets: Vec<String>,
    /// The joining machine's key.
    pub machine: String,
}

/// A hive, as `musubi list` shows it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveInfo {
    pub id: String,
    pub name: String,
    pub backend: Backend,
    pub urls: Vec<String>,
    /// Names of the machines with workspaces in the hive.
    pub machines: Vec<String>,
}

/// The outcome of a join.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Joined {
    pub hive: HiveInfo,
    pub created: bool,
    /// Why this hive, for telling the user: `matched origin`, say.
    pub reason: String,
}

/// How long the hub counts what a joining repository brings as the hive's before the
/// repository has pushed it: long enough for its first sync to start.
const PENDING_LIFETIME: Duration = Duration::from_secs(120);

/// How long a hive's corrupt store, set aside when the hive was made again, stays once the
/// new one has accepted a head: long enough for someone curious to look at it.
const CORRUPT_LIFETIME: Duration = Duration::from_secs(24 * 3600);

struct Hive {
    dir: PathBuf,
    meta: HiveMeta,
    index: HiveIndex,
    /// Joins whose first push the hive hasn't accepted yet.
    pending: Vec<Pending>,
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
    hives: BTreeMap<String, Hive>,
    pending_lifetime: Duration,
    /// Corrupt stores set aside under `removed/` and not deleted yet (see
    /// [`Self::sweep_corrupt`]).
    corrupt: Vec<SetAside>,
}

/// A hive's corrupt store, set aside when the hive was made again.
struct SetAside {
    id: String,
    path: PathBuf,
    /// When it was set aside, in seconds since the epoch.
    stamp: u64,
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
                .map(str::to_owned)
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
            hives.insert(
                id,
                Hive {
                    dir: hive_dir,
                    meta,
                    index,
                    pending: vec![],
                },
            );
        }
        let mut hubs = Self {
            dir: dir.to_owned(),
            hives,
            pending_lifetime: PENDING_LIFETIME,
            corrupt: set_aside(dir),
        };
        for id in unindexed {
            let index = HiveIndex::rebuild(&hubs.open_store(&id)?)?;
            let hive = hubs.hives.get_mut(&id).expect("listed above");
            index.save(&hive.dir)?;
            hive.index = index;
        }
        hubs.sweep_corrupt();
        Ok(hubs)
    }

    /// Opens hive `id`'s store, making the hive again first if a power cut left the store
    /// corrupt or torn ([`open_whole`]).
    pub fn open_store(&mut self, id: &str) -> anyhow::Result<HubStore> {
        let dir = self.hive(id)?.dir.clone();
        match open_whole(&dir, true)? {
            Opened::Whole(store) => Ok(*store),
            Opened::Damaged(why) => {
                self.remake(id, &why)?;
                Ok(HubStore::open(&dir)?)
            }
        }
    }

    fn hive(&self, id: &str) -> anyhow::Result<&Hive> {
        self.hives
            .get(id)
            .ok_or_else(|| anyhow::anyhow!("no hive {id}"))
    }

    /// Makes hive `id`, whose store `why` found corrupt, again: empty, for its machines to
    /// fill, under its name and with the index joins match it by. The hive goes back to its
    /// root, and machines that knew its later heads follow it (docs/protocol.md, "Network
    /// and failures").
    ///
    /// Its store goes under `removed/` until a day after the new one has accepted a head,
    /// and a new one takes its place, made whole beside it first, so that a failure leaves
    /// the hive as it was, to be made again next time, and a crash between the two renames
    /// leaves it for the hub to finish as it next starts.
    pub fn remake(&mut self, id: &str, why: &dyn std::fmt::Display) -> anyhow::Result<()> {
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
            "hive {} ({id}) was corrupt ({why}), and is made again, empty, for its machines to \
             fill; the corrupt store is in {}, until a day from now once they have",
            hive.meta.name,
            aside.display()
        );
        self.corrupt.push(SetAside {
            id: id.to_owned(),
            path: aside,
            stamp,
        });
        Ok(())
    }

    /// Deletes each corrupt store [`Self::remake`] set aside a day after it did, once the hive
    /// made again has accepted a head, so that its machines have filled it, or is gone. In
    /// the background: a store can be large, and the caller holds the hub.
    fn sweep_corrupt(&mut self) {
        let now = now();
        let hives = &self.hives;
        self.corrupt.retain(|SetAside { id, path, stamp }| {
            if now.saturating_sub(*stamp) < CORRUPT_LIFETIME.as_secs() {
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
    pub fn hive_dir(&self, id: &str) -> Option<&Path> {
        self.hives.get(id).map(|hive| hive.dir.as_path())
    }

    /// Creates an empty hive.
    pub fn create(&mut self, name: &str, backend: Backend) -> anyhow::Result<String> {
        self.check_new_name(name).map_err(anyhow::Error::msg)?;
        let id = Uuid::new_v4().to_string();
        let dir = self.dir.join(&id);
        HubStore::init(&dir, backend)?;
        let meta = HiveMeta {
            name: name.to_owned(),
            backend,
        };
        write_meta(&dir, &meta)?;
        let index = HiveIndex::default();
        index.save(&dir)?;
        self.hives.insert(
            id.clone(),
            Hive {
                dir,
                meta,
                index,
                pending: vec![],
            },
        );
        Ok(id)
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
    pub fn resolve(&self, name: &str) -> Result<String, Refusal> {
        if let Some((id, _)) = self.hives.iter().find(|(_, h)| h.meta.name == name) {
            return Ok(id.clone());
        }
        if self.hives.contains_key(name) {
            return Ok(name.to_owned());
        }
        let by_name = |hive: &Hive, _: &str| hive.meta.name.starts_with(name);
        let by_id = |_: &Hive, id: &str| id.starts_with(name);
        for matches in [&by_name as &dyn Fn(&Hive, &str) -> bool, &by_id] {
            let found: Vec<(&String, &Hive)> = self
                .hives
                .iter()
                .filter(|(id, hive)| matches(hive, id))
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

    pub fn info(&self, id: &str) -> Option<HiveInfo> {
        let hive = self.hives.get(id)?;
        Some(HiveInfo {
            id: id.to_owned(),
            name: hive.meta.name.clone(),
            backend: hive.meta.backend,
            urls: hive.index.urls.iter().cloned().collect(),
            machines: display_names(&hive.index.machines),
        })
    }

    pub fn list(&self) -> Vec<HiveInfo> {
        let mut hives: Vec<HiveInfo> = self.hives.keys().filter_map(|id| self.info(id)).collect();
        hives.sort_by(|a, b| a.name.cmp(&b.name));
        hives
    }

    pub fn rename(&mut self, name: &str, to: &str) -> Result<HiveInfo, Refusal> {
        let id = self.resolve(name)?;
        if self.hives[&id].meta.name != to {
            self.check_new_name(to)?;
            let hive = self.hives.get_mut(&id).expect("resolved");
            let mut meta = hive.meta.clone();
            meta.name = to.to_owned();
            write_meta(&hive.dir, &meta).map_err(refusal)?;
            hive.meta = meta;
        }
        Ok(self.info(&id).expect("resolved"))
    }

    /// Takes a hive out of the hub, keeping its store under `removed/`. The caller has
    /// stopped serving it.
    pub fn remove(&mut self, id: &str) -> Result<HiveInfo, Refusal> {
        let info = self.info(id).ok_or_else(|| format!("no hive {id}"))?;
        let removed = self.dir.join("removed");
        fs::create_dir_all(&removed).map_err(refusal)?;
        let stamp = now();
        let hive = &self.hives[id];
        fs::rename(&hive.dir, removed.join(format!("{id}-{stamp}"))).map_err(refusal)?;
        self.hives.remove(id);
        Ok(info)
    }

    /// Adds what newly accepted operations brought to a hive's index, and forgets the
    /// pending joins of machines that are now in it.
    pub fn update_index(&mut self, id: &str, index: HiveIndex) -> anyhow::Result<()> {
        let Some(hive) = self.hives.get_mut(id) else {
            return Ok(());
        };
        hive.pending
            .retain(|pending| !index.machines.contains(&pending.machine));
        let mut changed = hive.index.machines != index.machines;
        for url in index.urls {
            changed |= hive.index.urls.insert(url);
        }
        for root in index.roots {
            changed |= hive.index.roots.insert(root);
        }
        hive.index.machines = index.machines;
        // Most heads bring nothing new. Saving anyway would replace the index at every push,
        // and ext4 writes out a file that replaces another at once.
        if changed {
            hive.index.save(&hive.dir)?;
        }
        self.sweep_corrupt();
        Ok(())
    }

    /// Every hive, as a candidate for `request` to join: whether it shares history with the
    /// joining repository, or will once its pending joins push, and the repositories its
    /// remotes name.
    fn candidates(&self, request: &JoinRequest) -> Result<Vec<Candidate>, Refusal> {
        let backend = request.backend;
        let roots: BTreeSet<&String> = request.roots.iter().collect();
        let targets: Vec<CommitId> = request
            .remote_targets
            .iter()
            .filter_map(CommitId::try_from_hex)
            .collect();
        let mut candidates = vec![];
        for (id, hive) in &self.hives {
            let pending_roots = hive.pending.iter().flat_map(|pending| &pending.roots);
            let related = hive.meta.backend == backend
                && (hive
                    .index
                    .roots
                    .iter()
                    .chain(pending_roots)
                    .any(|root| roots.contains(root))
                    || has_any(backend, &hive.dir, &targets).map_err(refusal)?);
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

    /// Decides which hive a repository joins, or creates one if asked to. See
    /// [`crate::matching`].
    pub fn join(&mut self, request: &JoinRequest) -> Result<Joined, Refusal> {
        let backend = request.backend;
        let chosen = match &request.choice {
            JoinChoice::Hive(name) => Some(self.resolve(name)?),
            JoinChoice::Match | JoinChoice::Create(_) => None,
        };
        let new_name = match &request.choice {
            JoinChoice::Create(Some(name)) => {
                self.check_new_name(name)?;
                Some(name)
            }
            _ => None,
        };
        let now = Instant::now();
        for hive in self.hives.values_mut() {
            hive.pending.retain(|pending| pending.until > now);
        }
        let candidates = self.candidates(request)?;
        let joiner = Joiner {
            has_commits: !request.roots.is_empty(),
            chosen,
            create: matches!(request.choice, JoinChoice::Create(_)),
            named: new_name.is_some(),
            remotes: request
                .remotes
                .iter()
                .filter_map(|(name, url)| Some((name.clone(), RemoteUrl::parse(url)?.key())))
                .collect(),
        };
        let (id, created, reason) = match matching::decide(&joiner, &candidates) {
            Decision::Refuse(message) | Decision::Ambiguous(message) => return Err(message),
            Decision::Join { id, reason } => (id, false, reason),
            Decision::Create => {
                let name = match new_name {
                    Some(name) => name.clone(),
                    None => names::choose_name(
                        &names::name_candidates(&request.remotes, &request.dir_name),
                        |name| self.name_taken(name),
                    ),
                };
                let id = self.create(&name, backend).map_err(refusal)?;
                (id, true, "new".to_owned())
            }
        };
        let hive = self.hives.get_mut(&id).expect("chosen or created");
        hive.pending.push(Pending {
            machine: request.machine.clone(),
            urls: request.remotes.iter().map(|(_, url)| url.clone()).collect(),
            roots: request.roots.iter().cloned().collect(),
            until: now + self.pending_lifetime,
        });
        let mut info = self.info(&id).expect("chosen or created");
        let mut machines = self.hives[&id].index.machines.clone();
        machines.insert(request.machine.clone());
        info.machines = display_names(&machines);
        Ok(Joined {
            hive: info,
            created,
            reason,
        })
    }
}

/// Machines' names, as `musubi list` shows them: told apart by their keys where they are
/// alike.
fn display_names(keys: &BTreeSet<String>) -> Vec<String> {
    workspaces::display_names(keys, |_| false)
        .into_values()
        .collect()
}

/// Whether the hive's store in `dir` has any of `commits`.
fn has_any(backend: Backend, dir: &Path, commits: &[CommitId]) -> anyhow::Result<bool> {
    if commits.is_empty() {
        return Ok(false);
    }
    let missing = store::object_store(backend, dir).missing(commits)?;
    Ok(missing.len() < commits.len())
}

/// A hive's store, opened as its hub first opens it.
pub enum Opened {
    Whole(Box<HubStore>),
    /// Corrupt or torn, as said, and to be made again.
    Damaged(String),
}

/// Opens the store in `dir`: one that won't open because it is corrupt, or, if `look` says
/// to look over it, that opens but in which something is torn ([`HubStore::torn`]), is
/// damaged. Nothing tears while the hub runs, so a store need be looked over only the first
/// time a process opens it; that reads all of it. Fails if it can't tell, as when the hub
/// is out of file descriptors.
pub fn open_whole(dir: &Path, look: bool) -> anyhow::Result<Opened> {
    let store = match HubStore::open(dir) {
        Ok(store) => store,
        Err(err) if store::is_corrupt(&err) => return Ok(Opened::Damaged(err.to_string())),
        Err(err) => return Err(err.into()),
    };
    let torn = if look { store.torn()? } else { vec![] };
    Ok(if torn.is_empty() {
        Opened::Whole(Box::new(store))
    } else {
        Opened::Damaged(format!("torn: {}", torn.join("; ")))
    })
}

/// Where [`HubDir::remake`] makes hive `id` of the hub in `hub_dir` again: not a hive's
/// name, which is its id.
fn remade(hub_dir: &Path, id: &str) -> PathBuf {
    hub_dir.join(format!(".{id}.remade"))
}

/// Finishes what [`HubDir::remake`] began in the hub in `dir` before a crash: puts a hive made
/// again in place of the store it renamed away, and deletes one it never got as far as.
fn finish_remakes(dir: &Path) -> anyhow::Result<()> {
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
fn now() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_or(0, |d| d.as_secs())
}

/// The corrupt stores set aside under `removed/` in the hub in `dir`.
fn set_aside(dir: &Path) -> Vec<SetAside> {
    let Ok(entries) = fs::read_dir(dir.join("removed")) else {
        return vec![];
    };
    entries
        .flatten()
        .filter_map(|entry| {
            let name = entry.file_name().into_string().ok()?;
            let (id, stamp) = name.strip_suffix(".corrupt")?.rsplit_once('-')?;
            Some(SetAside {
                id: id.to_owned(),
                path: entry.path(),
                stamp: stamp.parse().ok()?,
            })
        })
        .collect()
}

fn write_meta(dir: &Path, meta: &HiveMeta) -> anyhow::Result<()> {
    files::replace(&dir.join(HIVE_FILE), toml::to_string(meta)?.as_bytes())?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(machine: &str, url: &str) -> JoinRequest {
        JoinRequest {
            backend: Backend::Git,
            remotes: vec![("origin".to_owned(), url.to_owned())],
            dir_name: "project".to_owned(),
            roots: vec!["11".repeat(20)],
            machine: format!("{machine}#00000000"),
            choice: JoinChoice::Match,
            remote_targets: vec![],
        }
    }

    fn creating(request: JoinRequest) -> JoinRequest {
        JoinRequest {
            choice: JoinChoice::Create(None),
            ..request
        }
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
            machines: BTreeSet::from(["alpha#00000000".to_owned()]),
            ..HiveIndex::default()
        };
        hubs.update_index(&id, pushed).unwrap();
        assert!(hubs.hives[&id].pending.is_empty());
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

    /// Machines of one name, which their keys tell apart, are listed apart, and a joining
    /// machine is listed as it will be once it has pushed.
    #[test]
    fn machines_of_one_name_are_told_apart() {
        let dir = tempfile::tempdir().unwrap();
        let mut hubs = HubDir::open(dir.path()).unwrap();
        let url = "https://example.com/a";
        let id = hubs.join(&creating(request("mac", url))).unwrap().hive.id;
        let pushed = HiveIndex {
            machines: BTreeSet::from(["mac#00000000".to_owned(), "mac#11111111".to_owned()]),
            roots: BTreeSet::from(["11".repeat(20)]),
            ..HiveIndex::default()
        };
        hubs.update_index(&id, pushed).unwrap();
        assert_eq!(hubs.info(&id).unwrap().machines, ["mac-0000", "mac-1111"]);
        let third = JoinRequest {
            choice: JoinChoice::Hive(id.clone()),
            machine: "mac#22222222".to_owned(),
            ..request("mac", url)
        };
        let joined = hubs.join(&third).unwrap();
        assert_eq!(joined.hive.machines, ["mac-0000", "mac-1111", "mac-2222"]);
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
        let hive_dir = dir.path().join(&id);
        fs::write(hive_dir.join("backend"), b"").unwrap();
        let Err(err) = HubStore::open(&hive_dir) else {
            panic!("opened a store with no backend");
        };
        assert!(store::is_corrupt(&err), "{err}");
        hubs.remake(&id, &err).unwrap();
        let store = HubStore::open(&hive_dir).unwrap();
        assert_eq!(store.backend(), Backend::Git);
        assert_eq!(store.head().0, 0);
        assert_eq!(hubs.info(&id).unwrap().name, "a");
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
        let hive_dir = dir.path().join(&id);
        fs::remove_file(hive_dir.join("index.json")).unwrap();
        let mut heads = fs::read(hive_dir.join("heads")).unwrap();
        heads.extend_from_slice(b"1 0123");
        fs::write(hive_dir.join("heads"), heads).unwrap();
        let hubs = HubDir::open(dir.path()).unwrap();
        assert_eq!(hubs.info(&id).unwrap().name, "a");
        assert_eq!(HubStore::open(&hive_dir).unwrap().head().0, 0);
        assert_eq!(set_aside(dir.path()).len(), 1);
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
        fs::rename(dir.path().join(&renamed), remade(dir.path(), &renamed)).unwrap();
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
        let (new, old) = (aside(60), aside(CORRUPT_LIFETIME.as_secs() + 60));
        for aside in [&new, &old] {
            fs::create_dir_all(aside).unwrap();
        }
        // As a hub started since finds them.
        let mut hubs = HubDir::open(dir.path()).unwrap();
        assert!(
            new.exists() && old.exists(),
            "swept before the hive was filled"
        );
        let heads = dir.path().join(&id).join("heads");
        let filled = format!(
            "{}1 {}\n",
            fs::read_to_string(&heads).unwrap(),
            "ab".repeat(64)
        );
        fs::write(&heads, filled).unwrap();
        hubs.sweep_corrupt();
        // Deleted in the background.
        let deadline = Instant::now() + Duration::from_secs(10);
        while old.exists() && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(new.exists(), "swept within a day");
        assert!(!old.exists(), "kept a day after the hive was filled");
    }
}

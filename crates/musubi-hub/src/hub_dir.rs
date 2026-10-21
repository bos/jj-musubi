//! A hub's directory: one subdirectory per hive, named by the hive's id, each holding a hub
//! store (see [`crate::store`]), the hive's `hive.toml` (its name and backend), and its
//! index (see [`crate::index`]). Removed hives move to `removed/`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::time::Duration;
use std::time::Instant;

use jj_lib::backend::CommitId;
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
use crate::store::Backend;
use crate::store::HubStore;

pub const HIVE_FILE: &str = "hive.toml";

/// A hive's `hive.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HiveMeta {
    pub name: String,
    pub backend: String,
}

/// What a joining repository tells the hub.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinRequest {
    /// A hive to join, by name, name prefix, or id.
    pub hive: Option<String>,
    /// Start a new hive (`musubi create`), rather than join one that matches.
    #[serde(default)]
    pub create: bool,
    /// The new hive's name, in place of one from the repository's remote or directory.
    /// Implies `create`.
    pub new: Option<String>,
    /// `git` or `simple`.
    pub backend: String,
    /// Names and URLs of its remotes.
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
    pub backend: String,
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
}

/// Errors that are the requester's to fix, worded for them.
pub type Refusal = String;

fn refusal(err: impl std::fmt::Display) -> Refusal {
    format!("{err:#}")
}

impl HubDir {
    /// Opens the hub directory `dir`, which must exist, rebuilding any missing index.
    pub fn open(dir: &Path) -> anyhow::Result<Self> {
        let mut hives = BTreeMap::new();
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
            let index = match HiveIndex::load(&hive_dir) {
                Some(index) => index,
                None => {
                    let index = HiveIndex::rebuild(&HubStore::open(&hive_dir)?)?;
                    index.save(&hive_dir)?;
                    index
                }
            };
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
        Ok(Self {
            dir: dir.to_owned(),
            hives,
            pending_lifetime: PENDING_LIFETIME,
        })
    }

    /// How long a join counts for matching before its first push, for tests.
    pub fn with_pending_lifetime(mut self, lifetime: Duration) -> Self {
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
        names::check_name(name).map_err(anyhow::Error::msg)?;
        anyhow::ensure!(
            !self.name_taken(name),
            "there is already a hive named {name}"
        );
        let id = Uuid::new_v4().to_string();
        let dir = self.dir.join(&id);
        HubStore::init(&dir, backend)?;
        let meta = HiveMeta {
            name: name.to_owned(),
            backend: backend.name().to_owned(),
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
            backend: hive.meta.backend.clone(),
            urls: hive.index.urls.iter().cloned().collect(),
            machines: machine_names(&hive.index.machines),
        })
    }

    pub fn list(&self) -> Vec<HiveInfo> {
        let mut hives: Vec<HiveInfo> = self.hives.keys().filter_map(|id| self.info(id)).collect();
        hives.sort_by(|a, b| a.name.cmp(&b.name));
        hives
    }

    pub fn rename(&mut self, name: &str, to: &str) -> Result<HiveInfo, Refusal> {
        names::check_name(to)?;
        let id = self.resolve(name)?;
        if self.hives[&id].meta.name == to {
            return self.info(&id).ok_or_else(|| "vanished".to_owned());
        }
        if self.name_taken(to) {
            return Err(format!("there is already a hive named {to}"));
        }
        let hive = self.hives.get_mut(&id).expect("resolved");
        let mut meta = hive.meta.clone();
        meta.name = to.to_owned();
        write_meta(&hive.dir, &meta).map_err(refusal)?;
        hive.meta = meta;
        self.info(&id).ok_or_else(|| "vanished".to_owned())
    }

    /// Takes a hive out of the hub, keeping its store under `removed/`. The caller has
    /// stopped serving it.
    pub fn remove(&mut self, id: &str) -> Result<HiveInfo, Refusal> {
        let info = self.info(id).ok_or_else(|| format!("no hive {id}"))?;
        let removed = self.dir.join("removed");
        fs::create_dir_all(&removed).map_err(refusal)?;
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(0, |d| d.as_secs());
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
        hive.index.urls.extend(index.urls);
        hive.index.roots.extend(index.roots);
        hive.index.machines = index.machines;
        hive.index.save(&hive.dir)?;
        Ok(())
    }

    /// The hive's current index, to update from its store.
    pub fn index(&self, id: &str) -> Option<HiveIndex> {
        self.hives.get(id).map(|hive| hive.index.clone())
    }

    /// Decides which hive a repository joins, or creates one if asked to. See
    /// [`crate::matching`].
    pub fn join(&mut self, request: &JoinRequest) -> Result<Joined, Refusal> {
        let backend = Backend::parse(&request.backend).map_err(refusal)?;
        let chosen = request
            .hive
            .as_deref()
            .map(|name| self.resolve(name))
            .transpose()?;
        if let Some(name) = &request.new {
            names::check_name(name)?;
            if self.name_taken(name) {
                return Err(format!("there is already a hive named {name}"));
            }
        }
        let now = Instant::now();
        for hive in self.hives.values_mut() {
            hive.pending.retain(|pending| pending.until > now);
        }
        let roots: BTreeSet<&String> = request.roots.iter().collect();
        let targets: Vec<CommitId> = request
            .remote_targets
            .iter()
            .filter_map(CommitId::try_from_hex)
            .collect();
        let mut candidates = vec![];
        for (id, hive) in &self.hives {
            let pending_roots = hive.pending.iter().flat_map(|pending| &pending.roots);
            let related = hive.meta.backend == backend.name()
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
        let joiner = Joiner {
            has_commits: !request.roots.is_empty(),
            chosen,
            create: request.create || request.new.is_some(),
            named: request.new.is_some(),
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
                let name = match &request.new {
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
        let joining = workspaces::machine_name(&request.machine).to_owned();
        let mut machines: BTreeSet<String> = info.machines.into_iter().collect();
        machines.insert(joining);
        info.machines = machines.into_iter().collect();
        Ok(Joined {
            hive: info,
            created,
            reason,
        })
    }
}

fn machine_names(keys: &BTreeSet<String>) -> Vec<String> {
    keys.iter()
        .map(|key| workspaces::machine_name(key).to_owned())
        .collect()
}

/// Whether the hive's store in `dir` has any of `commits`.
fn has_any(backend: Backend, dir: &Path, commits: &[CommitId]) -> anyhow::Result<bool> {
    if commits.is_empty() {
        return Ok(false);
    }
    let missing = backend.object_store(dir).missing(commits)?;
    Ok(missing.len() < commits.len())
}

fn write_meta(dir: &Path, meta: &HiveMeta) -> anyhow::Result<()> {
    let tmp = tempfile::NamedTempFile::new_in(dir)?;
    fs::write(tmp.path(), toml::to_string(meta)?)?;
    tmp.persist(dir.join(HIVE_FILE))?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(machine: &str, url: &str) -> JoinRequest {
        JoinRequest {
            backend: "git".to_owned(),
            remotes: vec![("origin".to_owned(), url.to_owned())],
            dir_name: "project".to_owned(),
            roots: vec!["11".repeat(20)],
            machine: format!("{machine}#00000000"),
            ..JoinRequest::default()
        }
    }

    fn creating(request: JoinRequest) -> JoinRequest {
        JoinRequest {
            create: true,
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
}

//! The git backend's objects: packfiles built and indexed by the `git` binary, which jj
//! already requires for fetch and push, plus the backend extras jj cannot derive from them.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::fs::File;
use std::io;
use std::io::Write as _;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;
use std::process::Stdio;
use std::thread;

use jj_lib::backend::CommitId;
use jj_lib::git_backend::CHANGE_ID_COMMIT_HEADER;
use jj_lib::git_backend::GitBackend;
use jj_lib::git_backend::JJ_TREES_COMMIT_HEADER;
use jj_lib::git_backend::synthetic_change_id_from_git_commit_id;
use jj_lib::object_id::ObjectId as _;
use jj_lib::stacked_table::TableSegment as _;
use jj_lib::stacked_table::TableStore;
use prost::Message as _;

use super::ObjectError;
use super::ObjectStore;
use super::bundle;
use super::bundle::BundleWriter;
use super::bundle::Record;
use crate::hive_settings::Remote;

/// A git object database, driven through the `git` binary.
pub struct GitObjects {
    git_dir: PathBuf,
}

impl GitObjects {
    /// `git_dir` is the `.git` directory, or the repository itself if it is bare.
    pub fn new(git_dir: &Path) -> Self {
        Self {
            git_dir: git_dir.to_owned(),
        }
    }

    pub fn git_dir(&self) -> &Path {
        &self.git_dir
    }

    /// Creates a bare repository for a hub. git never garbage-collects it on its own: the
    /// hub decides what is unreferenced, not git, and a hub's repository has no refs. Only
    /// [`Self::maintain`] consolidates it.
    pub fn init_bare(git_dir: &Path) -> Result<Self, ObjectError> {
        // Not through `run`: GIT_DIR must not be set when the repository does not exist yet.
        let args = ["init", "--quiet", "--bare"];
        let output = Command::new("git")
            .args(args)
            .arg(git_dir)
            .output()
            .map_err(|source| spawn_err(&args, source))?;
        check_status(&args, &output)?;
        let objects = Self::new(git_dir);
        objects.run(&["config", "gc.auto", "0"], None)?;
        Ok(objects)
    }

    /// The remotes in this repository's own git config, with their URLs.
    pub fn remotes(&self) -> Result<BTreeMap<String, Remote>, ObjectError> {
        let output = self.run(&["config", "--local", "--list"], None)?;
        let mut remotes: BTreeMap<String, Remote> = BTreeMap::new();
        for line in String::from_utf8_lossy(&output).lines() {
            let Some((key, value)) = line.split_once('=') else {
                continue;
            };
            let Some((name, variable)) = key
                .strip_prefix("remote.")
                .and_then(|rest| rest.rsplit_once('.'))
            else {
                continue;
            };
            let remote = remotes.entry(name.to_owned()).or_default();
            match variable {
                "url" => remote.url = Some(value.to_owned()),
                "pushurl" => remote.push_url = Some(value.to_owned()),
                _ => {}
            }
        }
        Ok(remotes)
    }

    /// Changes this repository's git remotes from `from` to `to`, as `git remote` does:
    /// renaming a remote moves its remote-tracking refs, and removing one deletes them.
    pub fn change_remotes(
        &self,
        from: &BTreeMap<String, Remote>,
        to: &BTreeMap<String, Remote>,
    ) -> Result<(), ObjectError> {
        let mut removed: Vec<&String> = from.keys().filter(|n| !to.contains_key(*n)).collect();
        for (name, remote) in to {
            match from.get(name) {
                Some(old) if old == remote => continue,
                Some(_) => {}
                None => {
                    // The same remote under a new name is a rename.
                    if let Some(position) = removed.iter().position(|old| from[*old] == *remote) {
                        let old = removed.remove(position);
                        self.run(&["remote", "rename", old, name], None)?;
                        continue;
                    }
                    let url = remote.url.as_deref().unwrap_or_default();
                    self.run(&["remote", "add", name, url], None)?;
                }
            }
            self.set_remote_urls(name, remote)?;
        }
        for name in removed {
            self.run(&["remote", "remove", name], None)?;
        }
        Ok(())
    }

    fn set_remote_urls(&self, name: &str, remote: &Remote) -> Result<(), ObjectError> {
        for (variable, value) in [("url", &remote.url), ("pushurl", &remote.push_url)] {
            let key = format!("remote.{name}.{variable}");
            match value {
                Some(value) => self.run(&["config", "--local", &key, value], None)?,
                // Unsetting a variable that isn't set fails; that's fine.
                None => self
                    .run(&["config", "--local", "--unset-all", &key], None)
                    .unwrap_or_default(),
            };
        }
        Ok(())
    }

    /// The subset of `ids` not present in the object database.
    pub fn missing(&self, ids: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        if ids.is_empty() {
            return Ok(vec![]);
        }
        let input = hex_lines(ids.iter(), "");
        let output = self.run(&["cat-file", "--batch-check=%(objectname)"], Some(input))?;
        Ok(String::from_utf8_lossy(&output)
            .lines()
            .filter_map(|line| line.strip_suffix(" missing"))
            .filter_map(CommitId::try_from_hex)
            .collect())
    }

    /// Commits reachable from `wants` but not from `haves`.
    pub fn commits_between(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<Vec<CommitId>, ObjectError> {
        if wants.is_empty() {
            return Ok(vec![]);
        }
        let output = self.run(&["rev-list", "--stdin"], Some(revs_input(wants, haves)))?;
        Ok(String::from_utf8_lossy(&output)
            .lines()
            .filter_map(CommitId::try_from_hex)
            .collect())
    }

    /// Writes a thin pack of everything reachable from `wants` but not from `haves` to
    /// `out`. The receiver must have every object reachable from `haves`.
    pub fn write_pack(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
        out: &Path,
    ) -> Result<(), ObjectError> {
        let args = [
            "pack-objects",
            "--revs",
            "--thin",
            "--stdout",
            "--delta-base-offset",
            "-q",
        ];
        let mut child = self
            .command(&args)
            .stdin(Stdio::piped())
            .stdout(File::create(out)?)
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| spawn_err(&args, source))?;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        let input = revs_input(wants, haves);
        let writer = thread::spawn(move || stdin.write_all(&input));
        let output = child.wait_with_output()?;
        writer.join().expect("stdin writer panicked")?;
        check_status(&args, &output)
    }

    /// Stores a received pack's objects, completing a thin pack from local objects. As
    /// `git fetch` does by default, a pack of fewer than `UNPACK_LIMIT` objects is unpacked
    /// into loose objects rather than kept, so that small transfers don't each leave a pack
    /// behind: they slow git down, and jj-lib's gix sizes its table of packs only when it
    /// opens the repository.
    pub fn receive_pack(&self, pack: &Path) -> Result<(), ObjectError> {
        let args: &[&str] = if pack_object_count(pack)? < UNPACK_LIMIT {
            &["unpack-objects", "-q"]
        } else {
            &["index-pack", "--stdin", "--fix-thin"]
        };
        let output = self
            .command(args)
            .stdin(File::open(pack)?)
            .output()
            .map_err(|source| spawn_err(args, source))?;
        check_status(args, &output)
    }

    /// Consolidates packs and loose objects once there are enough of them, as git itself
    /// does after a fetch, with `git gc --auto` and the repository's own thresholds. It
    /// never deletes an object, reachable or not: jj's `refs/jj/keep` refs need not cover
    /// every commit an operation refers to, and a hub's repository has no refs at all. git
    /// may finish in the background.
    pub fn maintain(&self, hub: bool) -> Result<(), ObjectError> {
        let mut args = vec![
            "-c",
            "gc.pruneExpire=never",
            "-c",
            "gc.worktreePruneExpire=never",
        ];
        if hub {
            // A hub's objects are all unreachable to git: keep them in a cruft pack rather
            // than loose, and override the hub's own `gc.auto 0`.
            args.extend(["-c", "gc.cruftPacks=true", "-c", "gc.auto=6700"]);
        }
        args.extend(["gc", "--auto", "--quiet"]);
        self.run(&args, None)?;
        Ok(())
    }

    /// Fails unless every object reachable from `wants` is present, assuming everything
    /// reachable from `haves` is.
    pub fn check_connected(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<(), ObjectError> {
        if wants.is_empty() {
            return Ok(());
        }
        match self.run(
            &["rev-list", "--objects", "--quiet", "--stdin"],
            Some(revs_input(wants, haves)),
        ) {
            Ok(_) => Ok(()),
            Err(ObjectError::Git { stderr, .. }) => Err(ObjectError::NotConnected(stderr)),
            Err(err) => Err(err),
        }
    }

    /// Protects commits from `git gc` with refs under `namespace`, the way jj's
    /// `refs/jj/keep/` refs do.
    pub fn keep(&self, namespace: &str, ids: &[CommitId]) -> Result<(), ObjectError> {
        let mut input = String::new();
        for id in ids {
            writeln!(input, "update {namespace}{0} {0}", id.hex()).expect("writing to a String");
        }
        self.run(&["update-ref", "--stdin"], Some(input.into_bytes()))?;
        Ok(())
    }

    fn command(&self, args: &[&str]) -> Command {
        let mut command = Command::new("git");
        // Running inside the repository as well as naming it keeps a mistake from ever
        // touching the caller's working directory.
        command
            .current_dir(&self.git_dir)
            .env("GIT_DIR", &self.git_dir)
            .args(args);
        command
    }

    fn run(&self, args: &[&str], input: Option<Vec<u8>>) -> Result<Vec<u8>, ObjectError> {
        let mut child = self
            .command(args)
            .stdin(if input.is_some() {
                Stdio::piped()
            } else {
                Stdio::null()
            })
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| spawn_err(args, source))?;
        let writer = input.map(|input| {
            let mut stdin = child.stdin.take().expect("stdin is piped");
            thread::spawn(move || stdin.write_all(&input))
        });
        let output = child.wait_with_output()?;
        if let Some(writer) = writer {
            // A failing git may close stdin early; its exit status explains why.
            writer.join().expect("stdin writer panicked").ok();
        }
        check_status(args, &output)?;
        Ok(output.stdout)
    }
}

/// `fetch.unpackLimit`'s default: received packs with fewer objects are unpacked.
const UNPACK_LIMIT: u32 = 100;

/// The number of objects a pack holds, from its header. Anything that isn't a pack counts
/// as large, so that `git index-pack` reports what is wrong with it.
fn pack_object_count(pack: &Path) -> Result<u32, ObjectError> {
    let mut header = [0; 12];
    let mut file = File::open(pack)?;
    if io::Read::read_exact(&mut file, &mut header).is_err() || &header[..4] != b"PACK" {
        return Ok(u32::MAX);
    }
    Ok(u32::from_be_bytes([
        header[8], header[9], header[10], header[11],
    ]))
}

fn hex_lines<'a>(ids: impl Iterator<Item = &'a CommitId>, prefix: &str) -> Vec<u8> {
    let mut lines = String::new();
    for id in ids {
        writeln!(lines, "{prefix}{}", id.hex()).expect("writing to a String");
    }
    lines.into_bytes()
}

fn revs_input(wants: &[CommitId], haves: &[CommitId]) -> Vec<u8> {
    let mut input = hex_lines(wants.iter(), "");
    input.extend(hex_lines(haves.iter(), "^"));
    input
}

fn spawn_err(args: &[&str], source: io::Error) -> ObjectError {
    ObjectError::Spawn {
        args: args.join(" "),
        source,
    }
}

fn check_status(args: &[&str], output: &std::process::Output) -> Result<(), ObjectError> {
    if output.status.success() {
        Ok(())
    } else {
        Err(ObjectError::Git {
            args: args.join(" "),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        })
    }
}

/// A backend extras entry that a receiver could not derive from the commit object alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExtrasEntry {
    pub commit: CommitId,
    /// The encoded `git_store.Commit` from the sender's extras table.
    pub value: Vec<u8>,
}

/// Returns the extras entries for `commits` that differ from what jj would derive from the
/// commit objects: change ids of commits without a `change-id` header that were not derived
/// from the commit id, and conflicts written before the `jj:trees` header existed.
pub fn extras_to_ship(
    store_path: &Path,
    git_repo: &gix::Repository,
    commits: &[CommitId],
) -> Result<Vec<ExtrasEntry>, ObjectError> {
    let table_store = extras_table_store(store_path, git_repo);
    let table = table_store.get_head()?;
    let mut entries = vec![];
    for commit in commits {
        let Some(value) = table.get_value(commit.as_bytes()) else {
            continue;
        };
        let extras = jj_lib::protos::git_store::Commit::decode(value)
            .map_err(|_| ObjectError::MalformedExtras(commit.hex()))?;
        let read_err = || ObjectError::ReadCommit(commit.hex());
        let oid = gix::ObjectId::try_from(commit.as_bytes()).map_err(|_| read_err())?;
        let object = git_repo.find_object(oid).map_err(|_| read_err())?;
        let git_commit = object.try_to_commit_ref().map_err(|_| read_err())?;
        let header = |name: &str| git_commit.extra_headers().find(name).is_some();
        let derived_change_id = synthetic_change_id_from_git_commit_id(commit);
        let change_id_derivable = header(CHANGE_ID_COMMIT_HEADER)
            || extras.change_id.is_empty()
            || extras.change_id == derived_change_id.as_bytes();
        let conflict_derivable = extras.root_tree.is_empty() || header(JJ_TREES_COMMIT_HEADER);
        if !(change_id_derivable && conflict_derivable) {
            entries.push(ExtrasEntry {
                commit: commit.clone(),
                value: value.to_vec(),
            });
        }
    }
    Ok(entries)
}

/// Writes received extras entries that are not already present. Call this before jj first
/// reads the commits, because jj derives and saves its own entries on first read.
pub fn import_extras(
    store_path: &Path,
    git_repo: &gix::Repository,
    entries: &[ExtrasEntry],
) -> Result<(), ObjectError> {
    if entries.is_empty() {
        return Ok(());
    }
    let table_store = extras_table_store(store_path, git_repo);
    let (table, _lock) = table_store.get_head_locked()?;
    let mut mut_table = table.start_mutation();
    for entry in entries {
        if mut_table.get_value(entry.commit.as_bytes()).is_none() {
            mut_table.add_entry(entry.commit.to_bytes(), entry.value.clone());
        }
    }
    table_store.save_table(mut_table)?;
    Ok(())
}

fn extras_table_store(store_path: &Path, git_repo: &gix::Repository) -> TableStore {
    TableStore::load(
        store_path.join("extra"),
        git_repo.object_hash().len_in_bytes(),
    )
}

/// Where a [`GitStore`] keeps backend extras.
pub enum Extras<'a> {
    /// A node's jj repository: the extras table, maintained through jj-lib.
    Jj {
        store_path: PathBuf,
        backend: &'a GitBackend,
    },
    /// A hub: one file per commit, named by its id.
    Files(PathBuf),
}

/// The objects of a git-backed hive, in a node's repository or a hub's bare repository.
pub struct GitStore<'a> {
    git: GitObjects,
    extras: Extras<'a>,
}

impl<'a> GitStore<'a> {
    /// A node's repository. `store_path` is `.jj/repo/store`.
    pub fn for_node(store_path: &Path, backend: &'a GitBackend) -> Self {
        Self {
            git: GitObjects::new(backend.git_repo_path()),
            extras: Extras::Jj {
                store_path: store_path.to_owned(),
                backend,
            },
        }
    }

    /// A hub's bare repository and extras directory.
    pub fn for_hub(git_dir: &Path, extras_dir: &Path) -> Self {
        Self {
            git: GitObjects::new(git_dir),
            extras: Extras::Files(extras_dir.to_owned()),
        }
    }

    pub fn git(&self) -> &GitObjects {
        &self.git
    }

    fn extras_for(&self, commits: &[CommitId]) -> Result<Vec<ExtrasEntry>, ObjectError> {
        match &self.extras {
            Extras::Jj {
                store_path,
                backend,
            } => extras_to_ship(store_path, &backend.git_repo(), commits),
            Extras::Files(dir) => {
                let mut entries = vec![];
                for commit in commits {
                    match fs::read(dir.join(commit.hex())) {
                        Ok(value) => entries.push(ExtrasEntry {
                            commit: commit.clone(),
                            value,
                        }),
                        Err(err) if err.kind() == io::ErrorKind::NotFound => {}
                        Err(err) => return Err(err.into()),
                    }
                }
                Ok(entries)
            }
        }
    }

    fn store_extras(&self, entries: &[ExtrasEntry]) -> Result<(), ObjectError> {
        match &self.extras {
            Extras::Jj {
                store_path,
                backend,
            } => import_extras(store_path, &backend.git_repo(), entries),
            Extras::Files(dir) => {
                for entry in entries {
                    let path = dir.join(entry.commit.hex());
                    if !path.exists() {
                        let tmp = tempfile::NamedTempFile::new_in(dir)?;
                        fs::write(tmp.path(), &entry.value)?;
                        tmp.persist(&path).map_err(|err| err.error)?;
                    }
                }
                Ok(())
            }
        }
    }
}

impl ObjectStore for GitStore<'_> {
    fn missing(&self, commits: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        self.git.missing(commits)
    }

    fn check_connected(&self, wants: &[CommitId], haves: &[CommitId]) -> Result<(), ObjectError> {
        self.git.check_connected(wants, haves)
    }

    fn export(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
        out: &Path,
    ) -> Result<(), ObjectError> {
        let absent = self.git.missing(haves)?;
        let haves: Vec<CommitId> = haves
            .iter()
            .filter(|id| !absent.contains(id))
            .cloned()
            .collect();
        let mut writer = BundleWriter::create(out)?;
        let commits = self.git.commits_between(wants, &haves)?;
        for entry in self.extras_for(&commits)? {
            writer.extras(entry.commit.as_bytes(), &entry.value)?;
        }
        let pack = tempfile::NamedTempFile::new()?;
        self.git.write_pack(wants, &haves, pack.path())?;
        writer.pack(pack.path())?;
        writer.finish()
    }

    fn import(
        &self,
        bundle_path: &Path,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<(), ObjectError> {
        let mut extras = vec![];
        let mut packs = vec![];
        bundle::read(bundle_path, |record| {
            match record {
                Record::Extras { commit, value } => {
                    extras.push(ExtrasEntry {
                        commit: CommitId::new(commit),
                        value,
                    });
                }
                Record::Pack(file) => packs.push(file),
                Record::Object { .. } | Record::View { .. } | Record::Operation { .. } => {
                    return Err(ObjectError::MalformedBundle(
                        "unexpected record in a git object bundle".to_owned(),
                    ));
                }
            }
            Ok(())
        })?;
        // Extras first: jj derives and saves its own entries the first time it reads a
        // commit, and those must not win over the sender's.
        self.store_extras(&extras)?;
        for pack in &packs {
            self.git.receive_pack(pack.path())?;
        }
        self.git.check_connected(wants, haves)?;
        if let Extras::Jj { backend, .. } = &self.extras {
            backend.import_head_commits(wants)?;
        }
        self.git.maintain(matches!(self.extras, Extras::Files(_)))
    }
}

//! The git backend's objects: packfiles built and indexed by the `git` binary, which jj
//! already requires for fetch and push, plus the backend extras jj cannot derive from them.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::io;
use std::io::Write;
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
use super::bundle::PackRecord;
use super::bundle::Record;
use super::power;
use crate::git_command::GitError;
use crate::git_command::GitRepo;
use crate::git_command::check_status;
use crate::git_command::git;
use crate::git_command::run_err;

/// Where a hub's repository names the commits its head requires (see
/// [`GitObjects::mark_head`]).
const HEAD_REFS: &str = "refs/musubi/head/";

/// How many objects a hub's repository holds before a bitmap index is worth writing.
const BITMAP_AFTER: u64 = 10_000;

/// How long a hub without a bitmap index waits before looking into writing one again.
const BITMAP_RETRY: std::time::Duration = std::time::Duration::from_secs(3600);

/// Why a repository lacks history that musubi would need to send: everything an operation
/// requires, which the hub accepts only whole.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Incompleteness {
    /// A shallow clone, without the history below its shallow commits.
    Shallow,
    /// A partial clone, which leaves objects for its promisor remote to supply on demand.
    Partial,
}

impl std::fmt::Display for Incompleteness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Shallow => "a shallow clone",
            Self::Partial => "a partial clone",
        })
    }
}

/// A git object database, driven through the `git` binary.
pub struct GitObjects {
    repo: GitRepo,
}

impl GitObjects {
    /// `executable` is the git to run, and `git_dir` the `.git` directory, or the repository
    /// itself if it is bare.
    pub fn new(executable: &Path, git_dir: &Path) -> Self {
        Self {
            repo: GitRepo::new(executable, git_dir),
        }
    }

    pub fn git_dir(&self) -> &Path {
        self.repo.git_dir()
    }

    /// Creates a bare repository for a hub. git never garbage-collects it on its own: the
    /// hub decides what is unreferenced, not git, and its only refs, under
    /// `refs/musubi/head/`, are for git's bitmap index (see [`Self::mark_head`]). Only
    /// [`Self::maintain`] and [`Self::mark_head`] consolidate it.
    pub fn init_bare(executable: &Path, git_dir: &Path) -> Result<Self, ObjectError> {
        // Not through `run`: GIT_DIR must not be set when the repository does not exist yet.
        let args = ["init", "--quiet", "--bare"];
        let output = git(executable)
            .args(args)
            .arg(git_dir)
            .output()
            .map_err(|source| run_err(&args, source))?;
        check_status(&args, &output)?;
        let objects = Self::new(executable, git_dir);
        objects.run(&["config", "gc.auto", "0"], None)?;
        Ok(objects)
    }

    /// What this repository lacks of its history, if anything: a shallow clone has a
    /// `shallow` file listing its shallow commits, in the common directory of a linked
    /// worktree, and a partial clone a promisor remote.
    pub fn incompleteness(&self) -> Result<Option<Incompleteness>, ObjectError> {
        let common = match fs::read_to_string(self.git_dir().join("commondir")) {
            Ok(dir) => self.git_dir().join(dir.trim()),
            Err(_) => self.git_dir().to_owned(),
        };
        if fs::metadata(common.join("shallow")).is_ok_and(|shallow| shallow.len() > 0) {
            return Ok(Some(Incompleteness::Shallow));
        }
        let output = self.run(&["config", "--local", "--list"], None)?;
        let partial = String::from_utf8_lossy(&output).lines().any(|line| {
            // A boolean with no value is true.
            let (key, value) = line.split_once('=').unwrap_or((line, "true"));
            key == "extensions.partialclone"
                || key.starts_with("remote.")
                    && key.ends_with(".promisor")
                    && !["false", "no", "off", "0", ""]
                        .contains(&value.to_ascii_lowercase().as_str())
        });
        Ok(partial.then_some(Incompleteness::Partial))
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

    /// Parentless commits reachable from `wants` but not from `haves`.
    pub fn roots(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<Vec<CommitId>, ObjectError> {
        if wants.is_empty() {
            return Ok(vec![]);
        }
        let output = self.run(
            &["rev-list", "--max-parents=0", "--stdin"],
            Some(revs_input(wants, haves)),
        )?;
        Ok(String::from_utf8_lossy(&output)
            .lines()
            .filter_map(CommitId::try_from_hex)
            .collect())
    }

    /// Writes a thin pack of everything reachable from `wants` but not from `haves` to
    /// `out`, as git produces it. The receiver must have every object reachable from
    /// `haves`.
    pub fn write_pack(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
        out: &mut dyn Write,
    ) -> Result<(), ObjectError> {
        let mut args = vec![];
        if !haves.is_empty() {
            // With a bitmap index, git skips the walk that finds what the receiver has to
            // make deltas against, so an object with no delta stored, as one pushed a moment
            // ago often is, would go whole: hundreds of kilobytes for a small edit to a large
            // file. Counting is quick when there is something to leave out, so the index is
            // only for clones.
            args.extend(["-c", "pack.useBitmaps=false"]);
        }
        args.extend([
            "pack-objects",
            "--revs",
            "--thin",
            "--stdout",
            "--delta-base-offset",
            "-q",
        ]);
        let mut child = self
            .command(&args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| run_err(&args, source))?;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        let input = revs_input(wants, haves);
        let writer = thread::spawn(move || stdin.write_all(&input));
        let mut stderr = child.stderr.take().expect("stderr is piped");
        let errors = thread::spawn(move || {
            let mut bytes = vec![];
            io::Read::read_to_end(&mut stderr, &mut bytes).map(|_| bytes)
        });
        let copied = io::copy(&mut child.stdout.take().expect("stdout is piped"), out);
        let status = child.wait().map_err(|source| run_err(&args, source))?;
        writer.join().expect("stdin writer panicked")?;
        let stderr = errors.join().expect("stderr reader panicked")?;
        copied?;
        check_status(
            &args,
            &std::process::Output {
                status,
                stdout: vec![],
                stderr,
            },
        )?;
        Ok(())
    }

    /// Stores a received pack's objects, completing a thin pack from local objects. As
    /// `git fetch` does by default, a pack of fewer than `UNPACK_LIMIT` objects is unpacked
    /// into loose objects rather than kept, so that small transfers don't each leave a pack
    /// behind: they slow git down, and jj-lib's gix sizes its table of packs only when it
    /// opens the repository. The pack goes to git straight from the bundle.
    pub fn receive_pack(&self, pack: &PackRecord) -> Result<(), ObjectError> {
        let mut reader = pack.reader()?;
        let mut header = vec![];
        io::Read::read_to_end(&mut io::Read::take(&mut reader, 12), &mut header)?;
        let args: &[&str] = if pack_object_count(&header) < UNPACK_LIMIT {
            &["unpack-objects", "-q"]
        } else {
            &["index-pack", "--stdin", "--fix-thin"]
        };
        let mut input = io::Read::chain(io::Cursor::new(header), reader);
        let mut child = self
            .command(args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|source| run_err(args, source))?;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        let writer = thread::spawn(move || io::copy(&mut input, &mut stdin));
        let output = child
            .wait_with_output()
            .map_err(|source| run_err(args, source))?;
        // A failing git may close stdin early; its exit status explains why.
        writer.join().expect("stdin writer panicked").ok();
        check_status(args, &output)?;
        Ok(())
    }

    /// Consolidates packs and loose objects once there are enough of them, as git itself
    /// does after a fetch, with `git gc --auto` and the repository's own thresholds. It
    /// never deletes an object, reachable or not: jj's `refs/jj/keep` refs need not cover
    /// every commit an operation refers to, and a hub's refs cover only its head. git may
    /// finish in the background. On battery it waits for an import on mains power.
    pub fn maintain(&self, hub: bool) -> Result<(), ObjectError> {
        if power::on_battery() {
            return Ok(());
        }
        self.gc_auto(hub)
    }

    fn gc_auto(&self, hub: bool) -> Result<(), ObjectError> {
        let mut args = vec![
            "-c",
            "gc.pruneExpire=never",
            "-c",
            "gc.worktreePruneExpire=never",
        ];
        if hub {
            // Much of a hub's history is unreachable to git: keep it in a cruft pack rather
            // than loose, and override the hub's own `gc.auto 0`.
            args.extend(["-c", "gc.cruftPacks=true", "-c", "gc.auto=6700"]);
        }
        args.extend(["gc", "--auto", "--quiet"]);
        // git finishes `gc --auto` in the background (`gc.autoDetach`, true by default), but
        // can't on Windows, where whatever triggered it would wait for the whole repack.
        // Start it there without waiting, unless `gc.autoDetach` is false, as git would.
        if self.gc_in_background(&args)? {
            return Ok(());
        }
        self.run(&args, None)?;
        Ok(())
    }

    /// Starts `args` without waiting, if git would run it in the background, and says whether
    /// it did.
    #[cfg(windows)]
    fn gc_in_background(&self, args: &[&str]) -> Result<bool, ObjectError> {
        if !self.auto_detach()? {
            return Ok(false);
        }
        // Nothing waits for it, so as with git's own detached gc a failure goes unreported,
        // and the next `gc --auto` tries again.
        let mut command = self.command(args);
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        detach(&mut command);
        command.spawn().map_err(|source| run_err(args, source))?;
        Ok(true)
    }

    /// git detaches `gc --auto` itself here.
    #[cfg(not(windows))]
    fn gc_in_background(&self, _args: &[&str]) -> Result<bool, ObjectError> {
        Ok(false)
    }

    /// Whether git would run `gc --auto` in the background: `gc.autoDetach`, true by default.
    #[cfg(windows)]
    fn auto_detach(&self) -> Result<bool, ObjectError> {
        let value = self.run(
            &[
                "config",
                "--type=bool",
                "--default=true",
                "--get",
                "gc.autoDetach",
            ],
            None,
        )?;
        Ok(String::from_utf8_lossy(&value).trim() != "false")
    }

    /// Makes the refs under `refs/musubi/head/` name exactly `commits`, the visible heads of
    /// a hub's accepted head, so that git can index what they reach; nothing else on a hub
    /// refers to anything. The refs are the hub's own: what it sends nodes never includes
    /// refs, so jj never sees them. Then, unless the repository has a bitmap index, or is
    /// too small for one to matter, or tried to write one within the hour, starts a full
    /// `git gc` in the background to write one: with it, counting what a clone needs takes
    /// a fraction of the time ([`Self::write_pack`] uses it only for clones). Later full
    /// repacks, once `git gc --auto` finds enough packs, write a fresh one. Like
    /// [`Self::maintain`], the gc never deletes an object: what no ref reaches goes to a
    /// cruft pack.
    pub fn mark_head(&self, commits: &[CommitId]) -> Result<(), ObjectError> {
        let listed = self.run(&["for-each-ref", "--format=%(refname)", HEAD_REFS], None)?;
        let existing: BTreeSet<String> = String::from_utf8_lossy(&listed)
            .lines()
            .map(str::to_owned)
            .collect();
        // The root commit isn't a git object.
        let wanted: BTreeSet<String> = commits
            .iter()
            .filter(|commit| commit.as_bytes().iter().any(|&b| b != 0))
            .map(|commit| format!("{HEAD_REFS}{}", commit.hex()))
            .collect();
        let mut input = String::new();
        for name in wanted.difference(&existing) {
            let id = name.strip_prefix(HEAD_REFS).expect("named above");
            writeln!(input, "create {name} {id}").expect("writing to a String");
        }
        for name in existing.difference(&wanted) {
            writeln!(input, "delete {name}").expect("writing to a String");
        }
        if !input.is_empty() {
            self.run(&["update-ref", "--stdin"], Some(input.into_bytes()))?;
        }
        // Looked into at most hourly, since counting objects takes a moment, and a large
        // repository on a small machine may fail to write a bitmap index every time.
        let checked = self.git_dir().join("musubi-bitmap-checked");
        let recently = fs::metadata(&checked)
            .and_then(|meta| meta.modified())
            .is_ok_and(|at| at.elapsed().is_ok_and(|age| age < BITMAP_RETRY));
        if wanted.is_empty() || recently || self.has_bitmap()? {
            return Ok(());
        }
        fs::write(&checked, b"")?;
        if self.packed_objects()? >= BITMAP_AFTER {
            self.gc_for_bitmap()?;
        }
        Ok(())
    }

    fn has_bitmap(&self) -> Result<bool, ObjectError> {
        let dir = self.git_dir().join("objects/pack");
        let entries = match fs::read_dir(&dir) {
            Ok(entries) => entries,
            Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(false),
            Err(err) => return Err(err.into()),
        };
        for entry in entries {
            let name = entry?.file_name();
            let name = name.to_string_lossy();
            // Not a temporary one a killed gc left.
            if (name.starts_with("pack-") || name.starts_with("multi-pack-index-"))
                && name.ends_with(".bitmap")
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// How many objects the repository's packs hold.
    fn packed_objects(&self) -> Result<u64, ObjectError> {
        let output = self.run(&["count-objects", "-v"], None)?;
        Ok(String::from_utf8_lossy(&output)
            .lines()
            .find_map(|line| line.strip_prefix("in-pack: "))
            .and_then(|count| count.trim().parse().ok())
            .unwrap_or(0))
    }

    /// Starts a full `git gc` that writes a bitmap index, without waiting for it. git's own
    /// lock keeps two from running at once; one that fails is logged, and an accepted head
    /// tries again after [`BITMAP_RETRY`]. What git says goes to a file, not a pipe, so that
    /// the hub's exiting doesn't stop it partway.
    fn gc_for_bitmap(&self) -> Result<(), ObjectError> {
        let args = [
            "-c",
            "gc.pruneExpire=never",
            "-c",
            "gc.worktreePruneExpire=never",
            "-c",
            "gc.cruftPacks=true",
            "-c",
            "repack.writeBitmaps=true",
            "gc",
            "--quiet",
        ];
        let log = self.git_dir().join("musubi-bitmap-gc.log");
        let mut command = self.command(&args);
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(fs::File::create(&log)?);
        detach(&mut command);
        let mut child = command.spawn().map_err(|source| run_err(&args, source))?;
        let dir = self.git_dir().to_owned();
        // Waited for, so that it never lingers as a zombie, and so that a failure is heard.
        thread::Builder::new()
            .name("bitmap gc".to_owned())
            .spawn(move || match child.wait() {
                Ok(status) if status.success() => {}
                Ok(status) => tracing::warn!(
                    "writing a bitmap index in {}: git gc failed ({status}): {}",
                    dir.display(),
                    fs::read_to_string(&log).unwrap_or_default().trim()
                ),
                Err(err) => tracing::warn!("writing a bitmap index in {}: {err}", dir.display()),
            })?;
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
            Err(ObjectError::Git(GitError::Failed { stderr, .. })) => {
                Err(ObjectError::NotConnected(stderr))
            }
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
        self.repo.command(args)
    }

    fn run(&self, args: &[&str], input: Option<Vec<u8>>) -> Result<Vec<u8>, ObjectError> {
        Ok(self.repo.run(args, input)?)
    }
}

/// Starts `command` apart from whatever started this process, so that Ctrl-C there doesn't
/// stop it partway (git copes if something does, and repacks next time).
#[cfg(unix)]
fn detach(command: &mut Command) {
    use std::os::unix::process::CommandExt as _;
    command.process_group(0);
}

#[cfg(windows)]
fn detach(command: &mut Command) {
    use std::os::windows::process::CommandExt as _;
    const CREATE_NEW_PROCESS_GROUP: u32 = 0x0000_0200;
    const CREATE_NO_WINDOW: u32 = 0x0800_0000;
    command.creation_flags(CREATE_NEW_PROCESS_GROUP | CREATE_NO_WINDOW);
}

/// `fetch.unpackLimit`'s default: received packs with fewer objects are unpacked.
const UNPACK_LIMIT: u32 = 100;

/// The number of objects a pack holds, from its 12-byte header. Anything that isn't a pack
/// counts as large, so that `git index-pack` reports what is wrong with it.
fn pack_object_count(header: &[u8]) -> u32 {
    match header {
        [b'P', b'A', b'C', b'K', _, _, _, _, a, b, c, d] => u32::from_be_bytes([*a, *b, *c, *d]),
        _ => u32::MAX,
    }
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
    /// A node's repository, with the git it runs. `store_path` is `.jj/repo/store`.
    pub fn for_node(executable: &Path, store_path: &Path, backend: &'a GitBackend) -> Self {
        Self {
            git: GitObjects::new(executable, backend.git_repo_path()),
            extras: Extras::Jj {
                store_path: store_path.to_owned(),
                backend,
            },
        }
    }

    /// A hub's bare repository and extras directory, with the git it runs.
    pub fn for_hub(executable: &Path, git_dir: &Path, extras_dir: &Path) -> Self {
        Self {
            git: GitObjects::new(executable, git_dir),
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
                        // Through its own handle: reopened truncating, ext4 would write it
                        // out as it closed (see `BundleWriter::create`), once per commit.
                        let mut tmp = tempfile::NamedTempFile::new_in(dir)?;
                        tmp.write_all(&entry.value)?;
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

    fn roots(&self, wants: &[CommitId], haves: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        self.git.roots(wants, haves)
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
        writer.pack_from(|out| self.git.write_pack(wants, &haves, out))?;
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
                Record::Pack(pack) => packs.push(pack),
                Record::Object { .. }
                | Record::View { .. }
                | Record::ViewDelta { .. }
                | Record::Operation { .. } => {
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
            self.git.receive_pack(pack)?;
        }
        self.git.check_connected(wants, haves)?;
        if let Extras::Jj { backend, .. } = &self.extras {
            backend.import_head_commits(wants)?;
        }
        self.git.maintain(matches!(self.extras, Extras::Files(_)))
    }

    fn mark_head(&self, commits: &[CommitId]) -> Result<(), ObjectError> {
        match self.extras {
            Extras::Files(_) => self.git.mark_head(commits),
            Extras::Jj { .. } => Ok(()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shallow_and_partial_clones_are_incomplete() {
        let dir = tempfile::tempdir().unwrap();
        let run = |args: &[&str]| {
            let output = git(Path::new("git"))
                .current_dir(dir.path())
                .args(args)
                .output()
                .unwrap();
            assert!(output.status.success(), "git {args:?}: {output:?}");
        };
        run(&["init", "--quiet", "--initial-branch=main", "origin"]);
        for n in ["1", "2"] {
            fs::write(dir.path().join("origin/f"), n).unwrap();
            run(&["-C", "origin", "add", "f"]);
            let identity = ["-c", "user.name=t", "-c", "user.email=t@example.com"];
            run(&[
                &identity[..],
                &["-C", "origin", "commit", "--quiet", "-m", n],
            ]
            .concat());
        }
        run(&["-C", "origin", "config", "uploadpack.allowFilter", "true"]);
        // git takes a local path for a local clone, which can be neither shallow nor partial.
        let path = dir
            .path()
            .join("origin")
            .to_string_lossy()
            .replace('\\', "/");
        let url = format!(
            "file://{}{path}",
            if path.starts_with('/') { "" } else { "/" }
        );
        run(&["clone", "--quiet", &url, "full"]);
        run(&["clone", "--quiet", "--depth=1", &url, "shallow"]);
        // Checking files out would need the blobs it left out.
        run(&[
            "clone",
            "--quiet",
            "--no-checkout",
            "--filter=blob:none",
            &url,
            "partial",
        ]);
        let of = |clone: &str| {
            GitObjects::new(Path::new("git"), &dir.path().join(clone).join(".git"))
                .incompleteness()
                .unwrap()
        };
        assert_eq!(of("full"), None);
        assert_eq!(of("shallow"), Some(Incompleteness::Shallow));
        assert_eq!(of("partial"), Some(Incompleteness::Partial));
        // A promisor remote alone, written as git takes a boolean with no value.
        run(&["clone", "--quiet", &url, "promisor"]);
        let config = dir.path().join("promisor/.git/config");
        let text = fs::read_to_string(&config).unwrap();
        fs::write(&config, format!("{text}[remote \"origin\"]\n\tpromisor\n")).unwrap();
        assert_eq!(of("promisor"), Some(Incompleteness::Partial));
    }

    /// musubi's git runs no hooks: here, `gc --auto`'s `pre-auto-gc`, with a second pack
    /// making a gc due.
    #[cfg(unix)]
    #[test]
    fn git_runs_no_hooks() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let objects =
            GitObjects::init_bare(Path::new("git"), &dir.path().join("repo.git")).unwrap();
        let hooks = dir.path().join("repo.git/hooks");
        // Here, whatever the developer's own git config says.
        objects
            .run(&["config", "core.hooksPath", hooks.to_str().unwrap()], None)
            .unwrap();
        objects
            .run(&["config", "gc.autoPackLimit", "1"], None)
            .unwrap();
        objects.run(&["config", "gc.auto", "1"], None).unwrap();
        let pack = dir.path().join("repo.git/objects/pack/pack");
        for content in ["one", "two"] {
            let id = objects
                .run(&["hash-object", "-w", "--stdin"], Some(content.into()))
                .unwrap();
            objects
                .run(&["pack-objects", "-q", pack.to_str().unwrap()], Some(id))
                .unwrap();
        }
        let ran = dir.path().join("ran");
        let hook = hooks.join("pre-auto-gc");
        fs::write(&hook, format!("#!/bin/sh\ntouch '{}'\n", ran.display())).unwrap();
        fs::set_permissions(&hook, fs::Permissions::from_mode(0o755)).unwrap();
        // Not `maintain`, which on battery wouldn't run gc at all.
        objects.gc_auto(false).unwrap();
        assert!(!ran.exists(), "git ran the pre-auto-gc hook");
    }
}

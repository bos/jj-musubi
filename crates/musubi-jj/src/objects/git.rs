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
use crate::files;
use crate::git_command::GitError;
use crate::git_command::GitRepo;
use crate::git_command::check_status;
use crate::git_command::git;
use crate::git_command::run_err;

/// Where a hub's repository names the commits its head requires (see
/// [`GitObjects::mark_head`]).
const HEAD_REFS: &str = "refs/musubi/head/";

/// git's defaults for `gc.auto` and `gc.autoPackLimit`.
const GC_AUTO: i64 = 6700;
const GC_AUTO_PACK_LIMIT: i64 = 50;

/// For a gc that deletes nothing, reachable or not (see [`GitObjects::maintain`]).
const NEVER_PRUNE: [&str; 4] = [
    "-c",
    "gc.pruneExpire=never",
    "-c",
    "gc.worktreePruneExpire=never",
];

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
    /// [`Self::maintain`] and [`Self::mark_head`] consolidate it. Nor does git sync what it
    /// writes there, as it does packs and refs by default: a hub needn't be durable (see
    /// "Moving the hub" in docs/design.md).
    pub fn init_bare(executable: &Path, git_dir: &Path) -> Result<Self, ObjectError> {
        // Not through `run`: GIT_DIR must not be set when the repository does not exist yet.
        // In the files ref format, whatever git's default, since gix reads the hub's refs
        // ([`Self::gix`]) and knows no other. Without git's template, whose sample hooks
        // and description a hub never uses.
        let args = [
            "-c",
            "init.defaultRefFormat=files",
            "init",
            "--quiet",
            "--bare",
            "--template=",
        ];
        let output = git(executable)
            .args(args)
            .arg(git_dir)
            .output()
            .map_err(|source| run_err(&args, source))?;
        check_status(&args, output.status, &output.stderr)?;
        let objects = Self::new(executable, git_dir);
        objects.run(&["config", "gc.auto", "0"], None)?;
        objects.run(&["config", "core.fsync", "none"], None)?;
        Ok(objects)
    }

    /// Whether this repository is a shallow clone, which has a `shallow` file listing its
    /// shallow commits, in the common directory of a linked worktree.
    pub fn is_shallow(&self) -> bool {
        let common = match fs::read_to_string(self.git_dir().join("commondir")) {
            Ok(dir) => self.git_dir().join(dir.trim()),
            Err(_) => self.git_dir().to_owned(),
        };
        fs::metadata(common.join("shallow")).is_ok_and(|shallow| shallow.len() > 0)
    }

    /// This repository as gix opens it, to answer what needn't start git: which objects
    /// exist, which commits a walk reaches, and which refs there are. Starting git takes
    /// longer than any of these, on Windows most of all. Opened afresh each time, so that it
    /// sees what git has written since, and holds no pack open that git's gc would delete,
    /// which Windows forbids.
    fn gix(&self) -> Result<gix::Repository, ObjectError> {
        gix::open_opts(self.git_dir(), gix::open::Options::isolated()).map_err(gix_err)
    }

    /// The subset of `ids` not present in the object database.
    pub fn missing(&self, ids: &[CommitId]) -> Result<Vec<CommitId>, ObjectError> {
        if ids.is_empty() {
            return Ok(vec![]);
        }
        let repo = self.gix()?;
        Ok(ids
            .iter()
            .filter(|id| !object_id(id).is_ok_and(|id| repo.has_object(id)))
            .cloned()
            .collect())
    }

    /// The commits reachable from `wants` but not from `haves`, each with whether it has a
    /// parent, as `git rev-list` would find them.
    fn walk(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<Vec<(CommitId, bool)>, ObjectError> {
        if wants.is_empty() {
            return Ok(vec![]);
        }
        let repo = self.gix()?;
        let wants: Vec<gix::ObjectId> = wants.iter().map(object_id).collect::<Result<_, _>>()?;
        let haves: Vec<gix::ObjectId> = haves.iter().map(object_id).collect::<Result<_, _>>()?;
        repo.rev_walk(wants)
            .with_hidden(haves)
            .all()
            .map_err(gix_err)?
            .map(|info| {
                let info = info.map_err(gix_err)?;
                Ok((
                    CommitId::from_bytes(info.id.as_bytes()),
                    !info.parent_ids.is_empty(),
                ))
            })
            .collect()
    }

    /// Commits reachable from `wants` but not from `haves`.
    fn commits_between(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<Vec<CommitId>, ObjectError> {
        Ok(self
            .walk(wants, haves)?
            .into_iter()
            .map(|(commit, _)| commit)
            .collect())
    }

    /// Parentless commits reachable from `wants` but not from `haves`.
    pub fn roots(
        &self,
        wants: &[CommitId],
        haves: &[CommitId],
    ) -> Result<Vec<CommitId>, ObjectError> {
        Ok(self
            .walk(wants, haves)?
            .into_iter()
            .filter_map(|(commit, parented)| (!parented).then_some(commit))
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
        if !haves.is_empty() {
            // git otherwise leaves out only what the parents of `wants` reach, and makes
            // deltas only against that. A jj rewrite is a sibling of the commit it replaces,
            // with much the same tree, so a `jj commit` or `jj describe` after a snapshot
            // would send every file the snapshot did again, whole. `--shallow`, meant for
            // shallow clients, does both for everything `haves` reach, for a walk of their
            // trees: a few milliseconds for hundreds of haves in jj's own repository.
            args.push("--shallow");
        }
        let input = io::Cursor::new(revs_input(wants, haves));
        self.repo.stream(&args, input, out)?;
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
        let input = io::Read::chain(io::Cursor::new(header), reader);
        self.repo.stream(args, input, &mut io::sink())?;
        Ok(())
    }

    /// Consolidates packs and loose objects once there are enough of them, as git itself
    /// does after a fetch, with `git gc --auto` and the repository's own thresholds. It
    /// never deletes an object, reachable or not: jj's `refs/jj/keep` refs need not cover
    /// every commit an operation refers to, and a hub's refs cover only its head. git may
    /// finish in the background. On battery it waits for an import on mains power.
    pub fn maintain(&self, hub: bool) -> Result<(), ObjectError> {
        // Asked last: on macOS, it starts a process.
        if !self.gc_due(hub) || power::on_battery() {
            return Ok(());
        }
        self.gc_auto(hub)
    }

    /// Whether `git gc --auto` would find work, by git's own measures, so that git starts
    /// only when it would: more than `gc.autoPackLimit` packs that aren't kept, or more than
    /// `gc.auto` loose objects, which git estimates from `objects/17`, one of the 256
    /// directories they spread across. A hub's `gc.auto` is git's default, as
    /// [`Self::gc_auto`] sets it. Where the config can't be read, git decides.
    fn gc_due(&self, hub: bool) -> bool {
        let Ok(repo) = gix::open(self.git_dir()) else {
            return true;
        };
        let config = repo.config_snapshot();
        let threshold = if hub {
            GC_AUTO
        } else {
            config.integer("gc.auto").unwrap_or(GC_AUTO)
        };
        if threshold <= 0 {
            return false;
        }
        let objects = self.git_dir().join("objects");
        let entries = |dir: &Path| fs::read_dir(dir).into_iter().flatten().flatten();
        let pack_limit = config
            .integer("gc.autoPackLimit")
            .unwrap_or(GC_AUTO_PACK_LIMIT);
        let packs = entries(&objects.join("pack"))
            .map(|entry| entry.path())
            .filter(|path| {
                path.extension().is_some_and(|ext| ext == "pack")
                    && !path.with_extension("keep").exists()
            })
            .count();
        if pack_limit > 0 && i64::try_from(packs).unwrap_or(i64::MAX) > pack_limit {
            return true;
        }
        let loose = entries(&objects.join("17"))
            .filter(|entry| {
                let name = entry.file_name();
                let name = name.as_encoded_bytes();
                name.len() == 38 && name.iter().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
            })
            .count();
        i64::try_from(loose).unwrap_or(i64::MAX) > (threshold + 255) / 256
    }

    fn gc_auto(&self, hub: bool) -> Result<(), ObjectError> {
        let mut args = NEVER_PRUNE.to_vec();
        let gc_auto = format!("gc.auto={GC_AUTO}");
        if hub {
            // Much of a hub's history is unreachable to git: keep it in a cruft pack rather
            // than loose, and override the hub's own `gc.auto 0`.
            args.extend(["-c", "gc.cruftPacks=true", "-c", &gc_auto]);
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
        let repo = self.gix()?;
        let existing: BTreeSet<String> = repo
            .references()
            .map_err(gix_err)?
            .prefixed(HEAD_REFS)
            .map_err(gix_err)?
            .map(|reference| Ok(reference.map_err(gix_err)?.name().as_bstr().to_string()))
            .collect::<Result<_, ObjectError>>()?;
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
        let mut args = NEVER_PRUNE.to_vec();
        args.extend([
            "-c",
            "gc.cruftPacks=true",
            "-c",
            "repack.writeBitmaps=true",
            "gc",
            "--quiet",
        ]);
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
        // Commits that `haves` all reach are connected already, by the assumption: git need
        // walk no trees. A want missing here fails the walk, and git says why.
        if self.walk(wants, haves).is_ok_and(|new| new.is_empty()) {
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

fn object_id(id: &CommitId) -> Result<gix::ObjectId, ObjectError> {
    gix::ObjectId::try_from(id.as_bytes()).map_err(|_| ObjectError::MalformedObject {
        kind: "commit",
        id: id.hex(),
    })
}

fn gix_err(err: impl Into<Box<dyn std::error::Error + Send + Sync>>) -> ObjectError {
    ObjectError::Gix(err.into())
}

fn revs_input(wants: &[CommitId], haves: &[CommitId]) -> Vec<u8> {
    let mut input = hex_lines(wants.iter(), "");
    input.extend(hex_lines(haves.iter(), "^"));
    input
}

/// A backend extras entry that a receiver could not derive from the commit object alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExtrasEntry {
    pub commit: CommitId,
    /// The encoded `git_store.Commit` from the sender's extras table.
    pub value: Vec<u8>,
}

/// The error for `commit`, which couldn't be read for the reason `source` gives.
fn read_err<E: std::fmt::Display>(commit: &CommitId) -> impl FnOnce(E) -> ObjectError + '_ {
    move |source| ObjectError::ReadCommit {
        commit: commit.hex(),
        source: source.to_string().into(),
    }
}

/// Returns the extras entries for `commits` that differ from what jj would derive from the
/// commit objects: change ids of commits without a `change-id` header that were not derived
/// from the commit id, and conflicts written before the `jj:trees` header existed.
pub(crate) fn extras_to_ship(
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
        let oid = gix::ObjectId::try_from(commit.as_bytes()).map_err(read_err(commit))?;
        let object = git_repo.find_object(oid).map_err(read_err(commit))?;
        let git_commit = object.try_to_commit_ref().map_err(read_err(commit))?;
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
pub(crate) fn import_extras(
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
                        files::replace(&path, &entry.value)?;
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
        // With no commit to send, as for an operation that only moves bookmarks, git would
        // be started to make a pack of nothing, and the receiver's to unpack it.
        if !commits.is_empty() {
            writer.pack_from(|out| self.git.write_pack(wants, &haves, out))?;
        }
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

    fn init(dir: &Path) -> impl Fn(&[&str]) -> String {
        let dir = dir.to_owned();
        move |args: &[&str]| {
            let output = git(Path::new("git"))
                .current_dir(&dir)
                .args(["-c", "user.name=t", "-c", "user.email=t@example.com"])
                .args(args)
                .output()
                .unwrap();
            assert!(output.status.success(), "git {args:?}: {output:?}");
            String::from_utf8(output.stdout).unwrap().trim().to_owned()
        }
    }

    #[test]
    fn walks_find_what_rev_list_finds() {
        let dir = tempfile::tempdir().unwrap();
        let run = init(dir.path());
        run(&["init", "--quiet", "--initial-branch=main"]);
        let commit = |message: &str| {
            run(&["commit", "--quiet", "--allow-empty", "-m", message]);
            run(&["rev-parse", "HEAD"])
        };
        let a = commit("a");
        let b = commit("b");
        run(&["checkout", "--quiet", "--orphan", "other"]);
        let c = commit("c");
        run(&[
            "merge",
            "--quiet",
            "--allow-unrelated-histories",
            "-m",
            "d",
            "main",
        ]);
        let d = run(&["rev-parse", "HEAD"]);
        let e = commit("e");
        let objects = GitObjects::new(Path::new("git"), &dir.path().join(".git"));
        let ids = |hexes: &[&String]| -> Vec<CommitId> {
            hexes
                .iter()
                .map(|hex| CommitId::try_from_hex(hex).unwrap())
                .collect()
        };
        let sorted = |mut ids: Vec<CommitId>| {
            ids.sort();
            ids
        };
        let rev_list = |args: &[&str], wants: &[&String], haves: &[&String]| -> Vec<CommitId> {
            let mut args = args.to_vec();
            let haves: Vec<String> = haves.iter().map(|have| format!("^{have}")).collect();
            args.extend(wants.iter().map(|want| want.as_str()));
            args.extend(haves.iter().map(String::as_str));
            let out = run(&args);
            sorted(
                out.lines()
                    .map(|line| CommitId::try_from_hex(line).unwrap())
                    .collect(),
            )
        };
        for (wants, haves) in [
            (vec![&e], vec![]),
            (vec![&e], vec![&b]),
            (vec![&e], vec![&c]),
            (vec![&e], vec![&d]),
            (vec![&d, &a], vec![&c]),
            (vec![&b], vec![&e]),
        ] {
            assert_eq!(
                sorted(objects.commits_between(&ids(&wants), &ids(&haves)).unwrap()),
                rev_list(&["rev-list"], &wants, &haves),
                "{wants:?} ^{haves:?}"
            );
            assert_eq!(
                sorted(objects.roots(&ids(&wants), &ids(&haves)).unwrap()),
                rev_list(&["rev-list", "--max-parents=0"], &wants, &haves),
                "{wants:?} ^{haves:?}"
            );
        }
        let absent = CommitId::try_from_hex("1".repeat(40)).unwrap();
        assert_eq!(
            objects.missing(&ids(&[&a, &e])).unwrap(),
            Vec::<CommitId>::new()
        );
        assert_eq!(
            objects
                .missing(&[absent.clone(), CommitId::from_bytes(&[0; 20])])
                .unwrap(),
            [absent, CommitId::from_bytes(&[0; 20])]
        );
    }

    /// Commits that the haves reach are connected without starting git, which would walk
    /// their trees; anything else is git's to answer.
    #[test]
    fn commits_the_haves_reach_are_connected_without_git() {
        let dir = tempfile::tempdir().unwrap();
        let run = init(dir.path());
        run(&["init", "--quiet", "--initial-branch=main"]);
        let commit = |message: &str| {
            run(&["commit", "--quiet", "--allow-empty", "-m", message]);
            CommitId::try_from_hex(run(&["rev-parse", "HEAD"])).unwrap()
        };
        let a = commit("a");
        let b = commit("b");
        // A git that can't be started: what goes to git fails.
        let objects = GitObjects::new(Path::new("no-such-git"), &dir.path().join(".git"));
        let (a, b) = (std::slice::from_ref(&a), std::slice::from_ref(&b));
        objects.check_connected(a, b).unwrap();
        objects.check_connected(b, b).unwrap();
        assert!(objects.check_connected(b, a).is_err());
        let missing = CommitId::from_bytes(&[1; 20]);
        assert!(objects.check_connected(&[missing], b).is_err());
    }

    /// A jj rewrite is a sibling of the commit it replaces, with much the same tree. A pack
    /// with the replaced commit as a have leaves out what that reaches, and sends a file
    /// edited since as a delta against its version there.
    #[test]
    fn packs_leave_out_what_a_replaced_sibling_reaches() {
        let dir = tempfile::tempdir().unwrap();
        let run = init(dir.path());
        run(&["init", "--quiet", "--initial-branch=main"]);
        let path = |name: &str| dir.path().join(name);
        let mut big = String::new();
        for i in 0..20_000 {
            writeln!(big, "line {i}").unwrap();
        }
        fs::write(path("big"), &big).unwrap();
        run(&["add", "."]);
        run(&["commit", "--quiet", "-m", "parent"]);
        // The snapshot: new files, and a large edit that compresses badly.
        let mut x: u64 = 1;
        let noise: String = (0..20_000)
            .map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                char::from(b'a' + u8::try_from(x % 26).unwrap())
            })
            .collect();
        for i in 0..20 {
            fs::write(path(&format!("new{i}")), format!("new file {i}\n")).unwrap();
        }
        fs::write(path("big"), format!("{noise}\n{big}")).unwrap();
        run(&["add", "."]);
        run(&["commit", "--quiet", "-m", "snapshot"]);
        let snapshot = run(&["rev-parse", "HEAD"]);
        // Its rewrite, on the same parent, with one more small edit.
        fs::write(path("big"), format!("{noise}\n{big}one more line\n")).unwrap();
        run(&["commit", "--quiet", "--all", "--amend", "-m", "described"]);
        let rewrite = run(&["rev-parse", "HEAD"]);
        let objects = GitObjects::new(Path::new("git"), &path(".git"));
        let id = |hex: &str| CommitId::try_from_hex(hex).unwrap();
        let mut pack = vec![];
        objects
            .write_pack(&[id(&rewrite)], &[id(&snapshot)], &mut pack)
            .unwrap();
        // The commit, its tree, and the big file's new version.
        assert_eq!(u32::from_be_bytes(pack[8..12].try_into().unwrap()), 3);
        assert!(pack.len() < noise.len() / 4, "{} bytes", pack.len());
    }

    #[test]
    fn gc_starts_only_where_git_would_collect() {
        let dir = tempfile::tempdir().unwrap();
        let run = init(dir.path());
        run(&["init", "--quiet"]);
        let git_dir = dir.path().join(".git");
        let objects = GitObjects::new(Path::new("git"), &git_dir);
        assert!(!objects.gc_due(false));
        // git estimates loose objects from one directory of the 256: here, more than 2 in it
        // stand for more than 512.
        run(&["config", "gc.auto", "512"]);
        let seventeen = git_dir.join("objects/17");
        fs::create_dir_all(&seventeen).unwrap();
        for name in ["0".repeat(38), "1".repeat(38), "not-an-object".to_owned()] {
            fs::write(seventeen.join(name), "").unwrap();
        }
        assert!(!objects.gc_due(false));
        fs::write(seventeen.join("2".repeat(38)), "").unwrap();
        assert!(objects.gc_due(false));
        // A hub's own `gc.auto` gives way to git's default.
        assert!(!objects.gc_due(true));
        run(&["config", "gc.auto", "0"]);
        assert!(!objects.gc_due(false));
        // Packs past `gc.autoPackLimit`, unless kept.
        fs::remove_dir_all(&seventeen).unwrap();
        run(&["config", "--unset", "gc.auto"]);
        run(&["config", "gc.autoPackLimit", "1"]);
        let packs = git_dir.join("objects/pack");
        fs::write(packs.join("pack-a.pack"), "").unwrap();
        assert!(!objects.gc_due(false));
        fs::write(packs.join("pack-b.pack"), "").unwrap();
        assert!(objects.gc_due(false));
        fs::write(packs.join("pack-b.keep"), "").unwrap();
        assert!(!objects.gc_due(false));
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
        fs::create_dir_all(&hooks).unwrap();
        let hook = hooks.join("pre-auto-gc");
        fs::write(&hook, format!("#!/bin/sh\ntouch '{}'\n", ran.display())).unwrap();
        fs::set_permissions(&hook, fs::Permissions::from_mode(0o755)).unwrap();
        // Not `maintain`, which on battery wouldn't run gc at all.
        objects.gc_auto(false).unwrap();
        assert!(!ran.exists(), "git ran the pre-auto-gc hook");
    }
}

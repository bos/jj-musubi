//! The git backend's objects: packfiles built and indexed by the `git` binary, which jj
//! already requires for fetch and push, plus the backend extras jj cannot derive from them.

use std::collections::BTreeMap;
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
use crate::hive_settings::Remote;

/// The variables git sets, for what it runs in a repository such as a hook, to name that
/// repository: the ones `git rev-parse --local-env-vars` lists. No git musubi runs gets
/// them, nor does a daemon a command starts, which serves every repository on the machine;
/// musubi run from a hook would otherwise hand them on.
pub const REPOSITORY_ENV: &[&str] = &[
    "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    "GIT_CONFIG",
    "GIT_CONFIG_PARAMETERS",
    "GIT_CONFIG_COUNT",
    "GIT_OBJECT_DIRECTORY",
    "GIT_DIR",
    "GIT_WORK_TREE",
    "GIT_IMPLICIT_WORK_TREE",
    "GIT_GRAFT_FILE",
    "GIT_INDEX_FILE",
    "GIT_NO_REPLACE_OBJECTS",
    "GIT_REPLACE_REF_BASE",
    "GIT_PREFIX",
    "GIT_SHALLOW_FILE",
    "GIT_COMMON_DIR",
];

/// `git` as musubi runs it: without [`REPOSITORY_ENV`], and running no hooks. jj runs none
/// when it writes to `.git`; musubi's `update-ref` and `git remote` would run the
/// repository's `reference-transaction`, and its `gc --auto` `pre-auto-gc`.
fn git() -> Command {
    let mut command = Command::new("git");
    for name in REPOSITORY_ENV {
        command.env_remove(name);
    }
    // A path under which no hook can exist.
    command.args(["-c", "core.hooksPath=/dev/null"]);
    command
}

/// The empty tree's id, which git knows without storing it.
const EMPTY_TREE: &str = "4b825dc642cb6eb9a060e54bf8d69288fbee4904";

/// Where a hub's repository names the commits its head requires (see
/// [`GitObjects::mark_head`]).
const HEAD_REFS: &str = "refs/musubi/head/";

/// How many objects a hub's repository holds before a bitmap index is worth writing.
const BITMAP_AFTER: u64 = 10_000;

/// How long a hub without a bitmap index waits before looking into writing one again.
const BITMAP_RETRY: std::time::Duration = std::time::Duration::from_secs(3600);

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
    /// hub decides what is unreferenced, not git, and its only refs, under
    /// `refs/musubi/head/`, are for git's bitmap index (see [`Self::mark_head`]). Only
    /// [`Self::maintain`] and [`Self::mark_head`] consolidate it.
    pub fn init_bare(git_dir: &Path) -> Result<Self, ObjectError> {
        // Not through `run`: GIT_DIR must not be set when the repository does not exist yet.
        let args = ["init", "--quiet", "--bare"];
        let output = git()
            .args(args)
            .arg(git_dir)
            .output()
            .map_err(|source| spawn_err(&args, source))?;
        check_status(&args, &output)?;
        let objects = Self::new(git_dir);
        objects.run(&["config", "gc.auto", "0"], None)?;
        Ok(objects)
    }

    /// This repository's own git config file.
    pub fn config_path(&self) -> PathBuf {
        self.git_dir.join("config")
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
            self.set_remote_urls(name, from.get(name), remote)?;
        }
        for name in removed {
            self.run(&["remote", "remove", name], None)?;
        }
        Ok(())
    }

    /// Points remote `name`, which `old` describes as this repository has it, where `remote`
    /// says. A URL that already names the repository `remote`'s does is left as this
    /// machine spells it (see [`Remote`]'s equality), and a push URL is removed once it no
    /// longer names where pushes should go.
    fn set_remote_urls(
        &self,
        name: &str,
        old: Option<&Remote>,
        remote: &Remote,
    ) -> Result<(), ObjectError> {
        let set = |variable: &str, value: Option<&str>| -> Result<(), ObjectError> {
            let key = format!("remote.{name}.{variable}");
            match value {
                Some(value) => self.run(&["config", "--local", &key, value], None)?,
                // Unsetting a variable that isn't set fails; that's fine.
                None => self
                    .run(&["config", "--local", "--unset-all", &key], None)
                    .unwrap_or_default(),
            };
            Ok(())
        };
        let mut now = old.cloned().unwrap_or_default();
        if old.is_none() || now.url_repository() != remote.url_repository() {
            set("url", remote.url.as_deref())?;
            now.url.clone_from(&remote.url);
        }
        if old.is_none() || now.push_repository() != remote.push_repository() {
            set("pushurl", remote.push_url.as_deref())?;
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
            .map_err(|source| spawn_err(&args, source))?;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        let input = revs_input(wants, haves);
        let writer = thread::spawn(move || stdin.write_all(&input));
        let mut stderr = child.stderr.take().expect("stderr is piped");
        let errors = thread::spawn(move || {
            let mut bytes = vec![];
            io::Read::read_to_end(&mut stderr, &mut bytes).map(|_| bytes)
        });
        let copied = io::copy(&mut child.stdout.take().expect("stdout is piped"), out);
        let status = child.wait()?;
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
        )
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
            .map_err(|source| spawn_err(args, source))?;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        let writer = thread::spawn(move || io::copy(&mut input, &mut stdin));
        let output = child.wait_with_output()?;
        // A failing git may close stdin early; its exit status explains why.
        writer.join().expect("stdin writer panicked").ok();
        check_status(args, &output)
    }

    /// Consolidates packs and loose objects once there are enough of them, as git itself
    /// does after a fetch, with `git gc --auto` and the repository's own thresholds. It
    /// never deletes an object, reachable or not: jj's `refs/jj/keep` refs need not cover
    /// every commit an operation refers to, and a hub's refs cover only its head. git may
    /// finish in the background.
    pub fn maintain(&self, hub: bool) -> Result<(), ObjectError> {
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
        command.spawn().map_err(|source| spawn_err(args, source))?;
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
        let checked = self.git_dir.join("musubi-bitmap-checked");
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
        let dir = self.git_dir.join("objects/pack");
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
        let log = self.git_dir.join("musubi-bitmap-gc.log");
        let mut command = self.command(&args);
        command
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(fs::File::create(&log)?);
        detach(&mut command);
        let mut child = command.spawn().map_err(|source| spawn_err(&args, source))?;
        let dir = self.git_dir.clone();
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
        let mut command = git();
        // Running inside the repository as well as naming it keeps a mistake from ever
        // touching the caller's working directory.
        command
            .current_dir(&self.git_dir)
            .env("GIT_DIR", &self.git_dir)
            // git 2.43 to 2.45 read a bare repository's attributes from HEAD's tree, and
            // `pack-objects` asks for each path's. Where HEAD names a branch that doesn't
            // exist, as in a hub's repository or a non-colocated jj repository's, every
            // ask tried each way of spelling HEAD as a ref, and failed: a million file
            // lookups for a clone of jj, three times as long as the packing itself. Run here,
            // git has no attributes to read anyway (a colocated `.git` is no working tree),
            // so name the empty tree. Other gits ignore the setting, or use no tree in a bare
            // repository already.
            .args(["-c", &format!("attr.tree={EMPTY_TREE}")])
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

    fn args(objects: &GitObjects) -> Vec<String> {
        objects
            .command(&["pack-objects"])
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect()
    }

    #[test]
    fn attributes_come_from_the_empty_tree() {
        assert_eq!(
            args(&GitObjects::new(Path::new("unused"))),
            [
                "-c",
                "core.hooksPath=/dev/null",
                "-c",
                &format!("attr.tree={EMPTY_TREE}"),
                "pack-objects"
            ]
        );
    }

    /// The list is git's own, so that a variable a newer git adds is noticed here.
    #[test]
    fn repository_env_is_what_git_lists() {
        let output = Command::new("git")
            .args(["rev-parse", "--local-env-vars"])
            .output()
            .unwrap();
        assert!(output.status.success());
        for name in String::from_utf8(output.stdout).unwrap().lines() {
            assert!(REPOSITORY_ENV.contains(&name), "{name} is missing");
        }
    }

    /// musubi's git runs no hooks: here, `gc --auto`'s `pre-auto-gc`, with a second pack
    /// making a gc due.
    #[cfg(unix)]
    #[test]
    fn git_runs_no_hooks() {
        use std::os::unix::fs::PermissionsExt as _;

        let dir = tempfile::tempdir().unwrap();
        let objects = GitObjects::init_bare(&dir.path().join("repo.git")).unwrap();
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
        objects.maintain(false).unwrap();
        assert!(!ran.exists(), "git ran the pre-auto-gc hook");
    }
}

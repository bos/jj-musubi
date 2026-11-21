//! Explore schedules around a real jj op-head unlink and musubi's abandon check.

#![allow(clippy::unwrap_used)]

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};

use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::{OpStore, OperationId, ViewId};
use musubi_jj::node::{NodeError, NodeRepo};
use musubi_jj::op_id::LocalOp;
use musubi_testutil::{TestEnv, TestRepo};
use pollster::FutureExt as _;
use serde::{Deserialize, Serialize};

mod gate;
use gate::{Gate, PausedCommand};

use crate::translation::abandon_put_back_fixture;

const MAX_STEPS: usize = 8;
const CONCURRENT_STEPS: usize = 14;
/// A native merge widens the search: it reaches every state by this many actions.
const LOADER_STEPS: usize = 18;
const VERSION: u8 = 2;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Action {
    StartAbandon,
    PrepareAbandon,
    PreparePeer,
    PublishAbandon,
    PublishPeer,
    FinishAbandon,
    FinishPeer,
    KillAbandon,
    KillPeer,
    Check,
    InterruptBeforePublication,
    InterruptPublication,
    Reopen,
    ReopenWithoutCache,
    MergeHeads,
    StartLoader,
    PublishLoader,
    FinishLoader,
    KillLoader,
}

/// What the second native command does in a concurrent search: the same `jj op abandon`, or
/// an ordinary write on the same old head, which the daemon must not mistake for an abandon
/// or lose.
#[derive(Clone, Copy, Debug, Default, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Peer {
    #[default]
    Abandon,
    Write,
}

impl Peer {
    fn is_abandon(&self) -> bool {
        *self == Self::Abandon
    }
}

/// The description the write peer gives the working-copy commit, to find it afterwards.
const WRITE_MARKER: &str = "musubi head-schedule write";

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "snake_case")]
enum Native {
    Ready,
    Prepared,
    Paused,
    Finished,
    Killed,
}

#[derive(Clone, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
struct State {
    native: Native,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    peer: Option<Native>,
    /// A native command that loads the repository at several heads, merging them.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    loader: Option<Native>,
    heads: Vec<String>,
    checked_heads: Option<Vec<String>>,
    online: bool,
    interrupted: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    stopped_before_publication: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    lost_cache: bool,
    #[serde(default)]
    put_back: bool,
    pending_drops: Vec<String>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct Step {
    action: Action,
    state: State,
    #[serde(default)]
    failed: bool,
}

// Exclude process IDs and absolute paths. Compare the snapshot after every replayed action.
#[derive(Clone, Debug, Deserialize, Serialize)]
struct Schedule {
    version: u8,
    unpublished: bool,
    #[serde(default)]
    concurrent: bool,
    #[serde(default, skip_serializing_if = "Peer::is_abandon")]
    peer: Peer,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    loader: bool,
    steps: Vec<Step>,
}

struct Fixture<'a> {
    gate: &'a Gate,
    directory: PathBuf,
    parent: String,
    unpublished: bool,
    concurrent: bool,
    peer: Peer,
    loader: bool,
}

impl<'a> Fixture<'a> {
    fn load(
        gate: &'a Gate,
        cache: &Path,
        unpublished: bool,
        concurrent: bool,
        peer: Peer,
        loader: bool,
    ) -> Self {
        let case = if unpublished {
            "unpublished"
        } else {
            "realized"
        };
        let directory = musubi_testutil::recorded(cache, case, |directory| {
            let (env, node, parent, _) = abandon_put_back_fixture(unpublished);
            drop(node);
            env.save(directory);
            fs::write(directory.join("abandon"), parent).unwrap();
        });
        let parent = fs::read_to_string(directory.join("abandon")).unwrap();
        Self {
            gate,
            directory,
            parent,
            unpublished,
            concurrent,
            peer,
            loader,
        }
    }

    fn restore(&self) -> World<'_> {
        let env = TestEnv::restore(&self.directory);
        let repo = env.repo_handle("beta");
        let node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        let heads = read_heads(&repo);
        let [old_head] = heads.try_into().unwrap();
        let store = node.loader().op_store().clone();
        let old_id = OperationId::try_from_hex(&old_head).unwrap();
        let old_view = store.read_operation(&old_id).block_on().unwrap().view_id;
        // The history the fixture starts with is the same on every run: only operations a
        // schedule writes need keys other than their ids.
        let mut keys = HashMap::new();
        let mut pending = vec![old_id];
        while let Some(id) = pending.pop() {
            if !keys.contains_key(&id) {
                pending.extend(store.read_operation(&id).block_on().unwrap().parents);
                keys.insert(id.clone(), id);
            }
        }
        World {
            gate: self.gate,
            parent: &self.parent,
            old_head,
            node: Some(node),
            native: [Native::Ready; 2],
            children: [None, None],
            loader: self.loader.then_some(Native::Ready),
            loader_child: None,
            concurrent: self.concurrent,
            peer: self.peer,
            checked_heads: None,
            interrupted: false,
            stopped_before_publication: false,
            lost_cache: false,
            put_back: false,
            keys: RefCell::new(keys),
            write_published: false,
            store,
            old_view,
            repo,
            env,
        }
    }

    fn empty_schedule(&self) -> Schedule {
        Schedule {
            version: VERSION,
            unpublished: self.unpublished,
            concurrent: self.concurrent,
            peer: self.peer,
            loader: self.loader,
            steps: vec![],
        }
    }

    fn horizon(&self) -> usize {
        horizon(self.concurrent, self.loader)
    }
}

/// The most actions a schedule may take: `MUSUBI_HEAD_SCHEDULE_STEPS` if set, to search
/// deeper, or else the default for the kind of search.
fn horizon(concurrent: bool, loader: bool) -> usize {
    match std::env::var("MUSUBI_HEAD_SCHEDULE_STEPS") {
        Ok(steps) => steps
            .parse()
            .expect("MUSUBI_HEAD_SCHEDULE_STEPS is a number of actions"),
        Err(_) if loader => LOADER_STEPS,
        Err(_) if concurrent => CONCURRENT_STEPS,
        Err(_) => MAX_STEPS,
    }
}

struct World<'a> {
    gate: &'a Gate,
    parent: &'a str,
    old_head: String,
    node: Option<NodeRepo>,
    native: [Native; 2],
    // Reap the commands before removing the environment's directory.
    children: [Option<PausedCommand>; 2],
    loader: Option<Native>,
    loader_child: Option<PausedCommand>,
    concurrent: bool,
    peer: Peer,
    checked_heads: Option<Vec<String>>,
    interrupted: bool,
    stopped_before_publication: bool,
    lost_cache: bool,
    put_back: bool,
    /// Each operation's key, as `key` works it out.
    keys: RefCell<HashMap<OperationId, OperationId>>,
    /// Whether the write peer added its head: jj merges it later even if the write is killed
    /// before its unlink.
    write_published: bool,
    store: Arc<dyn OpStore>,
    old_view: ViewId,
    repo: TestRepo,
    env: TestEnv,
}

fn read_heads(repo: &TestRepo) -> Vec<String> {
    let mut heads: Vec<_> = fs::read_dir(repo.repo_path().join("op_heads/heads"))
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        // jj's op-heads lock lives beside the heads.
        .filter(|name| name != "lock")
        .collect();
    heads.sort_unstable();
    heads
}

impl World<'_> {
    fn head_keys(&self, heads: &[String]) -> Vec<String> {
        let mut keys: Vec<_> = heads
            .iter()
            .map(|head| self.key(&OperationId::try_from_hex(head).unwrap()).hex())
            .collect();
        keys.sort_unstable();
        keys
    }

    /// What identifies `id` across runs of the same schedule. jj orders a merge's parents by
    /// end time, and can put equal ones either way, as a rewrite and the operation it
    /// rewrote have: so a merge a schedule writes, and every operation written on one, gets
    /// a different id on another run. The key hashes the body with each parent replaced by
    /// its key, the parents of a merge sorted. Any other operation, and all the history the
    /// fixture starts with, keeps its id.
    fn key(&self, id: &OperationId) -> OperationId {
        if let Some(key) = self.keys.borrow().get(id) {
            return key.clone();
        }
        let mut body = self.store.read_operation(id).block_on().unwrap();
        let parents: Vec<OperationId> = body.parents.iter().map(|p| self.key(p)).collect();
        // Key what the metadata names first. A body names only operations written before
        // it, so this ends.
        for text in body
            .metadata
            .attributes
            .values()
            .chain([&body.metadata.description])
        {
            for word in text.split(|c: char| !c.is_ascii_hexdigit()) {
                if word.len() == id.hex().len()
                    && let Some(named) = OperationId::try_from_hex(word)
                    && self.store.read_operation(&named).block_on().is_ok()
                {
                    self.key(&named);
                }
            }
        }
        // musubi's metadata can name another operation, as a stamp of what a rewrite was
        // reconciled from does: name it by its key too.
        let renamed: Vec<(String, String)> = self
            .keys
            .borrow()
            .iter()
            .filter(|(id, key)| id != key)
            .map(|(id, key)| (id.hex(), key.hex()))
            .collect();
        let mut named = false;
        for text in body
            .metadata
            .attributes
            .values_mut()
            .chain([&mut body.metadata.description])
        {
            for (from, to) in &renamed {
                if text.contains(from.as_str()) {
                    *text = text.replace(from.as_str(), to);
                    named = true;
                }
            }
        }
        let key = if body.parents.len() <= 1 && parents == body.parents && !named {
            id.clone()
        } else {
            body.parents = parents;
            body.parents.sort_unstable();
            OperationId::new(blake2b_hash(&body).to_vec())
        };
        self.keys.borrow_mut().insert(id.clone(), key.clone());
        key
    }

    fn state(&self) -> State {
        let mut pending_drops = self.node.as_ref().map_or_else(Vec::new, |node| {
            node.pending_drops()
                .ops()
                .iter()
                .map(|op| op.0.0.hex())
                .collect()
        });
        pending_drops.sort_unstable();
        State {
            native: self.native[0],
            peer: self.concurrent.then_some(self.native[1]),
            loader: self.loader,
            heads: self.head_keys(&read_heads(&self.repo)),
            checked_heads: self.checked_heads.clone(),
            online: self.node.is_some(),
            interrupted: self.interrupted,
            stopped_before_publication: self.stopped_before_publication,
            lost_cache: self.lost_cache,
            put_back: self.put_back,
            pending_drops,
        }
    }

    fn choices(&self, state: &State) -> Vec<Action> {
        let mut choices = vec![];
        match self.native {
            [Native::Ready, _] => choices.push(if self.concurrent {
                Action::PrepareAbandon
            } else {
                Action::StartAbandon
            }),
            [Native::Prepared, Native::Ready] => choices.push(Action::PreparePeer),
            _ => {
                for (status, publish, finish, kill) in [
                    (
                        state.native,
                        Action::PublishAbandon,
                        Action::FinishAbandon,
                        Action::KillAbandon,
                    ),
                    (
                        self.native[1],
                        Action::PublishPeer,
                        Action::FinishPeer,
                        Action::KillPeer,
                    ),
                ] {
                    match status {
                        Native::Prepared => {
                            choices.push(publish);
                            choices.push(kill);
                        }
                        Native::Paused => {
                            choices.push(finish);
                            if self.concurrent {
                                choices.push(kill);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        if !state.online {
            choices.push(Action::Reopen);
            if self.concurrent {
                choices.push(Action::ReopenWithoutCache);
            }
        } else if state.checked_heads.as_ref() != Some(&state.heads) {
            choices.push(Action::Check);
            if self.abandon_paused()
                && !state.interrupted
                && !state.put_back
                && state.heads.len() == 2
                && state.heads.binary_search(&self.old_head).is_ok()
            {
                choices.push(Action::InterruptPublication);
                if self.concurrent {
                    choices.push(Action::InterruptBeforePublication);
                }
            }
        } else if self.concurrent && state.heads.len() > 1 && !self.locked() {
            choices.push(Action::MergeHeads);
        }
        match self.loader {
            // Loading at one head takes no lock and changes nothing.
            Some(Native::Ready) if state.heads.len() > 1 && !self.locked() => {
                choices.push(Action::StartLoader);
            }
            Some(Native::Prepared) => {
                choices.push(Action::PublishLoader);
                choices.push(Action::KillLoader);
            }
            Some(Native::Paused) => {
                choices.push(Action::FinishLoader);
                choices.push(Action::KillLoader);
            }
            _ => {}
        }
        choices
    }

    /// Whether a native command holds jj's op-heads lock, which loading at several heads
    /// waits for.
    fn locked(&self) -> bool {
        self.write_locked() || matches!(self.loader, Some(Native::Prepared | Native::Paused))
    }

    /// Whether the write peer holds jj's op-heads lock: an ordinary command takes it before
    /// adding its new head and keeps it until the old one is gone. Loading the repository at
    /// several heads waits for it, as merging them does; `jj op abandon` and the daemon's own
    /// publication of heads don't.
    fn write_locked(&self) -> bool {
        self.peer == Peer::Write && matches!(self.native[1], Native::Prepared | Native::Paused)
    }

    /// Whether a native abandon is paused before its unlink, so the daemon may see both heads.
    fn abandon_paused(&self) -> bool {
        self.native[0] == Native::Paused
            || (self.peer.is_abandon() && self.native[1] == Native::Paused)
    }

    fn prepare(&mut self, slot: usize) {
        let old = self
            .repo
            .repo_path()
            .join("op_heads/heads")
            .join(&self.old_head);
        let mut command = self.repo.program(Path::new("jj"));
        if slot == 1 && self.peer == Peer::Write {
            command.args([
                "--ignore-working-copy",
                "describe",
                "-r",
                "@",
                "-m",
                WRITE_MARKER,
            ]);
        } else {
            command.args(["--ignore-working-copy", "op", "abandon", self.parent]);
        }
        command.env("COLUMNS", "80").env("RAYON_NUM_THREADS", "1");
        self.children[slot] = Some(self.gate.spawn(
            &mut command,
            &old,
            &self.env.root().join(format!("gate-{slot}")),
        ));
        self.native[slot] = Native::Prepared;
        assert_eq!(
            read_heads(&self.repo),
            std::slice::from_ref(&self.old_head),
            "preparing must leave just the shared old head"
        );
    }

    fn publish(&mut self, slot: usize) {
        self.children[slot].as_mut().unwrap().publish();
        self.native[slot] = Native::Paused;
        self.write_published |= slot == 1 && self.peer == Peer::Write;
    }

    fn act(&mut self, action: Action) -> State {
        match action {
            Action::StartLoader => {
                let old = self
                    .repo
                    .repo_path()
                    .join("op_heads/heads")
                    .join(&self.old_head);
                let mut command = self.repo.program(Path::new("jj"));
                command
                    .args(["--ignore-working-copy", "op", "log", "-n1", "--no-graph"])
                    .args(["-T", "id"])
                    .env("COLUMNS", "80")
                    .env("RAYON_NUM_THREADS", "1");
                self.loader_child = self.gate.spawn_loader(
                    &mut command,
                    &old,
                    &self.env.root().join("gate-loader"),
                );
                self.loader = Some(if self.loader_child.is_some() {
                    Native::Prepared
                } else {
                    Native::Finished
                });
            }
            Action::PublishLoader => {
                let paused = self.loader_child.as_mut().unwrap().publish_or_exit();
                self.loader = Some(if paused {
                    Native::Paused
                } else {
                    self.loader_child.take();
                    Native::Finished
                });
            }
            Action::FinishLoader => {
                self.loader_child.take().unwrap().release();
                self.loader = Some(Native::Finished);
            }
            Action::KillLoader => {
                self.loader_child.take().unwrap().kill();
                self.loader = Some(Native::Killed);
            }
            Action::StartAbandon => {
                self.prepare(0);
                self.publish(0);
                let heads = read_heads(&self.repo);
                assert_eq!(
                    heads.len(),
                    2,
                    "jj must have added its new head before pausing"
                );
                assert!(
                    heads.contains(&self.old_head),
                    "the pending unlink already ran"
                );
            }
            Action::PrepareAbandon => self.prepare(0),
            Action::PreparePeer => self.prepare(1),
            Action::PublishAbandon => self.publish(0),
            Action::PublishPeer => self.publish(1),
            Action::FinishAbandon | Action::FinishPeer => {
                let slot = usize::from(action == Action::FinishPeer);
                self.children[slot].take().unwrap().release();
                self.native[slot] = Native::Finished;
            }
            Action::KillAbandon | Action::KillPeer => {
                let slot = usize::from(action == Action::KillPeer);
                self.children[slot].take().unwrap().kill();
                self.native[slot] = Native::Killed;
            }
            Action::Check | Action::InterruptPublication | Action::InterruptBeforePublication => {
                let heads = read_heads(&self.repo);
                let both = self.abandon_paused()
                    && heads.len() == 2
                    && heads.contains(&self.old_head)
                    && !self.put_back;
                let node = self.node.as_mut().unwrap();
                if action != Action::Check {
                    let before = action == Action::InterruptBeforePublication;
                    let expected = if before {
                        node.crash_taking_records(false);
                        "stopped for a test: Heads"
                    } else {
                        node.crash_publishing_taken_heads();
                        "stopped for a test: Publishing"
                    };
                    let error = node.check_abandon().unwrap_err();
                    assert!(
                        matches!(&error, NodeError::Io { source, .. }
                            if source.to_string() == expected),
                        "expected the publication interruption, got {error}"
                    );
                    self.node = None;
                    self.checked_heads = None;
                    self.interrupted = true;
                    self.stopped_before_publication = before;
                    self.put_back |= both;
                } else {
                    let noticed = node.check_abandon().unwrap();
                    self.checked_heads = (!noticed).then(|| self.head_keys(&heads));
                    self.put_back |= both && noticed;
                }
            }
            Action::Reopen | Action::ReopenWithoutCache => {
                if action == Action::ReopenWithoutCache {
                    let cache = self.repo.repo_path().join("musubi/translation");
                    match fs::remove_file(cache) {
                        Ok(()) => {}
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                        Err(error) => panic!("remove the disposable translation cache: {error}"),
                    }
                    self.lost_cache = true;
                }
                self.node =
                    Some(NodeRepo::open(&self.repo.repo_path(), &self.repo.settings()).unwrap());
            }
            Action::MergeHeads => {
                let node = self.node.as_mut().unwrap();
                node.settle().unwrap();
                node.merge_heads().unwrap();
                self.checked_heads = None;
            }
        }
        self.state()
    }

    /// Preserve the attempted action even if the real repository raised an error mid-step.
    fn attempt(&mut self, action: Action) -> (Step, Option<String>) {
        let (state, error) = match catch_unwind(AssertUnwindSafe(|| self.act(action))) {
            Ok(state) => (state, None),
            Err(error) => {
                let message = error
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| error.downcast_ref::<&str>().copied())
                    .unwrap_or("action panicked");
                (self.state(), Some(format!("{action:?}: {message}")))
            }
        };
        (
            Step {
                action,
                state,
                failed: error.is_some(),
            },
            error,
        )
    }

    fn violation(&mut self, state: &State) -> Option<String> {
        if state.heads.is_empty() {
            return Some("no operation heads".into());
        }
        for head in read_heads(&self.repo) {
            let id = OperationId::try_from_hex(&head).unwrap();
            if let Err(error) = self.store.read_operation(&id).block_on() {
                return Some(format!("unreadable operation head {head}: {error}"));
            }
        }
        if self.choices(state).is_empty() {
            if self.write_published
                && let Err(error) = self.check_write_kept()
            {
                return Some(error);
            }
            if self.put_back {
                return self.check_restored_head().err();
            }
        }
        None
    }

    /// The write's commit is in the view of every op head, settled, once it added its head.
    fn check_write_kept(&self) -> Result<(), String> {
        for head in read_heads(&self.repo) {
            let output = self
                .repo
                .program(Path::new("jj"))
                .args([
                    "--ignore-working-copy",
                    "--at-op",
                    &head,
                    "log",
                    "--no-graph",
                ])
                .args(["-r", &format!("description(substring:{WRITE_MARKER:?})")])
                .args(["-T", "commit_id"])
                .output()
                .map_err(|error| format!("run jj log: {error}"))?;
            if !output.status.success() {
                return Err(format!(
                    "jj log at {head} failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                ));
            }
            if output.stdout.is_empty() {
                return Err(format!("op head {head} lost the finished concurrent write"));
            }
        }
        Ok(())
    }

    fn check_restored_head(&mut self) -> Result<(), String> {
        let heads = read_heads(&self.repo);
        let [head] = heads.as_slice() else {
            return Err("put-back left multiple heads after settling".into());
        };
        let head = LocalOp(OperationId::try_from_hex(head).unwrap());
        let old = LocalOp(OperationId::try_from_hex(&self.old_head).unwrap());
        let restored = self.store.read_operation(&head.0).block_on().unwrap();
        // A published write changes the view; `check_write_kept` checks what it added.
        if !self.write_published && restored.view_id != self.old_view {
            return Err("put-back changed the original view".into());
        }
        let node = self.node.as_mut().unwrap();
        let id_before = node.canonicalize(&old).map_err(|error| error.to_string())?;
        let id_after = node
            .canonicalize(&head)
            .map_err(|error| error.to_string())?;
        // A second native publisher can put the rewritten head back after the daemon
        // retired it. jj may merge that alias with the restored head on the next sync.
        let kept = id_before == id_after
            || (self.concurrent
                && node
                    .canonical_store()
                    .is_ancestor_of(&id_before, &id_after)
                    .map_err(|error| error.to_string())?);
        if !kept || !node.pending_drops().is_empty() {
            return Err("put-back lost the original canonical history".into());
        }
        Ok(())
    }
}

/// Replays `trace`, checking each recorded state if `verify`. Returns where it ended, with any
/// error; or, for a schedule with a native merge, `None` if a step is disabled, as when jj
/// merged the heads otherwise this time.
fn replay(
    world: &mut World<'_>,
    trace: &Schedule,
    verify: bool,
) -> Option<(State, Option<String>)> {
    let mut state = world.state();
    for (index, step) in trace.steps.iter().enumerate() {
        let index = index + 1;
        if !world.choices(&state).contains(&step.action) {
            assert!(trace.loader, "step {index} ({:?}) is disabled", step.action);
            return None;
        }
        let (actual, error) = world.attempt(step.action);
        state = actual.state;
        if verify {
            assert_eq!(actual.failed, step.failed, "changed result at step {index}");
            assert_eq!(
                state, step.state,
                "replay diverged at step {index} ({:?})",
                step.action
            );
        }
        if error.is_some() {
            return Some((state, error));
        }
    }
    Some((state, None))
}

/// What the workers of a search share.
struct Search {
    agenda: VecDeque<(Schedule, Option<Action>)>,
    visited: HashMap<State, usize>,
    longest: Schedule,
    /// Workers running a branch, which may queue more.
    active: usize,
    /// Set once a worker finds a violation or panics: every worker stops.
    stop: bool,
    /// The first violation found, with the schedule that reached it.
    violation: Option<(Schedule, String)>,
}

#[derive(Default)]
struct Counts {
    runs: AtomicUsize,
    transitions: AtomicUsize,
    replayed: AtomicUsize,
    /// Branches a native merge made unreachable this time.
    dropped: AtomicUsize,
}

/// How many branches a search runs at once: `MUSUBI_HEAD_SCHEDULE_JOBS`, or half the CPUs,
/// leaving room on a shared machine.
fn jobs() -> usize {
    match std::env::var("MUSUBI_HEAD_SCHEDULE_JOBS") {
        Ok(jobs) => jobs
            .parse()
            .ok()
            .filter(|jobs| *jobs > 0)
            .expect("MUSUBI_HEAD_SCHEDULE_JOBS is a positive number"),
        Err(_) => std::thread::available_parallelism().map_or(1, |n| (n.get() / 2).max(1)),
    }
}

/// Explores the schedules after `prefix`, the first step after it other than
/// `different_from` if given, on several workers. Each worker restores its own copy of the
/// starting repositories for every branch, so branches share nothing but what `Search` holds.
fn explore(
    fixture: &Fixture<'_>,
    prefix: Schedule,
    different_from: Option<Action>,
) -> (Schedule, Option<String>) {
    let search = Mutex::new(Search {
        agenda: VecDeque::from([(prefix.clone(), None)]),
        visited: HashMap::new(),
        longest: prefix.clone(),
        active: 0,
        stop: false,
        violation: None,
    });
    let ready = Condvar::new();
    let counts = Counts::default();
    let horizon = fixture.horizon();
    let jobs = jobs();
    // Joined here, so that a violation one worker found is reported even if another panicked.
    let panicked = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..jobs)
            .map(|_| {
                scope.spawn(|| {
                    work(
                        fixture,
                        &prefix,
                        different_from,
                        horizon,
                        &search,
                        &ready,
                        &counts,
                    );
                })
            })
            .collect();
        // Join every worker, not just up to the first that panicked.
        let mut panicked = false;
        for worker in workers {
            panicked |= worker.join().is_err();
        }
        panicked
    });
    let Search {
        visited,
        longest,
        violation,
        ..
    } = search
        .into_inner()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let [runs, transitions, replayed, dropped] = [
        &counts.runs,
        &counts.transitions,
        &counts.replayed,
        &counts.dropped,
    ]
    .map(|count| count.load(Ordering::Relaxed));
    if let Some((trace, violation)) = violation {
        eprintln!("Found {violation} after {runs} runs and {transitions} explored transitions");
        return (trace, Some(violation));
    }
    assert!(!panicked, "a search worker panicked");
    assert!(
        different_from.is_none() || longest.steps.len() > prefix.steps.len(),
        "no alternative is enabled at that prefix"
    );
    if fixture.concurrent && prefix.steps.is_empty() {
        assert!(
            visited.keys().any(|state| {
                // Both abandons write the same new head; a write adds its own.
                state.native == Native::Paused
                    && state.peer == Some(Native::Paused)
                    && state.heads.len() == if fixture.peer.is_abandon() { 2 } else { 3 }
            }),
            "the search must reach two pending unlinks of the same old head"
        );
        assert!(
            !fixture.peer.is_abandon()
                || visited.keys().any(|state| {
                    state.online
                        && state.lost_cache
                        && state.stopped_before_publication
                        && [Some(state.native), state.peer].contains(&Some(Native::Finished))
                        && [Some(state.native), state.peer].contains(&Some(Native::Paused))
                        && state.heads.len() == 1
                }),
            "the search must restart after the first unlink while the second is pending"
        );
        assert!(
            fixture.peer.is_abandon()
                || visited.keys().any(|state| {
                    state.online
                        && state.lost_cache
                        && state.stopped_before_publication
                        && state.native == Native::Finished
                        && state.peer == Some(Native::Finished)
                }),
            "the search must finish both commands after a restart that lost the cache"
        );
        assert!(
            !fixture.loader
                || visited
                    .keys()
                    .any(|state| state.loader == Some(Native::Paused)),
            "the search must pause a native merge between adding and removing heads"
        );
        for (loader, what) in [
            (Native::Killed, "kill a native merge"),
            (Native::Finished, "finish a native merge"),
        ] {
            assert!(
                !fixture.loader || visited.keys().any(|state| state.loader == Some(loader)),
                "the search must {what}"
            );
        }
    }
    eprintln!(
        "Explored {transitions} transitions across {runs} runs and {} observed states \
         (replayed {replayed} prefix steps, dropped {dropped} branches, horizon {horizon}, \
         {jobs} jobs)",
        visited.len()
    );
    (longest, None)
}

/// Decrements the active workers when a branch ends, even by a panic, which stops the search.
struct Running<'a> {
    search: &'a Mutex<Search>,
    ready: &'a Condvar,
}

impl Drop for Running<'_> {
    fn drop(&mut self) {
        let mut search = self
            .search
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        search.active -= 1;
        search.stop |= std::thread::panicking();
        self.ready.notify_all();
    }
}

fn work(
    fixture: &Fixture<'_>,
    prefix: &Schedule,
    different_from: Option<Action>,
    horizon: usize,
    search: &Mutex<Search>,
    ready: &Condvar,
    counts: &Counts,
) {
    loop {
        let (mut trace, next) = {
            let mut shared = search.lock().unwrap();
            loop {
                if shared.stop {
                    return;
                }
                if let Some(branch) = shared.agenda.pop_front() {
                    shared.active += 1;
                    break branch;
                }
                if shared.active == 0 {
                    return;
                }
                shared = ready.wait(shared).unwrap();
            }
        };
        let _running = Running { search, ready };
        let mut world = fixture.restore();
        counts.runs.fetch_add(1, Ordering::Relaxed);
        // jj orders the parents of a merge it makes of heads with equal end times as it
        // pleases, and musubi's rewrites of the merge follow that order: a schedule with a
        // native merge need not reach the same states again. Continue from where it does.
        let Some((mut state, mut error)) = replay(&mut world, &trace, !fixture.loader) else {
            counts.dropped.fetch_add(1, Ordering::Relaxed);
            continue;
        };
        counts
            .replayed
            .fetch_add(trace.steps.len(), Ordering::Relaxed);
        let mut following = next;
        loop {
            if let Some(violation) = error.take().or_else(|| world.violation(&state)) {
                let mut shared = search.lock().unwrap();
                shared.stop = true;
                if shared.violation.is_none() {
                    shared.violation = Some((trace, violation));
                }
                return;
            }
            let action = if let Some(action) = following.take() {
                if !world.choices(&state).contains(&action) {
                    assert!(fixture.loader, "{action:?} is disabled after its prefix");
                    counts.dropped.fetch_add(1, Ordering::Relaxed);
                    break;
                }
                action
            } else {
                // Keep the budget in the key so an earlier, deeper visit cannot hide a
                // continuation that a shorter prefix has room to explore.
                let remaining = horizon - trace.steps.len();
                let mut key = state.clone();
                // Both commands run the same abandon against the same immutable inputs.
                // Swapping their slots gives the same continuations and head files.
                if let Some(peer) = &mut key.peer
                    && fixture.peer.is_abandon()
                    && *peer < key.native
                {
                    std::mem::swap(&mut key.native, peer);
                }
                let choosing_branch =
                    different_from.is_some() && trace.steps.len() == prefix.steps.len();
                let symmetric = !choosing_branch
                    && fixture.peer.is_abandon()
                    && state.peer == Some(state.native);
                let mut choices = world.choices(&state).into_iter().filter(|action| {
                    !(choosing_branch && Some(*action) == different_from
                        || symmetric
                            && matches!(
                                action,
                                Action::PublishPeer | Action::FinishPeer | Action::KillPeer
                            ))
                });
                let mut shared = search.lock().unwrap();
                if shared.stop {
                    break;
                }
                if trace.steps.len() > shared.longest.steps.len() {
                    shared.longest = trace.clone();
                }
                if remaining == 0
                    || shared
                        .visited
                        .get(&key)
                        .is_some_and(|seen| *seen >= remaining)
                {
                    break;
                }
                shared.visited.insert(key, remaining);
                let Some(action) = choices.next() else {
                    break;
                };
                let before = shared.agenda.len();
                shared
                    .agenda
                    .extend(choices.map(|other| (trace.clone(), Some(other))));
                if shared.agenda.len() > before {
                    ready.notify_all();
                }
                action
            };
            let (step, failure) = world.attempt(action);
            state.clone_from(&step.state);
            error = failure;
            trace.steps.push(step);
            counts.transitions.fetch_add(1, Ordering::Relaxed);
        }
    }
}

fn load(path: &Path) -> Schedule {
    let trace: Schedule = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    assert!(
        (1..=VERSION).contains(&trace.version),
        "unsupported schedule version"
    );
    assert!(
        trace.steps.len() <= horizon(trace.concurrent, trace.loader),
        "schedule exceeds the search horizon; pass a larger --steps"
    );
    trace
}

fn save(path: &Path, trace: &Schedule) {
    let mut json = serde_json::to_vec_pretty(trace).unwrap();
    json.push(b'\n');
    fs::write(path, json).unwrap();
    eprintln!("Saved replay schedule to {}", path.display());
}

#[test]
#[ignore = "requires a dynamically linked Linux jj and a C compiler; run just head-schedule search"]
fn run() {
    let cache = Path::new(env!("CARGO_TARGET_TMPDIR")).join("head_schedule");
    let library = musubi_testutil::recorded(&cache, "gate", |directory| {
        fs::create_dir_all(directory).unwrap();
        Gate::compile(directory);
    });
    let gate = Gate::load(&library);
    let mode = std::env::var("MUSUBI_HEAD_SCHEDULE_MODE").unwrap_or_else(|_| "search".into());
    let trace = std::env::var_os("MUSUBI_HEAD_SCHEDULE_INPUT").map(|input| load(Path::new(&input)));
    let unpublished = trace.as_ref().map_or_else(
        || std::env::var_os("MUSUBI_HEAD_SCHEDULE_UNPUBLISHED").is_some(),
        |trace| trace.unpublished,
    );
    let concurrent = trace.as_ref().map_or_else(
        || std::env::var_os("MUSUBI_HEAD_SCHEDULE_CONCURRENT").is_some(),
        |trace| trace.concurrent,
    );
    let peer = trace.as_ref().map_or_else(
        || match std::env::var("MUSUBI_HEAD_SCHEDULE_PEER").as_deref() {
            Ok("write") => Peer::Write,
            Ok("abandon") | Err(_) => Peer::Abandon,
            Ok(other) => panic!("unknown MUSUBI_HEAD_SCHEDULE_PEER {other}"),
        },
        |trace| trace.peer,
    );
    assert!(
        concurrent || peer.is_abandon(),
        "a write peer needs a concurrent search"
    );
    let loader = trace.as_ref().map_or_else(
        || std::env::var_os("MUSUBI_HEAD_SCHEDULE_LOADER").is_some(),
        |trace| trace.loader,
    );
    assert!(concurrent || !loader, "a loader needs a concurrent search");
    let fixture = Fixture::load(&gate, &cache, unpublished, concurrent, peer, loader);
    let (trace, violation) = match mode.as_str() {
        "search" => explore(&fixture, fixture.empty_schedule(), None),
        "replay" => {
            let trace = trace.unwrap();
            let mut world = fixture.restore();
            // As in a search, a native merge need not reach the recorded states again.
            let verify =
                std::env::var_os("MUSUBI_HEAD_SCHEDULE_ACTIONS_ONLY").is_none() && !trace.loader;
            let (state, error) = replay(&mut world, &trace, verify).expect(
                "a step is disabled: jj merged the heads otherwise this time; replay it again",
            );
            (trace, error.or_else(|| world.violation(&state)))
        }
        "branch" => {
            let mut trace = trace.unwrap();
            let at: usize = std::env::var("MUSUBI_HEAD_SCHEDULE_AT")
                .unwrap()
                .parse()
                .unwrap();
            assert!(
                at < trace.steps.len(),
                "branch requires a following action to replace"
            );
            let next = trace.steps[at].action;
            trace.steps.truncate(at);
            explore(&fixture, trace, Some(next))
        }
        _ => panic!("unknown schedule mode {mode}"),
    };
    if let Some(path) = std::env::var_os("MUSUBI_HEAD_SCHEDULE_OUTPUT") {
        save(Path::new(&path), &trace);
    }
    assert!(violation.is_none(), "{violation:?}");
}

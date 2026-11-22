//! Explore schedules around real jj writes to the op heads and musubi's moves of them.

#![allow(clippy::unwrap_used)]

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex};

use jj_lib::content_hash::blake2b_hash;
use jj_lib::object_id::ObjectId as _;
use jj_lib::op_store::{OpStore, OperationId};
use musubi_jj::node::NodeRepo;
use musubi_testutil::{TestEnv, TestRepo};
use pollster::FutureExt as _;
use serde::{Deserialize, Serialize};

mod gate;
use gate::{Gate, PausedCommand};

use crate::translation::{single_canonical_head, sync};

const MAX_STEPS: usize = 8;
const CONCURRENT_STEPS: usize = 14;
/// A native merge widens the search: it reaches every state by this many actions.
const LOADER_STEPS: usize = 22;
const VERSION: u8 = 4;

#[derive(Clone, Copy, Debug, Deserialize, Eq, Hash, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
enum Action {
    /// The first native command, prepared and published at once.
    StartFirst,
    PrepareFirst,
    PreparePeer,
    PublishFirst,
    PublishPeer,
    FinishFirst,
    FinishPeer,
    KillFirst,
    KillPeer,
    /// The daemon reads the op heads as each of its steps begins.
    Check,
    /// The daemon stops, and starts again with `Reopen`.
    Stop,
    Reopen,
    ReopenWithoutCache,
    MergeHeads,
    StartLoader,
    PublishLoader,
    FinishLoader,
    KillLoader,
    UnlinkLoader,
    Receive,
    /// The daemon's check while a native command holds jj's op-heads lock: should it move op
    /// heads, the command finishes before it takes the lock.
    CheckWhileLocked,
    /// The daemon receives the other machine's work while a native command holds the lock: its
    /// advance waits for the command to finish before it takes the lock.
    ReceiveWhileLocked,
}

#[allow(clippy::trivially_copy_pass_by_ref)]
fn is_zero(count: &usize) -> bool {
    *count == 0
}

/// The descriptions the first native command and the peer give the commits they write, to find
/// them afterwards.
const FIRST_MARKER: &str = "musubi head-schedule first";
const WRITE_MARKER: &str = "musubi head-schedule write";
const MARKERS: [&str; 2] = [FIRST_MARKER, WRITE_MARKER];
/// The description the other machine gives its work before this one receives it.
const RECEIVE_MARKER: &str = "musubi head-schedule received";

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
    /// How many heads the loader removed one at a time: two paused merges with the same heads
    /// can have different removals still to come.
    #[serde(default, skip_serializing_if = "is_zero")]
    loader_unlinks: usize,
    /// Whether the daemon received the other machine's work.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    received: bool,
    heads: Vec<String>,
    checked_heads: Option<Vec<String>>,
    online: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    lost_cache: bool,
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
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    loader: bool,
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    receive: bool,
    steps: Vec<Step>,
}

/// Whether replaying a schedule reaches the same states. jj orders the parents of a merge of
/// heads with equal end times as its hash set gives them, and musubi's rewrites of the merge
/// follow that order: a native command or a sync that loads the repository at several heads
/// makes one.
fn exact(loader: bool, receive: bool) -> bool {
    !loader && !receive
}

impl Schedule {
    fn exact(&self) -> bool {
        exact(self.loader, self.receive)
    }
}

/// Two copies of a hive: `alpha` and `beta`, which has realized what `alpha` wrote, with work of
/// its own that it hasn't published if `unpublished`. Returns `beta`'s node.
fn synced_copies(unpublished: bool) -> (TestEnv, NodeRepo) {
    let env = TestEnv::new();
    let a = env.init_repo("alpha");
    let b = env.init_repo("beta");
    let mut receiver = NodeRepo::open(&b.repo_path(), &b.settings()).unwrap();
    let mut sender = NodeRepo::open(&a.repo_path(), &a.settings()).unwrap();
    let joined = single_canonical_head(&mut receiver);
    sync(&receiver, &mut sender, &joined);
    a.jj(&["describe", "-m", "first"]);
    a.jj(&["describe", "-m", "second"]);
    let base = single_canonical_head(&mut sender);
    sync(&sender, &mut receiver, &base);
    if unpublished {
        b.jj(&["describe", "-m", "unpublished"]);
    }
    fs::write(b.repo_path().join("musubi/accepted_base"), base.0.hex()).unwrap();
    (env, receiver)
}

struct Fixture<'a> {
    gate: &'a Gate,
    directory: PathBuf,
    unpublished: bool,
    concurrent: bool,
    loader: bool,
    receive: bool,
}

impl<'a> Fixture<'a> {
    fn load(
        gate: &'a Gate,
        cache: &Path,
        unpublished: bool,
        concurrent: bool,
        loader: bool,
        receive: bool,
    ) -> Self {
        let case = if unpublished {
            "unpublished"
        } else {
            "realized"
        };
        let directory = musubi_testutil::recorded(cache, case, |directory| {
            let (env, node) = synced_copies(unpublished);
            drop(node);
            env.save(directory);
        });
        Self {
            gate,
            directory,
            unpublished,
            concurrent,
            loader,
            receive,
        }
    }

    fn restore(&self) -> World<'_> {
        let env = TestEnv::restore(&self.directory);
        let repo = env.repo_handle("beta");
        let node = NodeRepo::open(&repo.repo_path(), &repo.settings()).unwrap();
        let heads = read_heads(&repo);
        let [start] = heads.try_into().unwrap();
        let store = node.loader().op_store().clone();
        let old_id = OperationId::try_from_hex(&start).unwrap();
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
            node: Some(node),
            native: [Native::Ready; 2],
            children: [None, None],
            loader: self.loader.then_some(Native::Ready),
            loader_child: None,
            loader_unlinks: 0,
            receive: self.receive,
            received: false,
            concurrent: self.concurrent,
            checked_heads: None,
            lost_cache: false,
            keys: RefCell::new(keys),
            published: [false; 2],
            store,
            repo,
            env,
        }
    }

    fn empty_schedule(&self) -> Schedule {
        Schedule {
            version: VERSION,
            unpublished: self.unpublished,
            concurrent: self.concurrent,
            loader: self.loader,
            receive: self.receive,
            steps: vec![],
        }
    }

    fn horizon(&self) -> usize {
        horizon(self.concurrent, self.loader)
    }

    fn exact(&self) -> bool {
        exact(self.loader, self.receive)
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
    node: Option<NodeRepo>,
    native: [Native; 2],
    // Reap the commands before removing the environment's directory.
    children: [Option<PausedCommand>; 2],
    loader: Option<Native>,
    loader_child: Option<PausedCommand>,
    loader_unlinks: usize,
    /// Whether the search may receive the other machine's work, and whether it has.
    receive: bool,
    received: bool,
    concurrent: bool,
    checked_heads: Option<Vec<String>>,
    lost_cache: bool,
    /// Each operation's key, as `key` works it out.
    keys: RefCell<HashMap<OperationId, OperationId>>,
    /// Whether each native command added its head: jj merges it later even if the command is
    /// killed before its unlink.
    published: [bool; 2],
    store: Arc<dyn OpStore>,
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
        State {
            native: self.native[0],
            peer: self.concurrent.then_some(self.native[1]),
            loader: self.loader,
            loader_unlinks: self.loader_unlinks,
            received: self.received,
            heads: self.head_keys(&read_heads(&self.repo)),
            checked_heads: self.checked_heads.clone(),
            online: self.node.is_some(),
            lost_cache: self.lost_cache,
        }
    }

    fn choices(&self, state: &State) -> Vec<Action> {
        let mut choices = vec![];
        // A command that writes takes jj's op-heads lock before it adds its head, and keeps it
        // until the old one is gone, so the second starts once the first is done or killed, from
        // the one op head that is left.
        for (slot, status) in self.native.iter().enumerate() {
            let (prepare, publish, finish, kill) = if slot == 0 {
                (
                    if self.concurrent {
                        Action::PrepareFirst
                    } else {
                        Action::StartFirst
                    },
                    Action::PublishFirst,
                    Action::FinishFirst,
                    Action::KillFirst,
                )
            } else {
                (
                    Action::PreparePeer,
                    Action::PublishPeer,
                    Action::FinishPeer,
                    Action::KillPeer,
                )
            };
            match status {
                Native::Ready if slot == 0 => choices.push(prepare),
                Native::Ready
                    if self.concurrent
                        && self.native[0] != Native::Ready
                        && !self.locked()
                        && state.heads.len() == 1 =>
                {
                    choices.push(prepare);
                }
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
        if !state.online {
            choices.push(Action::Reopen);
            if self.concurrent {
                choices.push(Action::ReopenWithoutCache);
            }
        } else if state.checked_heads.as_ref() != Some(&state.heads) && self.locked() {
            // Moving op heads takes jj's op-heads lock, so a check that moves any waits for the
            // command holding it to finish. This lets it finish just before such a move.
            choices.push(Action::CheckWhileLocked);
        } else if state.checked_heads.as_ref() != Some(&state.heads) {
            choices.push(Action::Check);
        } else if self.concurrent && state.heads.len() > 1 && !self.locked() {
            choices.push(Action::MergeHeads);
        }
        if self.concurrent && state.online {
            choices.push(Action::Stop);
        }
        // Receiving publishes heads under jj's op-heads lock, so while a command holds it, the
        // command finishes first. The first native command starts first, and the daemon receives
        // during and after the commands.
        if self.receive && self.native[0] != Native::Ready && !self.received && state.online {
            choices.push(if self.locked() {
                Action::ReceiveWhileLocked
            } else {
                Action::Receive
            });
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
                choices.push(Action::UnlinkLoader);
                choices.push(Action::FinishLoader);
                choices.push(Action::KillLoader);
            }
            _ => {}
        }
        choices
    }

    /// Whether a native command holds jj's op-heads lock, which loading at several heads waits
    /// for.
    fn locked(&self) -> bool {
        self.writer().is_some() || matches!(self.loader, Some(Native::Prepared | Native::Paused))
    }

    /// The write that holds jj's op-heads lock, if one does: an ordinary command takes it before
    /// adding its new head and keeps it until the old one is gone. Loading the repository at
    /// several heads waits for it, as merging them does; the daemon's own publication of heads
    /// waits too.
    fn writer(&self) -> Option<usize> {
        self.native
            .iter()
            .position(|status| matches!(status, Native::Prepared | Native::Paused))
    }

    /// The daemon receives what the other machine wrote.
    fn receive(&mut self) {
        let alpha = self.env.repo_handle("alpha");
        alpha.jj(&["describe", "-m", RECEIVE_MARKER]);
        let mut from = NodeRepo::open(&alpha.repo_path(), &alpha.settings()).unwrap();
        let head = single_canonical_head(&mut from);
        sync(&from, self.node.as_mut().unwrap(), &head);
        self.received = true;
        self.checked_heads = None;
    }

    /// Starts native command `slot`, paused where it is about to add its head, on the one op
    /// head there is.
    fn prepare(&mut self, slot: usize) {
        let [head] = read_heads(&self.repo)
            .try_into()
            .expect("a command starts from one op head");
        let gated = self.repo.repo_path().join("op_heads/heads").join(&head);
        let mut command = self.repo.program(Path::new("jj"));
        // The first describes the working-copy commit, and the second adds one on top of it, so
        // that each leaves a commit with its description.
        if slot == 0 {
            command.args([
                "--ignore-working-copy",
                "describe",
                "-r",
                "@",
                "-m",
                MARKERS[0],
            ]);
        } else {
            command.args(["--ignore-working-copy", "new", "-m", MARKERS[1]]);
        }
        command.env("COLUMNS", "80").env("RAYON_NUM_THREADS", "1");
        self.children[slot] = Some(self.gate.spawn(
            &mut command,
            &gated,
            &self.env.root().join(format!("gate-{slot}")),
        ));
        self.native[slot] = Native::Prepared;
        assert_eq!(
            read_heads(&self.repo),
            [head],
            "preparing must leave just the old head"
        );
    }

    fn publish(&mut self, slot: usize) {
        self.children[slot].as_mut().unwrap().publish();
        self.native[slot] = Native::Paused;
        self.published[slot] = true;
    }

    fn act(&mut self, action: Action) -> State {
        match action {
            Action::StartLoader => {
                // Only the directory of the head matters to a command that merges heads.
                let heads = read_heads(&self.repo);
                let gated = self.repo.repo_path().join("op_heads/heads").join(&heads[0]);
                let mut command = self.repo.program(Path::new("jj"));
                command
                    .args(["--ignore-working-copy", "op", "log", "-n1", "--no-graph"])
                    .args(["-T", "id"])
                    .env("COLUMNS", "80")
                    .env("RAYON_NUM_THREADS", "1");
                self.loader_child = self.gate.spawn_loader(
                    &mut command,
                    &gated,
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
            Action::UnlinkLoader => {
                let paused = self.loader_child.as_mut().unwrap().unlink_one();
                self.loader_unlinks += 1;
                if !paused {
                    self.loader_child.take();
                    self.loader = Some(Native::Finished);
                }
            }
            Action::FinishLoader => {
                self.loader_child.take().unwrap().release();
                self.loader = Some(Native::Finished);
            }
            Action::KillLoader => {
                self.loader_child.take().unwrap().kill();
                self.loader = Some(Native::Killed);
            }
            Action::StartFirst => {
                let before = read_heads(&self.repo);
                self.prepare(0);
                self.publish(0);
                let heads = read_heads(&self.repo);
                assert_eq!(
                    heads.len(),
                    2,
                    "jj must have added its new head before pausing"
                );
                assert!(
                    before.iter().all(|head| heads.contains(head)),
                    "the pending unlink already ran"
                );
            }
            Action::PrepareFirst => self.prepare(0),
            Action::PreparePeer => self.prepare(1),
            Action::PublishFirst => self.publish(0),
            Action::PublishPeer => self.publish(1),
            Action::FinishFirst | Action::FinishPeer => {
                let slot = usize::from(action == Action::FinishPeer);
                self.children[slot].take().unwrap().release();
                self.native[slot] = Native::Finished;
            }
            Action::KillFirst | Action::KillPeer => {
                let slot = usize::from(action == Action::KillPeer);
                self.children[slot].take().unwrap().kill();
                self.native[slot] = Native::Killed;
            }
            Action::Check => {
                let heads = read_heads(&self.repo);
                // What each of the daemon's steps does first (`Node::read_heads`): reads the
                // op heads, canonicalizing them. Where that moves any, it checks again.
                let node = self.node.as_mut().unwrap();
                node.settle().unwrap();
                node.canonical_heads().unwrap();
                self.checked_heads = Some(self.head_keys(&heads));
            }
            Action::CheckWhileLocked | Action::ReceiveWhileLocked => {
                // Whichever command holds the lock: a write, or a native merge.
                let loader = matches!(self.loader, Some(Native::Prepared | Native::Paused));
                let writer = self.writer();
                let (holder, prepared) = if loader {
                    (
                        self.loader_child.take(),
                        self.loader == Some(Native::Prepared),
                    )
                } else {
                    let slot = writer.unwrap();
                    (
                        self.children[slot].take(),
                        self.native[slot] == Native::Prepared,
                    )
                };
                let holder = Arc::new(Mutex::new(holder));
                let finished = Arc::new(AtomicBool::new(false));
                let heads = read_heads(&self.repo);
                {
                    let (holder, finished) = (holder.clone(), finished.clone());
                    self.node.as_ref().unwrap().race_head_move(move || {
                        if let Some(mut command) = holder.lock().unwrap().take() {
                            // A merge whose heads settled first adds and removes none.
                            let paused = !prepared
                                || if loader {
                                    command.publish_or_exit()
                                } else {
                                    command.publish();
                                    true
                                };
                            if paused {
                                command.release();
                            }
                            finished.store(true, Ordering::Relaxed);
                        }
                    });
                }
                if action == Action::CheckWhileLocked {
                    let node = self.node.as_mut().unwrap();
                    node.settle().unwrap();
                    node.canonical_heads().unwrap();
                } else {
                    self.receive();
                }
                let back = holder.lock().unwrap().take();
                if finished.load(Ordering::Relaxed) {
                    if loader {
                        self.loader = Some(Native::Finished);
                    } else {
                        let slot = writer.unwrap();
                        self.native[slot] = Native::Finished;
                        self.published[slot] = true;
                    }
                    self.checked_heads = None;
                } else {
                    // It moved nothing, and so took no lock: the command waits where it was.
                    if loader {
                        self.loader_child = back;
                    } else {
                        self.children[writer.unwrap()] = back;
                    }
                    if action == Action::CheckWhileLocked {
                        self.checked_heads = Some(self.head_keys(&heads));
                    }
                }
            }
            Action::Stop => {
                self.node = None;
                self.checked_heads = None;
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
            Action::Receive => self.receive(),
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
            for (slot, marker) in MARKERS.into_iter().enumerate() {
                if self.published[slot]
                    && let Err(error) = self.check_kept(marker, "a native command's work")
                {
                    return Some(error);
                }
            }
            if self.received
                && let Err(error) = self.check_kept(RECEIVE_MARKER, "the received work")
            {
                return Some(error);
            }
        }
        None
    }

    /// A commit described with `marker` is in the view of every op head, settled.
    fn check_kept(&self, marker: &str, what: &str) -> Result<(), String> {
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
                .args(["-r", &format!("description(substring:{marker:?})")])
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
                return Err(format!("op head {head} lost {what}"));
            }
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
            assert!(
                !trace.exact(),
                "step {index} ({:?}) is disabled",
                step.action
            );
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
    // A merge that went otherwise makes a prefix unreachable now and then; many such would
    // mean the harness disables steps it shouldn't.
    assert!(
        dropped * 10 <= runs,
        "dropped {dropped} of {runs} branches: replay is not reaching the recorded steps"
    );
    assert!(
        different_from.is_none() || longest.steps.len() > prefix.steps.len(),
        "no alternative is enabled at that prefix"
    );
    if fixture.concurrent && prefix.steps.is_empty() {
        // Each command ends, finished or killed, before the next starts, around a daemon that
        // restarted and lost its cache. Two commands take three actions each, and the restart
        // one more; a shorter search is for a quick look.
        assert!(
            horizon < 7
                || visited.keys().any(|state| {
                    state.online
                        && state.lost_cache
                        && state.native == Native::Finished
                        && matches!(state.peer, Some(Native::Finished | Native::Killed))
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
        assert!(
            !fixture.receive
                || visited.keys().any(|state| {
                    state.received && matches!(state.native, Native::Finished | Native::Killed)
                }),
            "the search must receive the other machine's work after a command ends"
        );
        for (loader, what) in [
            (Native::Killed, "kill a native merge"),
            (Native::Finished, "finish a native merge"),
        ] {
            assert!(
                horizon < 8
                    || !fixture.loader
                    || visited.keys().any(|state| state.loader == Some(loader)),
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
        let Some((mut state, mut error)) = replay(&mut world, &trace, fixture.exact()) else {
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
                    assert!(!fixture.exact(), "{action:?} is disabled after its prefix");
                    counts.dropped.fetch_add(1, Ordering::Relaxed);
                    break;
                }
                action
            } else {
                // Keep the budget in the key so an earlier, deeper visit cannot hide a
                // continuation that a shorter prefix has room to explore.
                let remaining = horizon - trace.steps.len();
                let key = state.clone();
                let choosing_branch =
                    different_from.is_some() && trace.steps.len() == prefix.steps.len();
                let mut choices = world
                    .choices(&state)
                    .into_iter()
                    .filter(|action| !(choosing_branch && Some(*action) == different_from));
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
    let loader = trace.as_ref().map_or_else(
        || std::env::var_os("MUSUBI_HEAD_SCHEDULE_LOADER").is_some(),
        |trace| trace.loader,
    );
    assert!(concurrent || !loader, "a loader needs a concurrent search");
    let receive = trace.as_ref().map_or_else(
        || std::env::var_os("MUSUBI_HEAD_SCHEDULE_RECEIVE").is_some(),
        |trace| trace.receive,
    );
    let fixture = Fixture::load(&gate, &cache, unpublished, concurrent, loader, receive);
    let (trace, violation) = match mode.as_str() {
        "search" => explore(&fixture, fixture.empty_schedule(), None),
        "replay" => {
            let trace = trace.unwrap();
            let mut world = fixture.restore();
            // As in a search, a native merge need not reach the recorded states again.
            let verify =
                std::env::var_os("MUSUBI_HEAD_SCHEDULE_ACTIONS_ONLY").is_none() && trace.exact();
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

//! Explore schedules around a real jj op-head unlink and musubi's abandon check.

#![allow(clippy::unwrap_used)]

use std::collections::{HashMap, VecDeque};
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;

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
    steps: Vec<Step>,
}

struct Fixture<'a> {
    gate: &'a Gate,
    directory: PathBuf,
    parent: String,
    unpublished: bool,
    concurrent: bool,
    peer: Peer,
}

impl<'a> Fixture<'a> {
    fn load(gate: &'a Gate, cache: &Path, unpublished: bool, concurrent: bool, peer: Peer) -> Self {
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
        World {
            gate: self.gate,
            parent: &self.parent,
            old_head,
            node: Some(node),
            native: [Native::Ready; 2],
            children: [None, None],
            concurrent: self.concurrent,
            peer: self.peer,
            checked_heads: None,
            interrupted: false,
            stopped_before_publication: false,
            lost_cache: false,
            put_back: false,
            merge_ids: HashMap::new(),
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
            steps: vec![],
        }
    }

    fn horizon(&self) -> usize {
        horizon(self.concurrent)
    }
}

/// The most actions a schedule may take: `MUSUBI_HEAD_SCHEDULE_STEPS` if set, to search
/// deeper, or else the default for the kind of search.
fn horizon(concurrent: bool) -> usize {
    match std::env::var("MUSUBI_HEAD_SCHEDULE_STEPS") {
        Ok(steps) => steps
            .parse()
            .expect("MUSUBI_HEAD_SCHEDULE_STEPS is a number of actions"),
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
    concurrent: bool,
    peer: Peer,
    checked_heads: Option<Vec<String>>,
    interrupted: bool,
    stopped_before_publication: bool,
    lost_cache: bool,
    put_back: bool,
    merge_ids: HashMap<OperationId, OperationId>,
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
            .map(|head| {
                let id = OperationId::try_from_hex(head).unwrap();
                self.merge_ids
                    .get(&id)
                    .map_or_else(|| head.clone(), OperationId::hex)
            })
            .collect();
        keys.sort_unstable();
        keys
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
        } else if self.concurrent && state.heads.len() > 1 && !self.write_locked() {
            choices.push(Action::MergeHeads);
        }
        choices
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
                let head = node.merge_heads().unwrap();
                let mut body = self.store.read_operation(&head.0).block_on().unwrap();
                if body.parents.len() > 1 {
                    // The native merge orders by end time. Equal-time parents can come
                    // out in either order. Compare its whole body modulo that order.
                    for parent in &mut body.parents {
                        if let Some(key) = self.merge_ids.get(parent) {
                            parent.clone_from(key);
                        }
                    }
                    body.parents.sort_unstable();
                    self.merge_ids
                        .insert(head.0, OperationId::new(blake2b_hash(&body).to_vec()));
                }
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

fn replay(world: &mut World<'_>, trace: &Schedule, verify: bool) -> (State, Option<String>) {
    let mut state = world.state();
    for (index, step) in trace.steps.iter().enumerate() {
        let index = index + 1;
        assert!(
            world.choices(&state).contains(&step.action),
            "step {index} is disabled"
        );
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
            return (state, error);
        }
    }
    (state, None)
}

fn explore(
    fixture: &Fixture<'_>,
    prefix: Schedule,
    different_from: Option<Action>,
) -> (Schedule, Option<String>) {
    let mut agenda = VecDeque::from([(prefix.clone(), None)]);
    let mut visited = HashMap::new();
    let mut longest = prefix.clone();
    let mut runs = 0;
    let mut transitions = 0;
    let mut replayed = 0;
    let horizon = fixture.horizon();

    while let Some((mut trace, next)) = agenda.pop_front() {
        let mut world = fixture.restore();
        runs += 1;
        let (mut state, mut error) = replay(&mut world, &trace, true);
        replayed += trace.steps.len();
        let mut following = next;
        loop {
            if let Some(violation) = error.take().or_else(|| world.violation(&state)) {
                eprintln!(
                    "Found {violation} after {runs} runs and {transitions} explored transitions"
                );
                return (trace, Some(violation));
            }
            if trace.steps.len() > longest.steps.len() {
                longest = trace.clone();
            }
            let action = if let Some(action) = following.take() {
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
                if remaining == 0 || visited.get(&key).is_some_and(|seen| *seen >= remaining) {
                    break;
                }
                visited.insert(key, remaining);
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
                let Some(action) = choices.next() else {
                    break;
                };
                agenda.extend(choices.map(|other| (trace.clone(), Some(other))));
                action
            };
            let (step, failure) = world.attempt(action);
            state.clone_from(&step.state);
            error = failure;
            trace.steps.push(step);
            transitions += 1;
        }
    }

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
    }
    eprintln!(
        "Explored {transitions} transitions across {runs} runs and {} observed states \
         (replayed {replayed} prefix steps, horizon {horizon})",
        visited.len()
    );
    (longest, None)
}

fn load(path: &Path) -> Schedule {
    let trace: Schedule = serde_json::from_slice(&fs::read(path).unwrap()).unwrap();
    assert!(
        (1..=VERSION).contains(&trace.version),
        "unsupported schedule version"
    );
    assert!(
        trace.steps.len() <= horizon(trace.concurrent),
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
    let fixture = Fixture::load(&gate, &cache, unpublished, concurrent, peer);
    let (trace, violation) = match mode.as_str() {
        "search" => explore(&fixture, fixture.empty_schedule(), None),
        "replay" => {
            let trace = trace.unwrap();
            let mut world = fixture.restore();
            let verify = std::env::var_os("MUSUBI_HEAD_SCHEDULE_ACTIONS_ONLY").is_none();
            let (state, error) = replay(&mut world, &trace, verify);
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

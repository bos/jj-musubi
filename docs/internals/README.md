# Contributor docs

Start with [CONTRIBUTING.md](../../CONTRIBUTING.md) for setup and checks, and
[AGENTS.md](../../AGENTS.md) for the repository's working agreement. For using musubi, see
the [user guide](../README.md). These documents use the terms defined in the design's
[Vocabulary](design.md#vocabulary): hive, node, hub, canonical operation, realization.

## Architecture

- [Design](design.md): What does musubi replicate, how do machines agree, including on
  remotes and shared config, and why? Read it before changing what musubi does.
- [Sync protocol](protocol.md): What exactly do nodes and the hub say to each other, and what
  properties does that guarantee? This owns the state machines and their invariants.
- [Race catalogue](races.md): What happens when machines change the same thing at once, and
  which test pins each outcome?
- [Duplicates, moves and keys](copies.md): How does musubi distinguish copies, moves and
  reused machine names, and which cases does it refuse?

## Verification and testing

- [Testing philosophy](testing-philosophy.md): What must a test protect, what evidence does
  each kind of change need, and how do you know a test works? This owns testing policy.
- [Testing](testing.md): Which layers of tests are there, what does each guard against, and
  where does a new test belong?
- [Efficient tests](efficient-tests.md): How should a new test be written so that the suite
  stays fast?
- [Conformance](conformance.md): How are the Rust protocol core, and which copies a hive
  shows, checked against the Lean model? This owns the correspondence, assumptions and gaps.
- [Bounded storage verification](bounded-verification.md): What does the Kani harness check
  about storage failures and retries, and within which bounds?
- [The Lean model](../../formal/README.md): What does the model prove, and how does it
  correspond to the protocol?
- [Working on Lean proofs](lean.md): How do you state a proof boundary, check its source
  assumptions, develop the proof and connect it to the code?
- [Benchmarks](../../bench/README.md): How does musubi compare with git and jj's own clone,
  fetch and push, in time and bytes on the wire? How does the canonical store keep up with a
  long operation log?

## Review and release

- [Code reviews](code-reviews.md): What does a review look for, in what musubi does and in
  what users see?
- [Releasing](releasing.md): How is a release made?

Keep each rule in the document that owns it, and link to it from others. Describe the
current system; jj's history records how it got here.

## Finding the code

The crates, from the bottom up:

- [musubi-core](../../crates/musubi-core/src/lib.rs) is the sync protocol as state machines
  that do no I/O, [hub.rs](../../crates/musubi-core/src/hub.rs) and
  [node.rs](../../crates/musubi-core/src/node.rs), which correspond to the Lean model. It
  knows nothing of jj, storage, or networks.
- [musubi-transport](../../crates/musubi-transport/src/lib.rs) carries messages: in memory,
  for the hub and tests, or over a byte stream, for local sockets and ssh.
  [stream.rs](../../crates/musubi-transport/src/stream.rs) manages client connections and pending
  requests; its submodules own the [frames](../../crates/musubi-transport/src/stream/frame.rs),
  [greeting](../../crates/musubi-transport/src/stream/greeting.rs), and
  [server relay](../../crates/musubi-transport/src/stream/server.rs).
- [musubi-jj](../../crates/musubi-jj/src/lib.rs) is everything that touches jj-lib.
  [canonical.rs](../../crates/musubi-jj/src/canonical.rs) is the canonical store, the log of
  canonical operations that the hub and each machine keep. Its
  [transfer](../../crates/musubi-jj/src/canonical/transfer.rs) module imports and exports bundles;
  [validate](../../crates/musubi-jj/src/canonical/validate.rs) checks their encodings against what
  jj decodes. The
  [node](../../crates/musubi-jj/src/node.rs) module translates between local and canonical
  operations ([translate](../../crates/musubi-jj/src/node/translate.rs),
  [realize](../../crates/musubi-jj/src/node/realize.rs)), joins hives, and reconciles hive
  settings. Its [supersede](../../crates/musubi-jj/src/node/supersede.rs) module holds record
  state and naming; submodules handle persistence, normalization, detecting abandons, rewriting
  local operations, receiving records, and fix-ups.
  [objects](../../crates/musubi-jj/src/objects/mod.rs) moves commits and trees, and
  [format_guard.rs](../../crates/musubi-jj/src/format_guard.rs) refuses operations from a
  newer jj.
- [musubi-hub](../../crates/musubi-hub/src/lib.rs) stores hives:
  [store.rs](../../crates/musubi-hub/src/store.rs) is one hive's store,
  [hub_dir.rs](../../crates/musubi-hub/src/hub_dir.rs) a hub's directory of them, and
  [matching.rs](../../crates/musubi-hub/src/matching.rs) decides which hive a joining
  repository belongs in.
- [musubi-sync](../../crates/musubi-sync/src/lib.rs) binds the core to real repositories and
  hub stores, and defines the [wire format](../../crates/musubi-sync/src/wire.rs). Its tests
  hold the race catalogue and the generated end-to-end search.
- [musubi](../../crates/musubi/src/main.rs) starts the command-line tool and dispatches commands.
  [cli.rs](../../crates/musubi/src/cli.rs) defines arguments and help. Workflow modules own
  [joining and cloning](../../crates/musubi/src/join.rs),
  [leaving and forgetting](../../crates/musubi/src/leave.rs),
  [listing](../../crates/musubi/src/list.rs), and [syncing](../../crates/musubi/src/sync.rs);
  [repo.rs](../../crates/musubi/src/repo.rs) locates and validates the copy a command acts on.
  [hub.rs](../../crates/musubi/src/hub.rs) serves a hub,
  [daemon.rs](../../crates/musubi/src/daemon.rs) is the per-machine daemon, with shared hub
  connections in [connections.rs](../../crates/musubi/src/daemon/connections.rs).
  [top.rs](../../crates/musubi/src/top.rs) handles terminal interaction, with separate
  [sampling](../../crates/musubi/src/top/sample.rs) and
  [rendering](../../crates/musubi/src/top/view.rs) modules.
  [ssh.rs](../../crates/musubi/src/ssh.rs) reaches hubs over ssh and sets up keys, and
  [login.rs](../../crates/musubi/src/login.rs) starts the daemon at login.
- [musubi-testutil](../../crates/musubi-testutil/src/lib.rs) makes hermetic jj repositories
  for tests.

Outside the crates, [formal/](../../formal) holds the Lean model,
[fuzz/](../../fuzz) the fuzz targets, and [bench/](../../bench) the benchmarks.

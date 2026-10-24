# Contributor docs

Start with [CONTRIBUTING.md](../../CONTRIBUTING.md) for setup and checks, and
[AGENTS.md](../../AGENTS.md) for the repository's working agreement. For using musubi, see
the [user guide](../README.md).

Each document answers a different question:

- [Design](design.md): What does musubi replicate, how do machines agree, including on
  remotes and shared config, and why? Read it before changing what musubi does.
- [Sync protocol](protocol.md): What exactly do nodes and the hub say to each other, and what
  properties does that guarantee?
- [Race catalogue](races.md): What happens when machines change the same thing at once, and
  which test pins each outcome?
- [Testing](testing.md): Which layers of tests are there, what does each guard against, and
  where does a new test belong?
- [Efficient tests](efficient-tests.md): How should a new test be written so that the suite
  stays fast?
- [Conformance](conformance.md): How are the Rust protocol core, and which copies a hive
  shows, checked against the Lean model?
- [The Lean model](../../formal/README.md): What does the model prove, and how does it
  correspond to the protocol?
- [Releasing](releasing.md): How is a release made?
- [Benchmarks](../../bench/README.md): How does musubi compare with git and jj's own fetch and
  push on the wire?

Keep each rule in the document that owns it, and link to it from others. These documents
describe the current system; jj's history records how it got here.

## Finding the code

The crates, from the bottom up:

- [musubi-core](../../crates/musubi-core/src/lib.rs) is the sync protocol as sans-IO state
  machines, [hub.rs](../../crates/musubi-core/src/hub.rs) and
  [node.rs](../../crates/musubi-core/src/node.rs), which correspond to the Lean model. It
  knows nothing of jj, storage, or networks.
- [musubi-transport](../../crates/musubi-transport/src/lib.rs) carries messages: in memory,
  for the hub and tests, or over a byte stream, for local sockets and ssh.
- [musubi-jj](../../crates/musubi-jj/src/lib.rs) is everything that touches jj-lib. The
  [node](../../crates/musubi-jj/src/node.rs) module translates between local and canonical
  operations ([translate](../../crates/musubi-jj/src/node/translate.rs),
  [realize](../../crates/musubi-jj/src/node/realize.rs)), joins hives, and reconciles hive
  settings. [objects](../../crates/musubi-jj/src/objects/mod.rs) moves commits and trees, and
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
- [musubi](../../crates/musubi/src/main.rs) is the command-line tool:
  [hub.rs](../../crates/musubi/src/hub.rs) serves a hub,
  [daemon.rs](../../crates/musubi/src/daemon.rs) is the per-machine daemon,
  [ssh.rs](../../crates/musubi/src/ssh.rs) reaches hubs over ssh and sets up keys, and
  [login.rs](../../crates/musubi/src/login.rs) starts the daemon at login.
- [musubi-testutil](../../crates/musubi-testutil/src/lib.rs) makes hermetic jj repositories
  for tests.

Outside the crates, [formal/](../../formal) holds the Lean model,
[fuzz/](../../fuzz) the fuzz targets, and [bench/](../../bench) the benchmarks.

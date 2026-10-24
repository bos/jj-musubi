# Testing

Each layer of testing guards against a different risk, so a test belongs at the narrowest
layer that can catch its bug. Several layers use Hegel, the Rust port of Python's Hypothesis,
for property-based and stateful tests. [efficient-tests.md](efficient-tests.md) says how to
keep a test cheap.

| Layer | Where | Guards against | Cost |
| --- | --- | --- | --- |
| Formal model | `formal/` (Lean) | Protocol design errors: lost operations, dangling references, duplicate merges, livelock | Proof effort, no runtime |
| Protocol property tests | `crates/musubi-core/tests` | The Rust state machines departing from the model | Milliseconds per case |
| Presence conformance | `crates/musubi-jj/tests/it/presence.rs` | Which copies musubi shows departing from the Lean model's rule (docs/internals/conformance.md, "Presence") | A millisecond per case |
| Per-machine refs conformance | `crates/musubi-jj/tests/it/ref_laws.rs`, `crates/musubi-sync/tests/races/refs.rs` | jj's ref merge, import and export, and musubi's realization, departing from `formal/Musubi/Refs.lean` (docs/internals/conformance.md, "Per-machine refs") | ~0.3 s per case |
| Race catalogue | `crates/musubi-sync/tests/races` | Concurrent changes on different machines resolving differently from jj's local behavior (docs/internals/races.md) | ~0.3 s per test |
| Unit tests | `#[cfg(test)]` modules | Pure logic: URL normalization and hive names across forges, matching joining repositories to hives | Microseconds |
| Example tests | each crate's `tests/` | jj integration details: translation, git refs, objects, joins, transports, the hub's hives, the CLI | ~0.2–0.5 s per test |
| Fault tests | `crates/musubi-sync/tests/it/faults.rs` | Malformed requests reaching the hub's decoders, and links that die or stall partway through a sync | ~0.2–1.5 s per test |
| Fuzz targets | `fuzz/` | Bytes no honest peer sends reaching the decoders of frames, messages, bundles, and imported operations and views | Minutes to hours a run; opt-in |
| Generated end-to-end tests | `crates/musubi-sync/tests/e2e_search` | Everything interacting: real `jj` commands, real repositories, faults | Seconds per case; opt-in |

The costs are for one test among the rest of the suite on Linux, on 32 cores.

`just test` runs the default suite, `just property` the generated end-to-end search, and
`just check` everything, the Lean proofs included. The tests need `jj` 0.46.0 and `git` on
`PATH`. They don't read your own git config: `.cargo/config.toml` hides the global and
system config from the git they start, and the `jj` and `git` they run as commands get a
home directory of their own.

jj syncs each file it writes to disk, which on a real disk takes most of the suite's time,
so the tests keep their directories in memory where they can. On Linux they go in
`/dev/shm`, unless `TMPDIR` is set or `/dev/shm` is mounted `noexec`. On macOS, `just test`
makes a RAM disk for the run, which makes the suite three times as fast; a bare
`cargo nextest run` uses the disk. Setting `MUSUBI_KEEP_TEST_DIRS` keeps the directories
after a run, for inspecting a failure, and puts them on the disk.

CI runs clippy and the default suite on Linux, macOS and Windows, since each compiles code
the others don't, and on Linux checks the Lean model, runs the conformance tests against its
oracle, and runs each benchmark script once (`just bench-smoke`). The Search workflow runs
the end-to-end search nightly on Linux, each shard on a runner of its own, with a seed that
changes from run to run. A failing shard uploads its example database; its output gives the
seed and a `reproduce_failure` attribute for replaying the failure locally.

## Protocol property tests

A Hegel state machine owns a hub and several nodes, all of them sans-IO state machines from
`musubi-core`, joined by a simulated network that the test controls completely. Its rules:

- environment: a node makes a local operation on some local parent, not necessarily a head;
- progress: a node takes the next step of its policy (docs/internals/protocol.md, "Policy"),
  merging if it has several heads; sends a poll's `Fetch`; or takes a policy step whose requests
  and replies go through at once;
- delivery: deliver any message in flight, in any order, or deliver one again; a message
  never delivered is lost;
- misbehavior: a node pushes without uploading, a hub replies with operations it never
  accepted, or a hub forgets uploads it never accepted;
- failure: crash a node or the hub, keeping only persistent state, or crash a node partway
  through taking in a fetch; or send the hub back to an earlier head, as a power cut that
  loses the last heads it accepted would (`hubRegress` in the oracle). A node whose own
  request gets a reply with a head older than it knows, or another at the same sequence
  number, starts over from that reply (`loseKnown`, then `learn`).

Two tests run this machine: `protocol_invariants`, and `conformance`, which also checks every
step against the Lean model (docs/internals/conformance.md) and so leaves out the hub forgetting
uploads, which the model's oracle can't express.

After every rule the test checks the model's safety invariants (docs/internals/protocol.md,
"Properties"): HubClosed, HubMonotone, NodeClosed, Locality, MergeOwnership, that a node
stages only operations the hub accepted (staged-is-accepted), and that the head a node
knows is in the hub's history (KnownIsHubHistory). Once the hub has gone back, Locality,
staged-is-accepted and KnownIsHubHistory are checked against its history together with the
heads it lost, and MergeOwnership no longer is: two nodes can then merge the same heads
(`formal/Musubi/RegressScenario.lean`). A final `quiesce` step stops environment actions,
makes the network reliable, and runs every node's policy until nothing changes. The test
then checks liveness: every node's heads are `{hub.head}`, and every created operation is
in its ancestry. A bound on quiescence steps turns livelock into a failure. `conformance`
also asks the Lean model for its liveness measures after each exchange while quiescing, and
requires them to fall whenever the exchange changes the node, and every push the policy
sends to upload what the liveness proofs assume (docs/internals/conformance.md, "Liveness").

Operations here are abstract: ids, parents, and object sets. No jj repository is involved.

## Example tests

These pin down jj-specific behavior with real repositories created by the `jj` CLI, using
`musubi-testutil`'s hermetic environment. Each one names the hazard it guards against. Some
tests are deliberately negative controls. `verbatim_replication_reverts_bookmarks` shows that
copying operations without translation loses bookmark moves; if it ever starts failing, jj
has changed and the design needs revisiting, not the test.

### The hub and the CLI

`musubi-sync/tests/it/server.rs` runs one hub serving several hives over the in-memory
transport: a first copy creating a hive, a copy with the same remote spelled differently
joining it, a fork getting its own, an unrelated repository refused, requests for a hive the
hub lacks failing, and listing, renaming, removing, and an index rebuilt after a restart.
`musubi-hub`'s unit tests cover URL normalization, naming, and the matching rules case by
case.

`musubi/tests/cli.rs` runs the binary as a user would: `musubi hub`, `musubi create`
starting a hive and `musubi join` matching it, over the hub's socket and over a stand-in
for ssh whose shell prints a banner first, `musubi clone` by a prefix of the hive's name,
`musubi list`, `leave`, and each machine's daemon, which the first `create` or `join`
starts in the background, serving a repository added later without a restart, even when
that `create` ran with git's variables naming another repository, as in a git hook. Each
test machine has its own state directory and jj config, and so its own daemon and control
socket; the tests stop the daemons when they finish. One test turns on commit signing, with
`ssh-keygen` as jj's signer, and checks that the commits musubi rewrites are signed, which
shows that the binary loads jj's config as jj does; it runs only on Unix.

One CLI test installs a real login service, and so runs only with
`MUSUBI_TEST_LOGIN_SERVICE=1`, which CI sets on its throwaway runners: never set it where
musubi is installed for real. It installs the daemon with launchd or systemd and checks
that the service manager starts it, restarts it after it is killed but not after `musubi
daemon stop`, and starts it for a command that needs it; on Windows it runs the `Run`
entry's command as a login would. CI's Linux runners have no systemd user manager without
a login session, so the workflow enables lingering and starts one first. Logging in itself
is the one step no test exercises.

## Faults

The protocol tests lose, duplicate, or delay whole messages, but never corrupt one:
docs/internals/protocol.md assumes no message is corrupted. `musubi-sync/tests/it/faults.rs` tests
the implementation where that doesn't hold, and where a link fails partway through a call. It
records a real session over the in-memory transport: one machine pushes a commit, another fetches
it and pushes its own, and the first fetches that. The payload limit is small enough that each
commit's objects travel as a blob in several windows of chunks. A case can start from any point in
the session, from a snapshot of the hub's directory taken as each call started. The session is
recorded once per build of the test binary, under `target/tmp`, as is the hive most race tests
start from, since nextest runs each test in a process of its own.

- `hub_survives_malformed_requests` sends the hub requests no honest node sends: the
  session's requests and bundles cut short, corrupted, or spliced; chunks at extreme
  offsets; malformed requests sent as blobs; made-up ids and attachments; and envelopes from
  another protocol version. The hub must answer each without panicking, its head must move
  only forward, to operations whose closure it has (HubMonotone and HubClosed), and
  afterwards it must still answer a fetch from the root.
- `calls_finish_once_the_link_is_back` makes one of the session's calls through a link that
  fails at a chosen request. The request and everything after it may be lost, as when the
  wifi goes off; the request may arrive but its reply and everything after it be lost, as
  when a lid closes just after it went; or it may arrive an hour late, after the hub has
  swept away transfers in progress. Meanwhile the hub may receive malformed requests made
  from what the node sent. Once the link is back, the call, made again, must get the reply
  it got in the session (unless a malformed request happened to be a valid push that moved
  the head), within a bound on the number of requests.
- `node_recovers_when_its_link_fails_partway` fails the link the same ways with real
  repositories and the node's driver, retrying as the daemon does, while another machine
  syncs. Afterwards both machines must see the same commits. It is slow, so it runs few
  cases.

Smaller tests cover how long blobs live: a blob the hub prepares again for a second fetch
lasts as long as a new one (`blobs_prepared_again_last_as_long_as_new_ones`); uploading the
same content leaves a prepared blob alone (`uploads_leave_prepared_blobs_alone`); and a call
that fails or is dropped partway leaves no uploads behind, and no downloads but a partial
one, kept for a later call to resume (`calls_leave_no_uploads_behind`,
`calls_leave_no_downloads_behind`).

The truncated messages stand for a buggy or mismatched peer, not a dropped connection: the
stream transport frames each message with its length and drops one its connection ends
partway through, so a dropped connection looks like a lost request or reply, which the link
faults cover.

## Fuzzing

The fault tests make malformed input from a real session. `fuzz/` holds coverage-guided
fuzz targets, run by libFuzzer through cargo-fuzz, that make it from nothing, for each
decoder of what a peer sends. Each checks more than that nothing panics:

- `frames`: frames read from a byte stream. Each encodes to exactly the bytes it was read
  from, since a frame has only one encoding.
- `greeting`: what the hub's machine prints before the hub greets. The greeting is found only
  at the end of a line, within the noise allowed before it.
- `envelope`: messages of each kind, most behind this release's versions, which the fuzzer
  would otherwise have to find first. One that decodes encodes to one that decodes the same,
  and that encoding, with a byte after it, is refused. postcard takes varints longer than
  they need be, so a message can have more than one encoding.
- `bundle`: bundles, most behind the header. The records of one that reads, written to a
  bundle of their own, compressed or not, read back the same.
- `canonical`: operations and views imported into a canonical store, under an id they don't
  hash to and then under the one they do, which reaches the checks past the hash. One
  admitted reads back as what it hashes to, and none, admitted or refused, leaves the store
  holding anything that isn't what its name says. A panic in jj-lib, which panics on some
  malformed input, counts as a refusal, as it does on the hub; a panic anywhere else fails.

`just fuzz bundle` runs one until stopped, and takes libFuzzer's options after the target, as
in `just fuzz bundle -max_total_time=300`; `just fuzz-smoke` runs each briefly, to check that
they still build and run. They need `cargo-fuzz` and a nightly toolchain from rustup. `fuzz/`
is a workspace of its own, so that `just check` neither builds nor lints it; its targets reach
private code only through `cfg(fuzzing)` modules, which cargo-fuzz sets, and which tests build
too, so that `just check` checks them. Corpora and crashes stay in `fuzz/`, unversioned,
and the files the targets write go in `/dev/shm`.

The files musubi appends lines to have Hegel properties beside their parsers instead. In the
translation map and the joins, among whole lines, any torn anywhere names nothing, and the
whole ones are read. The hub's log of heads, cut where a line ends, reads as the heads before
the cut, and cut anywhere else is corrupt; and a store whose `heads` or `backend` a crash or a
disk damaged opens as it was or is corrupt, to be made again, never failing as if for now.
The canonical store's log, damaged from any point on (cut short, zero-filled, garbled, or
grown with zeros), reads each operation and view back as written or not at all, loses only
what was written after the damage, and is whole again once the next record is appended;
two writers sharing one log each find what the other appended.

## Generated end-to-end tests

A Hegel state machine drives two or three real colocated repositories, each served by a
musubi node, through an in-process hub that `musubi_sync::hive::Hive` delivers their
requests to directly, one step at a time, so that a failing case replays exactly. Its rules
fall into groups, kept separate so that the inconsistent states between them get explored:
a machine can work on a stale view, git can move a branch jj has not imported, a node can
stop halfway through a sync.

- **Local work**, through the `jj` CLI on a chosen machine: commit, edit without
  snapshotting, describe, new (including merges), rebase, squash, abandon, resolve, bookmark
  and tag changes, undo, and commands at an older operation (`--at-op`), which create
  concurrent operations.
- **Workspaces**: add, rename, and forget them; forget another machine's; and rewrite or
  abandon another machine's working-copy commit.
- **The remote**: someone outside the hive advances `origin`; a machine fetches or pushes.
- **Git-side work**: move or delete a branch with `git`.
- **Sync**: one node syncs until it is idle, or takes only a few steps of a sync, which may
  stop partway through an upload.
- **Faults**: restart or crash a node, with or without its translation cache, or while it
  is still writing realizations; restart the hub, or send it back, dropping the last one to
  three lines of its `heads` before it restarts, as a power cut would; or lose a reply the
  hub sent. Faults are capped per sequence, so that a short walk still reaches recovery.

After each rule, every repository must still load. At the end of a sequence, and at most
once in the middle, the hive syncs to a fixed point, and the test checks:

- every node's canonical head equals the hub's;
- all repositories agree on visible commits, change ids, bookmarks, tags, and remote
  bookmarks;
- in every colocated repository, `refs/heads` matches the local bookmarks that are not
  conflicted or on the root commit, which git can't hold, and a further `jj status`
  imports nothing;
- every operation made on any machine appears in every machine's `jj op log`;
- no change diverges, and no bookmark or tag conflicts, unless jj would do the same with
  the same concurrent operations on one machine. A ledger of which machine's commands
  rewrote what explains each: two machines rewrote it, or a command at an older operation
  or a git-side move did; or a commit holds it visible that jj can't move, such as a
  descendant of a commit rewritten two ways, a target of a conflicted bookmark, or a branch
  imported from git. A bookmark on a merge commit that is abandoned conflicts between the
  merge's parents. Two commits of a change with the same parents and contents are the same
  rebase done twice, which the hub's sequencing exists to prevent.

To keep the search effective:

- a rule is eligible only when it has work to do, and its candidates are computed by a helper
  that its precondition shares;
- each search shard has its own Hegel example database;
- a case replays exactly, so that Hegel can shrink a failure and a stored example finds it
  again: jj's change ids, random otherwise, come from a counter that each test
  environment's repositories share, and rules choose among commits in change-id order, since
  commit ids and `jj log`'s order depend on when jj made the commits. A failure that doesn't
  replay exactly fails the run at once, saying where the replay diverged.
  `MUSUBI_SEARCH_FINGERPRINTS` writes each case's trace without the ids that differ between
  runs, for checking that two runs of a case did the same;
- the run ends by listing rules that never fired. An unreached rule is a search problem:
  give it a richer starting state or fix its precondition.

## Testing the tests

`just mutants` runs `cargo-mutants` over the protocol core's hub and node logic: each
surviving mutant is a change to the protocol that the property and conformance tests fail to
notice. docs/internals/conformance.md lists hand-made mutants and which check catches each.

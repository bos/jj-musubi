# Testing

musubi's correctness rests on three layers of evidence. Each guards a different risk, so a
test belongs at the narrowest layer that can catch its bug.

| Layer | Where | Guards against | Cost |
| --- | --- | --- | --- |
| Formal model | `formal/` (Lean) | Protocol design errors: lost operations, dangling references, duplicate merges, livelock | Proof effort, no runtime |
| Protocol property tests | `crates/musubi-core/tests` | The Rust state machines departing from the model | Milliseconds per case |
| Race catalogue | `crates/musubi-sync/tests/races` | Concurrent changes on different machines resolving differently from jj's local behavior (docs/races.md) | ~0.3 s per test |
| Unit tests | `#[cfg(test)]` modules | Pure logic: URL normalization and hive names across forges, matching joining repositories to hives | Microseconds |
| Example tests | each crate's `tests/` | jj integration details: translation, git refs, objects, joins, transports, the hub's hives, the CLI | ~0.2–0.5 s per test |
| Fault tests | `crates/musubi-sync/tests/it/faults.rs` | Malformed requests reaching the hub's decoders, and links that die or stall partway through a sync | ~0.2–1.5 s per test |
| Fuzz targets | `fuzz/` | Bytes no honest peer sends reaching the decoders of frames, messages, bundles, and imported operations and views | Minutes to hours a run; opt-in |
| Generated end-to-end tests | `crates/musubi-sync/tests/e2e_search` | Everything interacting: real `jj` commands, real repositories, faults | Seconds per case; opt-in |

The costs are for one test among the rest of the suite on Linux, on 32 cores.

Run the default suite with `cargo nextest run`, or everything with `just check`. It needs `jj` 0.46.0 and `git`
on `PATH`. jj syncs what it writes to disk, and on a disk waiting for that takes most of the
suite's time, so the tests' directories are in memory where possible. On Linux they are in
`/dev/shm`, unless `TMPDIR` is set or `/dev/shm` is mounted `noexec`. On macOS `just test`
(and so `just check`) makes a RAM disk for the run and sets `TMPDIR` to it, which makes the
suite three times as fast; `cargo nextest run` alone leaves them on the disk. Neither OS puts
them in memory when `MUSUBI_KEEP_TEST_DIRS` keeps them for inspecting a failure, and what a
test binary records once per build stays under `target/`. Run the generated end-to-end
search with `cargo nextest run --profile search`. Check
the formal model with `lake build` in `formal/`. `.cargo/config.toml` hides the developer's
global and system git config from the git that tests, and the musubi they run in-process,
start; the `jj` and `git` they run as commands get musubi-testutil's own home directory.

CI runs the default suite on Linux, macOS and Windows, and checks the Lean model and runs
the conformance test against its oracle on Linux. The Search workflow runs the end-to-end
search nightly on Linux, each shard on a runner of its own, with a seed that changes from
run to run. A failing shard uploads its example database; its output gives the seed and a
`reproduce_failure` attribute for replaying the failure locally.

## Protocol property tests

A Hegel state machine owns a hub and several nodes, all of them sans-IO state machines from
`musubi-core`, joined by a simulated network that the test controls completely. Its rules:

- environment: a node makes a local operation on some local parent, not necessarily a head;
  a node merges its heads;
- delivery: deliver, drop, duplicate, or delay a chosen in-flight message;
- failure: crash a node or the hub, keeping only persistent state; or send the hub back to
  an earlier head, as a power cut that loses the last heads it accepted would (`hubRegress`
  in the oracle). A node whose own request gets a reply with a head older than it knows, or
  another at the same sequence number, starts over from that reply (`loseKnown`, then
  `learn`);
- progress: let a node take its next policy step.

After every rule the test checks the model's safety invariants: HubClosed, HubMonotone,
NodeClosed, Locality, MergeOwnership, that a node stages only operations the hub accepted
(staged-is-accepted), and that the head a node knows is in the hub's history
(KnownIsHubHistory). Once the hub has gone back, Locality, staged-is-accepted and
KnownIsHubHistory are checked against its history together with the heads it lost, and
MergeOwnership no longer is: two nodes can then merge the same heads
(`formal/Musubi/RegressScenario.lean`). A final `quiesce` step stops environment actions,
makes the network reliable, and runs every node's policy until nothing changes. The test then
checks liveness: every node's heads are `{hub.head}`, and every created operation is in its
ancestry. A bound on quiescence steps turns livelock into a failure.

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
test machine has its own config directory, and so its own daemon and control socket; the
tests stop the daemons when they finish. One test turns on commit signing, with
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

The protocol tests deliver well-formed messages, and lose, duplicate, or delay whole ones;
docs/protocol.md assumes no message is corrupted. `musubi-sync/tests/it/faults.rs` tests the
implementation where that doesn't hold. It records a real session over the in-memory
transport, with a payload limit small enough that each commit's objects travel as a blob of
several windows of chunks: one machine pushes a commit, another fetches it and pushes its
own, and the first fetches that. It snapshots the hub's directory as each call starts, and
a case starts from any point in the session by copying the snapshot before it and replaying
the requests since. The session is recorded once per build of the test binary, under
`target/tmp`, and so is the hive most of the race catalogue's tests start from: nextest
runs each test in a process of its own, which would otherwise record them again. Two Hegel
tests use the session:

- `hub_survives_malformed_requests` sends a hub requests no honest node sends: the session's
  requests and bundles cut short, corrupted, or spliced; chunks at extreme offsets; requests
  that arrive as blobs, and are themselves malformed or indirect; protocol requests with ids
  and attachments taken from the session or made up; and envelopes from another version. The
  hub answers each without panicking, with a reply, or an error, that fits the transport, and
  its head moves only forward, to an operation whose closure it has (HubMonotone and
  HubClosed). Afterwards it still answers a fetch from the root, which reads everything up to
  its head.
- `calls_finish_once_the_link_is_back` makes one of the session's calls, a push and its
  uploads or a fetch and its downloads, through a link that fails at a chosen request. The
  request and all later ones may be lost, as when the wifi goes off. The request may arrive
  but its reply and all later requests be lost, as when a lid closes just after it went. Or
  an hour may pass before it arrives, in which the hub sweeps away transfers in progress,
  and then the link carries on, as when the lid opens. Meanwhile the hub may hear malformed
  requests made from what the node sent, and an hour may pass. Once the link is back, the
  call, made again, gets the reply it got in the session, unless a malformed request was a
  valid push that moved the head, within a bound on requests that catches a node that never
  starts over.

A third, `node_recovers_when_its_link_fails_partway`, fails the link the same ways with real
repositories and the node's driver, retrying as the daemon does, while another machine
syncs. Afterwards both machines see the same commits. It is slow, so it runs few cases.

An hour passing sweeps every blob at once, so those tests never meet a blob the hub
prepares twice. `blobs_prepared_again_last_as_long_as_new_ones` makes a fetch of the
session against the hub directly, downloads its blob, backdates the blob past the sweep's
hour, and makes the fetch again, as another node would. The second fetch gets the same
blob, and its download survives a sweep and outlasts the time the hub keeps a blob it has
served. So does the download for a third fetch, made before the second download finishes
and paced to span that time. `uploads_leave_prepared_blobs_alone` downloads a fetch's
blob, then uploads the same content and pushes it, as another node would push what the
first fetched, and downloads the blob again. `calls_leave_no_uploads_behind` makes a push
of the session through a link that fails partway through its upload, and again with the
call dropped partway, as the daemon drops a sync when the connection comes back; either
way the node's blob store is left empty. `calls_leave_no_downloads_behind` does the same
partway through the second of a fetch's two downloads, which leaves only the partial
download, for a later call to resume until it has gone a day untouched; and when the
fetch succeeds, its downloads go once its reply is dropped.

A connection that dies partway through a message never delivers part of it: the stream
transport frames each message with its length and drops an incomplete one. A killed connection reaches
musubi as a lost request or reply, which the link faults model. The truncated messages
stand for a buggy or mismatched peer.

## Fuzzing

The fault tests make malformed input from a real session. `fuzz/` holds coverage-guided
fuzz targets, run by libFuzzer through cargo-fuzz, that make it from nothing, for each
decoder of what a peer sends. Each checks more than that nothing panics:

- `frames`: frames read from a byte stream. Each encodes to one that reads back the same.
- `greeting`: what the hub's machine prints before the hub greets. The greeting is found only
  at the end of a line, within the noise allowed before it.
- `envelope`: messages of each kind, most behind this release's versions, which the fuzzer
  would otherwise have to find first. One that decodes encodes to one that decodes the same.
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
too, so that `just check` checks them. Corpora and crashes
stay in `fuzz/`, unversioned, and the files the targets write go in `/dev/shm`.

The files musubi appends lines to have Hegel properties beside their parsers instead. In the
translation map and the joins, among whole lines, any torn anywhere names nothing, and the
whole ones are read. The hub's log of heads, cut where a line ends, reads as the heads before
the cut, and cut anywhere else is corrupt; and a store whose `heads` or `backend` a crash or a
disk damaged opens as it was or is corrupt, to be made again, never failing as if for now.

## Generated end-to-end tests

Modeled on jj-stack's generated integration tests. A Hegel state machine drives two or three
real colocated repositories, each served by a real musubi node, through an in-process hub
that `musubi_sync::hive::Hive` delivers their requests to directly, one step at a time, so
that a failing case replays exactly.

Rules fall into separate groups, and are kept separate so that the inconsistent states
between them get explored:

- **Local work**, through the `jj` CLI on a chosen machine: write files and commit, describe,
  new on a random commit, rebase, squash, abandon, bookmark create, move, and delete, undo,
  and commands at an older operation (`--at-op`), which create concurrent operations.
- **Git-side work** in a colocated repository: move or delete a branch with `git`.
- **Sync**: let one node sync until it is idle, or take a few steps, which may stop partway
  through an upload.
- **Faults**: restart a node, losing its protocol state; crash one, losing its caches, its
  translation cache too, or realizations it was still writing, or crash it partway through
  realizing what a sync fetched; restart the hub, or send it back, dropping the last one to
  three lines of its `heads` before it restarts, as a power cut would (`hub_goes_back`); or
  lose the reply to a request the hub handled. Faults are capped per sequence, so that a
  short walk still reaches recovery.

After each rule, every repository must still load, and `jj status` must succeed. At the end,
`converge` syncs every node to a fixed point, then checks:

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

As in jj-stack:

- a rule is eligible only when it has work to do, and its candidates are computed by a helper
  that its precondition shares;
- each seeded search shard has its own Hegel example database;
- a case replays exactly, so that Hegel can shrink a failure and a stored example finds it
  again: jj's change ids, random otherwise, come from a counter that each test
  environment's repositories share (musubi-testutil), origin's upstream commits carry
  change ids of their own, and rules choose among commits in change-id order, since commit
  ids and `jj log`'s order depend on when jj made the commits.
  `MUSUBI_SEARCH_FINGERPRINTS` writes each case's trace without the ids that differ between
  runs, for checking that two runs of a case did the same. A failure that doesn't replay
  exactly fails the run at once, saying where the replay went another way. By default
  Hegel would replay it in batches, for minutes, pass the run if that didn't confirm it,
  and could keep it to replay in batches again in later runs;
- the search run ends by listing rules that never fired. An unreached rule is a search
  problem: give it a richer starting state or fix its precondition.

## Testing the tests

`just mutants` runs `cargo-mutants` over the protocol core's hub and node logic: each
surviving mutant is a change to the protocol the property tests and the Lean conformance
check fail to notice. docs/conformance.md lists hand-made mutants and which check catches
each.

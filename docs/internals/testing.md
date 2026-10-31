# Testing

The layers of musubi's tests, what each guards against, and how to run them.
[testing-philosophy.md](testing-philosophy.md) says what a test must protect, which layer a
new one belongs in, and what evidence each kind of change needs;
[efficient-tests.md](efficient-tests.md) says how to keep a test cheap. Terms such as hive,
node, hub and realization are defined in [design.md, "Vocabulary"](design.md#vocabulary).

Several layers use Hegel (the `hegeltest` crate), a Rust port of Python's Hypothesis. A Hegel
property test generates inputs and, on a failure, shrinks the failing input to a small case. A
stateful test is a state machine of *rules*, each with a precondition, which Hegel runs in
generated sequences. Hegel keeps failing cases in an example database and tries them again first
on the next run. *The search* is the generated end-to-end tests below, run with `just property`.

| Layer | Where | Guards against | Cost |
| --- | --- | --- | --- |
| Formal model | `formal/` (Lean) | Protocol design errors: lost operations, dangling references, duplicate merges, livelock | Proof effort, no runtime |
| Protocol property tests | `crates/musubi-core/tests` | The Rust state machines departing from the model | Milliseconds per case |
| Presence conformance | `crates/musubi-jj/tests/it/presence.rs` | Which copies (machines' repositories) a hive shows departing from `formal/Musubi/Presence.lean` ([conformance.md, "Presence"](conformance.md#presence); [design.md, "Copies that go away"](design.md#copies-that-go-away)) | A millisecond per case |
| Copies conformance | `crates/musubi/src/copy/conformance.rs` | Which repository musubi takes for the copy of a key, and the daemon's check before each sync, departing from `formal/Musubi/Copies.lean` ([conformance.md, "Copies"](conformance.md#copies); [copies.md](copies.md)) | Under a second for all 4212 cases |
| Chunked blob conformance | `crates/musubi-sync/src/blobs.rs` | The blob receiver departing from the prefix receiver of `formal/Musubi/Chunks.lean` ([conformance.md, "Chunked blobs"](conformance.md#chunked-blobs)) | A few milliseconds per case |
| Workspace names conformance | `crates/musubi-jj/src/workspaces.rs` | The names under which a machine shows other machines' workspaces departing from `formal/Musubi/Names.lean` ([conformance.md, "Workspace names"](conformance.md#workspace-names)) | A millisecond per case |
| Per-machine refs conformance | `crates/musubi-jj/tests/it/ref_laws.rs`, `crates/musubi-sync/tests/races/refs.rs` | jj's ref merge, import and export, and musubi's realization, departing from `formal/Musubi/Refs.lean` ([conformance.md, "Per-machine refs"](conformance.md#per-machine-refs)) | ~0.3 s per case |
| Race catalogue | `crates/musubi-sync/tests/races` | Concurrent changes on different machines resolving differently from jj's local behavior ([races.md](races.md)) | ~0.3 s per test |
| Unit tests | `#[cfg(test)]` modules | Pure logic: URL normalization and hive names across forges, matching joining repositories to hives | Microseconds |
| Example tests | each crate's `tests/` | jj integration details: translation, git refs, objects, joins, transports, the hub's hives, the CLI | ~0.2–0.5 s per test |
| Fault tests | `crates/musubi-sync/tests/it/faults.rs` | Malformed requests reaching the hub's decoders, and links that die or stall partway through a sync | ~0.2–1.5 s per test |
| Fuzz targets | `fuzz/` | Bytes no honest peer sends reaching the decoders of frames, messages, bundles, and imported operations and views | Minutes to hours a run; opt-in |
| Kani proofs | `#[cfg(kani)]` modules | Arithmetic on sizes and offsets a peer controls going wrong for any value, however unlikely | Under a second each; opt-in |
| Generated end-to-end tests | `crates/musubi-sync/tests/e2e_search` | Everything interacting: real `jj` commands, real repositories, faults | Seconds per case; opt-in |

Costs are for one test running among the rest of the suite, on 32 Linux cores. When a change
moves them, update them.

## Running the tests

`just test` runs the default suite and `just property` the search. `just check` runs formatting,
clippy, the Lean proofs, the default suite, the doc build, cargo-deny, cargo-machete and typos;
[testing-philosophy.md, "Beyond `just check`"](testing-philosophy.md#beyond-just-check) says when
to run the rest.

The tests need `jj` 0.46.0 and `git` on `PATH`. They don't read your own git config:
`.cargo/config.toml` hides the global and system config from the git they start, and the `jj`
and `git` they run as commands get a home directory of their own.

jj syncs each file it writes, which on a real disk takes most of the suite's time, so test
directories go in memory where they can. On Linux they go in `/dev/shm`, unless `TMPDIR` is
set or `/dev/shm` is mounted `noexec`. On macOS, `just test` makes a RAM disk for the run,
which makes the suite three times as fast; a bare `cargo nextest run` uses the disk. Setting
`MUSUBI_KEEP_TEST_DIRS` keeps the directories after a run, for inspecting a failure, and puts
them on the disk.

## CI

CI runs clippy and the default suite on Linux, macOS and Windows, since each compiles code the
others don't; each first builds the Lean oracle (the executable model,
[conformance.md](conformance.md)) for the tests that check the code against it. On Linux it also
runs the rest of `just check`'s lints (formatting, rustdoc, cargo-deny, cargo-machete, typos),
checks the Lean model's proofs, and runs each benchmark script once (`just bench-smoke`).

The Search workflow runs the search nightly on Linux, each shard on a runner of its own, with a
seed that changes from run to run. A failing shard uploads its example database; its output
gives the seed and a `reproduce_failure` attribute for replaying the failure locally.

The jj main workflow builds musubi and jj from jj's main branch nightly and runs the default
suite with the workflow's filter, so that changes to jj-lib that will break musubi show up
before a release brings them. To do the same locally against a checkout of jj outside this
workspace:

1. Run `.github/scripts/use-jj-checkout.sh <jj checkout>`.
2. From this workspace, build the matching jj with `cargo build -p jj-cli --bin jj`, which the
   script has pointed at the checkout, and put `target/debug` on `PATH`.
3. Run the tests with the workflow's filter.
4. Afterwards, `jj restore` the files the script rewrote, and `Cargo.lock`.

## Protocol property tests

A Hegel state machine owns a hub and several nodes, all of them `musubi-core`'s sans-IO state
machines (they do no I/O themselves), joined by a simulated network that the test controls
completely. Operations are abstract: ids, parents and object sets, with no jj repository.
The rules, in the terms of [protocol.md](protocol.md):

- **Environment**: a node makes a local operation on some local parent, not necessarily a head.
- **Progress**: a node takes the next step of its policy ([protocol.md,
  "Policy"](protocol.md#policy)), merging if it has several heads; sends a poll's `Fetch`; or
  takes a policy step whose requests and replies go through at once.
- **Delivery**: deliver any message in flight, in any order, or deliver one again. A message
  never delivered is lost.
- **Misbehavior**: a node pushes without uploading; a hub replies with operations it never
  accepted; or a hub forgets everything outside `closure(head)` (the head's history and the
  objects it needs), including uploads it never accepted.
- **Failure**: crash a node or the hub, keeping only persistent state, or crash a node partway
  through taking in a fetch. Send the hub back to an earlier head, as a power cut that loses
  the last heads it accepted would (`hubRegress` in the oracle), or make the hive again,
  empty, as the hub does one whose store is corrupt (`hubRegress` to 0, then `hubForget`). A
  node whose own request gets a reply with a head older than it knows, or another at the same
  sequence number, starts over from that reply (`loseKnown`, then `learn`).

Two tests run this machine: `protocol_invariants`, and `conformance`, which also checks every
step against the Lean model.

After every rule the test checks the model's safety invariants ([protocol.md,
"Properties"](protocol.md#properties)): HubClosed, HubMonotone, NodeClosed, Locality,
MergeOwnership, KnownIsHubHistory, and that a node stages only operations the hub accepted
(staged-is-accepted). Once the hub has gone back, Locality, staged-is-accepted and
KnownIsHubHistory are checked against its history together with the heads it lost, and
MergeOwnership no longer is: two nodes can then merge the same heads
(`formal/Musubi/RegressScenario.lean`).

A final `quiesce` step stops environment actions, makes the network reliable, and runs every
node's policy until nothing changes. The test then checks liveness: every node's heads are
`{hub.head}`, and every operation created is in its ancestry. A bound on quiescence steps
turns livelock into a failure. While quiescing, `conformance` also asks the Lean model for its
liveness measures after each exchange, and requires them to fall whenever the exchange changes
the node, and every push the policy sends to upload what the liveness proofs assume
([conformance.md, "Liveness"](conformance.md#liveness)).

## Example tests

These pin down jj-specific behavior with real repositories made by the `jj` CLI in
`musubi-testutil`'s hermetic environment.

### The hub and the CLI

`musubi-sync/tests/it/server.rs` runs one hub serving several hives over the in-memory
transport: a first copy creating a hive; a copy with the same remote spelled differently
joining it; a fork getting its own; an unrelated repository refused; requests for a hive the
hub lacks failing; and listing, renaming, removing, and an index rebuilt after a restart.
`musubi-hub`'s unit tests cover URL normalization, naming, and the matching rules case by
case.

`musubi/tests/cli.rs` runs the binary as a user would: `musubi hub`; `musubi create` starting
a hive and `musubi join` matching it, over the hub's socket and over a stand-in for ssh whose
shell prints a banner first; `musubi clone` by a prefix of the hive's name; `musubi list` and
`leave`; and each machine's daemon. The first `create` or `join` starts the daemon in the
background, and it serves a repository added later without a restart, even when that `create`
ran with git's variables naming another repository, as in a git hook. Each test machine has
its own state directory and jj config, and so its own daemon and control socket; the tests stop
the daemons when they finish. One test, Unix only, turns on commit signing with `ssh-keygen`
as jj's signer and checks that the commits musubi rewrites are signed, which shows that the
binary loads jj's config as jj does. Another, Unix only too, puts a stand-in for a hub of a newer
release on a hub's socket, and checks that the daemon runs `musubi.upgrade-command`, starts
again in place once its binary is that release, and that `musubi status` shows an upgrade that
installed nothing; it can't run a real newer release, so the command installs a script that
only says it is one.

`the_quick_start_works_as_written` follows the README's quick start as a new user would:
`musubi hub` run in a repository rather than in the home directory, then the commands it
prints, pasted as printed, on the hub's machine and over the stand-in for ssh, the refusals a
new user meets first, and `musubi list` with no `--hub`. Its inline insta snapshot is
everything the user sees, so a change to what a new user meets shows in the diff. Change the
quick start and the test with it. `cargo insta review` accepts a new snapshot. No test reaches
a real machine over ssh: `musubi-testutil` points `MUSUBI_SSH` at a program that doesn't
exist, so a test that needs ssh must give a stand-in.

One CLI test installs a real login service, and so runs only with
`MUSUBI_TEST_LOGIN_SERVICE=1`, which CI sets on its throwaway runners: never set it where
musubi is installed for real. It installs the daemon with launchd or systemd and checks that
the service manager starts it, restarts it after it is killed but not after
`musubi daemon stop`, and starts it for a command that needs it; on Windows it runs the `Run`
registry entry's command as a login would. CI's Linux runners have no systemd user manager
without a login session, so the workflow enables lingering and starts one first. Logging in
itself is the one step no test exercises.

## Faults

The protocol tests lose, duplicate or delay whole messages but never corrupt one, as
[protocol.md](protocol.md) assumes. `musubi-sync/tests/it/faults.rs` tests the implementation
where that doesn't hold, and where a link fails partway through a call.

It records a real session over the in-memory transport: one machine pushes a commit, another
fetches it and pushes its own, and the first fetches that. The payload limit is small enough that
each commit's objects travel as a blob in several windows of chunks ([design.md, "Size limits and
chunking"](design.md#size-limits-and-chunking)). A case can start at the start of any call in the
session, from a snapshot of the hub's directory taken then. The session is recorded once per build
of the test binary, under `target/tmp`, as is the hive most race tests start from
([efficient-tests.md, "Make an expensive fixture once per
build"](efficient-tests.md#make-an-expensive-fixture-once-per-build)).

- `hub_survives_malformed_requests` sends the hub requests no honest node sends: the session's
  requests and bundles cut short, corrupted or spliced; chunks at extreme offsets; malformed
  requests sent as blobs; made-up ids and attachments; and envelopes from another protocol
  version. The hub must answer each without panicking; its head must move only forward, to
  operations whose closure it has (HubMonotone and HubClosed); and afterwards it must still
  answer a fetch from the root.
- `calls_finish_once_the_link_is_back` makes one of the session's calls through a link that
  fails at a chosen request, in one of three ways: the request and everything after it are
  lost, as when the wifi goes off; the request arrives but its reply and everything after it
  are lost, as when a lid closes just after it went; or it arrives an hour late, after the hub
  has swept away transfers in progress. Meanwhile the hub may receive malformed requests made
  from what the node sent. Once the link is back, the call, made again, must get the reply it
  got in the session (unless a malformed request happened to be a valid push that moved the
  head), within a bound on the number of requests.
- `node_recovers_when_its_link_fails_partway` fails the link the same ways with real
  repositories and the node's driver, retrying as the daemon does, while another machine
  syncs. Afterwards both machines must see the same commits. It is slow, so it runs few cases.

Smaller tests cover how long blobs live: a blob the hub prepares again for a second fetch lasts
as long as a new one (`blobs_prepared_again_last_as_long_as_new_ones`); uploading the same
content leaves a prepared blob alone (`uploads_leave_prepared_blobs_alone`); and a call that
fails or is dropped partway leaves no uploads behind, and no downloads but a partial one, kept
for a later call to resume (`calls_leave_no_uploads_behind`, `calls_leave_no_downloads_behind`).

The truncated messages stand for a buggy or mismatched peer, not a dropped connection: the
stream transport frames each message with its length and drops one whose connection ends
partway through, so a dropped connection looks like a lost request or reply, which the link
faults cover.

## Fuzzing

The fuzz targets in `fuzz/` make malformed input from nothing, where the fault tests make it
from a real session. They are coverage-guided, run by libFuzzer through cargo-fuzz, one for
each decoder of what a peer sends, and each checks more than that nothing panics:

- `frames`: frames read from a byte stream. Each encodes to exactly the bytes it was read from,
  since a frame has only one encoding.
- `greeting`: what the hub's machine prints before the hub greets. The greeting is found only
  at the end of a line, within the noise allowed before it.
- `envelope`: messages of each kind, most behind this release's versions, which the fuzzer
  would otherwise have to find first. A message that decodes re-encodes to one that decodes
  the same, and that encoding with a byte after it is refused. (postcard accepts varints
  longer than they need be, so a message can have more than one encoding.)
- `bundle`: bundles, most behind the header. The records of one that reads, written to a
  bundle of their own, compressed or not, read back the same.
- `canonical`: operations and views imported into a canonical store, under an id they don't
  hash to and then under the one they do, which reaches the checks past the hash. One admitted
  reads back as what it hashes to, and none, admitted or refused, leaves the store holding
  anything that isn't what its name says. jj-lib, and jj-core beneath it, panic on some
  malformed input, so a panic in them counts as a refusal, as it does on the hub; a panic
  anywhere else fails.
- `import`: bundles of a small history imported into a canonical store. Each view comes in one
  of three encodings that decode to it, or as bytes of the fuzzer's, whole or as a delta against
  any encoding of any view before it; some are sent twice or with a byte changed, some without
  their operation. Whatever the store makes of a bundle, it holds nothing that isn't what its
  id says, in normal form. A whole bundle such as musubi makes is stored byte for byte as sent;
  the fuzzer's empty first input is one. Panics in jj-lib and jj-core count as refusals, as for
  `canonical`.

`just fuzz bundle` runs one target until stopped, and takes libFuzzer's options after the
target, as in `just fuzz bundle -max_total_time=300`; `just fuzz-smoke` runs each briefly, to
check that they still build and run. They need `cargo-fuzz` and a nightly toolchain from
rustup. `fuzz/` is a workspace of its own, so that `just check` neither builds nor lints it.
Its targets reach private code only through `cfg(fuzzing)` modules, which cargo-fuzz sets and
the tests build too, so that `just check` checks them. Corpora and crashes stay in `fuzz/`,
unversioned, and the files the targets write go in `/dev/shm`.

The files musubi appends lines to have Hegel properties beside their parsers instead:

- the translation map and the joins: among whole lines, a line torn anywhere names nothing,
  and the whole ones are read;
- the hub's log of heads: cut where a line ends, it reads as the heads before the cut; cut
  anywhere else, it is corrupt;
- a hub store whose `heads` or `backend` a crash or a disk damaged opens as it was, or is
  corrupt and made again, and never fails as if the damage were temporary;
- the canonical store's log, damaged from any point on (cut short, zero-filled, garbled, or
  grown with zeros), reads each operation and view back as written or not at all, loses only
  what was written after the damage, and is whole again once the next record is appended; two
  writers sharing one log each find what the other appended.

## Kani proofs

[Kani](https://model-checking.github.io/kani/) checks a Rust function for every value of its
inputs at once, rather than for those a test or a fuzzer happens to try, and gives a failing
input when it finds one. It suits small, pure arithmetic on numbers a peer sends or a hub
offers, where the case that goes wrong is one no test would pick:

- `blobs::proofs`: where the bytes of a chunk that extend what a blob's receiver has start,
  for any length so far, offset and chunk length, including offsets near `u64::MAX`.
- `wire::proofs`: a chunk leaves at least as much room for its envelope at every payload a
  hub may offer as at the smallest, where the unit test `a_full_chunk_fits` shows that it is
  enough.
- `service::proofs`: the hub's check for the last chunk of a download can't overflow, for any
  offset and length a node asks for, and holds exactly when the read reached the end.
- `remote::proofs`: each window of chunks an upload or download sends starts at its offset,
  goes up a chunk at a time without overflowing, and either reaches the end or is a full
  window.

It is slow on code that handles strings or long buffers: a proof that `fit_error` cuts a
message to fit, which takes more than 1 KiB of message to reach the cut, ran for 15 minutes
without finishing. Keep that to the fuzz targets and Hegel. A harness that collects into a
`Vec` can run out of memory where one that walks the same iterator takes a second.

`just kani` runs every proof. It needs `cargo install --locked kani-verifier` and then
`cargo kani setup`, once. The proofs build only under `cargo kani`, so `just check` doesn't
build them.

## Generated end-to-end tests

A Hegel state machine drives two or three real colocated repositories, each served by a musubi
node, through an in-process hub. `musubi_sync::hive::Hive` delivers their requests to the hub
directly, one step at a time, so that a failing case replays exactly. The rules fall into
groups, kept separate so that the inconsistent states between them get explored: a machine can
work on a stale view, git can move a branch jj hasn't imported, a node can stop halfway through
a sync.

- **Local work**, through the `jj` CLI on a chosen machine: commit, edit without snapshotting,
  describe, new (including merges), rebase, squash, abandon, resolve, bookmark and tag changes,
  undo, and commands at an older operation (`--at-op`), which create concurrent operations.
- **Workspaces**: add, rename and forget them; forget another machine's; and rewrite or abandon
  another machine's working-copy commit.
- **The remote**: someone outside the hive advances `origin`; a machine fetches or pushes.
- **Git-side work**: move or delete a branch with `git`.
- **Sync**: one node syncs until it is idle, or takes only a few steps of a sync, which may stop
  partway through an upload.
- **Faults**: restart or crash a node, with or without its translation cache, or while it is
  still writing realizations; restart the hub, or send it back by dropping the last one to
  three lines of its `heads` before it restarts, as a power cut would; or lose a reply the hub
  sent. Faults are capped per sequence, so that a short sequence still reaches recovery.

After each rule, every repository must still load, and no import of git refs or of git's HEAD
may revert anything (`e2e_search/imports.rs`; for refs, `noSpuriousRevert` in
`formal/Musubi/Refs.lean`). Every `jj` command imports any difference between its record of
`.git` and `.git` itself as a change made with git, so a record musubi gets wrong moves a
bookmark back with no git command run. The search makes every move git makes of a machine's refs
outside `jj` itself, so it records, per machine, which refs git moved since jj last imported
there, and what `.git` had before. Each operation that imports (jj's "import git refs") may
change a bookmark, remote bookmark or tag only through a ref git moved in that time, from the
value jj's record had, or where jj does the same in one repository: it resolves a conflicted
remote bookmark, which its export never writes, to the side in `.git`
(`remote_reset_without_export`), or, where `jj op restore` put the conflict back, to the value
from before the restore, which musubi writes everywhere as the restoring machine's `.git` kept
it (the expected value in `Refs.lean`); an undo, redo, `jj op restore` or `jj op revert` on that
machine restored a record its export couldn't then write over, such as a conflicted bookmark's;
or jj's merge of two op heads that both changed the record, each as jj does
(`concurrent_records_revert`). Otherwise the check walks back from the import to the operation
that left the record differing from `.git`, and the failure names it. Imports of git's HEAD
("import git head"), which move a workspace's working copy onto what HEAD has, are checked the
same way against jj's record of each workspace's HEAD (`git_heads`). git moves HEAD only where
it is still a symbolic ref to the branch git moves, as in a new repository until jj first writes
HEAD, and jj writes HEAD only as it records it, so such an import may change the record only
after such a move, or where jj's merge of two op heads that both changed the record left it
differing from `.git`, as after a command at an older operation (`--at-op`), which still writes
HEAD ([races.md, "Known jj limitations"](races.md#known-jj-limitations)).

At the end of a sequence, and at most once in the middle, the hive syncs to a fixed point,
and the test checks that:

- every node's canonical head equals the hub's;
- translation does what the protocol's model assumes of it ([protocol.md, "Translation
  layer"](protocol.md#translation-layer)): in a copy of each repository that has lost its
  translation cache, translating again from nothing gives what the machine remembered, makes no
  canonical operation, gives distinct local operations reachable from the op heads distinct
  canonical forms, with the parents' forms as their parents but at a join point, and gives every
  operation of the hive's history a realization that translates back to it;
- all repositories agree on visible commits, change ids, bookmarks, tags, and remote bookmarks;
- in every colocated repository, `refs/heads` matches the local bookmarks that are neither
  conflicted nor on the root commit (which git can't hold), and a further `jj status` imports
  nothing;
- every operation made on any machine appears in every machine's `jj op log`;
- no change diverges, and no bookmark or tag conflicts, unless jj makes the same of the same
  operations in one repository (the reference, below);
- no change has two commits with the same parents and contents that two merges rewrote from
  one commit: the same rebase done twice, which the hub's sequencing exists to prevent. A
  ledger (`e2e_search/ledger.rs`) of which machine's commands rewrote what tells this apart
  from rewrites that commands make alike.

The reference (`e2e_search/reference.rs`) is a jj repository of the test's own that replays
the hub's history, operation by operation, with the same parents:

1. Each machine's commands, and the operations musubi writes for it such as a forget, go in as
   the hive has them. Each merge goes in as jj's own merge of the same parents, in the same
   order, as jj merges concurrent processes on one machine.
2. Where jj's merge gives what the hive's did, comparing commits by contents, change ids and
   parents, the reference goes on from the hive's operation. Where it doesn't, it goes on from
   its own, applying later operations three-way as jj applies a concurrent one, until the two
   agree again past every point where they parted.
3. A merge that makes a change diverge into more commits than jj's merge of the same parents
   does, or a name conflict with terms jj's lacks, is musubi's doing, and so is any such excess
   at the hive's head over the reference's. The failure lists where the merges parted.

Merges staged through the hub are judged as staged: a node that merges part of another
machine's work and later the rest makes what jj makes of the same two merges. A merge made on a
machine, rather than realized there, is judged against the parents as that machine had them
too, where they lack only the working-copy commit of another machine's workspace it forgot,
which the hive keeps: jj there merges as if the forget abandoned it ([races.md, "Known jj
limitations"](races.md#known-jj-limitations)).

The test also checks that the hive's history can stand for one repository's: every machine's
realization of each operation has the hive's view of it, and no operation but a merge makes
anything diverge or conflict unless what it did explains it: a fetch, an undo or restore, or an
import of git refs or of git's HEAD.

To keep the search effective:

- a rule is eligible only when it has work to do, and its candidates come from a helper that
  its precondition shares;
- each search shard has its own Hegel example database;
- a case replays exactly, so that Hegel can shrink a failure and a stored example finds it again
  ([efficient-tests.md, "Make generated cases replay
  exactly"](efficient-tests.md#make-generated-cases-replay-exactly)). A failure that doesn't
  replay exactly fails the run at once, saying where the replay diverged.
  `MUSUBI_SEARCH_FINGERPRINTS` writes each case's trace without the ids that differ between runs,
  for checking that two runs of a case did the same;
- the run ends by listing rules that never fired. An unreached rule is a search problem: give
  it a richer starting state or fix its precondition.

## Testing the tests

`just mutants` runs `cargo-mutants` over the protocol core's hub and node logic: each surviving
mutant is a change to the protocol that the property and conformance tests fail to notice.
[conformance.md](conformance.md) lists hand-made mutants and which check catches each.

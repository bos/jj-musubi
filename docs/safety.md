# Trying musubi safely

musubi shares unfinished work and repository history between your machines. Background sync
leaves checked-out files alone, and you can stop it while keeping ordinary jj repositories.
It also passes on mistakes, so it helps to know what sync changes before joining active work.

## What sync can change

Each machine has its own repository and checkout. A **hub** stores shared history and passes
updates between the machines; their background sync processes are **daemons**. The copies of
one project form a **hive**.

- **Files in your checkout stay put.** Received work becomes available in the repository.
  You choose when to check it out. If another machine rewrites the commit you're using, jj
  reports a stale working copy; [update it when you're
  ready](guides/working-across-machines.md#when-another-machine-rewrites-your-working-copy).
- **Repository history and Git refs change.** Commits, bookmarks and the record of repository
  operations are shared. A mistaken rewrite, restore or operation abandon can therefore reach
  every machine. [Undo across machines](guides/working-across-machines.md#undo-across-machines)
  explains how to inspect and reverse repository changes.
- **Concurrent edits stay visible.** musubi uses jj's merge behavior, as for concurrent
  commands on one repository. Bookmarks can conflict and changes can become divergent;
  [resolve them once](guides/working-across-machines.md#when-machines-change-the-same-thing)
  and that resolution syncs too.
- **Edits jj hasn't recorded stay local.** Neither `musubi status` nor `musubi sync --outgoing`
  snapshots files. Newly created, nonignored files normally enter jj's next snapshot and can
  then spread too. Keep secrets and generated files ignored before recording them.

Keep your usual backups. A synced copy carries deliberate deletions and history removals too.
If a hub loses its state, surviving repositories can [rebuild the
hub](guides/manage.md#replace-or-move-a-hub) from work they retained. Work that existed only on
an entirely lost machine needs that machine's backup. Recovery after hub rollback can leave
changes divergent, which you resolve with jj.

## Try a disposable project first

Use the [setup guide](guides/setup.md) with a project you're comfortable sharing. After its
[first-sync check](guides/setup.md#check-your-first-sync), pick up the recorded work in the
second copy and make an edit there. Check that it appears in the first copy's `jj log` while
its checked-out files stay put. This lets you see the handoff before using active work.

To stop this machine's background syncing, run:

```sh
musubi daemon stop
```

This stops the daemon for all its copies on this machine. It keeps their hive memberships,
repositories and files, and leaves the hub and other machines running. It does not undo
anything already sent or received. Explicit `musubi sync` still syncs without the daemon;
`musubi create`, `join` or `clone` can start the daemon again. `musubi daemon uninstall` also
removes its login startup. [Pause syncing or leave](guides/manage.md#pause-syncing-or-leave)
explains resuming and removing just one copy.

When you're done trying it, `musubi leave` in each trial copy attempts one last sync, then
removes that copy from its hive. The files and repository stay. `--force` allows leaving if
that attempt fails; it still attempts the sync, so use `musubi daemon stop` to pause background
traffic while deciding what to do.

## When accidental files are recorded

jj's older snapshots can retain files even after you remove them from the current version.
To limit how much of that content spreads, musubi holds sending above 100 extra file paths or
8 MiB. Content needed by changes you've deliberately committed or rewritten, and content
already shared with the hive, doesn't count against the limits. Receiving continues.

[Accidental-file recovery](troubleshooting.md#accidentally-added-files-and-sending-stopped)
shows how to inspect the hold and keep useful local files. Cleanup has a preview: it preserves
current work and versions created by deliberate changes such as `jj commit` or `jj describe`,
but can discard earlier uncommitted versions.
Exact approval sends the inspected history instead. Files below the limits can still spread;
these limits do not identify secrets.

## What backs this up

The protocol has machine-checked Lean proofs. Tests compare the Rust implementation with
those models and run real jj repositories through concurrent commands, crashes, interrupted
connections and simulated loss of hub state. CLI tests exercise the quick start.

These checks cover different parts of the system. A proof about a protocol model is not a
proof of every line of jj or musubi, and the tests cover the cases they run. The sections
below explain the evidence and its boundaries. The [race
catalogue](internals/races.md) lists tested outcomes and known limitations, with links to the
tests. The [conformance guide](internals/conformance.md) records where implementation and
model agree and where obligations remain.

## Lean proofs

Lean is a theorem prover: it checks mathematical proofs about a model of the protocol. The model
defines the states a sync can reach and the steps between them. Its safety proofs cover every
reachable state, for any number of machines, with message loss, duplication, delay and reordering,
and process crashes. They establish history retention, availability of referenced operations and
objects, and the absence of feedback and duplicate merges. The hub-rollback model identifies which
guarantees survive rollback.

The convergence proofs assume that user edits, hub rollbacks, crashes, transport failures and
storage errors eventually stop. Machines must resume syncing, and their requests must succeed with
correct replies. Protocol actions whose prerequisites remain satisfied must eventually run. Old
replies must eventually stop affecting protocol state. Repository calls must behave as specified,
and musubi's maintenance routines must eventually stop writing operations. The proofs assume this
last condition; they do not prove termination of those routines. Snapshot publication holds
must eventually be resolved, disabled or approved; the convergence proofs do not establish
progress through a deliberate hold.

Other models cover operation abandonment, git-ref import and export, distinguishing a joined
repository from a duplicate of its directory, workspace names, and chunked transfers.

## Hegel conformance tests

Hegel is a property-testing framework for Rust. It generates sequences of actions and, when a test
fails, reduces the sequence while preserving the failure. These tests run the production Rust
protocol core with test implementations of its storage interfaces and a simulated network. The
harness creates operations represented by ids, parent links and object sets; it can lose or
duplicate messages, crash participants, and inject storage errors.

For actions the model can represent, the tests compare the Rust state with an executable Lean
model, called the oracle. The oracle uses the proof definitions or executable definitions proved
to agree with them. The tests also compare the Rust implementation's progress with the convergence
models. If a storage failure leaves a state the model cannot represent, that case stops consulting
the oracle. It continues checking data retention, availability of required operations and objects,
and convergence after failures stop.

The core harness does not use jj repositories. Conformance tests for jj's ref handling, operation
abandonment, copy selection, and receiving and sending chunked data compare each with its Lean
model.
Repository tests also check effects the core harness cannot represent, such as merging incoming
history with local edits and retrying updates after hub rollback.

The proofs do not cover every combination of these behaviors. For history rewritten by operation
abandonment, individual steps have proofs that they preserve properties such as keeping the
operations and objects required by the hub's accepted history. Those proofs do not establish that
the preconditions for every step continue to hold across all possible sequences combining them
with the rest of the protocol.

## Kani checks of Rust code

Kani is a model checker for Rust. It uses a solver to look for inputs and execution paths that
violate assertions in the code, covering all choices allowed by a check within its loop bounds.
The checks for chunk offsets, lengths and message size limits verify that:

- The chunk-overlap check identifies the first new byte at the end of the received data, or
  reports that the chunk adds nothing or leaves a gap.
- At every supported message size, the chunk-size calculation reserves at least as much space for
  metadata as at the smallest size. A unit test verifies that the metadata fits at that minimum.
- The end-of-download check cannot overflow and reports completion exactly when the read reaches
  the end of the data, for any offset and requested length.
- Each batch of an upload or download starts at the requested offset and advances by the chunk
  size without overflow. A batch ends after its size in chunks, at most eight, or on reaching
  the end of the data; the next batch continues the transfer.

The storage check exercises how the hub accepts pushes. The hub's head is the latest operation it
has accepted. A push names the head it was built on, called its expected head. A new update must
extend the accepted history and name the current head as its expectation. A replay of an already
accepted push must succeed without counting as another update. The hub's sequence number counts
accepted head changes.

The Kani harness runs the production push handler against a three-operation graph. The hub starts
at `root → A`, and the proposed operation is `B`:

| Proposed history | Expected head | Result |
| --- | --- | --- |
| `root → A → B` | `A` | Accept `B` once its dependencies are present |
| `root → A → B` | `root` | Reject the stale expectation |
| `root → B`, beside `A` | `A` | Reject a sibling that does not extend `A` |
| `root → B`, beside `A` | `root` | Reject |

Each case sends four pushes with the same expected head. The first two send a possibly incomplete
upload; each fallible storage call can fail independently. A failed import may retain any subset
of the uploaded data. The third push supplies all objects with failures disabled; the fourth
replays it.

Kani exhausts these choices. Errors and incomplete uploads must leave the accepted head unchanged.
The complete retry must install `B` in the first case and leave the hub at `A` in the others.
Successful replies must report the stored head and sequence. If an earlier push already installed
`B`, its replay must succeed despite still naming `A` as the expected head, without advancing the
sequence again.

This checks four handler calls with one writer. It excludes crashes, operation abandonment, longer
histories and the storage implementations used by the hub.

## Tests against jj repositories

Regression tests exercise races between machines through the sync protocol and hub storage,
comparing the result with jj's concurrent-command semantics. Examples include rewriting a change
while another machine has unsaved edits above it, and forgetting a workspace while another machine
is using it. Tests also duplicate a repository directory and verify that the two directories
cannot sync as the same copy.

Hegel end-to-end tests generate command sequences and invoke the `jj` and `git` executables across
two to four repositories. They interleave edits, rebases, undo, operation abandonment, ref
changes and workspace changes with interrupted syncs, lost replies, hub restarts and rollback.
During each sequence, checks ensure that repositories remain readable. The harness tracks external
git ref changes and jj's own import behavior to detect imports that revert work because musubi
recorded the refs incorrectly. After synchronization, the repositories must agree on shared
commits, refs and retained operation history.

A reference repository replays the shared history using jj's own merges. Comparing the
synchronized repositories with this reference identifies divergence and conflicts introduced by
musubi. The tests also detect duplicate rebases. Hegel records failing command sequences for
replay.

CLI tests execute the README's quick start, including commands printed by musubi. On Linux and
macOS CI runners, service tests install the daemon through systemd or launchd, kill it, and check
that the service manager restarts it. They also check that `musubi daemon stop` does not trigger a
restart.

## Fault injection

Transport tests record a session in which two machines push and fetch commits, then replay its
calls with faults. The payload limit forces transfers to use multiple chunks. A request can be
lost before reaching the hub, or its reply can be lost after the hub has acted on it. Another case
delivers the request an hour late, after the hub has deleted expired transfer data. Once the link
recovers, a retry must complete; the test fails if it sends more than 2,000 requests without
finishing. Another test moves data so slowly that each call takes hours, while the hub keeps
deleting transfer data left untouched for an hour; each call must still complete without sending
any chunk of data twice. A third gets only the first reply of each batch back in time, so that
calls time out again and again; they must still complete. A fourth sends data one message at a
time each way, so slowly that each chunk takes 80 seconds to cross; each call must complete
without any chunk crossing the link twice.

Tests with jj repositories replace the hub's replies with well-formed but false ones: a head the
hub does not have, operations with changed parents, objects for another operation, or another
request's reply. Once the hub resumes answering correctly, the repositories must converge without
losing commits.

Other tests send malformed requests to the hub. After each request, the hub must still serve
fetches and may advance only to history whose dependencies it has.

Stream tests use pipes with one-byte buffers to exercise cancellation, timeouts, disconnects and
late replies during transmission. Other tests split frames at different byte offsets and pause
reads and writes. A hub-worker test panics after accepting a push but before replying; the next
fetch must reopen the service and find the accepted history intact. Another hive served by the
same hub must continue syncing. Another test holds a hive's worker while requests behind it time
out; the worker must skip them, but for a chunk of an upload, which it must still store, and
answer the requests whose senders still wait.

Each operation refers to a view, which records the visible commits, bookmark targets and each
workspace's working-copy commit. Hegel tests truncate, zero-fill and garble the logs storing
operations and views. Each entry must read back exactly as written or be absent; corruption must
never produce different contents under an existing id. Records before the damaged region must
remain readable.

## Fuzzing

libFuzzer, through cargo-fuzz, drives the frame, message, bundle and operation-import decoders.
The message and bundle targets test raw inputs and inputs prefixed with valid version fields or
headers to reach the parser logic behind those checks.

A decoded frame must encode back to exactly its input bytes. Messages may have multiple encodings,
so their decode/encode/decode round trips must preserve the decoded value; trailing bytes must be
rejected. Bundle records must survive rewriting with and without compression.

Import fuzzers submit operations under both incorrect and correct content hashes. They also
construct histories with duplicate or altered views, missing operations, and views encoded as
differences from earlier views. Whether an import succeeds or fails, every stored object must have
the contents its id names.

## Mutation testing

Tests run against implementations that accept stale pushes or apply operations before their
parents; each violation must be detected. `cargo-mutants` changes production logic and runs tests
against each variant. Mutations that pass require inspection: they can expose missing coverage or
preserve observable behavior.

## Continuous checks

CI checks the Lean proofs and runs protocol, repository and CLI tests on Linux, macOS and Windows.
The Hegel end-to-end search runs nightly with changing seeds. A nightly compatibility job builds
and tests against jj's main branch to detect upstream changes that would break musubi before a jj
release.

# Correctness and verification

musubi keeps copies of a jj repository in sync through a hub; together they form a hive. Its
verification combines proofs of a protocol model with checks of the Rust implementation and tests
against jj repositories.

## Required behavior

A jj operation records a change to repository state, such as creating or rebasing commits, moving
bookmarks, or updating workspaces.

Concurrent edits must resolve as jj resolves concurrent commands in a single repository. musubi
uses jj's merge implementation and sequences updates through the hub to prevent two machines from
independently rebasing the same concurrent work. Receiving an operation must not create a
duplicate to send back; merging concurrent edits creates a new operation.

Once edits and failures stop, copies that resume syncing must converge on the same history.
Repositories retain the work they send and receive, allowing a replacement hub to be rebuilt from
those copies. Hub rollback permits duplicate merges, which can leave a change divergent, but must
not prevent eventual convergence after rollback stops.

Synchronization must leave working-copy files alone, and leaving a hive must preserve the
repository. A reconnecting copy must adopt published operation abandonments instead of
reintroducing the removed history.

[Working across machines](guides/working-across-machines.md) explains how concurrent edits and
operation abandonment appear in jj.

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
last condition; they do not prove termination of those routines.

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
calls time out again and again; they must still complete.

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
same hub must continue syncing.

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

# How jj-musubi keeps your work safe

jj-musubi shares finished and unfinished work and repository history between your machines.
Mistakes and bugs can affect every copy, so we work hard to eliminate bugs.

## Minimal interaction with jj

With jj-musubi, each machine maintains its own repo, workspaces, and working copies. The daemon
exchanges jj's operation log. Incoming work becomes available in the repo, and you choose when
to check it out. If another machine rewrites the commit you're using, jj reports a stale working
copy. Files only change when you update them.

Commits, bookmarks, Git refs and repo operations are synced across repos. A mistaken rewrite
or restore can reach every machine. Concurrent edits can leave conflicted bookmarks or
divergent changes, as in local jj workspaces.

The daemon syncs edits once jj records a snapshot. You can opt in to
[background snapshots](guides/working-across-machines.md#record-saves-automatically) so the daemon
records edits even while you aren't running jj. It reads checked-out files and leaves them in
place.

Because jj-musubi syncs normal jj metadata and doesn't modify jj itself, jj works normally at
all times, regardless of whether your machine is online and syncing, offline and busy, or coming
back online after sleeping or being powered off.

## How jj-musubi is tested and verified

As of November 18, 2026, the [coverage report](../contrib/assurance/data/2026-11-18/README.md)
records **92.8% line coverage** across production Rust code, including **98.1%** in the sync
protocol core. Of course code coverage is an imperfect measure, but it's about the best we have.
An [interactive map](https://www.serpentine.com/software/jj-musubi/assurance/) shows, module by
module, which lines the tests and fuzzers ran and what the proofs cover.

<!-- musubi-assurance: Measured on November 18, 2026, using jj 0.47.1. -->

jj-musubi is checked at several levels:

* Mathematical models of the protocol
* Comparisons between those models and production Rust
* Tests with real jj repositories
* Deliberately interrupted and corrupted exchanges
* Fuzzing
* Tests against deliberately broken code (mutation testing)

Each catches failures the others can miss. The checks below ask both whether work survives and
whether syncing can finish once transient failures stop.

### Machine-checked protocol proofs

Lean checks mathematical proofs about the states the sync protocol can reach. The core safety
proofs cover any number of machines and arbitrary sequences of message loss, duplication, delay,
reordering and process crashes. They establish that accepted history is retained, referenced
operations and objects are available, and receiving work does not feed it back as new work. With
the hub's accepted history intact, they also rule out machines independently creating the same
merge. A separate model covers the hub (which stores shared history) going back to an earlier
state or being rebuilt; such a rollback could permit duplicate merges.

The progress proofs establish that the sync policy converges: when work stops and each exchange
with the hub succeeds, every sequence of syncing steps ends with the machines on the same shared
history, also after the hub goes back to an earlier state. They check that progress cannot
continue forever without finishing, rather than relying on a timeout in a test. They are about
the policy's atomic exchanges, not the running system, whose requests can be lost, repeated and
answered late. That convergence is tested, not proved: the generated end-to-end tests check
that every machine ends on the hub's history at the end of every case, and the race and
fault-injection tests check the parts that make it hold, such as retries after a lost reply.

The models extend beyond the main sync loop. Separate models cover Git-ref import and export,
which machines still belong to a shared repo, distinguishing a joined repo from a duplicate of
its directory, workspace names, chunked transfers, how musubi moves jj's operation heads, and
the limits, approval and cleanup of accidental snapshots.

A further model covers how incoming work is written into your repo while your jj commands run
and the daemon may crash at any step. It models jj's operation log and its merging, with tests
checking the merge rules against real jj. It assumes the daemon adds a new operation head before
it removes old ones, removes only those the new one descends from, under jj's lock and once it
has checked they haven't changed, and writes nothing but incoming work and the merges jj would
write itself. Within it, the proofs show that no operation your jj commands record leaves the
operation log, unless you abandon it with `jj op abandon`, which the model leaves out; that once
incoming work is in, you see what jj shows when it merges your work with the incoming work; that
a crash leaves the repo as an uninterrupted sync would, apart from extra operation heads that jj
drops the next time any jj command runs; and that once you stop running commands, nothing in the
repo can stop syncing from finishing with the incoming work in. Tests with real jj check where
the daemon's code ends up, not its individual steps. How each incoming change becomes an
operation in your repo, including what it records of each workspace, is checked by tests, not
proofs. Where your own commands moved a workspace two ways at once, jj can keep the other move
once incoming work arrives.

These models have different scopes; they are not all one combined proof.

The proofs have no unfinished Lean placeholders and introduce no additional axioms. The
[formal guide](../formal/README.md) lists the theorems and their assumptions. The remaining
implementation and composition gaps are described [below](#what-remains-outside-the-guarantees).

### Checking production Rust against the models

The Lean definitions also run as an executable reference, called the **oracle**. Tests drive
the production Rust protocol core through generated sequences and compare its actions and
state with the oracle after each step. The executable definitions are the proof definitions,
or have proofs connecting them to those definitions.

Hegel, the property-testing framework, chooses sequences of local work, concurrent syncs,
out-of-order messages, repeated replies, crashes and hub rollback. On failure, it shrinks the
sequence to a small reproducer and saves it for replay. The tests also check safety properties
directly on Rust state, independently of the oracle comparison. During recovery, they check
that the progress measures used by the convergence proofs decrease.

These core tests use abstract operations and controlled storage instead of jj repositories.
Further conformance tests compare real ref handling, copy selection, workspace naming,
snapshot cleanup and transfer code with their own Lean models. Tests with
real repos cover effects the core abstraction cannot express, such as merging received work
with concurrent local work and retrying writes after hub rollback.

The [conformance guide](internals/conformance.md) records exactly which Rust behavior each
comparison covers, including where a partial storage failure stops fitting the model and
independent retention and recovery checks continue instead.

### Storage failures and bounded verification of Rust

Generated tests inject errors at storage calls before a write, after its complete logical
effect, and after only part of an import has succeeded. They check retained operations and
objects immediately after the error, before recovery can hide damage. Then they reopen state,
retry as the background sync process does, and require the machines to converge. A fixed sweep
visits every reachable fallible storage method in its schedule, including uncommon error paths
that random generation can miss.

The [Kani model checker](https://github.com/model-checking/kani) verifies some of our low-level
Rust code using a solver. Its arithmetic checks cover every supported input value for chunk
offsets, overlaps, message capacity and download completion, including values near integer
limits, and transfer windows of up to eight chunks.

Another Kani check runs the production push handler over a small history with independently
failing storage calls. The first two attempts may fail and retain any subset of an upload;
a complete retry follows, then a replay. Across all choices within those bounds, the hub must
retain the dependencies of its accepted history, report what it actually stored, reject
incomplete or stale updates, and accept a retry without counting it twice. This checks the
Rust handler itself over four calls and a three-operation graph. The
[bounded-verification guide](internals/bounded-verification.md) gives the exact scope and
shows deliberate defects that make its assertions fail.

### Races and generated work in real repositories

Focused regression tests put machines into difficult races: one rewrites a change while another
has work above it; one forgets a workspace another is using; an accepted update loses its reply;
or a machine comes back online after history it relied on has been removed. They compare
outcomes with jj's own behavior for concurrent commands. The [race
catalogue](internals/races.md) links each scenario to its test.

The generated end-to-end search goes further. It runs the actual `jj` and `git` executables in
two or three repos, interleaving edits, snapshots, commits, rebases, merges, squash, undo,
operation abandonment, bookmark and tag changes, workspace changes, fetches and pushes. Machines
can work from stale state, stop partway through syncing, lose their translation cache, disappear
and rejoin, or encounter a restarted, rolled-back or rebuilt hub.

After each action, every repo must still load. The search tracks changes made directly with
Git so that an incorrect import cannot silently move a bookmark or working copy back. When
the machines finish syncing, they must agree on visible commits, change ids, bookmarks, tags
and remote bookmarks, and retain the shared operation history that was not deliberately
abandoned.

Agreement between machines is not enough: they could all agree on the same wrong result.
An independent reference repo replays shared history using jj's own merges. Comparing with
that reference checks for changes, conflicts and duplicate rebases introduced by syncing.
The search also discards translation caches and reconstructs mappings to check that cached
state was not concealing an inconsistent history. Failures shrink to replayable command
sequences. The [test guide](internals/testing.md#generated-end-to-end-tests) describes these
checks and the cases that require explicit user recovery.

### Interrupted transfers, wrong replies and damaged storage

Fault tests replay real push/fetch exchanges with faults at chosen boundaries. A request can
vanish before reaching the hub, its reply can vanish after the hub acted, or it can arrive
after temporary transfer data has expired. Other cases keep timing out partway through
multi-chunk transfers or make each chunk take 80 seconds on a controlled clock. Transfers
must recover and finish without repeatedly sending chunks that already arrived.

Tests also replace replies with messages that decode correctly but lie: an unknown head,
wrong parents, another operation's objects, or the reply to a different request. Once correct
replies resume, syncing must recover without losing the machines' commits. Malformed-request
tests require the hub to remain able to serve valid fetches and to accept only history whose
dependencies it has.

At the stream boundary, one-byte pipes and generated read/write interruptions exercise
cancellation, timeouts, disconnects, partial frames, late replies and full queues. Process
tests use controlled child processes to check reconnection, bounded cleanup, children that
ignore EOF, and large stderr output that must not deadlock the connection. A hub-worker test
panics after accepting a push but before replying: the next fetch must recover the accepted
history, and another repo served by the hub must continue syncing.

Storage tests truncate, zero-fill and garble append-only logs. An entry must read back with
its original contents or be rejected; damaged bytes must never become different data under
an existing content id. Entries before the damaged region must remain readable. These
checks exercise recovery from specific damage; the hub does not promise durable storage
across power loss.

### Coverage-guided fuzzing

libFuzzer drives the parsers for frames, greetings, messages, bundles and imported operations
with generated bytes. Some inputs begin with valid headers and version fields so that fuzzing
reaches deeper validation instead of stopping at the first check.

The assertions go beyond avoiding crashes. Frames must encode back to their exact bytes;
messages must preserve their decoded value through a round trip and reject trailing bytes;
bundle records must survive rewriting with and without compression. Import fuzzers submit
both correct and incorrect content hashes, duplicate and altered views, missing operations,
and views encoded as differences from earlier ones. Whether the import succeeds or fails,
stored objects must have the contents their ids name.

### Checking that the tests detect broken code

Mutation testing deliberately changes production logic, then runs the tests against each
variant. The core campaign changes the hub and machine protocol logic. Further campaigns
cover selected stream and repo-adapter decisions, including ancestry, missing objects,
recovery after lost history and classification of retryable failures.

Hand-written defects check important boundaries too: accepting a push without its required
objects, accepting a stale expectation, ignoring a failed head write, or applying an operation
before its parents. Each must cause a relevant assertion to fail. This provides evidence
that a passing test observes the behavior it claims to protect.

A surviving mutation is inspected: it can reveal a missing check or preserve observable
behavior while changing an optimization. A compilation failure is not counted as a defect
caught by testing. The [mutation-testing guide](internals/testing.md#testing-the-tests) and
[conformance examples](internals/conformance.md#evidence-that-the-check-has-teeth) record the
campaigns, deliberate defects and their results.

### Continuous checks and recorded evidence

CI checks the Lean proofs and runs Rust protocol, repo and CLI tests on Linux, macOS and
Windows. Command tests exercise the quick start through the shipped binary, including the
commands it prints. Service tests on Linux and macOS install background services and check
restart and deliberate-stop behavior.

The generated end-to-end search runs nightly in separate shards with changing seeds and
saves failing examples. Another nightly job builds and tests against jj's main branch to
catch upstream changes before a jj release. Longer fuzzing, Kani and mutation campaigns are
separate runs; they are not all part of every CI job.

The [saved assurance data](../contrib/assurance/data/2026-11-07/README.md) connects individual
test executions, observed Lean-oracle calls, fuzz checkpoints and mutation results with the
production code they reached. Line coverage measures execution; the assertions, model
comparisons and mutation results provide the evidence about what those executions checked.

### What remains outside the guarantees

The proofs establish properties of their models; they do not prove every line of Rust or jj.
Convergence assumes that edits and failures eventually stop, machines resume successful
syncing with correct replies, and snapshot holds are resolved, disabled or approved. It also
assumes maintenance eventually stops adding repo operations; that termination is not proved.
No proof covers convergence of the running system, with its retries and late replies, or the
translation between jj's operations and the shared history; the tests above are the evidence for
both. The [conformance guide](internals/conformance.md) describes the boundaries between the
models and real repository behavior, and the [race condition
catalogue](internals/races.md) records known limitations alongside tested outcomes.

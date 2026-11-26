# Conformance between the Lean models and the code

The [Lean models](../../formal/README.md) are checked against the Rust implementation through
an executable *oracle*. The oracle evaluates the models' own definitions, or executable forms
proved sound against them. Rust tests run the production code and compare its transitions,
results and state with the oracle. This document owns that correspondence and its limits;
[testing.md](testing.md) describes the test layers and how to run them.

| Model | Code | Test | Section |
| --- | --- | --- | --- |
| The sync protocol ([protocol.md](protocol.md)) | `crates/musubi-core` | `conformance`, through the oracle | [The claim](#the-claim) to [Wire format](#wire-format) |
| `Presence.lean`: which copies a hive shows | `Presence` | `presence::conformance`, through the oracle | [Presence](#presence) |
| `Refs.lean`: per-machine refs | jj's import and export, and musubi's realization | `ref_laws` (the laws the model assumes), and `refs` and `view::tests`, through the oracle | [Per-machine refs](#per-machine-refs) |
| `OpHeads.lean` and `OpHeadsRace.lean`: moving op heads | `node/heads.rs` | `same_conformance` through the oracle, and `heads_laws` against jj | [Moving op heads](#moving-op-heads) |
| `Realize.lean`: realization among jj commands and crashes | `node/realize/advance.rs` | `concurrent_tests` against jj's own merge, through the oracle, and `realize_laws` against jj | [Realization](#realization) |
| `Expected.lean`: conflicted-ref history | `node/git.rs::expected` | `expected_history_conforms_to_model`, through the oracle | [Expected values from history](#expected-values-from-history) |
| `Chunks.lean`: chunked blobs | `BlobStore::receive`, and `RemoteHub`'s `upload` and `download` | `receive_follows_the_prefix_model` and `transfers_follow_the_attempt_model`, through the oracle | [Chunked blobs](#chunked-blobs) |
| `Copies.lean`: which local repository is a joined copy | `copy::standing`, `refine` and `check` | `copy::conformance::decisions_conformance`, through the oracle | [Copies](#copies) |
| `Publication.lean`: cumulative snapshot budgets, scoped approval and selected cleanup | `node/publication` and the pre-upload gate | `node::publication::tests` through the oracle, and `musubi-sync` publication fixtures | [Snapshot publication](#snapshot-publication) |
| `Identity.lean`, `Names.lean`: the names other machines' workspaces show under | `workspaces::display_names` | `workspaces::tests::names_conform`, through the oracle | [Workspace names](#workspace-names) |

## The claim

Every behavior of the Rust protocol core, at the level of abstraction of the model, is a
behavior of the Lean model. The Lean safety theorems hold for every reachable model state, so
they hold for every state the Rust core reaches. A run in which the hub goes back, or the hive
is made again, is a behavior of the extended model of `formal/Musubi/Regress.lean`, and the
weaker invariant proved there holds in it. [Storage errors](#storage-errors) add representable
prefixes and explicit limits to that correspondence.

The chain has three links:

1. **Relational model to executable model.** The proofs are about a relational model: `Step`
   says which transitions are allowed, over states that need not be finite.
   `formal/Musubi/Exec.lean` defines `execStep` on finite states. `exec_sound` proves that
   whenever `execStep` accepts an action other than `hubRegress`, the corresponding
   relational `Step` exists between the abstracted states, and `exec_rsound` that whenever it
   accepts any action, an `RStep` of the extended model does. The executable model therefore
   never accepts anything the proofs don't cover.
2. **Executable model to oracle.** `formal/Oracle.lean` is a thin JSON wrapper around
   `execStep`, built by `lake build oracle`. It contains no protocol logic of its own.
3. **Oracle to Rust.** The Hegel test `conformance`, in `crates/musubi-core/tests/protocol.rs`,
   runs the Rust hub and nodes, translates every step they take into model actions, and checks
   each one with the oracle. It fails on any action the oracle rejects, or any difference
   between the Rust state and the oracle's state. Hegel shrinks failures to a minimal trace.

That carries safety, not liveness. The test also runs the nodes to convergence, which
catches a node that never gets there, but not one whose steps the termination proof does
not cover, or whose pushes don't upload what the proof assumes. So it also checks the Rust
policy against the liveness proofs ([Liveness](#liveness)).

## The abstraction

The conformance test runs the real Rust core (the hub's `hub::handle` and `NodeCore`) against
test implementations of its storage traits, in `crates/musubi-core/tests/support/model.rs`.
These keep exactly the model's state:

| Model | Rust test implementation |
| --- | --- |
| Universe (every operation created): `next`, `par`, `objs` | the test's operation table; operation and object ids are small integers, root `0` |
| Hub `ops`, `objs`, `head`, `seq` | `FakeHub` |
| Node `lops`, `lobj`, `heads`, `known`, `sops`, `sobj` | `FakeRepo` (`lops`…`sobj`) and `NodeCore` (`known`) |
| `net`, the set of every message sent | the test's network: a set, so any message can be delivered any number of times, or never |

`lops` and `lobj` are a node's local operations and objects, and `sops` and `sobj` what it
has staged. The jj-specific parts of a real node (canonicalization, realization, bundles) are
not covered by this link; the jj example tests and the generated end-to-end tests cover them
([testing.md](testing.md)).

## Storage errors

The hub's logical loss and rollback rules describe recovery to a healthy hub. Normal body
loss preserves every retained historical operation, since `HubStore::open` replays those
bodies. Objects needed only by an older head may still be lost. The harness records that
loss, verifies the requested rollback target is incomplete, then explicitly chooses the
existing remake action. Native startup does not validate every historical object, so this
is an environment recovery choice, not a claim about automatic native detection or every
observable damaged-store prefix. Physical recovery across that interval remains outside
the refinement; no hub durability is added.

`storage_failures_preserve_operations` runs the same generated protocol sequences through
`support/storage.rs`'s fallible wrappers around `FakeHub` and `FakeRepo`. One shared countdown
counts actual trait calls, including reads through `&self`, without counting helper calls
inside a fake. A call can fail before its effect. Selected writes can fail after a logical
effect; imports can retain a nonempty proper prefix, parents first for operations. The
fixed `storage_boundaries::every_storage_boundary_recovers` schedule sweeps every countdown
and asserts the boundary catalogue is complete. A countdown beyond the event's calls leaves
it successful; the harness never invents an error to reach a quota.

| Injected effect before returning an error | Production basis |
| --- | --- |
| None, at 26 reachable fallible trait methods | The core must propagate the trait's errors. Some adapter methods currently always return `Ok`; these test their fallible contract, not a physical I/O failure there. |
| All or a proper prefix of `store_ops` / `stage_ops` | `CanonicalStore::import_operations` can retain earlier batches before a later failure. `NodeAdapter` can also fail after import while checking announced parents. |
| All or a proper prefix of `store_objects` / `stage_objects` | Simple-backend import stores objects individually; a later error can leave earlier objects present. The abstract objects have no internal structure. |
| A merge or advance | jj can publish before later ref export, working-copy repair or canonicalization fails (`advance`). This projects the complete logical effect, not each intermediate translation. |
| A complete accepted-base write | `write_all` may finish before `set_len` fails. Partial or invalid bytes are outside this logical-id abstraction. |

The fixed-node harness reaches 26 of the traits' 27 fallible methods, including the
push/acceptance bookkeeping (`pushing`, `learned`, `set_accepted_base`). `permit_publication`,
a local policy the fake leaves at its default, isn't wrapped.

The harness requires every injected error to reach the caller before another entry point
or the end of injection; selecting a fault alone does not count as coverage. For each
failed entry point the wrappers journal the actual completed logical effects.
Where they fit, the harness checks them against the oracle **before recovery**: a stuttering read
error, `learn`, complete `recvOps` / `recvObjs`, `advance` or `merge`. It checks the unchanged
state too when no action occurred. The adapter's accepted base and the core's realization plan are
not model state. The error return and their intermediate changes are not themselves proved
transitions.

An errored merged push can store operations without objects, or only some of either, without
sending a reply. The oracle's merged push actions combine storage and reply; its separate
upload actions would require fictitious messages. A partly received bundle likewise need
not match an entire message in `net`. These transitions explicitly retire the oracle for the
rest of that case; no model reachability claim is made from there. Imports of content
already stored are stutters and keep the oracle, checked explicitly by
`duplicate_upload_errors_stutter_in_the_model`. Rust closure, ownership,
retention and final convergence checks still run, as do checks that successful hub replies
and publications describe the actual store. The next case resets and reuses the oracle.

After an error, before any restart, the harness checks every published head's required data,
all existing safety invariants, and that previously retained operations, objects and heads
remain present or reachable. The daemon's failed-sync path attempts `NodeDriver::reopen`
and falls back to `restart` if reopening fails. Here reopening preserves the fake's persisted
operations, objects, staging and accepted base, and restarts `NodeCore`; there are no jj/gix
handles or translation caches to reopen. A hub's ordinary error keeps the same adapter,
as `HubService` does, and fails the requesting node's sync. The error reply's bytes are
abstracted away. Recovery is not a claim that retrying the same node core is sufficient.
Every fake process restart also clears its armed crash injection and the interrupted
receipt's object-loss latch. Those are transient test controls, not retained store data.
`storage_boundaries::an_interrupted_fetch_does_not_discard_a_later_object_reply` fails a
fetch after its operations were staged, then receives the objects separately. Keeping the
old latch discards that new reply and fails the oracle's `recvObjs` comparison; the test
keeps the oracle throughout recovery.
Once faults stop, ordinary honest exchanges must converge with every created operation
retained; representable cases also keep the oracle's liveness checks during that suffix.

Limits: this tests errors between logical storage effects, not real storage implementations.
The abstract attachments contain complete operations; view-delta imports whose base is
missing (which `HubAdapter::store_ops` can leave incomplete without returning an error) are
outside this projection, as are partial pushed/accepted bookkeeping files. It does not model a
torn head log, a partial accepted-base id, `set_head`'s append or accepted-index side effects
before an error, batched/asynchronous realization writes, ref export or working-copy repair inside
a composite advance. `set_head` is injected only before any such effect; no atomic rollback or
successful full head change on error is invented. Real adapter fault injection is still needed for
those boundaries. It adds no hub durability or power-cut recovery guarantee.

`translation::failed_realization_writes_forget_the_batch` covers a native asynchronous-write
boundary outside that logical projection. A filesystem obstacle makes the pinned jj simple op
store fail to persist one view or operation while earlier and dependent later operations succeed.
The test checks the error, both directions of the discarded batch mappings, no translation-file
append, unchanged published heads, and closed history after same-handle retry or reopening. A
healthy repository copy supplies exact realization identities; a direct store walk independently
checks closure and retention. The fourth hinted view also goes through recovery after a partially
realized batch. These are runtime obligations of the translation layer, not new model transitions
or panic, append-error, or durability guarantees. [testing.md](testing.md#example-tests) describes
the fixture and fault.

## How Rust events map to model actions

A "test rule" is something the test's state machine does to the system, not something the
core does.

| Rust core event | Model actions |
| --- | --- |
| A machine runs a `jj` command (test rule) | `userOp` |
| `NodeCore` asks the repo to merge heads | `merge` |
| `NodeCore` sends `Fetch { base, haves }`, on every poll | `fetchAll` |
| `NodeCore` sends `GetObjects { for_ops: S, haves: H, .. }` | `fetchObjs` with `objs(S) \ H` |
| `NodeCore` sends `Push { ops: S, objects: O, expected, new, .. }` | `pushAll` |
| `NodeCore` accepts a head-carrying reply | `learn`; a stale one it ignores maps to nothing |
| `NodeCore` takes in a `Fetched` reply | `learn` if its head is newer, then `recvOps` and `recvObjs` if it stages the operations; the states are compared after the last |
| `NodeCore` stages an `Objects` reply | `recvObjs` |
| `NodeCore` realizes or advances | `realize` / `advance` |
| The hub handles `Fetch` | `hubFetch` |
| The hub handles `GetObjects { for_ops: S, haves: H, .. }` | `hubGetObjs` with `objs(S) \ H` |
| The hub handles `Push` | `hubPushIdem`, `hubPushAccept`, `hubPushReject`, or `hubPushIncomplete` |
| A node restarts | `loseKnown` (its staged files survive; `known` does not) |
| A node restarts while taking in a `Fetched` reply, after staging its operations and before staging its objects (test rule) | `learn` if its head is newer, `recvOps`, then `loseKnown` |
| The hub restarts | `crashHub` |
| The hub goes back (test rule) | `hubRegress` |
| The hub loses data outside its current closure (test rule) | `hubForget` preserves operation bodies needed by retained history; historical-only objects may be lost. A requested rollback to an incomplete target takes a separately identified environment-chosen remake |
| The hive is made again, empty, as `HubDir::remake` makes one whose store is corrupt (test rule) | `hubRegress` to 0, then `hubForget` keeping only the root: `State.remake` (`exec_remake`), a run of the extended model (`remake_reachable`) |
| A reply to the node's own request that says the hub went back (`NodeCore::handle_reply`) | `loseKnown`, then `learn` if the reply's `seq` is above 0 (at 0, the restarted node already knows `(0, root)`) |

The Rust hub decides how to answer a `Push`, and the test sends whichever of `hubPushIdem`,
`hubPushAccept`, `hubPushReject`, or `hubPushIncomplete` it chose. The oracle checks that
choice's guard, so a hub that accepts a `Push` the model would reject is caught, and so is
one that rejects a `Push` the model says is incomplete. The Rust core sends only the merged
requests (`Push`, `Fetch`); the finer-grained actions remain in the model and the oracle.

The test's objects have no structure, so the test's hub ignores `closure(base)` and leaves
out exactly what the haves name, as the model's `hubFetch` does; a node's haves there are
every object it holds.

## A repository advance that also merges

The core harness's `FakeRepo::advance` updates heads only. `NodeRepo::advance` can also
merge concurrent heads and repair the working copy. These are composite transitions, not one
`SyncStep.advance`, and need native checks beyond the core harness.

`Safety.lean`'s `advance_merge_parents` identifies the intermediate heads as the incoming
`known.head` plus every old head not below it. `advance_merge_refines` proves that, when
concurrent heads remain, advancing then merging that exact set is a reachable two-step run:
`SyncStep.advance` then `EnvStep.merge`. It retains all local operations, adds one canonical
operation and leaves the hub and network unchanged. The returned local id represents the
incoming operation, not the merge.

In a colocated repository, the git lock excludes a jj command's publication while musubi
exports the realization and merge and publishes only the merge. In a non-colocated repository,
working-copy cleanup can perform the merge. A graph read after `advance` returns includes that
cleanup, so it cannot establish the internal publication order; that relies on the lock/export
code argument.

The native checks read raw heads before any subsequent jj command or head-merging helper:

| Test | Correspondence checked |
| --- | --- |
| `translation::advance_with_concurrent_heads_refines_advance_then_merge` | Real colocated and non-colocated histories agree with the oracle's advance then merge, including exact parents, returned realization, retention and exported bookmarks. |
| `abandoning_a_root_child_beside_a_merge_converges` | Concurrently abandoning a root child and merging it with another commit converges. |

In an ordinary advance, a later unpublished merge can fail after preflight succeeds. The
colocated path then publishes the advanced head set, and working-copy cleanup tries the normal
merge. Cleanup can also fail, returning an error after publication; this is not an atomic
rollback.
`node::realize::advance_tests::late_merge_store_errors_preserve_heads_and_recover` injects
real op-store permission errors at these later writes. It checks successful fallback,
failed fallback and non-colocated cleanup failure, with every old operation and the incoming
realization still reachable. Reopening and retrying must converge. A rebased bookmark must
also be exported, so a later jj git import neither creates an operation nor reverts it.

This Unix regression skips with a reason when mode bits cannot deny a write. It does not
inject view-write or read failures. The oracle's
two-step proof does not cover these intermediate store effects. A working-copy repair that
creates an operation is another operation-creating action.

`node::realize::concurrent_tests` runs real `jj` commands inside `advance` and `merge_heads`,
interposing only at the op stores' edge to run a command at a chosen point, and checks what a
user would see afterwards; none of them counts how often the code reads the op heads.

| Test | What it checks |
| --- | --- |
| `a_command_finishing_before_publication_is_merged_and_exported` | A command that finishes after the realization was prepared, or while it is, is merged with it at publication, not left as a second op head: the first op head `advance` publishes already has the command's operation behind it, and afterwards its bookmark move and the received work are in the one head, `.git` agrees, a later `jj status` or `jj git import` moves nothing back, and the workspaces `a` and `b` keep their commits. Fails if `advance` publishes without comparing the op heads under the locks with those it prepared for, or without merging with the heads concurrent with it. |
| `a_workspace_with_a_slash_added_meanwhile_stops_advance` | A workspace the user names `alpha/c` as alpha's workspace `c` arrives stops `advance` before it publishes anything, whether the user added it before the realization was prepared or after; renamed `c`, it keeps its commit, as `a` and `b` do, and alpha's shows as `alpha/c`. Fails if realizing (`realize_pending`), or publishing a realization prepared before the workspace was added (`current_realization`), doesn't refuse while there is one (`refuse_slashed_workspaces`). |
| `merge_heads_exports_when_a_second_head_arrives` | A head that arrives while `merge_heads` looks at the op heads is merged under the Git export lock, and the bookmark the merge rebases is moved in `.git` as in jj's import record, as when the head was there at the start. |
| `advance_exports_the_merge_before_publishing_it` | Every bookmark of the op head `advance` publishes is in `.git` when the head goes in. |
| `publication_interrupted_before_the_old_heads_go_loses_nothing` | In a colocated repository, with taking out an old op head refused, as a crash before it would, the new head is beside the old and no operation is lost; realization resumed after a restart leaves one head with everything and exports the merge. This relies on jj's op-heads store putting a head in before taking any out. |

Mutation checks distinguish these obligations: returning the unpublished merge error,
replacing concurrent heads without a merge, suppressing cleanup errors, skipping cleanup's
ref export, or returning the merge id instead of the incoming id each fails the late-error
regression. A wrong dedup comparison needs the ordinary advance test, because forced fallback
can mask it; a wrong merge-input guard needs the prepared-survivor case, where it produces
three physical parents instead of two. These are checks of specific defects, not exhaustive
coverage of the adapter.

`noFeedback` says a modeled sync step, realization included, leaves the operation universe
unchanged. jj's merge of concurrent work is an `EnvStep.merge`, whether a jj command or
musubi invokes it, and is published normally. Once converged, no concurrent set remains to
merge (`converged_quiescent`), so realization causes no echo.

## Liveness

`formal/Musubi/Liveness.lean` proves that once users stop, nodes following the policy
(`PStep`) converge: a lexicographic measure falls on every policy step, and some step is
enabled until every node is at the hub's head. `Regress.lean` proves the same of a hub that
has gone back, with the policy `PStepR` and the measure `rmeasure`. The policy there takes
single steps; the Rust core sends merged requests instead. `Merged.lean` shows that the
merged `Push` and `Fetch` reach states that agree with policy steps on everything the measure
reads, provided a `Push` uploads `upOps` and `upObjs`: `anc*(new) \ anc*(known.head)` and the
objects of `closure(new) \ closure(known.head)`, both for a hub that has never gone back,
against `PStep`, and for one that may have, against `PStepR` and `rmeasure`
(`pushAcceptR_merged`, `fetchR_merged` and the rest; `fetchR_current` for a `Fetch` by a
node that knows the hub's head and `seq` already, for which the policy has no step).

`formal/Musubi/Exec.lean` computes these on the oracle's state: `measureE`, `rmeasureE`,
`convergedE`, `upOpsL` and `upObjsL`, proved equal to `measure`, `rmeasure`, `Converged`,
`upOps` and `upObjs` of the abstracted state (`measureE_eq`, `rmeasureE_eq`,
`convergedE_iff`, `mem_upOpsL`, `mem_upObjsL`, in `ExecSound.lean`). The oracle answers with
them:

```json
{"op": "measure"}
{"ok": true, "measure": [1, 0, 0, 0, 0], "rmeasure": [1, 0, 0, 0, 0, 0], "converged": false}
{"op": "upload", "node": 0, "new": 1}
{"ok": true, "ops": [1], "objs": [10]}
```

`measure` is `(dirty nodes, Σ staleness, Σ missing ops, Σ pending advances, Σ pending
merges)`; `rmeasure` is `(nodes not good, inconsistent nodes, Σ staleness of consistent nodes,
Σ missing ops, Σ pending advances, Σ pending merges)`. Both compare lexicographically;
[formal/README.md](../../formal/README.md) defines their terms.

The conformance test checks:

- Every `Push` the policy sends (not one the test's `rogue_push` rule makes) carries exactly
  `upOps` and `upObjs`.
- `World::quiesce`, which stops users and runs every node's policy over a reliable network,
  asks for the measures after each exchange: a node's `Fetch` and the reply, or one policy
  step and the replies to what it sent. An exchange that changes the node's operations,
  heads or `known` must make the measure fall, and any other must leave it where it was or
  lower. `rmeasure` must do so in every case; `measure` only while the hub has never gone
  back, since its proof needs every state to be `Reachable`. Each node's turn starts with a
  `Fetch`, whose reply puts its `known` in the hub's current history before it realizes
  anything, as `PStepR` requires. A crash the test armed before quiescing, which happens
  when the node next stages a `Fetched` reply, is not a policy step, so the check starts
  afresh after it.
- Once the Rust side has converged, so has the oracle's state. The states already agree
  after every action, so this cross-checks `convergedE`.

The measure falling shows that the policy's steps are ones the termination proof covers, not
that each is a `PStep`. Hub-only work, such as storing a rejected push's upload, changes
nothing the measures read.

Two fixed runs check what random cases may reach only rarely. `regress_scenario_conformance`
drives the core through `RegressScenario.trace`, requires the actions it records to be that
trace, so that nodes A and B both merge heads `{1, 2}` (`duplicateMerge`), and then
quiesces. The trace restarts A and B before they fetch, so the test crashes them, rather
than have them restart on the hub's reply. `remade_hive_conformance` makes a hive again
under nodes that know heads it has lost, and requires each to take the hub's reply as
saying it went back (`NodeCore::handle_reply`) and fill it again.

`lost_acceptance_and_delayed_fetch_make_progress` checks the two split-exchange boundaries
against the core and the oracle: a push the hub accepts lowers `rmeasure` before its pusher
learns the new head, and a fetch reply delayed past another push, which teaches the node a
head that is no longer the hub's latest, still lowers it. `fetched_replies_mark_only_new_heads`
pins that an old `Fetched` reply carries data but doesn't mark its head accepted, by calling
`handle` directly. The driver's own replies use `handle_reply`, which can restart on a
rollback pair before learning it. The transport contract checks canceled calls, delayed
replies and duplicate completed replies (`replies_only_complete_the_matching_pending_call_once`
in `crates/musubi-transport/src/stream.rs` injects obsolete and duplicate frames into the
stream receiver). A still-pending reply may arrive after a hub remake.

## Running it

```sh
cargo nextest run -p musubi-core     # the property, conformance and false-reply tests
```

The conformance test runs `lake build oracle` first, so that the oracle matches the model;
it does nothing when the oracle is up to date. The oracle binary is
`formal/.lake/build/bin/oracle`. Setting `MUSUBI_ORACLE` to another binary skips the build,
as CI does with the one it has just built. `formal/test/run_smoke.sh` replays a fixed
two-node run through it.

The test makes 150 cases on CI and 50 elsewhere, where it would otherwise take most of
`just test`'s time (`hegel.toml`). `HEGEL_TEST_CASES` sets the number; `just mutants` sets
150.

## Evidence that the check has teeth

Deliberately broken versions of the core, each caught:

| Change | Caught by |
| --- | --- |
| Hub accepts a `Push` without checking the closure is stored | invariants (HubClosed) and conformance |
| Hub accepts a `Push` without checking ancestry | invariants and conformance |
| Hub accepts a `Push` when `head ≠ expected` | invariants and conformance |
| Node realizes an operation before its parents | invariants and conformance |
| Node realizes an operation before its objects arrive | invariants and conformance |
| An old `Fetched` reply marks its head accepted | `fetched_replies_mark_only_new_heads`, checking the storage callback |
| Node learns a head whose `seq` equals the one it knows | conformance only: harmless, but not a model step |
| Node's `Push` uploads every operation since the root, not since `known.head` | conformance only: not `upOps` |
| Node with two heads pushes one of them before merging | conformance only: the push raises the other nodes' staleness, and the measure rises; the run still converges |
| Node that believes a head at the largest sequence number doesn't start over when its own request's reply says otherwise | `nodes_recover_from_false_replies`, and rarely `nodes_recover_from_wrong_replies` with real repositories: no honest hub gets there, and the node never converges |
| Hub ignores a `set_head` error and reports acceptance | `storage_boundaries::every_storage_boundary_recovers`: a successful reply/publication must match the actual store; the infallible tests cannot enter this boundary |
| `settle` suppresses a background write error after joining the batch | `translation::failed_realization_writes_forget_the_batch`: the selected write must return `OpStoreError::WriteObject` for the blocked destination |
| `settle` forgets only unreadable batch entries, retaining a written child of the missing parent | The same test: every batch entry must lose both mapping directions, including the successful child |
| `settle` appends batch translations before returning its write error | The same test: the translation file must remain byte-for-byte unchanged after the failure |

The realization mutants distinguish write-error propagation, complete batch-map invalidation
and translation-file publication. Generated `forget` mutants fail the mapping assertions;
replacing all of `settle` with `Ok(())` fails during setup, so the separate hand-written
error-suppression mutant is needed to establish sensitivity at the failed write. This does
not independently test each cache reset or the writer-panic branch.

For ignored `set_head` errors, the fixed storage-boundary sweep is stronger than relying on
random frequency: an initial 50-case run missed that defect, whereas the sweep reaches it
deterministically. [Bounded verification](bounded-verification.md) separately exhausts a
small retry/storage adapter through the production handler.

"Invariants" means `protocol_invariants`, which checks safety directly on Rust state without the
oracle. Fixed tests cover recovery paths that honest generated policy reaches rarely or never.
`just mutants` runs cargo-mutants over `hub.rs` and `node.rs`; the property and conformance tests
should kill every mutant it makes.

The selected native campaigns in [testing.md](testing.md#native-adapter-campaigns) also
exercise assumptions outside the abstract core. These deliberate changes are checked at the
production boundary, rather than by changing a protocol fake:

| Change | Caught by |
| --- | --- |
| Peer timeout becomes a generic error | [Stream failure classification][stream-failures] |
| Native ancestry is constant or inverted | [Native ancestry law][native-ancestry] |
| Every error permanently pauses a copy | [Retryable-error classification][native-recovery] |
| No error permanently pauses a copy | [Permanent-error classification][native-recovery] |
| An import, on either backend, skips its check that the objects wanted are all present | `translation::an_import_missing_wanted_commits_fails` |

[stream-failures]: ../../crates/musubi-transport/src/stream.rs
[native-ancestry]: ../../crates/musubi-sync/tests/races/adapter.rs
[native-recovery]: ../../crates/musubi-sync/src/node/tests.rs

## SSH process boundary

The SSH supervisor's process and pipe behavior is outside the Lean transport assumptions.
The Unix tests in `crates/musubi/src/ssh/supervisor_tests.rs` run controlled local children
through the shipping supervisor, stderr reader and output wrapper. The reconnection test uses
the real stream client and relay. Tests inject wakes; they do not cover real sleep detection,
ssh authentication, remote hosts or daemon sync scheduling.

The checks cover active-child termination and reaping, explanations waiting for the reason a
connection let go didn't connect, deadlines for inherited stderr, bounded stderr retention,
wake/failure ordering, greeting-based health reset and reconnection notification. The
`waking_during_*` regressions also cover wakes during the EOF grace and inherited-stderr waits,
including health updates across runtime threads.

Negative controls establish sensitivity at these boundaries. Removing only the explicit
post-kill wait survived because Tokio's child-drop cleanup reaped the child in that run;
leaking ownership too fails the `waitpid` assertion. The surviving control does not prove
every scheduling of the shortened path reaps before return. All ten selected function-replacement
mutants were caught, with no timeout or compile failure; this was a selected campaign, not
exhaustive SSH mutation coverage. [Testing](testing.md#native-adapter-campaigns) describes how
to run targeted native campaigns.

## Upgrade process boundary

The upgrade worker's OS contracts are outside the protocol models. Unix tests in
`upgrade::process_tests` exercise the production worker, shell and file lock in disposable
processes. On 2026-11-03, each of these hand-written defects failed its named regression;
the source was restored after each run:

| Defect | Regression that fails |
| --- | --- |
| Drop the upgrade lock instead of passing it as the command's standard input | Lifetime |
| Leave `Tried.release` set when the upgrade lock is busy | Lifetime |
| On timeout, kill only the shell instead of its process group | Timeout |
| Keep the command in the daemon's process group | Timeout |
| Omit writing `upgrade-failed` after a nonzero command exit | Exit |
| Omit removing `upgrade-failed` when a retry takes the lock | Exit |

Lifetime is `an_upgrade_outlives_its_daemon_and_contention_can_retry`, timeout is
`timeout_stops_the_command_and_its_child_before_retry`, and exit is
`a_failed_command_is_reported_and_a_fresh_daemon_can_retry`.

The shell-only timeout is also the pre-fix regression: after the worker reported a timeout,
the installer's socket remained open and its inherited lock prevented retry. The fixed test
finishes in under a second locally. These checks require an ordinary foreground installer
that preserves standard input; they do not establish cleanup of detached processes or
Windows process trees.

A targeted generated campaign uses:

```sh
cargo mutants --in-place --no-config --package jj-musubi \
  --file crates/musubi/src/upgrade.rs \
  --re '(upgrade ->|wait|failure ->|failure_path|log_path|shell ->)' \
  --exclude-re 'replace != with == in consider_with_wait' \
  --test-tool nextest --timeout 40 -- -E 'test(/^upgrade::/)'
```

On 2026-11-03 this selected 17 mutants: 14 caught, three unviable, none surviving. The
unviable changes introduced an invalid `let` chain, `Command::default()`, or
`Instant * Duration`; none represents an executable defect. All six hand-written controls
above failed their tests as intended. Both campaigns restored the source before validation.

Run `--in-place` only in an isolated workspace. This selects the attempt gate, command,
wait, and failure-reporting code; it excludes the unrelated once-only notice about an unset
upgrade command. The CLI test covers the public entry point and actual daemon restart.

## Wire format

The oracle reads one JSON object per line on stdin and writes one per line on stdout. Every
request gets exactly one reply.

### Requests

```json
{"op": "reset", "nodes": 3}
{"op": "step", "action": <action>}
{"op": "measure"}
{"op": "upload", "node": 0, "new": 4}
```

`measure` and `upload` read the session's state and leave it as it was
([Liveness](#liveness)). The oracle also answers presence requests ([Presence](#presence)).

### Actions

Fields mirror the constructors of `EnvStep` and `SyncStep` in `formal/Musubi/Model.lean`.
`node` is a node index below `nodes`. Op and object ids are naturals. Sets are arrays,
compared as sets.

| `"kind"` | Fields | Model step |
| --- | --- | --- |
| `userOp` | `node`, `parent`, `objs` | `EnvStep.userOp`: the new op gets id `next` |
| `merge` | `node`, `parents`, `objs` | `EnvStep.merge`: `parents` must enumerate `heads` |
| `getHead` | `node` | `SyncStep.getHead` |
| `learn` | `node`, `headKind`, `seq`, `head` | `SyncStep.learn`: the `head` message must be in `net`, and `seq > known.seq` |
| `fetchOps` | `node`, `ops` | `SyncStep.fetchOps` |
| `fetchObjs` | `node`, `objs` | `SyncStep.fetchObjs` |
| `recvOps` | `node`, `ops` | `SyncStep.recvOps` |
| `recvObjs` | `node`, `objs` | `SyncStep.recvObjs` |
| `realize` | `node`, `opId` | `SyncStep.realize` |
| `advance` | `node` | `SyncStep.advance` |
| `uploadOps` | `node`, `ops` | `SyncStep.uploadOps` |
| `uploadObjs` | `node`, `objs` | `SyncStep.uploadObjs` |
| `push` | `node`, `expected`, `new` | `SyncStep.push` |
| `pushAll` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.pushAll`: the merged `Push` |
| `fetchAll` | `node`, `base`, `haves` | `SyncStep.fetchAll`: the merged `Fetch` |
| `crashNode` | `node` | `SyncStep.crashNode` |
| `loseKnown` | `node` | `SyncStep.loseKnown`: `known := (0, root)` |
| `loseVolatile` | `node` | `SyncStep.loseVolatile` |
| `hubGetHead` | `node` | `SyncStep.hubGetHead` |
| `hubPutOps` | `node`, `ops` | `SyncStep.hubPutOps` |
| `hubPutObjs` | `node`, `objs` | `SyncStep.hubPutObjs` |
| `hubGetOps` | `node`, `ops` | `SyncStep.hubGetOps` |
| `hubGetObjs` | `node`, `objs` | `SyncStep.hubGetObjs` |
| `casIdem` | `node`, `expected`, `new` | `SyncStep.casIdem` |
| `casAccept` | `node`, `expected`, `new` | `SyncStep.casAccept` |
| `casReject` | `node`, `expected`, `new` | `SyncStep.casReject` |
| `hubPushIdem` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushIdem` |
| `hubPushAccept` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushAccept` |
| `hubPushReject` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushReject` |
| `hubPushIncomplete` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushIncomplete` |
| `hubFetch` | `node`, `base`, `haves` | `SyncStep.hubFetch`: replies with a `head`, an `ops` and an `objs` message |
| `crashHub` | none | `SyncStep.crashHub` |
| `hubForget` | `ops`, `objs` | `SyncStep.hubForget` plus the retained-body guard: the kept subset closes the current head and preserves historical operation bodies, while historical-only objects may be lost |
| `hubRegress` | `seq` | `State.regress`: `seq ≤ hub.seq` and the target is closed; head and sequence return to that entry. Recovery from an incomplete target is an explicit environment-chosen remake |

`headKind` is one of `head`, `accepted`, `rejected`, `incomplete`, `notify`.

### Replies

```json
{"ok": true, "state": <state>}
{"ok": false, "error": "casAccept: closure of 7 not stored at hub (missing op 6)"}
```

A rejected action leaves the oracle's state unchanged. The error names the action and the
guard that failed, as `"<action>: <guard>"`.

Two consequences of the model that the Rust test implementations must match:

- `realize` adds an operation to `lops` and its objects to `lobj` but does not remove them
  from `sops` and `sobj`. Staging is only ever cleared by `loseVolatile`.
- `casAccept` adds an `accepted` reply for the sender and a `notify` message for every node
  below `nodes`, including the sender.

### State

```json
{
  "next": 5,
  "ops": [{"id": 1, "parents": [0], "objs": [10]}, ...],
  "hub": {"ops": [0, 1], "objs": [10], "head": 1, "seq": 1},
  "nodes": [
    {"lops": [0, 1], "lobj": [10], "heads": [1], "known": [1, 1], "sops": [], "sobj": []}
  ],
  "net": [
    {"msg": "getHead", "node": 0},
    {"msg": "putOps", "node": 0, "ops": [1]},
    {"msg": "putObjs", "node": 0, "objs": [10]},
    {"msg": "getOps", "node": 0, "ops": [1]},
    {"msg": "getObjs", "node": 0, "objs": [10]},
    {"msg": "cas", "node": 0, "expected": 0, "new": 1},
    {"msg": "head", "node": 0, "headKind": "accepted", "seq": 1, "head": 1},
    {"msg": "ops", "node": 0, "ops": [1]},
    {"msg": "objs", "node": 0, "objs": [10]},
    {"msg": "stored", "node": 0},
    {"msg": "push", "node": 0, "ops": [1], "objs": [10], "expected": 0, "new": 1},
    {"msg": "fetch", "node": 1, "base": 0, "haves": []}
  ]
}
```

Every array is sorted ascending. `net` is sorted by `(msg, node, ...)`. `ops` lists every
created operation except the root.

## Presence

`formal/Musubi/Presence.lean` proves which copies a hive shows when copies go away ([design.md,
"Copies that go away"](design.md#copies-that-go-away) defines copies, their work, and forgets).
musubi computes it with `Presence::merge` and `Presence::apply`
(`crates/musubi-jj/src/presence.rs`), from each operation's parents' presence alone. The chain has
three links:

1. **The incremental rule.** What `Presence` keeps for each copy present, its latest work
   that no forget saw (`UMax`), follows from the parents' alone as the Rust computes it
   (`umax_merge`, `umax_work`, `umax_forget`), and says whether the copy is present
   (`present_iff_umax`). `Presence` keeps each copy's latest `musubi.name` records too, through
   forgets, and the largest generation of its marks, its name records and its returns (work
   where it was absent just before): what a copy's name is (`Identity.NHist.NameIs`) and how
   long it has held it (`Identity.NHist.SinceIs`), on which naming depends ([Workspace
   names](#workspace-names)).
2. **Relational to executable.** `formal/Musubi/PresenceExec.lean` defines the rule on a
   finite history: `presentB` and `latestB`, proved to compute `Present` and `UMax`
   (`presentB_iff`, `mem_latestB`); `nameB`, proved to compute `NameIs` (`nameB_some`,
   `nameB_none`); and `sinceB`, with generations `genB` one above the largest parent's
   (`genB_mono`), proved to compute `SinceIs` and to have a value for every copy present
   (`sinceB_some`, `sinceB_present`). The oracle answers with them.
3. **Oracle to Rust.** The Hegel test `presence::conformance`, in
   `crates/musubi-jj/tests/it/presence.rs`, makes histories of up to 12 operations and 3
   copies, each operation work by one copy, which may record a name, or a forget of some, never
   both, as musubi makes them. It computes every operation's presence with `Presence::merge`
   and `apply`, and requires it to equal the oracle's, copy by copy, latest work, name and
   since included.

The test checks the rule, not where it is applied: that `canonical_view` publishes exactly
the present copies' workspaces, and that realizing keeps a forgotten copy's own, is for the
race catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

The oracle's presence request and reply:

```json
{"op": "presence", "ops": [{"parents": [], "work": 7, "forgets": []}, {"parents": [0], "work": 7, "forgets": [], "name": 3}, {"parents": [1], "work": null, "forgets": [7]}, {"parents": [2], "work": 7, "forgets": []}]}
{"ok": true, "presence": [[{"copy": 7, "latest": [0], "name": null, "since": 1}], [{"copy": 7, "latest": [1], "name": 3, "since": 2}], [], [{"copy": 7, "latest": [3], "name": 3, "since": 4}]]}
```

Operation `i` is the `i`th of `ops`, and its parents must come before it. `work` is the copy
the operation is work by, or `null`, and `forgets` the copies it forgets. `name`, which may be
left out, is the name the operation records for the copy whose work it is, as a number ordered
as the names it stands for, or `null`. The reply has, for each operation, the copies present
there, ascending, each with its latest work that no forget saw; its `name` there, `null` where
it has recorded none and its name is the one in its key; and its `since`, the largest
generation of its marks there, an operation with no parents being of generation 1. A presence
request leaves the oracle's session as it was.

```sh
cargo nextest run -p musubi-jj -E 'test(/^presence::/)'
```

`HEGEL_TEST_CASES` sets the number of histories, 300 by default: each takes the
oracle about a millisecond. Dropping the check that a parent whose history has a copy's work
keeps it, which lets a forget's merge bring the copy back, fails within a few histories.

## Per-machine refs

Join repair uses the same native fetch and selected-ref import as ordinary explicit fetches.
`Refs.TSlot.import_remote` and `import_record` establish that a selected upstream observation
sets the remote target and its Git record, independently of the previous target or physical
ref. `import_following` establishes that a tracked local bookmark equal to its remote follows
that observation; `import_L` keeps local differences subject to jj's merge. The existing
`RefsModel::import` oracle path checks this computation in `bookmarks_conform_to_refs_model`.
`joining_fetches_ambiguous_remote_bookmarks` checks the actual command, unavailable upstream,
retry, a fresh target outside both snapshots, and preservation of local work and files.
The stale copy holds an obsolete revision with the same change id and tree as its successor.
It also exercises restricted fetch filters, a remote name containing expression syntax, and
a non-colocated primary workspace whose secondary workspace is colocated. The native
`a_stalled_fetch_stops_its_git_descendant` test accepts a real HTTP Git request, advances the
deadline, and checks for EOF or a connection reset to establish that the network child stopped.
`interrupts_stop_the_fetch_and_still_work_afterwards` sends actual interrupts to a subprocess,
checking fetch cleanup and termination after the fetch runtime has ended.
`e2e_join_after_upstream_rewrite` reaches an ambiguous join before continuing the generated
walk and independent native replay. The model does not order independently cached observations
by commit or observation timestamps, or assume an entire failed fetch had no effects.

In a colocated repository, each view records what jj last saw in this machine's `.git` (`git_refs`
and the `git` remote, such as `x@git`). With jj 0.47, an ordinary command imports a ref
only when its physical Git value differs from `git_refs`; an unchanged ref is an identity step,
including a conflicted remote bookmark. An explicit fetch still imports its returned target even
when the physical ref has not moved. The conformance harness uses the executable model's import
for those actual imports and checks every resulting slot and invariant, including identity steps.
musubi keeps the record per-machine ([design.md, "Per-machine state in a replicated
view"](design.md#per-machine-state-in-a-replicated-view)).

`formal/Musubi/Refs.lean` proves properties of the import and export functions, assuming jj's ref
merge obeys three laws (`RefAlg`). Its result that importing a conflicted remote bookmark's
expected value resolves the conflict applies when that import runs; an ordinary command on
jj 0.47 leaves an unchanged physical ref alone. The restore and realization checks still use the
model's slot functions ([formal/README.md, "Per-machine refs
(`Refs.lean`)"](../../formal/README.md#per-machine-refs-refslean) lists the theorems).

The model's functions are executable already, over any `RefAlg`, but the tests' targets are
jj's, merged by jj-lib, which the oracle can't run. So `formal/Musubi/RefsExec.lean` runs them
on targets a test numbers, `0` for none, with `tableAlg` as the `RefAlg`: the three laws, which
so hold by construction, and otherwise jj's merge as a table the test sends with each request,
with which targets are resolved and writable and the terms of each conflict. Every merge the
slot functions make is of their arguments' targets, so the test, in
`crates/musubi-jj/tests/support/refs_model.rs` (`RefsModel`), sends jj-lib's
`merge_ref_targets` of every triple of a request's targets that the laws don't settle. A target
the request needed and wasn't sent comes back as `4294967295`, which the test refuses. Equal
targets have equal numbers, so the model compares targets as jj does. The chain has three
links:

1. **The laws.** `ref_laws::merge_ref_targets_obeys_ref_alg`, in
   `crates/musubi-jj/tests/it/ref_laws.rs`, checks `merge a b b = a`, `merge b b c = c` and
   `merge a b a = a` for jj-lib's `merge_ref_targets` on 300 triples of synthetic targets:
   absent, one commit id (the root among them), or a conflict of three or five terms, any of
   them absent. jj resolves these before looking at commits (`trivial_merge`), so the test
   needs only an empty repository's index, with no commit graph to build. A failure means a
   jj upgrade changed that. `ref_laws::a_fetch_can_resolve_a_conflict_to_neither_side` pins a
   merge a run Hegel found: `base - one + absent`, merged with `one` against `base`, resolves
   to absence, which neither side had.
2. **The steps.** `refs::bookmarks_conform_to_refs_model`, in
   `crates/musubi-sync/tests/races/refs.rs`, is a Hegel state machine over two colocated
   repositories synced through an in-process hub, as in the race catalogue. It follows a
   local bookmark `x`, which git moves; a local bookmark `y`, which git doesn't; `y@origin`,
   which `y` tracks and which git and fetches move; and a tag `t`, which git moves, whose slot
   is a local bookmark's (`t`, `t@git`, `refs/tags/t`). Beside the real machine it keeps the
   model's `Machine` for each of the four, its slot a `TSlot` with the remote ref's tracking
   state, and steps them as each real action does, each of the model's functions asked of the
   oracle:

   | Real action | Model steps |
   | --- | --- |
   | `git update-ref` moves or deletes `refs/heads/x`, `refs/tags/t` or `refs/remotes/origin/y` | `gitMove` |
   | A `jj` command moves `x`, `y` or `t` (`jj bookmark set`, `jj bookmark delete`, `jj tag set`, `jj tag delete`), or changes nothing (`jj status`) | `jjImport` of each ref whose physical value differs from `git_refs`; `jjExport` of every ref even when importing changed nothing; then, if the command moves a bookmark, `set` and `jjExport` of every ref |
   | `y` moves in `origin`, and `jj git fetch` fetches it | as a `jj` command, whose change is `RStep.fetch` |
   | A `jj` command at the operation before the latest action (`--at-op`) moves `x` or `y`, and `jj status` follows | on the older operation's slots, `set` and `jjExport` of every ref (it imports nothing); then `TSlot.merge` of the head with them against the older operation's, in the order of the merge operation's parents, then as a `jj` command that changes nothing |
   | `jj undo`, or `jj op restore` to the operation before the latest action or to the one both machines last synced at | as a `jj` command that changes nothing; then, if it restored an operation, which its description names, every ref's slot but `K` from that operation's view (`restoreLocal`, `restoreRemote`), the expected value the head's (`restoreC`), and `jjExport` of every ref |
   | The other machine moves `x` or `t` or fetches `y`, and both sync, with `refs/heads/x.lock` held here or not | `LStep.advance` of `x`, `y` and `t` and `CStep.advance` of `y@origin`, with this machine's expected value, then `jjExport` of every ref, except where the lock makes `x`'s update fail, then `exportConflicted` of `y@origin`; nothing if there was nothing to realize |
   | The other machine moves `x` or `t` or fetches `y` before it has this machine's latest operations, merges them with its own as it syncs, and this machine syncs | the other's operation realized from the slots both last synced at, and `realizeMerge` of it with the head, against those slots, in the order of the merge's parents, which is `TSlot.merge`; then the exports, as above. Two fetches that moved `y@origin` to different values merge to a conflict, whose expected value is its side; a conflict from one parent keeps that parent's, and a merge that resolves it has the remote bookmark itself |
   | Either of the last two, with a `jj` command here that moves `x`, `y` or `t` or fetches `y` after the other machine's operations and before this machine syncs | the command, as above; then the other's operation realized as above from this machine's slots before the command, and `jjExport` of every ref, against `.git` as the command left it, then `exportConflictedBeside` of `y@origin` against the command's record; then `TSlot.merge` of the two against the slots before the command, in the order of the merge's parents, and the exports, as above, with the merge's expected value: `LStep.beside` and `CStep.beside`. The other machine then syncs |

   The mapping follows what jj does. jj imports `x@git`, `y@git` and `y@origin` in that
   order, and the two refs of `y` share the bookmark, so an import of one that sets the
   bookmark is a `set` of the other. An integrated command exports after its import phase
   even when importing changed nothing. This completes pending exports after native op-head
   merges, and exports that failed earlier, as where git's lock on a ref was held; the
   command's own transaction still exports only if it changes the view.
   `an_unchanged_import_exports_a_bookmark_selected_by_a_merge` pins this jj 0.47 behavior
   with concurrent fetches followed by a bookmark command at an older operation, and
   `a_restore_first_exports_what_a_lock_held_back` with a realization whose export git's lock
   refused, followed by `jj op restore`.

   After every action the test requires, for each ref, the bookmark, the remote bookmark
   and its tracking state, its `git_refs` entry and the git ref to be the model's, `LInv`
   (`CInv` for `y@origin`) to hold, and the repository to have one op head. A restore that
   isn't `Restorable` may leave a record behind `.git` until the next import, which only it
   may (the ghost `restored`). The test also checks that the other machine's command left
   its bookmarks and tag as the model says, and that both `.git`s keep the same expected
   value for a conflicted `y@origin`. `undo_of_an_unexportable_bookmark_keeps_it` shows that
   a restored root bookmark stays there through an ordinary command, since `git_refs`
   still matches `.git`. `restore_of_a_conflicted_remote_bookmark_waits_for_a_fetch` checks
   that a restored remote-bookmark conflict survives ordinary commands and resolves after
   an explicit fetch whose physical ref is unchanged. `realization_beside_a_fetch_keeps_the_fetch`
   checks that a concurrent fetch wins the merge without musubi overwriting its physical ref.
   `realization_beside_a_fetch_here_keeps_the_fetch` is the same on this machine, against the
   model (`beside_keeps_fetch`): the other machine merges its own operation with this one's
   restore of a conflict, keeping it, while this machine fetches a term of it.
   `a_pending_git_move_does_not_change_the_other_machines_import_record` checks that the
   other machine's next command imports against its own record. A pending git move can leave
   this machine's record behind while the other machine has exported the shared conflict.
   The harness checks the other machine's shared fields before its command, then uses its
   own slots and physical refs as inputs to the oracle's import, command and export steps.
   It compares every resulting slot and physical ref, including the unchanged-ref case.
   `a_resolved_merge_is_its_own_expected_value` checks the test's expected-value helper
   directly, without a repository or oracle: a resolved merge, absent included, has its own
   expected value even if neither parent had it, and never asks for a conflict side.

   musubi's *shortcut* for merging per-machine fields (`PerMachine::merged_trivially`) takes
   the side that changed, where at most one did; otherwise, or where a side has a tracked
   remote ref with no target, it leaves the merge to jj. In the other machine's merge, that
   machine's own side always has the per-machine fields both machines last synced at, so the
   state machine reaches the shortcut, or jj's merge where a tracked `x@git` with no target is
   involved, but never a merge where both sides changed. The merges' test, next, covers that.
3. **The merges.** `node::view::tests::merges_conform_to_refs_model`, in
   `crates/musubi-jj/src/node/view.rs`, writes three operations whose views give a bookmark
   `x`, `x@git` and its tracking state, and `git_refs`, drawn from a small real repository,
   including views musubi's realization makes and jj doesn't, and merges them with jj's own
   merge, as `merged_by_jj` does. It requires jj's merge to be the model's `TSlot.merge`, as the
   oracle computes it,
   and the shortcut, wherever it applies, to be jj's (`shortcut_agrees`). Beside it are
   tests of the two shapes of #56, where an unguarded shortcut disagrees with jj, and a
   criss-cross merge, where musubi must merge against the heads' closest common ancestors
   merged, as jj does, not the first of them (`firstBase_reverts`). That test's commits are
   beside each other, since jj resolves such a conflict where they are in a line.
   In `node::realize::tests`,
   `forgetting_a_workspace_merges_its_git_head_as_jj` checks that jj removes a workspace's
   Git HEAD even if all parents' per-machine records agree. Workspace cleanup is outside
   the refs model; the caller leaves changes in workspace names to jj.

The tests have teeth: a model whose exports refuse an update to the value git already has
fails `refs`, and merging per-machine fields against the first of several closest common
ancestors (`firstBase_reverts`) fails `criss_cross_merges_per_machine_fields_as_jj`.

What the test relies on of jj, and what it leaves out:

- **An update to the value git already has succeeds.** jj's export counts an update of a
  ref a success if `.git` already has the new value (`move_git_ref`, `create_git_ref`,
  `delete_git_ref`), and records it, though `.git` didn't have `git_refs`'s value. That
  happens when git moves `refs/heads/x` to a commit and musubi then realizes another
  machine's move of `x` there. The model's `exportLocal` and `exportRemote` do the same.
- **Tracking.** The model merges into a bookmark as from a tracked remote bookmark. jj keeps
  a tracked remote bookmark with no target only while its bookmark exists, so once git or a
  fetch deletes `refs/remotes/origin/y` and the import deletes `y` with it, jj forgets that
  `y` tracked it. When `y@origin` comes back, jj imports it untracked and leaves `y` absent,
  where the model sets `y`. The test has both machines track `y` automatically
  (`remotes.origin.auto-track-bookmarks`), as the model assumes; without that, a deletion
  and a fetch fail it.
- **Creating a bookmark tracks it.** `jj bookmark set`, creating `y`, tracks `y@origin`,
  which `remotes.origin.auto-track-bookmarks` covers, even with no target there
  (`TSlot.track`). It changes no target, so only comparing tracking states shows it.
- **Merges.** jj merges each remote ref's target and tracking state separately, and drops a
  tracked remote ref with no target when its bookmark goes, so a merge can leave `x@git`
  untracked. So the shortcut leaves to jj any merge where a side has such a ref; without
  that guard it would disagree with jj (#56, `shortcutUnguarded_keeps_absent`,
  `shortcutUnguarded_untracks`). Where the heads have several closest common ancestors,
  musubi merges the per-machine fields against those ancestors merged, as jj does. Against
  only the first, the record could be left a conflict that the export can't correct, and the
  next import would move the bookmark with no `git` command having run (`firstBase_reverts`).
- **Concurrent records.** Two heads that each import or export can merge to a record that
  doesn't match `.git`, and the next import moves the bookmark
  (`concurrent_records_revert`). jj does this too, with or without musubi, and the test
  expects it.
- **Restores.** `jj undo` and `jj op restore` restore `x@git` with the bookmark but keep
  `git_refs`. Where the restored bookmark can't be exported, an ordinary command leaves it
  alone if the physical ref still matches `git_refs`. The model's unconditional import
  counterexample `restore_reverts` is not an ordinary jj command in that state. The native
  regression is `undo_of_an_unexportable_bookmark_keeps_it`. Before restoring, `jj undo` and
  `jj op restore` import and export as any integrated command does, so a bookmark whose export
  failed earlier, as when git's lock on its ref was held, reaches `.git` and `git_refs` first,
  and stays there if the restored bookmark can't be exported, as Hegel found
  (`a_restore_first_exports_what_a_lock_held_back`). Where that import or export makes an
  operation, `jj undo` undoes it, so the test reads what a restore restored from its
  description. Otherwise jj refuses to undo a merge operation or a realization attributed to
  another machine's workspace.
- **Conflicted remote bookmarks.** musubi writes and records the expected value in `.git`:
  one conflict side after concurrent fetches, or the value from before a restore. Ordinary
  commands leave the conflict alone; an explicit fetch imports its result even if the
  physical ref is unchanged. The slot model takes the expected value as given with each
  operation. This test computes it from the parents and checks both machines' physical refs;
  the history conformance below also checks the shipping computation at join boundaries.
- **Not covered.** The state machine makes no merges of more than two heads and no
  criss-cross merges. It runs a command beside a realization only while every local
  bookmark's record agrees with itself, as `LStep.beside` assumes of the operation the
  realization descends from (`LStep.agrees`): a restore can leave it otherwise. Hegel seldom
  reaches a realization that keeps a conflicted `y@origin` beside a fetch of one of its
  terms, where musubi's export skips the ref, so
  `realization_beside_a_fetch_here_keeps_the_fetch` goes there. The other machine's
  realizations beside its own operations, when it merges this machine's, aren't modeled,
  since only this machine's refs are; the test checks them through that machine's `.git`
  for a conflicted `y@origin`, and `realization_beside_a_fetch_keeps_the_fetch` through its
  next command. Since musubi publishes only the merge, the test can't reach the moment between
  a realization's publication and its merge that musubi once left;
  `beside_published_apart_disagrees` shows what a `jj` command did there. The state machine
  locks no remote ref, since `CStep.advance` admits only exports that can succeed (a failed
  one ends as `remote_reset_without_export` says). The realization
  keeps a tracked absent `x@git` that jj would drop when the canonical operation deletes `x`
  (`realize_not_WF`); the test's model does the same, so the test checks the code as it is.

The oracle's request names one of the model's functions, `fn`, with its arguments, slots
`{"L", "R", "K", "tr"}` and targets, and the table:

```json
{"op": "refs", "fn": "merge", "table": {"resolved": [0, 1, 2, 3], "writable": [1, 2, 3], "terms": [{"conflict": 4, "terms": [1, 2, 3]}], "merges": [[2, 1, 3, 4]]}, "b": {"L": 1, "R": 1, "K": 1, "tr": true}, "v": {"L": 2, "R": 1, "K": 1, "tr": true}, "w": {"L": 3, "R": 1, "K": 1, "tr": true}}
{"ok": true, "slot": {"K": 1, "L": 4, "R": 1, "tr": true}}
```

The functions are `set` (`l`), `track`, `import` (`g`, a new remote ref tracked by default),
which replies whether jj's import `sets` the bookmark too (`TSlot.importSets`, which
`import_L` ties to the merge into the bookmark), `merge` (`b`, `v`, `w`), `exportLocal` and
`exportRemote` (`g`), `exportConflicted` (`g`, `e`), which reply with a slot and `.git`'s value
`g` too, and `linv` (`g`, `moved`), `cinv` (`g`, `moved`, `e`), `restorable` and
`restorableRemote` (`o`), which reply whether they `holds`. Each takes the slot `s` unless it
says otherwise.

```sh
cargo nextest run -p musubi-jj -E 'test(/^ref_laws::/) | test(/view::tests/)'
cargo nextest run -p musubi-sync -E 'test(/^refs::/)'
```

The state machine makes 12 cases of up to 10 actions, about 4 seconds on 32 cores;
`HEGEL_TEST_CASES` sets the number. Each case runs real `jj`, `git` and syncs, so
shrinking a failure takes minutes; `.config/nextest.toml` gives the test time for it, and
starts it early, as the longest test after the protocol's conformance test.

## Moving op heads

[design.md, "Moving op heads"](design.md#moving-op-heads) says how musubi replaces the op heads it
read earlier, under jj's op-heads lock and only while they are still those it read, so that no
operation a jj command wrote is lost. Two Lean files model it
([formal/README.md](../../formal/README.md#moving-op-heads-opheadslean-opheadsracelean)):

- `OpHeads.lean` has what musubi decides, as a function of the op heads: `same` (the check before
  a move). It computes, so the oracle answers from it.
  `crates/musubi-jj/src/node/heads/plan.rs` has the same function in Rust, with no jj and no
  files.
- `OpHeadsRace.lean` has the op heads among the actors that change them, and its theorems.

**What is checked.** `same_conformance` in `heads_conformance.rs` runs `plan.rs` and the model on
two random lists of operations and compares what they answer.

```json
{"op": "opHeads", "call": "same", "a": [0, 1], "b": [1, 0]}
{"ok": true, "same": true}
```

**What the code is checked to do, by steps of the race model.** The model's steps are what jj and
musubi do to the op heads. musubi's writes are one file system call each. A landing is one step,
though jj makes it with two calls, an add and a removal: a read of the op heads between them is
not a state of the model.

| In the model | In the code |
| --- | --- |
| `cmdLoad`, `cmdLoadAt`, `cmdPublish`, `cmdMerge` | A jj command loads the one op head, or any operation run `--at-op`, publishes its operation on it under the lock, or merges several op heads under the lock |
| `locklessBegin`, `land` | `jj op abandon` writes its rewrite of an op head, and later adds it and removes the head, with no lock; `jj op integrate` the same for an operation on parents it names |
| `mkOp`, `plan` | `replace_heads`'s caller writes the operations it will put in, and reads the op heads |
| `lock`, `check` | `lock_heads`, then `same(local_heads, read)`: otherwise it moves nothing |
| `write`, `written`, `release` | The `update_op_heads` calls: each new head in, then the old ones out; then the lock goes |

What the model takes from `heads.rs`, and the conformance test checks, is `same`. The rest, that
the code does these steps in this order, holding the lock as it says, is the reading of
`heads.rs`, and the tests of [races.md](races.md) and the schedule search of
[testing.md](testing.md#search-and-replay-operation-head-schedules) run it: `replace_heads` takes
the lock, checks, and writes the new heads before it removes the old.

**What is proved.** The theorems are listed in
[formal/README.md](../../formal/README.md#moving-op-heads-opheadslean-opheadsracelean): the lock
and the check keep every command out of a move (`check_no_event`, `locked_blocks_commands`), so
that a move takes out only op heads it read and no operation a command wrote is among them.
`Trace.landing_before_the_lock` is a landing the check turns the move away for, and
`Trace.landing_during_the_move` one the move leaves in place.

**What jj is assumed to do**, pinned against jj by `heads_laws.rs`, as `ref_laws` pins the ref
laws: `jj op abandon` takes no lock (`jj_op_abandon_takes_no_lock`); `jj op integrate` adds its
operation with no lock and merges under it
(`jj_op_integrate_lands_with_no_lock_and_merges_under_it`); a command publishes under the lock,
and merges several op heads under it (`a_jj_command_publishes_and_merges_under_the_lock`), and
merges them before it writes anything, which is why no command's operation sits on one op head
with another beside it, unless run `--at-op`
(`a_command_that_loads_several_op_heads_merges_them_before_it_writes`); and `update_op_heads` adds
the new head before it removes the old, ignores one that is gone, and leaves one it replaces with
itself (`update_op_heads_adds_before_it_removes_and_ignores_a_head_that_is_gone`); and jj's
rewrite of an operation keeps its fingerprint and gets another id, which is how a join point that
`jj op abandon` rewrote is known
(`a_rewritten_operation_keeps_its_fingerprint_and_gets_another_id`). The tests hold the lock in
the test, in process, and run the `jj` binary: that no command finishes while it is held takes 400
ms of watching, three times in all, the only waits on the clock; the rest wait for what they need.
That the commands wait on the lock is seen by watching: a command that was slower than 400 ms to
reach its lock would pass, so these tests can miss jj taking no lock, never report that it takes
one; `jj describe` is waited for until it has written its operation, which it does before the
lock.

**Evidence that the check has teeth.** `same` comparing counts instead of sets is caught by
`same_conformance`.

**What it doesn't cover.**

- A move is a reading of `heads.rs`, not a check of it: a move's writes in the wrong order, or
  without the lock, are not caught by the conformance test, but by the schedule search.
- The model gives musubi's moves one lock of their own. Moves that run inside a lock the caller
  holds already (publication cleanup, an advance) take no lock again; the model has them hold it
  the whole way, which is no weaker.
- A `jj op abandon` or `jj op integrate` that lands while musubi moves the op heads, or after,
  stays: musubi doesn't take out its own work beside one, and a jj command that merges the two
  brings back what the abandon dropped, as it does on one machine
  ([races.md, "Known jj limitations"](races.md#known-jj-limitations)).

**Refinement of the protocol model.** A command's publish and merge are, on the op heads,
`EnvStep.userOp` and `EnvStep.merge` (`Safety.lean`'s `advance_merge_refines` composes the second
with an advance): a merge of every op head into one with those as parents, and a publish that
replaces the one it loaded. To the commands, which can't run while musubi holds the lock, a move
by musubi that has passed its check is one replacement of the op heads it read by the ones it puts
in (`check_no_event`, `locked_blocks_commands`); to a lockless reader it isn't, since between
adding the new heads and removing the old both are op heads, which is the second window above.
What isn't proved is the refinement itself: `Node.heads` in the protocol
model are canonical operations, and what relates them to local op heads is the translation, whose
code is `translate.rs`. Proving that a move refines
`SyncStep.realize` or `advance` needs that relation, which `OpHeadsRace.lean` leaves abstract.

## Realization

`Realize.lean` models jj and what users are promised of realization, not musubi's code
([formal/README.md](../../formal/README.md#realization-realizelean)), so nothing compares the
code with it step by step. The code is checked by what it ends with, and the model's jj by laws.

**What is checked.** `assert_shows_jj_merge`, in `node/realize/concurrent_tests.rs`, sends the
oracle the operations below the op heads there were before publication, numbered parents first,
and the realization. The oracle answers with `settledE` and `keptE` of `Realize.lean`: the
operations whose merge jj shows once the realization is published (`publish_shows_merge`), and
those that stay in the op log (`log_kept`).

```json
{"op": "realization", "parents": [[1, [0]], [2, [1]], [3, [1]]], "heads": [2], "realization": 3}
{"kept": [0, 1, 2, 3], "merge": [2, 3], "ok": true}
```

jj then resolves op heads made of `merge`, in an op-heads store of their own, with
`resolve_op_heads`, as it does on loading them. The op head musubi published must show the same,
but for this machine's record of `.git`, which [Per-machine refs](#per-machine-refs) covers, and
every operation of `kept` must be in the op log. Commits are compared by change id, description,
tree and parents, since a merge that rewrites a commit records when it did; a commit no input
had, as the new working-copy commit jj makes for a workspace whose commit went, by description,
tree and parents, since jj gives it a random change id. The comparison is of the op head musubi
published, which in these colocated tests is its merge. Two of the tests that race real `jj`
commands with realization use it:

- `a_command_finishing_before_publication_is_merged_and_exported`: a command finishes before
  `advance`, or while it prepares, with the hive having forgotten this copy or not;
- `publication_interrupted_before_the_old_heads_go_loses_nothing`: publication stops between
  putting the new op head in and taking the old ones out, and resumes after a restart. The
  prediction is that of an uninterrupted run (`crash_harmless`).

Either fails if musubi publishes anything but jj's merge of the op heads with the realization,
for example a merge with op heads it read before the command, or takes an operation out of the
op log.

**What jj is assumed to do**, pinned against jj by `node::realize_laws`, as `heads_laws` pins
what `OpHeadsRace.lean` assumes: an op head below another is dropped, with no merge written
(`jj_drops_an_op_head_below_another_without_merging`, `load_drop`); op heads are merged in the
order they ended: the one that ended first keeps a workspace both moved, whichever move it made
(`jj_merges_op_heads_in_the_order_they_ended`, `load_congr`); and beside one op head workspaces
are merged name by name, so that an operation that leaves a workspace alone doesn't move it, and
another machine's workspace it adds appears, whichever ended first
(`jj_merges_workspaces_name_by_name`, `load_keeps`, `load_takes`), unless it rewrites the commit
the op head put the workspace on, which moves it
(`jj_moves_a_workspace_whose_commit_the_other_operation_rewrote`, why `keeps` names a commit).
The tests write operations with jj-lib on an older operation, put them beside the op heads with
no lock, and have the `jj` binary load them. They can't choose the order the file system lists
op heads in. `load_congr` assumes operations that end at different times: jj sorts op heads by
when they ended, to the millisecond, and two that end together it takes in the order the file
system lists them. `load_single` and `load_local` are how jj loads at all, and aren't pinned;
`heads_laws` pins that commands publish under the lock and that `update_op_heads` adds before it
removes.

**What the code is assumed to do**, by reading `advance.rs`, as `OpHeadsRace.lean`'s steps are
read from `heads.rs`. R1: `prepare_advance` writes the realization, and `merge_unpublished` its
merge, before `move_heads_to` touches the op heads. R2: `move_heads_to` makes one
`update_op_heads` call, which adds before it removes. R3: `lock_if_unchanged` takes the locks
and compares the op heads with those it captured, and otherwise prepares again;
`move_heads_to` takes out the realization's parents, the op heads it descends from, and, if it
published a merge, those it merged, all below what it adds. What it writes: `realize_one`
makes the realization, and `merge_unpublished` jj's merge of it with the concurrent op heads, in
the order they ended. `export_refs` writes a copy of each with the same parents and a view
differing only in this machine's record of `.git`. The merge and the copies are written under
the lock after the check, where the model writes them before musubi reads the op heads; writing
touches neither, and a check that passes means the op heads haven't changed since they were read,
so the code's run is the model's with those writes moved earlier.

**What it doesn't cover.**

- The order of the code's steps is read, not checked, as for moving op heads; the tests above
  check their outcome on the interleavings they set up, and the e2e search on those it
  generates.
- What a realization's view is, its parents and its mark are translation's: the theorems about
  workspaces take what a realization records as given, and the tests of
  [races.md](races.md#workspaces) check it. Promise 4 follows from what the model assumes
  musubi writes.
- Promise 6, that realization never moves your workspace, has one exception: where two op heads
  of yours moved it apart, jj's own tie-break decides, as it would without musubi:
  `a_workspace_moved_two_ways_follows_jjs_tie_break_after_realization` pins it
  ([formal/README.md](../../formal/README.md#realization-realizelean) says why).
- `jj op abandon` and `jj op integrate`, which take no lock ([Moving op
  heads](#moving-op-heads)).
- The tests above are colocated. Without `.git`, `advance` publishes the realization beside the
  concurrent op heads and merges them as the next step of the sync, which `shown_step` covers
  as a publication followed by jj's load, and `advance_tests` runs.

## Expected values from history

`formal/Musubi/Expected.lean` models `expected` in `crates/musubi-jj/src/node/git.rs` for one
conflicted remote bookmark. This is separate from `Refs.lean`'s slot transitions and uses no
model of jj's ref algebra. An operation supplies its remote target, cached and recorded
checkpoints, join classification and ordered parent targets.

The rule, in priority order, is:

| Observation | Result |
| --- | --- |
| An entry in `History.known` | That value, including no expectation; it overrides a recorded attribute. |
| `musubi.expected` records this ref | That value, including absence or no expectation. |
| A local join point, or an operation whose only effective parent is a root | Choose a side of its target. Private history before the join is not shared. |
| One or more parents have this operation's target | Follow the first such parent, retaining the target. |
| No parent has that target, and there is exactly one parent | Return its resolved target, absence included, or follow its conflicted target. This covers restored conflicts. |
| Otherwise | Choose a side of this operation's target. |

A side is a positive, present conflict term: the greatest committer timestamp, then the
lexicographically greatest commit id. A removal is never a candidate. No present side means
no expectation, not an expectation that the ref is absent. Parent order is significant: two
restores can have identical conflicted targets but different expectations.

The walk reads direct parents, not merge bases, from the operation store.
`musubi.expected` records a value on an operation; the checkpoint that cleanup after
`musubi sync --prune` writes carries one, so a later walk can stop there. The computation
preserves what those checkpoints say; proving that their producer captured the right value, and
that they survive publication and restart, is not an assumption discharged by this file.

`eval_congr_on` proves equality under operation renaming when the observations agree on the
followed path: the target and effective checkpoint, or the join boundary, or the ordered parents
and their targets. Its domain contains the start and is closed under the parent the rule follows;
it need not include history hidden by a checkpoint or a join. Shared target and commit metadata
give the same side function. `eval_terminates` needs a decreasing rank on followed parent edges;
`eval_stable` makes the result independent of excess fuel. `eval_without_known_agrees` removes
correct memoized answers: their correctness means that an uncached `Computes` derivation gives
that value. Thus differently populated export caches need not be assumed equal. This is
conditional on cache correctness; recorded checkpoints are authoritative, not memoization
justified by this lemma. `conflicted_import_agrees_of_history` binds the two successful, present
results to the slot states and derives the old theorem's `hE`. It still needs reachable slot
states, equal `L` and `R`, and no external ref move. No-side results are computed and tested but
do not bind a slot state's `E` or claim that a skipped export establishes its invariant.

`node::git::expected_tests::expected_history_conforms_to_model` writes small operation DAGs
through jj's op store and calls the shipping `expected`. The oracle runs the proof's `eval`
on the same target observations. Commit target numbers are ordered by commit id, and side
candidates carry their real committer timestamps; the Rust test does not choose the model's
side. Cases distinguish:

- inheriting the first matching parent from always choosing a side or using the last parent,
  including a matching third parent;
- a single-parent restore from a newly merged conflict, including a changed conflicted parent
  and a resolved absent parent;
- join cuts from following private ancestors, and a parents callback from following the
  operation store's parents;
- absent expectations, absent refs, recorded values and higher-priority known values;
- commit-time order from commit-id order, ties by commit id, and positive terms from removals;
- a three-parent conflict and two merges of concurrent fetches followed by their merge (the
  minimal criss-cross shape).

These fixtures cover those shapes **as history-walk inputs**. They do not extend `refs`'s
state-machine runs: constructing the merged targets, merging all closest common ancestor
views, and interleaving imports/exports at each intermediate merge require run semantics
beyond the binary slot laws. `merge3_synced` and `firstBase_reverts` constrain slot merges,
but alone prove neither that recursive merge-base construction nor multihead runs preserve
the history observations. No production mismatch is established by this refinement.

### Request and reply

`op: "expected"` supplies `nodes` in topological order and a `head` index. Each node has
`target`, `parents`, `boundary`, `known` and `recorded`. Checkpoints are `[]` when missing,
`[null]` for no expectation, or `[target]` for a resolved value; target `0` denotes absence.
`resolved` lists resolved target numbers. `sides` lists each target's `candidates`, pairs of
signed timestamp and commit-id-ordered resolved target number. The reply is
`{"ok": true, "value": target}` or `{"ok": true, "value": null}`. Invalid indices or parents
that do not precede their child are refused. Requests do not change the protocol session.

## Chunked blobs

`formal/Musubi/Chunks.lean` proves that a finished blob is the one sent, despite corrupt, stale or
duplicated chunks, and that every transfer finishes once chunks are delivered. It also models
musubi's narrower receiver, `BlobStore::receive` (`crates/musubi-sync/src/blobs.rs`), which keeps
only a contiguous prefix ([protocol.md, "Chunked blobs"](protocol.md#chunked-blobs)), and
musubi's senders, `RemoteHub::upload` and `RemoteHub::download`
(`crates/musubi-sync/src/remote.rs`), which send a window of chunks at a time, each request with
a deadline. The chain has three links:

1. **Refinement.** `Chunks.receive` is the prefix receiver, and `PStep` its steps: a chunk
   delivered with any claimed length, and a sweep of the partial blob or the stored one.
   For an injective hash, as `stored_identical` assumes, each is a run of the model's
   `CStep`s (`preach_abs`): a chunk taken is `recv`, one dropped no step, a hash match is
   `finishOk` then `crashRecv`, a mismatch is `crashRecv`, a chunk of a stored blob is
   `finishStored`, and the sweeps are `crashRecv` and `evict`. So `stored_identical` holds
   of it. A sender that resends from the prefix it reports finishes (`prefix_finishes`).
2. **The receiver's steps.** The Hegel test `receive_follows_the_prefix_model`, in
   `crates/musubi-sync/src/blobs.rs`, delivers up to 40 chunks at any offset up to one past the
   blob's end, some corrupt, some running past the end, some claiming a length one short or one
   long, and among them sweeps that remove the partial blob, the stored one, or both, so that
   chunks also reach a stored blob. It sends the case's steps to the oracle, which takes them from
   `initP` with `Chunks.receive` itself and the sweeps, its hash telling the blob from every other
   byte string, as an injective hash does. After each step, the reply, the partial file's bytes
   and whether the blob is stored must be the oracle's. Then a sender resends from the prefix it
   was last told, and the blob must be stored, and be the one sent, within `2 ⌈len / chunk⌉ + 1`
   resends (3 for an empty blob): `⌈len / chunk⌉` to reach the end of a corrupt prefix and start
   over, as many again from the start (the steps of `prefix_finishes`'s measure), and one that
   finds the prefix gone after a sweep.
3. **The senders' attempts.** In the model's attempt (`Chunks.attempt`), a sender sends a
   window of honest chunks from an offset; the receiver takes the first `m`, in order, and the
   sender hears its replies to the first `k` before the deadline, going on from the furthest
   prefix they report (`Chunks.next`), or from where it started if it heard none. An uploader
   starts each attempt from where it went on from after the last, or from the start once it
   has started afresh; a downloader, being the receiver, from its own prefix
   (`ARun.reread`). Each attempt is a run of `PStep`s, so the receiver's safety holds of it;
   every attempt that hears a reply takes `ameasure` down (`attempt_decreases`), and nothing
   else in a run takes it up (`late_le`, `ameasure_reread`), so that a run whose receiver
   hasn't the blob has made fewer attempts that heard a reply than the measure of where it
   started (`attempts_bounded`), and one of that many has stored it (`attempts_finish`). The
   Hegel test `transfers_follow_the_attempt_model`, in `crates/musubi-sync/src/remote.rs`,
   runs the real `upload` or `download` of a blob up to 4000 bytes long, in chunks of 256,
   against a `HubService`, through a link on which, for each window, the first `m` chunks
   reach the hub and replies to the first `k` of them come back in time, the rest timing out;
   for a download, a chunk reaches the node only with its reply. Between calls, cut short by a
   timeout, it may sweep the receiver's partial blob, and may start the sender afresh, as a
   new process. It sends each window, as an attempt, and each sweep and fresh start to the
   oracle, which runs `Chunks.attempt` itself from `initP`. After each window, its offsets,
   the hub's replies to an upload's chunks, the receiver's partial blob and whether it has
   stored the blob must be the oracle's. The test also checks the number of chunks in each
   window, which the model leaves to the sender: as many as came back in time from the last
   one cut short, or one; one more after each four in a row that all came back, up to eight;
   and none past the end.

| `BlobStore` | Model |
| --- | --- |
| `partial/<id>` | `PState.pre` |
| `complete/<id>` | `PState.store` |
| `Received::Prefix(n)`, `Received::Complete` | `some n`, `none` |
| `sweep` of the partial blob, of the stored one | `sweepPartial` (`crashRecv`), `sweepStored` (`evict`) |
| A chunk in the middle of a write when the process dies | `inject` of the part written, claiming a length past it |
| A window of `PutChunk`s or `GetChunk`s, the deadline cutting it short | `attempt` of `m` delivered, `k` heard |
| How far the hub last said it had an upload (`RemoteHub::told`) | The uploader's offset, `next` of what it heard |
| What a download has received (`BlobStore::prefix`) | The downloader's offset, `ARun.reread` |
| A new `RemoteHub`, as after a restart | The uploader's offset back to `0` |
| A chunk of a window timed out that reaches the hub after all | `ARun.late` |

A model without `evict` fails the receiver's test, since the code sweeps stored blobs. A sender
that starts each attempt from the beginning, as musubi's did, fails the senders' test as soon as
an attempt is cut short after a chunk reached the receiver and, for an upload, the sender heard
so: the model's next window starts from what the receiver reported. `restart_stalls` proves that
such a sender takes the prefix nowhere once it holds the chunks an attempt delivers, however
often it tries.

The model's sweeps take place at any time, which the safety proof allows. In time, they don't:
`TStep` adds the time since a chunk last touched the sender's blob and what the receiver has of
it, sweeps either only once that reaches `life`, and renews each, at most every `renew`
(`Chunks.refresh`), at an attempt that delivers a chunk, at a chunk that moves nothing
(`touch`), and, at the receiver, at a chunk that arrives late. In a fair run (`FairRun`), no more
than `gap` passes without an attempt or a touch. With `renew + gap ≤ life`, no state a fair run
reaches can be swept (`fair_unswept`), a stored blob kept by touches among them; a fair run is a
run of `TStep`s (`fair_tsteps`), and its attempts a run of `ARun`'s (`fair_arun`), so that it
finishes (`fair_finishes`); and a transfer whose sender's blob was swept never does
(`swept_source_stalls`). That an attempt of a fair run hears a reply at all is the network's
part: on a real link it also depends on how much of the sender's own windows, timed out, still
takes the link's time ahead of it, which the model doesn't count. Giving each chunk of a window
a deadline for it and for each chunk ahead of it keeps a link that carries a chunk within a
deadline from cutting a window short at all, and narrowing the window after a timeout bounds
what one cut short leaves.

In the code, ages are files' modification times, `renew` is `blobs::RENEW_AFTER` (ten minutes),
and `life` an hour on the hub (`PREPARED_BLOB_LIFETIME`) and a day on a node
(`UNUSED_BLOB_LIFETIME`). While a transfer is under way its chunks are minutes apart at most, as
long as the link carries any: a request times out after two minutes (`REQUEST_TIMEOUT`), a chunk
of a window after as long again for each chunk ahead of it; a call tries again at once, going on
as long as each timeout comes after a chunk took a blob further than ever in the call, and the
daemon tries a failed sync again within a minute. A window of eight chunks takes 16 minutes at
most, so the touches beside each window are that far apart at most, and `renew` and that gap
together are well within the hub's hour. An upload reads its blob with `read_chunk`, as the hub
does a download's, so that a chunk renews the sender's blob at both ends. While a call moves one
blob, it touches the others of its request or reply beside each window: those it has uploaded,
with an empty `PutChunk` at their end, and those of the reply it has yet to download, with a
`GetChunk` of no bytes. A touch renews only the hub's end, unlike the model's: a node sweeps what
it holds only as a call begins, a day old, so that its end of a call's transfers needs no renewal
while the call lasts. The hub also forgets a prepared blob 18 minutes after serving its last
chunk, which the model doesn't count: the longest a window waits for its replies, and a request
after it, so that a chunk of the last window cut short can be asked for again; once the reply has
come, a call goes on with its downloads rather than asking for it again, and needs no blob again
once it has downloaded it. Tests tie the model to the code:

- `blobs::tests::chunks_renew_what_they_touch` checks the renewal against `Chunks.refresh`,
  through the oracle: a chunk read to send, one taken of a stored blob, and one taken of a
  partial blob that adds nothing renew what they touch if `RENEW_AFTER` has passed since it
  last was, and not otherwise.
- `faults::blobs_last_while_chunks_of_them_move` makes a push and a fetch of two blobs each
  over a link on which a minute passes before each request, as far as the hub's blobs can tell,
  and the hub sweeps every hundred requests: one blob of each call waits over an hour, and the
  call must get its reply without moving any chunk twice. It fails without the renewal of a
  blob being read to send, or of a stored upload confirmed, and without touching the other
  blobs of a request or a reply while one moves.
- `remote::tests::uploads_the_hub_loses_go_again`: an upload the hub loses while the next
  uploads goes again, from what the hub has, once a touch finds it gone, and a hub that loses
  each as the other goes is given up on.
- `faults::calls_finish_on_a_link_that_cuts_every_window_short` makes a push and a fetch of two
  blobs each over a link that carries back in time the reply to only the first chunk of each
  window: each call times out more than twice as often as it would ask again with nothing
  moving, and must get its reply without asking again for a chunk whose reply came, as it
  would for a blob downloaded before a later one timed out if the call asked for the reply
  again. It fails if timeouts count against the call however far its blobs went, in either
  its uploads or its downloads.
- `faults::calls_finish_on_a_slow_link` makes a push and a fetch of more than a window of
  chunks over a link that takes 80 seconds to carry a chunk each way, one message after another,
  with the production deadline: each call must get its reply without any chunk crossing the
  link twice. It fails if a window's chunks all have one deadline: those cut short still cross
  the link, and cross it again behind the next attempt's.
- `faults::calls_give_up_on_a_request_never_answered` makes a push the hub never answers in
  time, its request too large to send whole, so that each time the call asks it uploads the
  request again: the call must give up, since that takes no blob further than it had been. It
  fails if every reply to a chunk counts as going further.

Not covered: a blob the receiver adds itself (`insert_file`, `insert_bytes`) during a
transfer, which only the uploading machine does; a stored blob a power cut left torn, which
`get` removes; and two receives of one blob at once, which the hub and the downloader don't
make. The senders' test delivers a window's chunks in order, as one connection to the hub does,
and gives each request of a window the same fate as the model's attempt does; the windows of
other blobs that a call keeps at the hub aren't among its attempts. The chunks of an upload's
window that time out may reach the hub later, after the next attempt has begun, which the model
takes as `ARun.late`, not as part of an attempt. A reply too large to send whole travels as a
blob downloaded before the call knows its attachments, which it can't touch meanwhile. No theorem
covers a run of `TStep`s built step by step from its end, as a real one is: `FairRun` is built
from its start, and every state partway through one ends a `FairRun` of its own.

```sh
cargo nextest run -p musubi-sync -E 'test(/^blobs::/) | test(/^remote::/)'
```

The receiver's test makes 200 cases, a few milliseconds each, and the senders' 100, a few
milliseconds each on jj's simple backend, one oracle serving each test's. Dropping the check
that the prefix is the length the chunk claims, so that a blob is stored when a chunk claims one
byte too few, fails the receiver's test at once, as does checking the hash a byte early.
Starting either sender's attempts at the beginning fails the senders' test, as does not
narrowing the window after a timeout.

The oracle's chunks request and reply, for a blob of three bytes:

```json
{"op": "chunks", "blob": [1, 2, 3], "steps": [{"off": 0, "data": [1, 2], "total": 3}, {"sweep": {"partial": true, "stored": false}}, {"off": 0, "data": [1, 2, 3], "total": 3}]}
{"ok": true, "steps": [{"received": 2, "pre": [1, 2], "stored": false}, {"pre": [], "stored": false}, {"received": null, "pre": [], "stored": true}]}
```

A step is a chunk, `off` and `data`, delivered claiming the blob is `total` bytes long, or a
sweep of the partial blob, the stored one, or both. The reply has, for each step, the
receiver's reply to a chunk (`n` for `Received::Prefix(n)`, `null` for `Received::Complete`),
the prefix it has, and whether it has stored the blob. A chunks request leaves the oracle's
session as it was.

The oracle's attempts request and reply, for a download of five bytes in chunks of two:

```json
{"op": "attempts", "blob": [1, 2, 3, 4, 5], "limit": 2, "sender": "download", "steps": [{"attempt": {"window": 3, "delivered": 1, "heard": 1}}, {"attempt": {"window": 2, "delivered": 2, "heard": 2}}]}
{"ok": true, "steps": [{"next": 2, "offsets": [0, 2, 4], "pre": [1, 2], "replies": [2], "stored": false}, {"next": null, "offsets": [2, 4], "pre": [], "replies": [4, null], "stored": true}]}
```

`sender` is `upload` or `download`, and `limit` the chunk size. A step is an attempt with a
window of `window` chunks, of which the receiver takes the first `delivered` and the sender
hears of the first `heard`, which the oracle refuses unless `heard ≤ delivered ≤ window`; a
sweep, as in a chunks request; or `{"restart": true}`, the sender starting afresh. The reply
has, for each attempt, the offsets of its window, the receiver's replies to the chunks it took,
the prefix it has, whether it has stored the blob, and where the sender goes on from (`null`
once it has heard that the receiver has the blob); for the other steps, the prefix and whether
the blob is stored. An attempts request leaves the oracle's session as it was.

The oracle's refresh request and reply, for ages either side of `renew`, ten minutes:

```json
{"op": "refresh", "renew": 600, "ages": [0, 599, 600, 3600]}
{"ok": true, "ages": [0, 599, 0, 0]}
```

The reply has, for each age, what `Chunks.refresh` makes of it, as a chunk touches the blob:
`0` where it renews it.

## Copies

`formal/Musubi/Copies.lean` proves, for one machine, that musubi syncs only the copy of a key,
follows a moved copy, and makes keys only by joining ([copies.md](copies.md)). What it decides
from are pure functions, as in `crates/musubi/src/copy.rs`: which repository is the copy of a
key (`standing`), given the repository's record, key and config-id and this machine's entry
for its key; whether that holds up against what is at the entry's path (`refine`), given
whether the entry's path holds the copy the entry names and whether it is this repository's
directory; and whether a repository is the copy an entry names (`check`). The chain has two
links:

1. **The rules.** The model's machine moves, copies, deletes and replaces repositories, runs
   jj's config-id rule (`handle_metadata_path`) in them, joins them, and syncs and follows
   entries. It decides with `standing` then `refine`, as `copy::standing_of` does, and with
   `check`. With no aliases, another directory is another path. In every reachable state:
   - every push is of a repository joined to the hive pushed to, under its own key
     (`right_hive`);
   - while an entry's path holds its copy, no other repository with the key is the copy,
     whatever jj decides when it runs there (`duplicates_refused`);
   - a duplicate with a record from an interrupted leave, an older release, or a removed hive
     can't join, since its config-id differs from its record's (`join_refuses_duplicate`);
   - no step but `join` makes a key, though a repository the user puts in place may bring
     its own (`only_join_makes_keys`);
   - if an entry's path holds its copy, and jj last saw the copy's config-id there, then
     once the copy is moved and jj has run in it, the daemon follows it (`moves_followed`);
   - syncing and following a move change no repository and nothing jj records
     (`daemon_writes_nothing`).

   Two runs show what jj's rule leaves to musubi. In both, jj ran in the copy at another
   path, and the copy came back before jj ran in it again. In `duplicate_taken_for_moved`, jj
   then takes a duplicate for the copy moved: `standing` alone says it is the copy, and
   `refine` makes it a duplicate. In `move_taken_for_duplicate`, the other path is reused, jj
   takes the copy moved for a duplicate, and the daemon can't follow it, as copies.md says
   under "Out of scope".
2. **The decisions.** The test `copy::conformance::decisions_conformance`, in
   `crates/musubi/src/copy/conformance.rs`, asks the oracle for `standing`, `refine` and
   `check` of every combination of: no record, or one with either of two hives, either of
   two config-ids, and any state; no key, or either of two; no config-id, or either of two;
   no entry, or one with either of two keys, hives and config-ids; and both answers to each
   of `refine`'s two questions. That is 4212 cases, in one request. The test makes the ids
   uuids and strings, and requires `copy::standing`, `copy::refine` and `copy::check` to give
   the oracle's answer for each.

The test checks the decisions, not where musubi makes them: that `musubi join` and
`musubi list` have jj resolve the config-id first and look at the entry's path, and that the
daemon checks before each sync, is for the CLI tests (`crates/musubi/tests/cli.rs`) to check.

### Request and reply

```json
{"op": "copies", "cases": [{"repo": {"key": 0, "cid": 0, "record": {"hive": 0, "cid": 0, "state": "joined"}}, "entry": {"key": 0, "hive": 0, "cid": 0}, "elsewhereHolds": true, "sameDirectory": false}, {"repo": {"key": null, "cid": null, "record": null}, "entry": null}]}
{"ok": true, "copies": [{"standing": "copy", "refined": "duplicate", "check": true}, {"standing": "outside", "refined": "outside"}]}
```

A case is a repository, with its key, config-id (`cid`) and record, each `null` if it has
none; this machine's entry for its key, or `null`; and `refine`'s two questions, whether the
entry's path holds the copy the entry names (`elsewhereHolds`) and whether it is the
repository's directory (`sameDirectory`), each false if not given. A record's `state` is
`joined`, `left` or `removed`. The reply has, for each case, the repository's standing
(`outside`, `removed`, `copy`, `broken`, `duplicate` or `unknown`), that standing refined,
and, if the case has an entry, whether the repository passes its check. A copies request
leaves the oracle's session as it was.

```sh
cargo nextest run -p jj-musubi -E 'test(/^copy::conformance::/)'
```

The test takes under a second. Dropping, from the oracle's check, the comparison of the
record's config-id with the entry's fails 32 of the 4212 cases, and ignoring `sameDirectory`
in its `refine` fails 8.

### Detach and join write boundaries

`Copies.Detach` models one checkout's local writes after the worker has stopped and leave has
finished talking to the hive. It takes a completed write as a boundary and resumes from the
files at that boundary. The checkout keeps its key: a leave marks its record left and drops the
daemon's entry, and the next join, once the hub accepts it for the same jj config-id, takes up
that key. Only a fresh join (`--fresh`) takes a new one. Local join and leave commands run
serially under the membership lock.

- `leave_prefix_safe` proves that saving the left record blocks a stale daemon entry, even
  while that entry is still on disk, and that the key stays throughout.
- `leave_retry` proves that finishing leave from every prefix yields the same left checkout,
  with its key, record and config-id.
- `join_retry` and `join_prefix_safe` cover joining again under the key the checkout left
  with, from any prefix, and enabling the entry exactly once the joined record is saved.
- `leave_retry_prefix` and `join_retry_prefix` prove that another interruption during a retry
  leaves a state already covered by the original prefixes.
- `fresh_prefix_safe` proves that a fresh join, which discards the checkout's shared history
  and its key before joining, never leaves the old key with part of that history, nor part
  of it without the mark that makes the next join finish discarding it, and enables no entry
  before the joined record is saved. `fresh_retry` proves that a plain join retried from any
  point after the mark joins under a new key without that history, as the fresh join would
  have, and `fresh_retry_again` that stopping that retry too, and retrying again, does the
  same.

The `copy-detach` oracle request takes `old` and `fresh` entries, the second the key a fresh
join takes. It returns the states before and after each write of a leave, a join from where the
leave ended and a fresh join from there, with the outcome of retrying each state with a plain
join. The test reads the shared history as kept when both the joins file
and the canonical store have the first join operation, as gone when neither does, and as part
otherwise.
`detach_and_rejoin_conform_at_write_boundaries` uses the real local join and leave code on
disposable jj repos, terminating a process after each membership write. A fresh process reads
the files, checks both daemon identities with `copy::check`, retries,
and compares both observations with the oracle. The model assumes completed atomic file
writes. Hub behavior and translation of earlier operations have separate tests.

## Workspace names

`formal/Musubi/Identity.lean` says which name each copy has at an operation, and proves that the
names under which a machine shows a view's workspaces are distinct: its own under their own
names, and each other copy's as `<prefix>/<workspace>` ([design.md, "Which workspaces are this
machine's own"](design.md#which-workspaces-are-this-machines-own)). Canonicalizing reads the
names back as machine-qualified keys, so two workspaces shown alike would be taken for one. The
chain has two links:

1. **The rule.** Only the copies present at an operation are named, each by its name there: the
   greatest its latest `musubi.name` records give, or the name in its key ([Presence](#presence)
   checks how musubi keeps those). Where copies share a name, the one with the smallest
   priority, the generation since which it has held its name and then its key, keeps it plain
   (`Naming.wins`). `Naming.assign` names those copies first, then the rest, in their keys'
   order, each taking the first of its candidate prefixes (`Names.lean`) that is free: its name,
   if it keeps it plain, then `name-1a2b`, `name-1a2b3c4d`, and that with ever more dashes. A
   prefix is free if no copy before took it and no name of this machine's own starts with it and
   `/`. One is always free (`Names.choose_free`), and so the names are injective, whatever the
   copies, their names and priorities, and the names of this machine's own
   (`Naming.localName_injective`); a copy that keeps its name and priority keeps its label
   whichever others rename, leave or return (`Naming.keeps_label`).
2. **The code.** `workspaces::display_names` makes the same choices. The Hegel test
   `workspaces::tests::names_conform`, in `crates/musubi-jj/src/workspaces.rs`, draws copies with
   names, suffixes and sinces chosen to clash, and names of this machine's own, this machine
   among the copies named or not, and requires each copy's prefix to be the one the oracle's
   `Naming.assign` gives it, the tie-break included, and the name `workspaces::local_name` gives
   each copy's workspaces here, this machine's own names among them, to be the oracle's
   `Naming.localName`, and all of them distinct. Only the copies given are named. Letting a copy
   take a prefix an earlier one took, or one that starts a name of this machine's own, or
   giving the plain name to any but the copy with the smallest priority, fails it.
   `Identity.lean` checks the cases where candidates collide with `#guard`.

The test checks the rule, not where musubi applies it: that `local_names`, `canonical_view`,
`local_view` and the hub's list pass it the copies present at the operation, with their names
and priorities there, and all of this machine's own names, including those in the op heads a
realization is merged with, is for the race catalogue (`crates/musubi-sync/tests/races/`) and
the CLI tests to check.

The oracle's names request and reply:

```json
{"op": "names", "machines": [{"name": "mac", "suffix": "aaaa1111", "since": 7}, {"name": "mac", "suffix": "aaaa2222", "since": 3}, {"name": "beta", "suffix": "1a2b3c4d", "since": 1}], "own": ["beta/x", "beta-1a2b/default"], "me": 2, "workspaces": [{"machine": 0, "workspace": "default"}, {"machine": 1, "workspace": "default"}, {"machine": 2, "workspace": "beta-1a2b/default"}]}
{"names": ["mac-aaaa/default", "mac/default", "beta-1a2b/default"], "ok": true, "prefixes": ["mac-aaaa", "mac", "beta-1a2b3c4d"]}
```

The copies go in their keys' order, numbered so, each with its name at the operation, its key's
suffix and `since`, the generation since which it has held its name; a copy's priority is its
`since`, then its number. `me` is this machine's number, which may be past the copies named
when this copy isn't present, and `own` holds the names of this machine's own. `workspaces` are
the workspaces to name, each a copy's number and the workspace's name on it. The reply has each
copy's prefix, in the order given, and each workspace's name here (`Naming.localName`): the
second `mac` keeps the plain name, having held it since an earlier generation. A names request
leaves the oracle's session as it was.

## Snapshot publication

`Musubi.Publication` models file versions as `(path, content)` pairs and supplies each commit's
complete file closure as a native contract. Its own executable definitions classify jj output
facts, subtract shared and intentional content, deduplicate paths and content bytes, decide
publication, and plan selected whole-operation cleanup. Frozen source intent is a distinct
hash-visible annotation step before `Contract.cpar` changes ordered parents. The contraction
ancestry theorems of `Contract.lean` are used directly, rather than assuming that a flat list
proves graph safety.

`node::publication::tests` builds actual repositories using jj commands. It compares exact
file-version sets, intentional commit sets, unique path counts, byte counts, budget decisions,
approval and stale-source decisions with the oracle. Selected-cleanup fixtures compare the preview
and the *applied native state*, including ordered contracted parents and checkpoint frontier with
distinct shared-boundary labels, plus the partial README commit with current AGENTS content and
removed accidental files. Other fixtures pin duplicate content, new paths reusing intentional
bytes, ten large transient files, symlinks, automatic operation merges, initial joins, explicit
revision selections, conservative Git imports, untracking accidental files, automatic descendant
rewrites and native abandonment followed by GC before first inspection. Automatic import/rebase,
fresh import keys and failed-export retries grant no exemptions; explicit import invocation and
jj's argument rendering are pinned separately. The import fuzz target checks arbitrary invocation
strings and quoted option values alongside retained-intent decoding. Unknown command records
exercise `intentKnown = false` and cleanup refusal. The gate runs before uploads in the real
`Hive` integration fixtures; those assert unwanted commits never reach the hub while incoming work
still arrives. The CLI fixture snapshots inspection, preview, successful cleanup and exact
override through real hub and CLI processes. Applying cleanup records current edits and deletions;
dry runs leave them unsnapshotted. It also checks that inspection includes the 51st retained path,
so approval never depends on a truncated path list. The fixture stops its daemons after setup to
keep the inspected operation rows reproducible.

The native source contracts remain explicit: jj's creation/rewrite records, automatic snapshot
flag and pinned command descriptions identifying selected revisions; complete commit/tree-side
object closure and actual byte sizes; collision-resistant content identities, with operation-image
coalescence refused; and canonicalization's view, expected-ref and causal-presence projections.
Prepared native effects are read back and checked before op-head installation. These focused
checks do not establish a full refinement of every native jj command. A publication hold is an
intentional lack of send progress; convergence requires holds eventually resolving.

# Conformance between the Lean models and the code

The [Lean models](../../formal/README.md) are checked against the Rust implementation through
an executable *oracle*. The oracle evaluates the models' own definitions, or executable forms
proved sound against them. Rust tests run the production code and compare its transitions,
results and state with the oracle. This document owns that correspondence and its limits;
[testing.md](testing.md) describes the test layers and how to run them.

| Model | Code | Test | Section |
| --- | --- | --- | --- |
| The sync protocol ([protocol.md](protocol.md)), with supersedes | `crates/musubi-core` | `conformance`, through the oracle | [The claim](#the-claim) to [Wire format](#wire-format) |
| `Presence.lean`: which copies a hive shows, and `PresenceContract.lean`: how a contraction keeps it | `Presence`, and the stamps of `Contraction` | `presence::conformance` and `presence::contraction_keeps_presence`, through the oracle | [Presence](#presence) |
| `Refs.lean`: per-machine refs | jj's import and export, and musubi's realization | `ref_laws` (the laws the model assumes), and `refs` and `view::tests`, through the oracle | [Per-machine refs](#per-machine-refs) |
| `AbandonRefs.lean`: survivor graph and one ref | record adoption, fix-ups and publication in `NodeRepo` | `realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon`, through the oracle | [Abandonment and refs](#abandonment-and-refs) |
| `Expected.lean`: conflicted-ref history | `node/git.rs::expected` | `expected_history_conforms_to_model`, through the oracle | [Expected values from history](#expected-values-from-history) |
| `Chunks.lean`: chunked blobs | `BlobStore::receive`, and `RemoteHub`'s `upload` and `download` | `receive_follows_the_prefix_model` and `transfers_follow_the_attempt_model`, through the oracle | [Chunked blobs](#chunked-blobs) |
| `Copies.lean`: which local repository is a joined copy | `copy::standing`, `refine` and `check` | `copy::conformance::decisions_conformance`, through the oracle | [Copies](#copies) |
| `Names.lean`: the names other machines' workspaces show under | `workspaces::display_names` | `workspaces::tests::names_conform`, through the oracle | [Workspace names](#workspace-names) |

## The claim

The generated core tests check that each transition of the Rust protocol core, using the
repository abstraction below, is a behavior of the Lean model. [Storage errors](#storage-errors)
add representable prefixes and explicit limits to that correspondence. `Regress.lean` covers hub
rollback and remaking a hive; `Supersede.lean` adds abandonment and its publication, over each
operation's original. Their safety theorems hold for every reachable model state. Applying them
to a real execution requires its states and transitions to have the stated projection.

`ContractedExec.lean` extends that original-operation submodel with survivor advancement,
atomic preparation and record adoption, and contracted-head acceptance. The oracle checks the
explicit union relation `ContractedRStep`; it does not identify these added transitions with
`SRStep`. Each added primitive preserves `ContractedSafety.Safe`, the common store and frontier
facts that do not assume an original-ancestry chain of accepted heads. These are primitive
invariant cases, not a global invariant or convergence theorem for the union relation.

The projection still does not cover every real repository transition. Raw canonical versions
and normalization already present in their birth parents cannot in general be reconstructed
from an original label and a party's current dropped set alone. A cached restoring write and
a separate publication tip are also not the old policy's atomic `supFix`. The focused checks
below pin those boundaries; they do not establish a complete safety refinement. The
[asynchronous convergence bridge](#liveness) uses a separate raw-namespace model with explicit
source contracts.

The chain has three links:

1. **Relational model to executable model.** The proofs are about a relational model: `Step`
   says which transitions are allowed, over states that need not be finite.
   `formal/Musubi/Exec.lean` defines `execStep` on finite states. `exec_sound` proves that
   whenever `execStep` accepts an action other than `hubRegress`, the corresponding
   relational `Step` exists between the abstracted states, and `exec_rsound` that whenever it
   accepts any action, an `RStep` of the extended model does. The executable model therefore
   preserves the original relational guards. `formal/Musubi/SupersedeExec.lean` adds
   the hub's records and each node's dropped set: `sexec_sound` proves every action
   `sexecStep` accepts an `SRStep` of the system with supersedes, or no step.
   `ContractedExec.cexecAction_sound` proves that the extended oracle accepts only an old
   checked transition or one of its explicit added transitions. `cexecAction_ok` preserves
   record custody, including the records held before preparation changes a frontier.
2. **Executable model to oracle.** `formal/Oracle.lean` is a thin JSON wrapper around
   `cexecAction`, built by `lake build oracle`. It contains no protocol logic of its own.
3. **Oracle to Rust.** The Hegel test `conformance`, in `crates/musubi-core/tests/protocol.rs`,
   runs the Rust hub and nodes, translates every step they take into model actions, and checks
   each one with the oracle. It fails on any action the oracle rejects, or any difference
   between the Rust state and the oracle's state. Hegel shrinks failures to a minimal trace.

The original relation's safety theorems and the added primitive safety cases have the scopes
above. The test also runs the nodes to convergence, which
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
| Hub records, node `nodeD` and the records it took last | `FakeHub::records`, `FakeRepo::dropped` and `applied` |
| Every list of records a node has taken, `held` | `FakeRepo::held` |
| Hub `pruned` | `FakeHub::pruned`, which keeps every record, as the model's `recs` does, those pruned standing for their count and digest |
| `net`, the set of every message sent | the test's network: a set, so any message can be delivered any number of times, or never |

`lops` and `lobj` are a node's local operations and objects, and `sops` and `sobj` what it has
staged. Operations are their originals, as in `Supersede.lean`: dropping renames nothing here, so
the test's storage keeps every operation it had, dropped or not, and checks storage closure over
all of them. Its locality test deliberately still requires the original body: realization in this
submodel needs original parents, whereas the native adapter can realize only their surviving
images. Advancement and the hub's comparison use `exp` and `Below`. A record state's digest is the
index of its records in a table of every list of records seen, so equal digests are equal records.
The jj-specific parts of a real node (canonicalization, realization, bundles) are not covered by
this link; the jj example tests and the generated end-to-end tests cover them
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
| None, at 39 reachable fallible trait methods | The core must propagate the trait's errors. Some adapter methods currently always return `Ok`; these test their fallible contract, not a physical I/O failure there. |
| All or a proper prefix of `store_ops` / `stage_ops` | `CanonicalStore::import_operations` can retain earlier batches before a later failure. `NodeAdapter` can also fail after import while checking announced parents. |
| All or a proper prefix of `store_objects` / `stage_objects` | Simple-backend import stores objects individually; a later error can leave earlier objects present. The abstract objects have no internal structure. |
| A merge, advance, adoption or fix-up | jj can publish before later ref export, working-copy repair, record persistence or canonicalization fails (`merged_repo_unchecked`, `advance`, `adopt_records`, `write_fixup`). This projects the complete logical effect, not each intermediate translation. |
| A complete accepted-base write | `write_all` may finish before `set_len` fails. Partial or invalid bytes are outside this logical-id abstraction. |

The fixed-node harness reaches 39 of the traits' 40 fallible methods, including record
pruning, held-prefix lookup, sharing and push/acceptance bookkeeping. The `fresh` method is
wrapped too, but is unreachable here: all modeled nodes already belong to the hive, and
pruning waits for all of them. Errors while a new node joins after pruning remain outside
this layer. Pruning is server upkeep: its error is logged and the same hub adapter is kept,
without failing the request or restarting a node. Only pre-effect pruning errors are injected;
partial writes of its records or indexes need real-adapter coverage.

The harness requires every injected error to reach the caller before another entry point
or the end of injection; selecting a fault alone does not count as coverage. For each
failed entry point the wrappers journal the actual completed logical effects.
Where they fit, the harness checks them against the oracle **before recovery**: a stuttering
read error, `learn`, complete `recvOps` / `recvObjs`, `advance`, `merge`, `adopt`,
or a fix-up's `userOp`. It checks the unchanged state too when no action occurred. The
adapter's accepted base, the core's realization plan and its announced-record cache are not
model state. The error return and their intermediate changes are not themselves proved
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
Once faults stop, ordinary honest exchanges must converge with every created operation
retained; representable cases also keep the oracle's liveness checks during that suffix.

Limits: this tests errors between logical storage effects, not real storage implementations.
The abstract attachments contain complete operations; view-delta imports whose base is
missing (which `HubAdapter::store_ops` can leave incomplete without returning an error) are
outside this projection, as are partial pushed/accepted bookkeeping files.
It does not model a torn head log, a partial accepted-base id, `set_head`'s append/contraction
or accepted-index side effects before an error, partially renamed histories in
`prepare_records`/`adopt`, batched/asynchronous realization writes, ref export or
working-copy repair inside a composite advance. `set_head` is injected only before any
such effect; no atomic rollback or successful full head change on error is invented. Real
adapter fault injection is still needed for those boundaries. It adds no hub durability or
power-cut recovery guarantee.

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
| A machine runs `jj op abandon` of operations below its heads (test rule) | `abandon` |
| `NodeCore` asks the repo to merge heads | `merge` |
| `NodeCore` sends `Fetch { base, haves }`, on every poll | `fetchAll` |
| `NodeCore` sends `GetObjects { for_ops: S, haves: H, .. }` | `fetchObjs` with `objs(S) \ H` |
| `NodeCore` sends `Push { ops: S, objects: O, expected, new, .. }` | `pushAll`, then `sendSup` with `new`: every push carries the records its node took and what it dropped |
| `NodeCore` takes the hub's records | `adopt`, with all of them |
| `NodeCore` writes the fix-up and pushes it with what it dropped | `userOp` on its head, then `pushAll` and `sendSup` |
| `NodeCore` accepts a head-carrying reply | `learn`; a stale one it ignores maps to nothing |
| `NodeCore` takes in a `Fetched` reply | `learn` if its head is newer, then `recvOps` and `recvObjs` if it stages the operations; the states are compared after the last |
| `NodeCore` stages an `Objects` reply | `recvObjs` |
| `NodeCore` realizes | `realize` |
| `NodeCore` advances through the fake repo | `advance`, including surviving images for a dropped known head; `advancePrepared` also takes prepared records atomically; a real repo may also merge ([below](#a-repository-advance-that-also-merges)) |
| The hub handles `Fetch` | `hubFetch`, then `sendD`: its reply carries the hub's records |
| The hub handles `GetObjects { for_ops: S, haves: H, .. }` | `hubGetObjs` with `objs(S) \ H` |
| The hub handles `Push` | `hubPushIdem`, `hubSupAccept` then `sendD`, `hubPushReject`, `hubPushIncomplete`, or `hubPushRefuse` |
| `NodeCore` takes in a `Refused` reply | nothing |
| A node restarts | `loseKnown` (its staged files survive; `known` does not) |
| A node restarts while taking in a `Fetched` reply, after staging its operations and before staging its objects (test rule) | `learn` if its head is newer, `recvOps`, then `loseKnown` |
| The hub restarts | `crashHub`; the hub forgets what each node said it took |
| The hub goes back (test rule) | `hubRegress`; the hub forgets what each node said it took, as a restart does, and how many records it had pruned goes back too |
| The hub prunes (test rule, half the time after a `quiesce`, and once after each case's final one): `hub::prune`, which prunes every record once every node's last `Fetch` or `Push` said it took them all | `prune` with the count, if it pruned any |
| The hub loses data outside its current closure (test rule) | `hubForget` preserves operation bodies needed by retained history; historical-only objects may be lost. A requested rollback to an incomplete target takes a separately identified environment-chosen remake |
| The hive is made again, empty, as `HubDir::remake` makes one whose store is corrupt (test rule) | `hubRegress` to 0, then `hubForget` keeping only the root: `State.remake` (`exec_remake`), a run of the extended model (`remake_reachable`) |
| A reply to the node's own request that says the hub went back (`NodeCore::handle_reply`) | `loseKnown`, then `learn` if the reply's `seq` is above 0 (at 0, the restarted node already knows `(0, root)`) |

The Rust hub decides how to answer a `Push`, and the test sends whichever of `hubPushIdem`,
`hubSupAccept`, `hubPushReject`, `hubPushIncomplete` or `hubPushRefuse` it chose. The oracle
checks that choice's guard, so a hub that accepts a `Push` the model would reject is caught,
and so is one that rejects a `Push` the model says is incomplete. Every push the hub accepts
is a supersede in the model, which adds a record only for what the push drops that the hub
hadn't; the hub refuses, storing nothing, one whose records aren't its own, or whose new head
is among the records it remembers or the push's pending drops. The reply to an accepted push
carries the hub's records as a state, from which, with the records it took and what it
dropped, the node knows them all, so the model's hub announces them with it (`sendD`). A
notification carries them too, but the node doesn't take them from it: another node may have
dropped what it did, and the model announces nothing with a notification. The Rust core sends
only the merged requests (`Push`, `Fetch`); the finer-grained actions remain in the model and
the oracle. The hub prunes only when every node has said, in a request, that it took every
record, and the oracle checks that each node has held them when it does. A node takes the
records a reply about the head it knows announces, however old, so it may take fewer than it
took, after a restart; it takes the hub's records after those pruned from records it held
(`LocalRepo::held`), and the oracle checks that it held them, as `adopt` requires. The model's
nodes are fixed, so none joins after a prune: `FakeRepo` holds every record whole, and a node
that lacked records the hub pruned would panic.

The test's objects have no structure, so the test's hub ignores `closure(base)` and leaves
out exactly what the haves name, as the model's `hubFetch` does; a node's haves there are
every object it holds.

The old original-ancestry relation cannot represent every accepted production push.
`history::a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup`
uses real stores, interrupted adoption and hub rollback to reach an accepted push whose
expected head is not an original ancestor of the cached fix-up. The pending drops contract
that head into ancestors of the fix-up. Both real adapters allow this, while `SStep.sup`
requires original ancestry. The trace then converges; narrowing the production guard to fit
the model would change that valid behavior. The extended core harness now checks such a
comparison under the acceptance's full retained record union and packet drops. Rejection is
packet-specific too: the oracle refuses an original-ancestry rejection when the contracted
packet is acceptable. It retains the acceptance's drop set for subsequent history checks,
even after the hub prunes the corresponding record ids.

`ContractOrder.lean` defines `Below` for the comparison through all surviving images, and
`belowB` additionally requires a nonempty image, as `HubAdapter::descends` does. The real
trace supplies the immutable parent material from its actual stores to the
`contractedAncestry` oracle route, checks `descends=true` and `original=false` at that accepted
push, and separately checks its hub head and sequence. This is the current expected hub head;
the hub's temporary contraction starts there, so this test does not establish equivalence
for arbitrary ancestor queries. The production closure and surviving-new-head guards still
apply. `below_contracted_iff` and `below_two_step` connect the mathematical comparisons across
contraction; the CId/physical-store projection and a revised full-state refinement remain
necessary. Expansion may contain duplicate images; the check is universal membership, not
an exact image-list comparison.

`history::a_dropped_head_published_again_is_dropped_by_who_took_it` reaches the supported
departure case: the original producer leaves successfully, the hub rolls back, and another
copy republishes a head a remaining machine already dropped. That machine must combine every
surviving image with its own work and publish the drop itself. The native helper test
`advancing_to_what_survives_of_a_dropped_head` compares the complete image frontier and merge
parents with `SurvivorAdvance.lean` through `survivorAdvance`, including separate images,
non-colocated repositories and git fetches. It samples the raw heads before a jj observer
can merge them. The generated core tests check the abstract network transitions; these real
repository tests check the native projection at the new boundary.

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
| `realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon` | After record adoption, the merge uses `max(images(old heads) ∪ {incoming})`, with no dropped ancestor, and keeps the fetched ref. [Abandonment and refs](#abandonment-and-refs) covers its combined graph/ref projection. |
| `translation::prepared_advance_merges_each_survivor_once` | A prepared multi-image advance publishes each survivor exactly once. It supplies valid canonical survivors; it does not check `NodeAdapter` deriving that frontier while records remain prepared. |
| `advancing_to_what_survives_of_a_dropped_head` | The full surviving frontier agrees with `SurvivorAdvance`, including physical parent count so duplicate parents cannot hide behind a set comparison. With that head as the accepted base, several images in most cases, reading the op heads passes `read_heads`'s check of every image: the only code-side evidence for `BaseImages.lean`, which no oracle call checks. |
| `abandoning_a_root_child_beside_a_merge_converges` | Concurrently abandoning a root child and merging it with another commit converges. |

In an ordinary advance, a later unpublished merge can fail after preflight succeeds. The
colocated path then publishes the advanced head set, and working-copy cleanup tries the normal
merge. Cleanup can also fail, returning an error after publication; this is not an atomic
rollback. Root-based transitions merge before the first export and return a later merge error
without that separate-head fallback. The fault regression below has no prepared records and
does not establish error-path coverage for that branch.
`node::realize::advance_tests::late_merge_store_errors_preserve_heads_and_recover` injects
real op-store permission errors at these later writes. It checks successful fallback,
failed fallback and non-colocated cleanup failure, with every old operation and the incoming
realization still reachable. Reopening and retrying must converge. A rebased bookmark must
also be exported, so a later jj git import neither creates an operation nor reverts it.

This Unix regression skips with a reason when mode bits cannot deny a write. It does not
inject view-write or read failures, partial head writes, crashes, concurrent commands, or
record-taking changes to merge bases. The oracle's two-step proof does not cover these
intermediate store effects. A working-copy repair that creates an operation is another
operation-creating action.

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

`FineAssembly.hive_converges_observed` derives a fixed hub and convergence of surviving
participants from the record, retry, raw-entry and event-replay arguments. Its native source
contracts, environmental assumptions and fairness premises remain explicit in the
[formal guide](../../formal/README.md#the-asynchronous-liveness-bridge). Component oracle
checks and native regressions support those contracts; they do not formally verify arbitrary
Rust executions.

`AsyncLiveness.bad_accept_before_reply` proves that acceptance makes the pusher good before
it learns the new head. `measureR_delayed_learn` proves descent when learning a strictly newer
pair from current hub history, even if that pair is no longer latest.
`lost_acceptance_and_delayed_fetch_make_progress` checks both boundaries against the core
and oracle before final quiescence. `settling_hub_stabilizes` proves fixed-hub progress for
its constrained `SettlingStep` suffix, rather than establishing native correspondence itself.

Record stabilization does not assume head stabilization. `RecordStability` derives eventual
full-record and pruned-prefix stability from bounded immutable original drops and cessation
of rollback. `ContractedRecordCut.cexec_record_and_drop_sets_stabilize` carries this across
the extended executable transitions and derives a common cut for records, pruning and bounded
participant drop sets. It adds no runtime transition. Equal dropped unions can still have
different ordered records; [the measure checks below](#policy-measures) account for that debt.

### Record custody and recovery

The atomic fake cannot reach native record-taking interruptions or reconcile different raw
names of one original. The following real-repository tests cover those boundaries:

| Test in `history` | Obligation |
| --- | --- |
| `a_sync_stopped_while_taking_an_abandon_the_hub_then_loses` | Hold the records before moving heads. After interruption, restart and hub rollback, the affected machine alone publishes the drop and reaches idle; a control with retained hub records needs no push. |
| `taking_an_abandon_resumes_where_it_stopped` | Resume before the hold save, after it, after adding new heads, and after moving heads but before workspaces. Recover the saved exact move through cache loss while preserving newer commands or abandons and all images of a dropped merge. A multi-image working-copy rewrite has no unique single target. |
| `a_receiver_takes_records_that_drop_its_head_above_a_cached_fixup` | Advance to take prepared records even when the receiver already descends from the hub head. An accepted head can be an ancestor of a dropped operation. A finite core regression pins the same choice. |
| `record_bodies_keep_pending_drops_named_after_hub_rollback` | Retain metadata for a drop never realized locally, rename it and publish the actual new raw target. `record_metadata_arrives_without_current_operations_or_parent_views` separately checks record-only bundle custody, ordering, deduplication and refusal of missing names. |
| `lost_records_follow_an_older_name_the_receiver_never_held` | Normalize pending names after local abandon discovery and again when lost records become pending, even without another fetch. Publish the older target and supply its metadata to a remade hub. |
| `received_records_survive_departure_and_drop_local_aliases` | Save custody before preparation writes local operations; recover received drops after the producer leaves and the hub rolls back. Retain off-frontier aliases across reopening and consume receipts even when applied records are unchanged. |

Custody and applied records are distinct: saving a receipt does not report its effects as
applied. The `recordEpoch` route checks the equal-record adoption that consumes custody and
makes those effects pending. The core retains an equal-record announcement while receipts
need reconciliation. `advance` clears its staged graph and ancestry cache when record state
changes, even if a later part of the advance fails.

The production driver ends a round on an incomplete reply with a refusal error. The low-level
hive harness can continue past that boundary, so its bounded retry traces do not demonstrate
one endless driver round. Nor do these regressions establish a full asynchronous refinement.

### Cached writes and publication

`history::op_abandon_replicates` compares the production fix-up cache with `Retry.Fixup.write`
through `retryFixup`: the first write creates an operation, retries and reopening reuse it,
and adoption clears pending drops. Omitting the write guard fails the same-handle retry;
omitting its persisted marker fails the reopened retry. The model bounds restoring writes
within an epoch whose pending originals shrink after its first current adoption. This test
pins reuse, not eventual entry into that epoch or the monotonicity premise.

A cached restoring head can already equal the hub's while its drop remains pending. The core
then requests a neutral publication child. The adapter rechecks the current ids and keeps the
current view, presence and expected values; it does not replay the old payload.
`history::pending_drops_get_a_new_tip_when_the_hub_already_has_the_cached_fixup` checks that
choice against `Retry.Publication`, including a lost request, retry, reopening, child contents,
acceptance and cleared pending. Its reachable orphan-realization prefix includes loss of a
recent custody save in a power cut. The earlier interrupted-adoption case remains in
`history::a_cached_fixup_publishes_pending_drops_even_when_its_head_is_known`.

`cached_restoration_still_publishes_a_pending_drop_at_the_known_head` uses an opt-in cached
fake to check the core's request and reuse against the same route. Generated core runs use
eager restoring writes and do not exercise that production cache.
`realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon` also checks the neutral
child at a conflicted-ref boundary, including current Git/ref values and presence through
sync and reopening. Restoring-write credit does not bound these additional neutral tips.

### Packets, replies and raw identities

Each sent core-harness push keeps its actual request and supersede metadata together. Its
ordered records and complete drop set are checked against the sender's snapshot; policy pushes
also check the known pair and sent head with `PushPacket.sourceMatchesB` through `pushSnapshot`.
Rogue pushes retain their nonpolicy fields. `CutHistory`, `PacketCoupling` and `RecordReplies`
use the actual packet and send-time state to derive head/record pairing, sender alignment and
prefix custody, rather than substituting another packet with the same target.

`head_replies_update_records_only_for_the_known_pair` and
`fetched_replies_mark_only_new_heads_and_take_only_current_records` pin filtering and storage
callbacks not distinguished by the original generated projection. They call `handle` directly.
The driver's own replies use `handle_reply`, which can restart on a rollback pair before
learning it. Successful head handling is checked with `headControl`; storage-error prefixes
are covered separately and may retain effects.

The transport contract checks canceled calls, delayed replies and duplicate completed replies.
`replies_only_complete_the_matching_pending_call_once` additionally injects obsolete/duplicate
frames into the shipping stream receiver while a later request is pending, comparing matched
slots and remaining ids with `Retry.Inbox.finish` through `retryInbox`. Finite pre-cut slot
consumption does not force an old live call to finish or bound notifications. Allocation and
disconnect are not exercised by that unit; its correspondence assumes the `u64` counter is
not exhausted. A still-pending reply may arrive after a hub remake.

The raw-namespace checks avoid identifying raw versions with immutable originals.
`history::local_burst_conforms_across_a_pending_namespace` checks actual local control and
the pending packet's fields against the raw oracle routes. The hub-store test
`contraction_keeps_a_survivor_publishable_and_refuses_replayed_origins` checks that a survivor
remains publishable and replayed drops do not change existing current names, including after
reopening. These checks do not establish a universal raw-version-to-original mapping.
[Contraction identity](#contraction-identity) states the native identity obligations.

### Policy measures

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

`Supersede.lean` proves the same with supersedes, for the policy `SPStepR`, which adds
taking the hub's records (`adopt`) and publishing a node's own drops (`supPush`, and `supFix`,
which writes the fix-up first, as musubi does), with the measure `smeasure`.

`formal/Musubi/Exec.lean` computes these on the oracle's state: `measureE`, `rmeasureE`,
`convergedE`, `upOpsL` and `upObjsL`, proved equal to `measure`, `rmeasure`, `Converged`,
`upOps` and `upObjs` of the abstracted state (`measureE_eq`, `rmeasureE_eq`,
`convergedE_iff`, `mem_upOpsL`, `mem_upObjsL`, in `ExecSound.lean`); and
`SupersedeExec.lean` computes `smeasureE` and `sconvergedE`, proved equal to `smeasure` and
`SConverged` (`smeasureE_eq`, `sconvergedE_iff`). `recordMeasureE` appends `recordLagE`, the
number of nodes whose ordered applied records differ from the hub's. `RecordLiveness.lean`
proves its correspondence (`recordMeasureE_eq`) and the stronger convergence check
(`recordConvergedE_iff`) for the original policy. The oracle retains the original `measure`
and `rmeasure` outputs, but uses the extended record-aware suffix below for `smeasure`.
The old `recordMeasureE_eq` theorem does not itself cover those added transitions. The
oracle answers with:

```json
{"op": "measure"}
{"ok": true, "measure": [1, 0, 0, 0, 0], "rmeasure": [1, 0, 0, 0, 0, 0],
 "smeasure": [0, 0, 1, 0, 0, 0, 0, 0], "recordLag": 0, "converged": false}
{"op": "upload", "node": 0, "new": 1}
{"ok": true, "ops": [1], "objs": [10]}
```

`measure` is `(dirty nodes, Σ staleness, Σ missing ops, Σ pending advances, Σ pending merges)`;
`rmeasure` is `(nodes not good, inconsistent nodes, Σ staleness of consistent nodes, Σ missing
ops, Σ pending advances, Σ pending merges)`; the oracle's `smeasure` is `(drops not yet the hub's,
Σ the hub's drops not yet a node's)` followed by the contracted suffix `rmeasureCE` described
below. All compare lexicographically; [formal/README.md](../../formal/README.md) defines their
terms. `converged` is `RecordConverged`: `SConverged` and ordered-record agreement. The harness
compares `(smeasure, recordLag)` lexicographically. Dropped-set progress may increase record lag;
an adoption that changes only applied records must decrease it.

The extended oracle uses `ContractedMeasure.rmeasureCE` for the record-aware suffix. It counts
surviving images not covered by any local head, rather than original ancestry of a dropped
known head, and compares historical heads under the node's dropped set. A survivor advance
can add a second head while original `mAdv` stays one, increasing the old measure. The new
image count falls first; `uncoveredImages_after_advance` proves it is zero after the frontier
step. Historical comparability is checked against each surviving image, and a singleton
facing a dropped known head is unsettled until it covers every image of that head. Otherwise
adding multiple images could increase the earlier unsettled-node count. The fixtures check
the complete tuple for a receiver at one image and at a common ancestor of separate images.
`rmeasureCE_without_drops` proves exact agreement with the old check before drops.
The original `measure` and `rmeasure` outputs and their valid pre-drop checks are retained.
These component results do not prove termination of the full extended relation.

Equal dropped unions do not imply equal records. `regrouped_records_conformance` creates
`[[1],[2]]`, remakes the hub, and has one machine republish both drops as `[[1,2]]`. Another
machine still has the original two records. Its next adoption changes none of the eight
set-based measure components, but removes one record mismatch. No state is injected.

`RecordLiveness.lean` proves `recordMeasure_decreases` and `recordPolicy_wf` for projected
`SPStepR` steps and current-record adoptions with no missing drop. `record_finish` proves
that abstract convergence, where every node has dropped what the hub pruned, permits finite
completion to ordered-record agreement without changing the abstract state. At that point
every head is the hub's surviving head, so the adoption guard is satisfied. There is at most
one unit of debt per machine (`recordLag_le`), and each such adoption removes one; with the hub
fixed there are at most N repairs.
`reconcile_executable` checks the actual executable adoption after a current announcement.

The Rust correspondence is `NodeCore::note_announced` reconstructing the current records
from a fetch and `NodeCore::step` taking them before further work. Its comparison is of the
ordered lists, with no missing-drop condition. `prepare_records` checks the same head guard,
and `adopt` replaces the applied records even when the dropped union is unchanged. The
hub's `recEq` push guard is then open. As elsewhere, record digests are treated as identifying
the record lists; this argument does not prove collision resistance. Fair scheduling remains
an assumption. The asynchronous bridge in `FineAssembly.hive_converges_observed` derives
eventual fresh knowledge from correlated completed calls, consumptive old replies and notices,
and the stated recovery contracts.

The conformance test checks:

- Every `Push` the policy sends (not one the test's `rogue_push` rule makes) carries exactly
  `upOps` and `upObjs`.
- `World::quiesce`, which stops users and runs every node's policy over a reliable network,
  asks for the measures after each exchange: a node's `Fetch` and the reply, or one policy
  step and the replies to what it sent. An exchange that changes the node's operations,
  heads, `known` or dropped set must make the measure fall, and any other must leave it
  where it was or lower. A change only to applied records must strictly decrease the refined
  measure too. `(smeasure, recordLag)` must do so in every case; `rmeasure` only while no node
  has dropped anything, and `measure` only while the hub has never gone back too, since its
  proof needs every state to be `Reachable`. Each node's turn starts with a
  `Fetch`, whose reply puts its `known` in the hub's current history before it realizes
  anything, as `PStepR` requires. A crash the test armed before quiescing, which happens
  when the node next stages a `Fetched` reply, is not a policy step, so the check starts
  afresh after it.
- Each measure request cross-checks `recordLagE` against the Rust record lists and
  `recordConvergedE` against concrete convergence, in both directions. The states already
  agree after every action; neither side may declare convergence with records still unequal.

Before drops, the measure correspondence checks the policy against the original termination
proof. Through contracted transitions, strict decrease is an executable regression check;
the full union termination proof remains open. Hub-only work, such as storing a rejected
push's upload, changes nothing the measures read.

Two fixed runs check what random cases may reach only rarely. `regress_scenario_conformance`
drives the core through `RegressScenario.trace`, requires the actions it records to be that
trace, so that nodes A and B both merge heads `{1, 2}` (`duplicateMerge`), and then
quiesces. The trace restarts A and B before they fetch, so the test crashes them, rather
than have them restart on the hub's reply. `remade_hive_conformance` makes a hive again
under nodes that know heads it has lost, and requires each to take the hub's reply as
saying it went back (`NodeCore::handle_reply`) and fill it again. `supersede_conformance`
has a node abandon an operation the hub has, and the other take the record, and
`concurrent_supersedes_conformance` two nodes abandon different operations at once, the hub
ending up with both records.

### Contraction identity

`canonical::contract::tests::dropping_twice_is_dropping_both` checks the Rust contraction
against copies of `Contract.cpar` and `cid_eq_mk`: generated parent lists are expanded by index,
and ids become terms of immutable original identity and parent terms. It compares those terms
with the stored result, and sequential with union contraction, in shuffled query order. The
generator permits equal nonparent fields across different parents. If an initial operation
would duplicate an earlier one's full content, its description is changed to make a distinct
original. The test also checks that no dropped id returns and original identity stays.

`Contract.cpar_absorbs_subset` and `cid_absorbs_subset` specialize that composition: contracting
an already contracted body by a subset of its drops preserves its parents and canonical id.
`image_absorbs_subset` supplies the singleton image of a surviving body, and
`anc_cpar_survives` covers every ancestor of that body. When drops name originals,
`image_original_survives` excludes all historical versions of those originals, without
requiring originals to distinguish raw versions. `PresenceContract.sid_absorbs_subset` also
keeps stamps and the cumulative dropped set. Native use requires a complete, surviving body
written under the larger set. It cannot use an incomplete metadata lookup's identity fallback
as that witness.

`abandoning_twice_around_another_machines_record_publishes_all` checks that native witness
after taking the hub's first record while keeping additional pending drops. The applied
record identities match; the node's dropped originals strictly include the hub's. Every
body in the selected heads' closure is read and has a surviving original. A nonempty native
contraction by the hub's drops then returns each exact head unchanged, and the hub's cache
also keeps it without marking it superseded. This does not equate the two whole normalizers.
At the same snapshot the test checks the strict raw closure of every marked operation in
the hub's store: each contains a dropped original, with at least one cached key that is not
a remembered raw drop name. `local_burst_conforms_across_a_pending_namespace` checks the
actual post-write `Push.new`, including the root, against the node's applied and pending
dropped originals. These are the direct cache-cause and sent-body premises of
`NodeSys.Exec.unsuperseded_of_normal`.

`a_drop_outside_the_hub_head_is_remembered_without_a_cached_image` checks the separate dropped
name and cached-renaming cases used by `SysAcceptance.not_dropped_of`. It publishes a drop
whose metadata is beside the surviving head's closure: the hub remembers and refuses it, while
its cached `current` lookup leaves the id unchanged, before and after reopening. Thus a
nonidentity cached image is not required of every remembered drop.

`contraction_does_not_recreate_a_dropped_id` is the minimal store counterexample. Removing the
immutable original parents makes it fail by exact id equality; it is the Rust counterpart of
`Contract.equal_content_recreates_id`. `peer_cannot_put_two_versions_of_one_original_in_a_history`
checks refusal before rewrites. The hub test
`contraction_keeps_a_survivor_publishable_and_refuses_replayed_origins` checks that a survivor
remains closed and publishable, and that a hash-valid alternate version of a dropped original is
refused, including after reopening.
`original_parent_encoding_is_pinned_and_cannot_be_supplied_by_a_caller` pins the new encoding and
fresh-write enforcement.

`translation::repeated_restores_keep_distinct_identities_when_contracted` reaches the content
collision through real jj commands: repeated restores with an intervening describe and equal
operation timestamps. It checks canonical contraction, jj's own local-id coalescence, refusal
before any pending drops, and recovery by integrating the old head. It cannot recover the
user's abandon intent from identical local bytes; the protocol proofs assume that detection
has supplied the intended original set. The combined abandonment/ref refinement is tracked
separately in issue #77. The `import` fuzz target varies the reserved attribute with a valid
content hash so that origin validation is reached.

`taking_an_abandon_preserves_original_identity_after_cache_loss` covers a remote record and work
created on the old history: both local rewrite paths keep durable canonical markers, and
rebuilding the translation cache returns the same originals.
`coalesced_history_after_gc_is_refused_before_publishing_drops` covers jj collecting the old local
evidence before another command and sync: no drops are published when the original intent is no
longer recoverable. `fresh_equal_time_operation_is_not_an_old_counterpart` checks that unpublished
work with the same time metadata as an old operation keeps its view after an abandon, even after
jj gc, cache loss and restart. Removing the durable evidence too causes a refusal before any
drops. `node::originals::tests::torn_rows_never_establish_an_identity` checks partial rows
followed by a complete append, and preserves multiple fingerprints per original and shared
fingerprints across originals. The existing repeated-abandon restore tests also exercise a
translation walk resuming on an old unmarked jj rewrite after `check_abandon` moved the heads:
that source keeps its established canonical correspondence.
`a_delayed_child_of_a_jj_rewrite_keeps_its_origin_after_cache_loss` checks that the source alias
survives cache loss and restart, that retaining a counted step while losing its head move
completes the physical rewrite, and that a delayed child keeps the original identity afterward.
`torn_steps_lose_only_themselves` generates the source rows too: no partial counted block can
silently omit an alias that records depend on. These local translation and crash boundaries are
tested runtime obligations, not additional theorems of the abstract protocol model.

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
`just test`'s time. `MUSUBI_CONFORMANCE_CASES` sets the
number; `just mutants` sets 150.

## Evidence that the check has teeth

Deliberately broken versions of the core, each caught:

| Change | Caught by |
| --- | --- |
| Hub accepts a `Push` without checking the closure is stored | invariants (HubClosed) and conformance |
| Hub accepts a `Push` without checking ancestry | invariants and conformance |
| Hub accepts a `Push` when `head ≠ expected` | invariants and conformance |
| Node ignores fetched record regrouping when dropped unions agree | `regrouped_records_conformance`: the expected record-only adoption becomes a realization |
| Repository rewrites an already written fix-up on retry | `history::op_abandon_replicates`, against `Retry.Fixup.write` |
| Node omits the publication request when its cached head equals the hub's | `cached_restoration_still_publishes_a_pending_drop_at_the_known_head`, against `Retry.Publication.write`; the real orphan-realization regression also fails before the fix |
| An old head reply changes current record bookkeeping, or a notification acknowledges a pending drop | `head_replies_update_records_only_for_the_known_pair`, checking publication, fetching and adoption |
| An old fetch marks its head accepted, or replaces the current records | `fetched_replies_mark_only_new_heads_and_take_only_current_records`, checking the storage callback and adoption |
| Node realizes an operation before its parents | invariants and conformance |
| Node realizes an operation before its objects arrive | invariants and conformance |
| Node realizes the front of its queue without removing it | `regress_scenario_conformance`, against `EarlyEntry.Burst.stepB`: the second realization leaves every rank component unchanged |
| Node learns a head whose `seq` equals the one it knows | conformance only: harmless, but not a model step |
| Node's `Push` uploads every operation since the root, not since `known.head` | conformance only: not `upOps` |
| Node with two heads pushes one of them before merging | conformance only: the push raises the other nodes' staleness, and the measure rises; the run still converges |
| Node that believes a head at the largest sequence number doesn't start over when its own request's reply says otherwise | `nodes_recover_from_false_replies`, and rarely `nodes_recover_from_wrong_replies` with real repositories: no honest hub gets there, and the node never converges |
| Hub accepts a `Push` whose records aren't its own | `a_push_without_the_hubs_records_is_refused` |
| Hub accepts a `Push` with its records to a head it dropped, or that the push drops | `a_push_to_a_dropped_head_is_refused`; rarely conformance, for the second, through `rogue_push` |
| Node advances to a head it dropped | `a_node_never_advances_to_a_head_it_dropped`, through the oracle (`HeadsOK`) |
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

"Invariants" means `protocol_invariants`, which checks safety directly on Rust state without
the oracle. Fixed tests cover dropped-head refusals and recovery paths that honest generated
policy reaches rarely or never. `just mutants` runs cargo-mutants over `hub.rs` and `node.rs`;
the property and conformance tests should kill every mutant it makes.

The selected native campaigns in [testing.md](testing.md#native-adapter-campaigns) also
exercise assumptions outside the abstract core. These deliberate changes are checked at the
production boundary, rather than by changing a protocol fake:

| Change | Caught by |
| --- | --- |
| Peer timeout becomes a generic error | [Stream failure classification][stream-failures] |
| Native ancestry is constant or inverted | [Native ancestry law][native-ancestry] |
| Every error permanently pauses a copy | [Retryable-error classification][native-recovery] |
| No error permanently pauses a copy | [Permanent-error classification][native-recovery] |
| Repair omits copies lost with the whole base | [Offline trim regression][native-ancestry] |
| Repair replays old time over surviving work | [Offline trim regression][native-ancestry] |
| The hub finds a record count's digest by an unchecked subtraction of its pruned count | `history::a_forgotten_copy_behind_pruned_records_stops`: a fetch from behind the pruned records underflows in `records_since` |
| The hub answers a fetch from any count it has, ignoring the digest | `history::record_bodies_keep_pending_drops_named_after_hub_rollback` and six other race tests |
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
A session starts with no records and nothing dropped.

### Actions

Fields mirror the constructors of `EnvStep` and `SyncStep` in `formal/Musubi/Model.lean`,
and of `SAction` in `formal/Musubi/SupersedeExec.lean`, extended by `CAction` in
`ContractedExec.lean`. `node` is a node index below
`nodes`. Op and object ids are naturals. Sets are arrays, compared as sets. Records are an
array of sets, compared in order.

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
| `advance` | `node` | `SyncStep.advance`, or `ContractedRStep.advance` through every image of a dropped known head |
| `advancePrepared` | `node`, `records` | `ContractedRStep.prepared`: announced records contract the whole frontier and become applied/held in the same backend boundary |
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
| `hubPushReject` | `node`, `ops`, `objs`, `expected`, `new`, with `applied`, `dropped` for packet-specific checks | `SyncStep.hubPushReject` plus the contracted rejection guard; a matching, closed, acceptable contracted packet cannot be rejected |
| `hubPushIncomplete` | `node`, `ops`, `objs`, `expected`, `new` | `SyncStep.hubPushIncomplete` |
| `hubFetch` | `node`, `base`, `haves` | `SyncStep.hubFetch`: replies with a `head`, an `ops` and an `objs` message |
| `crashHub` | none | `SyncStep.crashHub` |
| `hubForget` | `ops`, `objs` | `SyncStep.hubForget` plus the retained-body guard: the kept subset closes the current head and preserves historical operation bodies, while historical-only objects may be lost |
| `hubRegress` | `seq` | `State.regress`: `seq ≤ hub.seq` and the target is closed; head, sequence and records return to that entry. Recovery from an incomplete target is an explicit environment-chosen remake |
| `abandon` | `node`, `ops` | `SStep.abandon`: `ops` are below `node`'s heads, none of them, and not the root |
| `sendSup` | `node`, `new` | `SStep.sendSup`: a `supersede` message with the records `node` took, its dropped set, and `new`, the head of the push it rides on, which no record `node` took drops |
| `sendD` | `node` | `SStep.sendD`: a `dropped` message with the hub's records, and how many of them it has pruned |
| `adopt` | `node`, `records` | `SStep.adopt`: `records` were announced to `node`, which has held as many of them as the hub had pruned then (`heldPrefix`), and drop none of its heads; its dropped set gains theirs, and they become the records it took, and among those it has held |
| `hubSupAccept` | `node`, `ops`, `objs`, `expected`, `new`, `applied`, `dropped` | The original `SStep.sup` case or contracted acceptance: matching packet and records, a closed surviving new head, and every surviving expected-head image below it under the acceptance's effective dropped union; the hub records new drops |
| `hubPushRefuse` | `node`, `ops`, `objs`, `expected`, `new`, `applied`, `dropped` | no step: the `push` and a `supersede` message are in `net`, and `applied` aren't the hub's records, or `new` is among the records it remembers or what `dropped` drops beyond `applied` |
| `prune` | `count` | `SStep.prune`: the hub prunes its first `count` records, at least as many as it had pruned and at most as many as it has; the oracle requires every node to have held them, though `SStep.prune` needs no such guard for safety |

`headKind` is one of `head`, `accepted`, `rejected`, `incomplete`, `notify`.

### Replies

```json
{"ok": true, "state": <state>}
{"ok": false, "error": "casAccept: closure of 7 not stored at hub (missing op 6)"}
```

A rejected action leaves the oracle's state unchanged. The error names the action and the
guard that failed, as `"<action>: <guard>"`.

Consequences of the model that the Rust test implementations must match:

- `realize` adds an operation to `lops` and its objects to `lobj` but does not remove them
  from `sops` and `sobj`. Staging is only ever cleared by `loseVolatile`.
- `casAccept` adds an `accepted` reply for the sender and a `notify` message for every node
  below `nodes`, including the sender.
- Every push the hub accepts is a `hubSupAccept`. The plain `hubPushAccept` stays in the
  model, guarded only by `HeadOK`; once the hub has pruned any records, that needs a
  `supersede` message with the hub's records for the new head. The Rust hub never takes it.
- A node's push never names an operation a record it took drops: `sendSup` refuses one, and
  the test's `rogue_push` picks only other operations. `a_push_to_a_dropped_head_is_refused`
  checks the Rust hub refuses one anyway, while it remembers dropping it.

### State

```json
{
  "next": 5,
  "ops": [{"id": 1, "parents": [0], "objs": [10]}, ...],
  "hub": {"ops": [0, 1], "objs": [10], "head": 1, "seq": 1, "records": [[2]], "pruned": 0},
  "nodes": [
    {"lops": [0, 1], "lobj": [10], "heads": [1], "known": [1, 1], "sops": [], "sobj": [],
     "dropped": [2], "applied": [[2]]}
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
    {"msg": "fetch", "node": 1, "base": 0, "haves": []},
    {"msg": "supersede", "node": 0, "applied": [], "dropped": [2], "new": 1},
    {"msg": "dropped", "node": 1, "records": [[2]]}
  ]
}
```

Every array is sorted ascending, but records, which keep their order, each sorted. `net` is
sorted by `(msg, node, ...)`. `ops` lists every created operation except the root.
`pruned` is how many of the hub's first records it has pruned.

### Retry control

These stateless routes evaluate `RetryControl.lean`'s definitions; they do not change the
protocol session.

`headControl` takes `root`, `known` and `incoming` pairs, `own`, and `notify`. It returns whether
this head-carrying response causes an own-call `restart`, and the resulting `known` pair from
`Retry.Serial.handleHead` (`SerialReply.lean`). Notifications use filtered learning; an older own
reply can reset to the root before learning its pair.

`hubRead` takes `call` (`fetch` or `objects`), `before` and `after` hub snapshots, the answer's
`kind`, nullable `replySnap`, and nullable `replyRecs`. Each snapshot has `seq`, raw `head`, and
`recs`, an identity of the full ordered-record state. It returns `matches` from
`SysAcceptance.checkAnswer`; `HubAnswer.observed_step` proves that a passing read observation
gives the system's answer step, with the other projected fields framed.
`history::local_burst_conforms_across_a_pending_namespace` observes both shipping read handlers
before and after its pending publication. It interns raw heads and full record states by exact
equality, retaining digest differences at equal counts. The smoke cases also refuse a changed
sequence, head, record identity or answer kind. This checks the hub's read boundary, not the
complete native node observation or its wire-slot map.

`nodeGrow` checks a structural write using `NodeSys.Exec.scopeB` and `growB`, proved sound
against `Scoped` and `GrowR`. Its `before` and `after` snapshots contain a parent-first
`rawParents` table, a parent-first `parents` table of the node's labels, and an `embedding`
giving each label's raw id. It returns `beforeScoped`, `afterScoped`, `grows`, and their
conjunction, `matches`. These labels expose structure; they do not establish that the node has
an operation's body, objects or realization.
`history::independent_merges_can_reuse_a_canonical_operation` makes two real copies advance
over the same incomparable frontier, with equal supported operation metadata. It checks the
first merge's fresh raw vertex and the second merge's reuse of that very canonical id, while
each adds its own label, against the same raw numbering. A fourth copy realizes the published
merge without advancing; after another hub rollback, its own advance recreates the same merge
with no new label or raw vertex. The smoke cases also refuse a duplicate label and catch an old
embedding changing or a new raw vertex absent from the node's write. The same native case
also leaves the merge and its ancestor as physical heads through the shipping head-store
update, then observes the core removing the redundant ancestor. The complete canonical body
set stays unchanged; `rawBurst` checks the actual head, locality and plan effects. Full
node-event projection remains separate.

`history::interrupted_git_export_can_leave_aliased_operation_heads` exercises a distinct
physical boundary: a prepared Git ref transaction makes a jj bookmark export fail. After it
is released, a real merge produces an operation and its Git-exported replacement, with
different physical ids and views but the same canonical body. Re-adding only that actual
removed operation through the shipping head store leaves two aliases. The core reads the
duplicate canonical heads and merges them into a new canonical child with one parent. The
fine-suffix projection must establish physical normalization before relying on unique
canonical heads; this native case does not yet check that cut against an executable model.

`NativeEvents.observed_hs` composes the individual event bindings into the eligible system's
run, replayed by `observedRun`. Its callback invariants follow from the initial filtered
snapshot and earlier events. `Event.removed_eligible_push` connects a removed eligible push
to its exact request, packet and checks. The event bindings still include the full
`Issue`, `Handle`, `Loc`, `Idle` and `HeadRep` relations as per-call correspondence obligations;
the current oracle checks their component guards and effects, not those whole relations.
Filtering another machine's answer additionally requires its actual post-answer hub snapshot
to equal the one before, bound to that decision's record/packet frame argument.
`FineAssembly` preserves the history of eligible replies and notifications across those
events and assembles the fine-system premises from replay. It derives consumed-message
freshness from the old-effects cutoff, notification capture times and serial completed
request batches. `NativeEvents.RecordView` connects the raw applied-record identity, the
fine node's identity and original-drop custody; entry and eligibility then derive applied
stability and empty pending. The local record-effect binding derives stability of the hub's
record identity without equating raw encodings that have the same dropped-original union.

The automatic-write cutoff includes semantic writes inside busy calls and before rounds,
as well as `when_idle`. `workspaces::forgotten_working_copies_can_be_abandoned` stops at the
actual `Advanced(B)` endpoint with current records and no pending drops: although the old
singleton head is an ancestor of the target B, the endpoint is a new child of B whose
operation records working-copy replacement. Thus the full-frontier advance law applies only
when no such cleanup writes. Finiteness of automatic writes is explicit; termination of the
maintenance routines from finite user/configuration changes is not proved here.

`pushSnapshot` reads the current protocol session without changing it. It takes `node`,
`ops`, `objs`, `expected`, ghost `knownSeq`, `new`, `applied`, and `pending`, and returns
`matches` and `allDropped`. Its source guard checks policy fields from the same snapshot;
the existing `upload` query separately checks the exact operation and object closure.

`localBurst` reads that session's immutable graph and drop set, plus `node`, frozen `known`,
`kind` (`realize`, `merge`, `advance`), and actual `before`/`after` snapshots of `local`,
`heads`, and `plan`. A realization also gives `opId`. It returns `matches`, from
`EarlyEntry.Burst.stepB`, and the ranks before and after. `stepB_sound` connects that check to
the per-branch relation; `step_rank` derives the strict decrease. This checks the effects of
the shipping core's local branches, including dequeuing an entry already made local by an
adapter batch. The protocol world checks every such step with unchanged drops and applied
records, excluding prepared record-taking advances. Native assembly still must establish
the locality-completeness and ancestry correspondence laws of its adapter.

`rawBurst` checks the same executable relation without a protocol session. It takes a
parent-first `parents` table, `rawClosure`, the node-space `images`, and the same branch and
snapshots. `history::local_burst_conforms_across_a_pending_namespace` builds the table from
the real hub and node canonical stores, preserving different raw versions as different
vertices. It checks each local step while beta has dropped an ancestor of the hub's head,
then checks that the resulting pending push is accepted and both machines converge. It
requires no projection to original-operation ids.
For that actual pending push, it also checks matching expected head and records, unpublished
originals, the raw drops contraction keeps, and the exact record appended by the actual
handler. These are the packet/record fields used by `raw_pending_empty_of_fixed_records` and
`raw_noneligible_answer_frame`; the model does not require an original-history execution for
a noneligible node. Current pending-name coverage remains an adapter law: `is_superseded`
alone includes rewritten surviving names as well as dropped ones.

`rawControl` computes the core's branch from a parent-first `parents` table, `rawClosure`,
node-space `images`, raw `known`, and a `before` snapshot. The snapshot adds `staged` (operations
with bodies) and `objects` (operations whose bodies and every required object are present),
both operation ids. Unknown bodies do not establish object readiness. `primitives` supplies
`announced`, `dropHead`, `differ`, `pending`, `headIsKnown` and `newIsKnown`, independently of
the returned step. The oracle returns `choice`; with `kind` and `after` it also returns
`matches` from `EarlyEntry.Control.callB`, whose soundness is proved. Kinds are the local
burst kinds above, `fetch` and `objects`; realization also gives `opId`.

`raw_recovery_choices_and_calls_match_the_model` checks the actual core with every combination
of missing bodies and per-operation objects on a short raw chain, several local frontiers,
pending drops, and equal or different heard records. Each operation requires three objects,
so object ids cannot substitute for operation readiness. A controlled Head reply announces no
records; no concurrent command can make the fake backend decline its fresh publication tip.
The query is built before the step. Local effects and actual hub replies consumed by the core
are checked against `callB`. The real adapter's raw-name distinction is covered by the native
burst test above. Replacing a needed metadata call with idle fails this choice comparison.

`rawPush` takes raw `seq`, `head`, `expected`, `new` and `dropped`, the full record-state
comparison `recordsMatch`, and storage checks `isDropped`, `isClosed` and `descends`. It returns
the outcome and resulting hub sequence and head. `raw_push_answers_as_the_model` compares
shipping `Push::answer` with it across all storage-check answers, head equalities, empty or
nonempty drops, and four offered record states: equal, different digest, different count, or
both different. This decision-layer test does not model backend record append effects.

`retryInbox` takes `next`, a list of live `pending` request ids, a `cut`, and `action`:
`start`, `finish` (with `id`), or `disconnect`. It returns `next`, `pending`, whether a
finish `matched` a live slot, and the remaining count `old` below `cut`. List order is not
part of the production correspondence. Delivery, timeout and canceled-call cleanup all
retire a matching slot; a canceled receiver may remain in the pending map until then.

`retryFixup` takes `pending` original-operation names, `written`, `aligned`, and `action`:
`write`, or `adopt` with `nextPending`. It returns those three state fields, whether a write
`emitted` a new fix-up, and the remaining `credit` (zero or one). `aligned` means a first
current-epoch adoption has occurred. A later adoption that grows pending is refused; that
guard is the epoch premise, not a proof about arbitrary production adoption. The model's
empty-pending `write` is a core-level no-op: `NodeCore` does not call the backend's
`write_fixup` when pending is empty.

`retryPublication` takes the same `pending`, `written` and `aligned` cache fields plus
`headKnown`, equality at the local write boundary. It returns the decision/cache projection
and separate `restoring` and neutral `tip` booleans. Its returned `headKnown=false` for a write
is the helper's fresh-result reading, not native equality when a restoring body reuses the
known canonical id. Tests compare native post-write equality only when the returned head is
distinct; the decision and cache remain applicable to reuse. Retrying the helper's result
emits neither kind; a native restoring reuse may still need a neutral tip without another
learned head. The restoring-write bound does not count these additional neutral tips.

`recordEpoch` takes `current` (the fixed ordered-record identity), `applied`, nullable
`announced`, `receipts`, `stalePlan`, and `action`: `fetched`, `keepReceipt`, `adopt`,
`staleFailure`, `reopen`, `clearPlan`, or `wait`. `keepReceipt` and `adopt` also take `records`.
It executes `Retry.Records.exec`, proved sound against `Step`, and returns the state,
`adopts`, `fails`, and the recovery credit before and after. The `reopen` action clears the
announcement and plan without counting a stale-plan failure or recharging credit; receipts and
applied records persist. Its smoke cases include an ordinary reset with no stale plan, a reset
with custody and an old announcement, and an already-clear state. These are model checks; native
restart/custody behavior is exercised by the departure and empty-object-reply regressions.
The native departure regression
checks an equal-record fetch and adoption against this route: custody is consumed while the
applied list stays empty, and its effects become pending. Only after that transaction can its
readable old prefix be held as earlier applied effects. Saving a receipt alone never does so.

### Contracted ancestry

`contractedAncestry` is stateless. `parents` is an array of parent lists with every parent
numbered before its child; `expected` and `head` are in that array, and `dropped` names
originals. It returns `descends` (`Contract.belowB`), `original` (ordinary ancestry), and
`images` (the expansion of the expected head, which may contain duplicates). The supplied
graph is immutable original parent material; the route does not interpret raw canonical ids
or check the production protocol's closure, record, root-drop or surviving-head guards.

## Presence

`formal/Musubi/Presence.lean` proves which copies a hive shows when copies go away ([design.md,
"Copies that go away"](design.md#copies-that-go-away) defines copies, their work, and forgets).
musubi computes it with `Presence::merge` and `Presence::apply`
(`crates/musubi-jj/src/presence.rs`), from each operation's parents' presence alone. The chain has
three links:

1. **The incremental rule.** What `Presence` keeps for each copy present, its latest work
   that no forget saw (`UMax`), follows from the parents' alone as the Rust computes it
   (`umax_merge`, `umax_work`, `umax_forget`), and says whether the copy is present
   (`present_iff_umax`).
2. **Relational to executable.** `formal/Musubi/PresenceExec.lean` defines the rule on a
   finite history: `presentB` and `latestB`, proved to compute `Present` and `UMax`
   (`presentB_iff`, `mem_latestB`). The oracle answers with them.
3. **Oracle to Rust.** The Hegel test `presence::conformance`, in
   `crates/musubi-jj/tests/it/presence.rs`, makes histories of up to 12 operations and 3
   copies, each operation work by one copy or a forget of some, never both, as musubi makes
   them. It computes every operation's presence with `Presence::merge` and `apply`, and
   requires it to equal the oracle's, copy by copy, latest work included.
   `presence::contraction_keeps_presence` writes such a history to a canonical store, drops a
   random set of its operations by contraction, and requires each copy's latest work that a
   store works out at what each operation it keeps becomes, from the stamps and the rest of
   the history, to be the oracle's at the operation: `formal/Musubi/PresenceContract.lean`
   proves that a contraction keeps presence (`pres_eq`).

The test checks the rule, not where it is applied: that `canonical_view` publishes exactly
the present copies' workspaces, and that realizing keeps a forgotten copy's own, is for the
race catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

`history::a_trim_below_an_accepted_push_keeps_the_other_copy_present` checks another native
application boundary: abandonment discovery must identify survivors across both the saved
fetch base and the last accepted push before applying the presence-preserving contraction.
It pauses after acceptance but before advancing the base, trims the earlier history, and
checks that both copies remain present, the survivor occurs once, and the hub waits for the
other copy's acknowledgement before pruning. Reverting combined-frontier discovery fails
the presence check. `PresenceContract.pres_eq` assumes the correct survivor has been selected;
it does not prove this native discovery. The protocol pruning model's participants are fixed;
it does not prove that native presence selects the correct set of copies to wait for.

`history::a_trim_below_an_accepted_forget_keeps_the_copy_forgotten` covers the complementary
case with only unpublished work surviving. A full trim removes both accepted frontiers:
either the saved base predates this copy's newer accepted forget, or a later remote forget
became its saved base beyond its older own push. That older push is seeded after all three
copies are present, so selecting it must observably restore the forgotten copy. The native
fallback selects a maximal accepted descendant, preserving the forget in either order.
Reinstating first-base selection fails the regression. The generated
`trim_below_accepted_forget` rule and `e2e_trim_below_accepted_forget` retain independent
import and history checks. This is another obligation to select the state that
`PresenceContract.pres_eq` preserves; it adds no model transition or durability assumption.

The first changed-branch mutation campaign exposed a gap: `&&` to `||` survived the
newer-own-push case. The complementary newer-saved-base case catches it: the mutated loop
replaces that newer state with the older own push. The final campaign caught all three
executable mutants; returning a default `CanonicalOp` was unviable, and none survived.
It selected `NodeRepo::standing_for` and its changed lines with `--in-diff`, excluding
unrelated field deletions, and ran these tests in `musubi-sync`: the new regression,
`adapter::pruning_waits_for_a_copy_whose_work_was_abandoned`, and
`history::a_trim_below_an_accepted_push_keeps_the_other_copy_present`. The command used
`--package musubi-jj --test-tool nextest --timeout 40 -- -p musubi-sync -E <selection>`.
The native regression also failed under a separate hand-written first-frontier mutant.
All defects were restored before validation.

When the prepared base becomes the root, native publication must also retain the current
physical heads' per-machine Git fields. `e2e_trim_below_accepted_push` checks the unchanged
HEAD through the independent import checker; `e2e_git_change_while_taking_a_trim` changes a
bookmark after realization, and
`history::a_second_trim_keeps_git_state_with_a_cached_root_realization`
checks a detached cached root child across two trims. An earlier realization-time fallback
failed the latter two cases.
`history::a_forward_bookmark_survives_a_command_inside_a_trim_advance` places a real command
between policy preparation and native advance, without a second policy step that would
adopt the records first. Before any import or convergence it checks the published bookmark,
its local Git slots and physical Git against `Refs.realizeLocal` followed by `exportLocal`,
through the oracle. The target is the command's known forward target; the source slots are
read before advance. Exporting the incoming tip before the normalized merge fails this case.
`Refs.lean` preserves the local slots supplied to realization;
selecting and refreshing that input is native code's obligation. The normalized-base slot
selection of `AbandonRefs.publish_refines` does not cover this publication of current local
state, and the one-ref model does not model Git HEAD or its working-copy import.

The oracle's presence request and reply:

```json
{"op": "presence", "ops": [{"parents": [], "work": 7, "forgets": []}, {"parents": [0], "work": null, "forgets": [7]}]}
{"ok": true, "presence": [[{"copy": 7, "latest": [0]}], []]}
```

Operation `i` is the `i`th of `ops`, and its parents must come before it. `work` is the copy
the operation is work by, or `null`, and `forgets` the copies it forgets. The reply has, for
each operation, the copies present there, ascending, each with its latest work that no
forget saw. A presence request leaves the oracle's session as it was.

```sh
cargo nextest run -p musubi-jj -E 'test(/^presence::/)'
```

`MUSUBI_CONFORMANCE_CASES` sets the number of histories, 300 by default: each takes the
oracle about a millisecond. Dropping the check that a parent whose history has a copy's work
keeps it, which lets a forget's merge bring the copy back, fails within a few histories.

## Per-machine refs

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
   tests of the two shapes of #56, where an unguarded shortcut disagrees with jj, and of a
   criss-cross merge, where musubi must merge against the heads' closest common ancestors
   merged, as jj does, not the first of them (`firstBase_reverts`). That test's commits are
   beside each other, since jj resolves such a conflict where they are in a line.

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
  one ends as `remote_reset_without_export` says). Nor does it take an abandon: `Refs.lean`
  knows nothing of supersedes, nor `Supersede.lean` of refs. The separate combined boundary
  in `AbandonRefs.lean` now covers that successful publication and is checked by
  `realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon`
  ([Abandonment and refs](#abandonment-and-refs)). The realization
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
`MUSUBI_CONFORMANCE_CASES` sets the number. Each case runs real `jj`, `git` and syncs, so
shrinking a failure takes minutes; `.config/nextest.toml` gives the test time for it, and
starts it early, as the longest test after the protocol's conformance test.

## Abandonment and refs

`AbandonRefs.lean` is a small combined boundary model, not a model of jj or another network
protocol. Its graph uses original-operation names, the union of dropped originals and the current
published heads. Its payload map, indexed by original operation, holds one remote bookmark, the
local bookmark tracking it, the per-machine ref record and saved expected value; `.git` is machine
state. The real current names are `Contract.cid content par D`; `abstraction_unique` makes their
inverse unambiguous under #73's immutable identity invariant. The graph keeps dropped originals as
ghost state; the actual store's reachable graph contains their contracted survivors.

The boundary is:

1. `prepare_records`/`rename_for` prepares rewrites without publishing them. Realization can write
   local operations, but changes neither published heads nor `.git` and creates no canonical
   identity. The incoming realization must canonicalize back to its input.
2. If a command published since preparation, `prepare_again_if_moved` works out the rewrites
   again. `takeHeads` computes `max(exp(current heads) ∪ {incoming})` in the contracted graph, not
   the obsolete prepared graph. `adoption_composes` justifies contracting an already contracted
   prefix by the union of drops; it says nothing about delivery liveness.
3. `History.publish` adds a fresh merge with those normalized parents and performs the ref action
   `cbeside`: export beside the renamed head, merge against the normalized common base, then
   export and publish the merge, retaining both the realized payload and the merge payload under
   their operation identities and recording the exported `.git` value. `publish_refines` proves
   that every surviving ancestor of every current head remains reachable and that `CInv` holds,
   with the ref projection a `CStep.beside`. This complements #74's ordinary advance/merge
   correspondence rather than pretending that its ordinary reachable-state premise covers record
   adoption.
4. A fix-up is a fresh child whose shared view is its parent's and whose expected value is the
   pre-abandon snapshot. `fixup_retains` preserves ancestry and that ref state. The implementation
   records the snapshot in `musubi.expected`; `pending_expected` supplies it before the fix-up is
   written, under both old and renamed keys during record adoption. Treating a fix-up or merge as
   realization would incorrectly claim no new canonical IDs.

The existing real-repository race now checks these boundaries, rather than only its eventual ref
result. It verifies the fix-up attribute and unchanged shared view; unchanged heads, `.git` and
canonical ID set after unpublished realization; and the realization/canonical inverse before
publication. It numbers the old local history first and identifies incoming contracted versions by
immutable original ID, retaining the old parents as ghost ancestry. Fresh fix-up originals are
numbered too. The `refs/abandonBeside` oracle call executes `takeHeads`, `Contract.cpar` and
`publish` directly with jj's ref algebra table. It checks the unique normalized merge base against
the base whose local slot the test reads, all survivors' contracted parents, the merge's exact
parents, and the published ref slot and `.git` value. The incoming payload comes from the
canonical shared view, compared independently with the local realization; slots and expectations
are keyed by original identity, and the model selects the base slot through its own graph
calculation rather than accepting an unkeyed base argument. Immediately after publication, before
a command or convergence, it checks reachable translation injectivity, parent correspondence, and
that the only added canonical ID is the merge. Join points stop the walk into pre-hive history.
Losing `musubi.expected` makes the snapshot assertion fail; using old parents or losing the
fetched branch fails the graph comparison; incorrect ref export fails the slot/`.git` comparison.

Limits and premises are explicit. The graph retention theorem permits any finite head list; the
executable ref case requires one surviving concurrent local head and a unique maximal common base,
so it does not cover several concurrent heads or criss-cross ref merges. The expected values are
supplied snapshots, with `CStep.beside`'s resolved-target and writable export premises checked by
the oracle; their derivation from arbitrary histories remains #76. Tracking is kept as in the
existing ref test and is not part of `CInv`. Hash collision freedom and jj's merge laws remain
assumptions, pinned by the existing encoding and ref-law tests. The lock preventing a colocated
command between export and publication remains a code argument; the test observes after
`advance`'s internal working-copy cleanup. Concurrent git writes, other-workspace publication
during the lock, later store-error fallback, crashes, and ordered record liveness are outside this
boundary. The convergence search still checks translation after cache loss; this trace adds
immediate checks, not a proof of the complete translation implementation or a new intermediate
cache-loss check.

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

The walk reads direct parents, not merge bases. `History.parents` can supply effective
pre-contraction parents while an abandon is recognized; otherwise it reads the operation
store. A pending fix-up supplies known values, and its first written operation records them,
so a later walk can stop without the dropped history. The computation preserves what those
checkpoints say; proving that their producer captured the right pre-contraction value, that
renaming preserves their association, and that they survive publication/restart is part of
the composite abandonment correspondence, not an assumption discharged by this file.

`eval_congr_on` proves equality under operation renaming when the observations agree on the
followed path: the target and effective checkpoint, or the join boundary, or the ordered
parents and their targets. Its domain contains the start and is closed under the parent the
rule follows; it need not include history hidden by a checkpoint or a join. Shared target
and commit metadata give the same side function. `eval_terminates` needs a decreasing rank
on followed parent edges; `eval_stable` makes the result independent of excess fuel.
`eval_without_known_agrees` removes correct memoized answers: their correctness means that
an uncached `Computes` derivation gives that value. Thus differently populated export caches
need not be assumed equal. This is conditional on cache correctness; pending pre-contraction
values are authoritative checkpoints, not memoization justified by this lemma.
`conflicted_import_agrees_of_history` binds the two successful, present results to the slot
states and derives the old theorem's `hE`. It still needs reachable slot states, equal `L`
and `R`, and no external ref move. No-side results are computed and tested but do not bind a
slot state's `E` or claim that a skipped export establishes its invariant.

`node::git::expected_tests::expected_history_conforms_to_model` writes small operation DAGs
through jj's op store and calls the shipping `expected`. The oracle runs the proof's `eval`
on the same target observations. Commit target numbers are ordered by commit id, and side
candidates carry their real committer timestamps; the Rust test does not choose the model's
side. Cases distinguish:

- inheriting the first matching parent from always choosing a side or using the last parent,
  including a matching third parent;
- a single-parent restore from a newly merged conflict, including a changed conflicted parent
  and a resolved absent parent;
- join cuts from following private ancestors, and a logical pre-contraction parent callback
  from following rewritten store parents;
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
   - a duplicate of a copy that left, or whose hive was removed, can't join, since its
     config-id isn't its record's (`join_refuses_duplicate`);
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

## Workspace names

`formal/Musubi/Names.lean` proves that the names under which a machine shows a view's
workspaces are distinct: its own under their own names, and each other machine's as
`<prefix>/<workspace>` ([design.md, "Which workspaces are this machine's
own"](design.md#which-workspaces-are-this-machines-own)). Canonicalizing reads the names back as
machine-qualified keys, so two workspaces shown alike would be taken for one. The chain has two
links:

1. **The rule.** `assign` gives each machine, in order, this one among them, as the hub names
   every machine, the first of its candidate prefixes that is free: its name, if no other machine
   has it, then `name-1a2b`, `name-1a2b3c4d`, and that with ever more dashes. A prefix is free if
   no machine before took it and no name of this machine's own starts with it and `/`. One is
   always free (`choose_free`), and so the names are injective, whatever the machines and the
   names of this machine's own (`localName_injective`).
2. **The code.** `workspaces::display_names` makes the same choices. The Hegel test
   `workspaces::tests::names_conform`, in `crates/musubi-jj/src/workspaces.rs`, draws up to five
   machines and three names of this machine's own from names, suffixes and names of its own chosen
   to clash, this machine among the machines, and requires each machine's prefix to be the one the
   oracle's `assign` gives it, and the name `workspaces::local_name` gives each machine's
   workspaces here, this machine's own names among them, to be the oracle's `localName`, and all
   of them distinct. Letting a machine take a prefix an earlier one took, or one that starts a
   name of this machine's own, fails it. `longer_names_where_shorter_clash` pins the cases the
   rule before this one named alike, which `Names.lean` checks with `#guard`.

The test checks the rule, not where musubi applies it: that `local_names`, `canonical_view` and
`local_view` pass it every machine the history has known, this one included, and all of this
machine's own names, including those in the op heads a realization is merged with, is for the
race catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

The oracle's names request and reply:

```json
{"op": "names", "machines": [{"name": "mac", "suffix": "aaaa1111"}, {"name": "mac", "suffix": "aaaa2222"}], "own": ["mac-aaaa2222/x"], "me": {"name": "mac", "suffix": "aaaa2222"}, "workspaces": [{"machine": 0, "workspace": "default"}, {"machine": 1, "workspace": "mac-aaaa2222/x"}]}
{"ok": true, "prefixes": ["mac-aaaa", "mac-aaaa2222-"], "names": ["mac-aaaa/default", "mac-aaaa2222/x"]}
```

The machines go in the order `display_names` takes them, their keys' order, each a key's name
and suffix, this machine, `me`, among them, and `own` holds the names of this machine's own.
`workspaces` are the workspaces to name, each a machine's index and the workspace's name on
it. The reply has each machine's prefix, in the same order, and each workspace's name here
(`localName`). A names request leaves the oracle's session as it was.

### Workspace bindings after a full trim

`a_full_trim_below_unpublished_work_keeps_workspace_owners` checks native operations whose
parents jj erased before musubi saw them. The stored context records namespace evidence, not
replacement ancestry or a new presence transition. Existing Names conformance checks render
its canonical keys; existing Presence conformance checks the fix-up WORK and FORGET steps.
The race checks both machines' resulting workspace ownership after translation-cache loss
and a delayed command using the unstamped native source. The separate
`a_trim_does_not_reserve_a_forgotten_copys_workspace_name` checks reuse of a foreign alias.

`a_full_trim_keeps_a_forgotten_receivers_private_workspaces` checks the receiving side when
contraction removes every shared basis for its own bindings. It merges actual native heads'
workspace slots against their actual native bases, using jj's existing slot rule. Local
ownership evidence reserves private names through fix-up realizations and native descendants;
it is stripped from canonical operations and never changes Presence. The race checks an
owned slash name that collides with a peer prefix, interrupted receipt, translation-cache loss,
unsnapshotted work, publication by the next native command, and explicit workspace removal.

`restoring_an_older_view_does_not_inherit_private_workspace_ownership` restores a real native
view where the private owned name was still a foreign alias. It checks the canonical binding
before further native commands and the peer's resulting workspace names. Private-name
reconstruction follows restore and revert sources and stops at native join boundaries.

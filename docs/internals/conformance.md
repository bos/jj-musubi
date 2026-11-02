# Conformance between the Lean models and the code

The Lean models in [formal/](../../formal/README.md) prove properties of musubi's designs. This
document says how each is tied to the code that implements it. Each tie is a chain: the model's
own definitions, where they compute, or an executable form of the model, proved to agree with it;
and a Hegel property-based test ([testing.md](testing.md)) that runs the real code and requires it
to agree with the model: step by step for the protocol and the blob receiver, and operation by
operation, law by law or merge by merge for the others. The Lean side runs as the *oracle*, a
program the tests send JSON requests to.

| Model | Code | Test | Section |
| --- | --- | --- | --- |
| The sync protocol ([protocol.md](protocol.md)), with supersedes | `crates/musubi-core` | `conformance`, through the oracle | [The claim](#the-claim) to [Wire format](#wire-format) |
| `Presence.lean`: which copies a hive shows, and `PresenceContract.lean`: how a contraction keeps it | `Presence`, and the stamps of `Contraction` | `presence::conformance` and `presence::contraction_keeps_presence`, through the oracle | [Presence](#presence) |
| `Refs.lean`: per-machine refs | jj's import and export, and musubi's realization | `ref_laws` (the laws the model assumes), and `refs` and `view::tests`, through the oracle | [Per-machine refs](#per-machine-refs) |
| `AbandonRefs.lean`: survivor graph and one ref | record adoption, fix-ups and publication in `NodeRepo` | `realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon`, through the oracle | [Abandonment and refs](#abandonment-and-refs) |
| `Expected.lean`: conflicted-ref history | `node/git.rs::expected` | `expected_history_conforms_to_model`, through the oracle | [Expected values from history](#expected-values-from-history) |
| `Chunks.lean`: chunked blobs | `BlobStore::receive` | `receive_follows_the_prefix_model`, through the oracle | [Chunked blobs](#chunked-blobs) |
| `Names.lean`: the names other machines' workspaces show under | `workspaces::display_names` | `workspaces::tests::names_conform`, through the oracle | [Workspace names](#workspace-names) |

## The claim

With successful storage calls, every behavior of the Rust protocol core, at the level of
abstraction of the model, is a behavior of the Lean model. [Storage errors](#storage-errors)
add representable prefixes and explicit limits to that correspondence. The Lean safety theorems
hold for every reachable model state, so
they hold for every state the Rust core reaches. A run in which the hub goes back, or the hive
is made again, is a behavior of the extended model of `formal/Musubi/Regress.lean`, and the
weaker invariant proved there holds in it. Every run, with `jj op abandon` and the supersedes
that publish it, is a behavior of the system with supersedes of
`formal/Musubi/Supersede.lean`, over each operation's original, and `SInv` holds in it.

The chain has three links:

1. **Relational model to executable model.** The proofs are about a relational model: `Step`
   says which transitions are allowed, over states that need not be finite.
   `formal/Musubi/Exec.lean` defines `execStep` on finite states. `exec_sound` proves that
   whenever `execStep` accepts an action other than `hubRegress`, the corresponding
   relational `Step` exists between the abstracted states, and `exec_rsound` that whenever it
   accepts any action, an `RStep` of the extended model does. The executable model therefore
   never accepts anything the proofs don't cover. `formal/Musubi/SupersedeExec.lean` adds
   the hub's records and each node's dropped set: `sexec_sound` proves every action
   `sexecStep` accepts an `SRStep` of the system with supersedes, or no step.
2. **Executable model to oracle.** `formal/Oracle.lean` is a thin JSON wrapper around
   `sexecStep`, built by `lake build oracle`. It contains no protocol logic of its own.
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
| Hub records, node `nodeD` and the records it took last | `FakeHub::records`, `FakeRepo::dropped` and `applied` |
| Every list of records a node has taken, `held` | `FakeRepo::held` |
| Hub `pruned` | `FakeHub::pruned`, which keeps every record, as the model's `recs` does, those pruned standing for their count and digest |
| `net`, the set of every message sent | the test's network: a set, so any message can be delivered any number of times, or never |

`lops` and `lobj` are a node's local operations and objects, and `sops` and `sobj` what it
has staged. Operations are their originals, as in `Supersede.lean`: dropping renames nothing
here, so the test's storage keeps every operation it had, dropped or not, and checks closure
and ancestry over all of them. A record state's digest is the index of its records in a
table of every list of records seen, so equal digests are equal records. The jj-specific parts of a real node (canonicalization, realization, bundles) are
not covered by this link; the jj example tests and the generated end-to-end tests cover them
([testing.md](testing.md)).

## Storage errors

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
| `NodeCore` advances through the fake repo | `advance`; a real repo may also merge ([below](#a-repository-advance-that-also-merges)) |
| The hub handles `Fetch` | `hubFetch`, then `sendD`: its reply carries the hub's records |
| The hub handles `GetObjects { for_ops: S, haves: H, .. }` | `hubGetObjs` with `objs(S) \ H` |
| The hub handles `Push` | `hubPushIdem`, `hubSupAccept` then `sendD`, `hubPushReject`, `hubPushIncomplete`, or `hubPushRefuse` |
| `NodeCore` takes in a `Refused` reply | nothing |
| A node restarts | `loseKnown` (its staged files survive; `known` does not) |
| A node restarts while taking in a `Fetched` reply, after staging its operations and before staging its objects (test rule) | `learn` if its head is newer, `recvOps`, then `loseKnown` |
| The hub restarts | `crashHub`; the hub forgets what each node said it took |
| The hub goes back (test rule) | `hubRegress`; the hub forgets what each node said it took, as a restart does, and how many records it had pruned goes back too |
| The hub prunes (test rule, half the time after a `quiesce`, and once after each case's final one): `hub::prune`, which prunes every record once every node's last `Fetch` or `Push` said it took them all | `prune` with the count, if it pruned any |
| The hub forgets every operation and object outside `closure(head)` (test rule) | `hubForget` with what it keeps |
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

The original-ancestry guards above are a known limit of this harness, not a guard on every
accepted production push. `history::a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup`
uses real stores, interrupted adoption and hub rollback to reach an accepted push whose
expected head is not an original ancestor of the cached fix-up. The pending drops contract
that head into ancestors of the fix-up. Both real adapters allow this, while `SStep.sup`
requires original ancestry. The trace then converges; narrowing the production guard to fit
the model would change that valid behavior.

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

## A repository advance that also merges

The core harness's `FakeRepo::advance` updates heads only. `NodeRepo::advance` can also call
jj's merge: a colocated repository exports and publishes the merge beside concurrent heads;
a non-colocated repository merges when the working-copy cleanup loads the repository. This
is a composite transition, not a single `SyncStep.advance`. The core harness alone does not
check this correspondence.

`Safety.lean`'s `advance_merge_parents` identifies the intermediate heads as the incoming
`known.head` plus every old head not below it. `advance_merge_refines` proves that when this
concurrent set is nonempty, advancing then merging that exact set is a reachable two-step run:
`SyncStep.advance` then `EnvStep.merge`. It retains every local operation, adds exactly one
canonical operation and leaves the hub and network unchanged. The intermediate head set need
not be physically published: in a colocated repository the git lock excludes a jj command's
publication while the realization and merge are exported and the merge alone is published.
The returned local id still represents the incoming operation, not the merge.

`translation::advance_with_concurrent_heads_refines_advance_then_merge`, in
`crates/musubi-jj/tests/it/translation.rs`, supplies the independent observation. It creates two
local heads beside an incoming history in real colocated and non-colocated repositories,
replays their observed canonical parent graphs through the Lean oracle, and compares the raw
published head and its parents with the oracle's advance followed by merge. It reads those
heads after `advance` returns, before any subsequent jj command or head-merging helper. It
checks the returned realization's identity, the retained history and the exported local bookmarks
too. The graph projection omits commit objects and ref semantics, which the object tests and
refs conformance cover. Removing a concurrent parent fails the exact-parent comparison. The observation is of
the final graph: cleanup inside `advance` can merge heads before it returns, so this test cannot
detect a realization temporarily published apart and then merged there. Intermediate publication
visibility relies on the lock/export code argument above, not on an observer at that boundary.

When taking abandonment records, the comparison is over the renamed history:
`max(images(old heads) ∪ {incoming})`, not the old local names. The existing race
`realization_beside_a_fetch_keeps_the_fetch_while_taking_an_abandon` now independently contracts
the old canonical heads, computes this maximal set, and requires the raw published merge to
have exactly those parents and no dropped ancestor, before any subsequent command can merge it.
It also checks the fetched ref in git and subsequent convergence. This is a concrete check of the
normalization boundary, not a proof combining contraction, refs and the protocol; that remains
[#77](https://github.com/bos/jj-musubi/issues/77).

`check_mergeable` refuses an unsafe merge before publishing the realization. The race
`root_parent_merge_bug_is_explained` checks both the refusal and that the affected machine's
raw heads stay unchanged. If the later unpublished merge fails (a store error, a jj bug, or
record-taking changing the merge base), `advance` publishes the advanced head set instead,
and its working-copy cleanup tries the normal merge path. That path may fail and return an
error after the advance; it must not be described as an atomic rollback. The fallback's
store-error branch is not fault-injected by these tests. A later working-copy repair, when
needed, is another operation-creating action, not part of this two-step lemma.

`noFeedback` says that a modeled sync step, realization included, leaves the operation universe
unchanged. It does not say that every call made during a sync is such a step. jj's legitimate
merge of concurrent work is an `EnvStep.merge`, whether a jj command or musubi invokes it;
that merge is published to the hub normally. Once the hive has converged, there is no
concurrent head set to merge (`converged_quiescent`), so realization does not cause an echo.

## Liveness

The real repository also has an adoption boundary the core harness's atomic fake cannot
reach. `history::a_sync_stopped_while_taking_an_abandon_the_hub_then_loses` stops immediately
after advancing to a head whose records drop the machine's old head, with and without a
restart, then makes the hub lose those records. Before the fix, the machine repeatedly pushed
the renamed head without the drop and received the same rejection. It now holds the records
in the save that counts the renaming, before the heads move. The test requires that machine
alone to make one accepted push carrying the drop and reach idle with matching records;
another machine cannot conceal the failure by publishing first. A control keeps the records
on the hub and requires no push.

`history::taking_an_abandon_resumes_where_it_stopped` stops the shipping taking path at
four finer boundaries: the hold save fails before writing; it succeeds but heads have not
moved; a new head was added but old heads remain; or heads have moved but workspaces have not.
It resumes the same handle for an error or reopens for a crash, including loss of the
translation cache. A saved exact move intent supplies the old heads and their images,
target heads and canonical facts. It preserves a newer command or abandonment made before
recovery, including a second cache loss before late reparenting finishes. A dropped merge
head expands to multiple parents, all of which must be recovered. The test checks held
records and drop state, raw
canonical heads, the singleton working copy's recorded operation, bounded progress without
another machine, and final convergence. The merge case does not require a workspace recorded
at a multi-image operation to move to one image; that pre-existing case has no unique rewrite.
The hooks stop the shipping path; no saved metadata is manufactured. This pins the concrete
recovery boundaries, not the full retry/response refinement, which remains
[#78](https://github.com/bos/jj-musubi/issues/78). The adapter clears its staged graph and
ancestry cache when `advance` changes record state, as a separate `Adopted` step used to do,
even if a later part of the advance fails.

`AsyncLiveness.lean` separates two events hidden by an atomic push/fetch exchange.
`bad_accept_before_reply` proves that acceptance makes the pusher good while its `known`
still names the old head. `measureR_delayed_learn` proves descent for learning a strictly
newer pair from the current hub history, even if it is no longer the latest pair.
`lost_acceptance_and_delayed_fetch_make_progress` drives the core and oracle through both:
it withholds an acceptance reply, checks descent immediately at the hub, recovers through a
new fetch, advances the hub again, and delivers a fetch that names the intermediate head.
It checks descent before final quiescence, so convergence alone cannot hide either boundary.

`settling_hub_stabilizes` proves that a reachable `SettlingStep` run eventually has a fixed
hub. It permits delayed consistent replies, bookkeeping and local policy steps; each hub
movement lowers `mBad`. The implementation-to-suffix correspondence is not yet established:
fix-ups written before a failed push, obsolete-history recovery and stale ordered-record
adoption still require their finite-disturbance arguments. This is partial progress on
[#78](https://github.com/bos/jj-musubi/issues/78), not full asynchronous convergence.

The transport contract additionally checks canceled calls and replies delayed beyond a
fresh exchange, and repeats a completed reply. A deterministic unit test of the shipping
stream receiver, `replies_only_complete_the_matching_pending_call_once`, injects the raw
obsolete/duplicate frames while a later request is pending. This pins the stream client's
own ID lookup and consume-once rule, which service-side reply inboxes can otherwise mask.
Neither test forbids a still-pending request's reply arriving after a hub remake.

The receiver unit also compares each injected reply's matched slot and remaining pending
ids with `Retry.Inbox.finish`, through the `retryInbox` oracle route. The Lean model proves
that only finitely many pre-cut slots can be consumed, even with infinitely many unmatched
duplicates. Request allocation and disconnect are read from the implementation, rather
than exercised by this unit; the correspondence assumes the `u64` request counter is not
exhausted. It does not bound notification delivery or force a live old call to finish.

`history::op_abandon_replicates` additionally checks the production fix-up cache against
`Retry.Fixup.write`, through `retryFixup`. After a supported jj abandon, it writes the
fix-up without publishing a push, retries, reopens `NodeRepo` from disk and retries again.
The first call creates an operation; both retries keep the same heads and pending record.
After the existing sync converges, adoption clears the modeled pending drops. Disabling the
`fixup_written` guard makes the first retry create another operation and fails this check;
omitting the marker when saving records fails the retry after reopening.
The model bounds writes by one within an epoch whose pending originals shrink after its
first current adoption. This test pins cached reuse and reopening, not that monotonicity
premise or eventual entry into such an epoch. Raw hub ids can change during adoption and
cannot serve as the immutable names in that premise. The causal connection from a cached
fix-up to `SPStepR` is still open, as is the final fair-retry convergence theorem.

`RecordStability.lean` derives eventual full-record-list and pruned-prefix stability from
bounded immutable original drops and cessation of rollback, without assuming that hub heads
stabilize. `sexec_record_control` reads the append/unchanged and pruning effects directly from
the existing executable rules. `sexec_record_prefix_stabilizes` composes those effects and
their pruning bound; it still has the original-drop bound as a premise. These are derived
counting theorems over existing record constructors, not a new transition system. They do
not extend `sexecStep` to the contracted acceptance above. The module also derives pending
shrink for record extensions from `adoptR`, and a common stabilization cut for finitely many
monotone bounded node drop sets; it does not prove every runtime adoption is an extension.
`eventual_original_chain` composes a record cut with `Contract.Below` on an immutable
birth-parent graph to recover an eventual reflexive ancestry chain. Its surviving-head and
contracted-comparison premises still need the physical-store projection described above.

`history::a_cached_fixup_can_idle_with_a_pending_drop_until_another_machine_syncs` reaches
truthful known/head equality and matching node/hub records with a cached fix-up and a pending
original. The core returns `Idle` there; the whole hive converges when another machine
syncs. This rules out a proposed per-node exclusion invariant, not global convergence. A
complete bridge still needs to account for the other machines' outstanding work.

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
(`recordConvergedE_iff`). The oracle answers with:

```json
{"op": "measure"}
{"ok": true, "measure": [1, 0, 0, 0, 0], "rmeasure": [1, 0, 0, 0, 0, 0],
 "smeasure": [0, 0, 1, 0, 0, 0, 0, 0], "recordLag": 0, "converged": false}
{"op": "upload", "node": 0, "new": 1}
{"ok": true, "ops": [1], "objs": [10]}
```

`measure` is `(dirty nodes, Σ staleness, Σ missing ops, Σ pending advances, Σ pending
merges)`; `rmeasure` is `(nodes not good, inconsistent nodes, Σ staleness of consistent nodes,
Σ missing ops, Σ pending advances, Σ pending merges)`; `smeasure` is `(drops not yet the
hub's, Σ the hub's drops not yet a node's)` and then `rmeasure`. All compare
lexicographically; [formal/README.md](../../formal/README.md) defines their terms.
`converged` is `RecordConverged`: `SConverged` and ordered-record agreement. The harness
compares `(smeasure, recordLag)` lexicographically. Dropped-set progress may increase record
lag; an adoption that changes only applied records must decrease it.

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
the record lists; this argument does not prove collision resistance. Delivering a fresh
honest fetch and scheduling the policy fairly remain assumptions; the asynchronous
reply/retry bridge is tracked in [#78](https://github.com/bos/jj-musubi/issues/78).

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

The measure falling shows that the policy's steps are ones the termination proof covers, not
that each is a `PStep`. Hub-only work, such as storing a rejected push's upload, changes
nothing the measures read.

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

`contraction_does_not_recreate_a_dropped_id` is the minimal store counterexample. Removing the
immutable original parents makes it fail by exact id equality; it is the Rust counterpart of
`Contract.equal_content_recreates_id`. `peer_cannot_put_two_versions_of_one_original_in_a_history`
checks refusal before rewrites. The hub test
`contraction_keeps_a_survivor_publishable_and_refuses_replayed_origins` checks that a survivor
remains closed and publishable, and that a hash-valid alternate version of a dropped original
is refused, including after reopening. `original_parent_encoding_is_pinned_and_cannot_be_supplied_by_a_caller`
pins the new encoding and fresh-write enforcement.

`translation::repeated_restores_keep_distinct_identities_when_contracted` reaches the content
collision through real jj commands: repeated restores with an intervening describe and equal
operation timestamps. It checks canonical contraction, jj's own local-id coalescence, refusal
before any pending drops, and recovery by integrating the old head. It cannot recover the
user's abandon intent from identical local bytes; the protocol proofs assume that detection
has supplied the intended original set. The combined abandonment/ref refinement is tracked
separately in issue #77. The `import` fuzz target varies the reserved attribute with a valid
content hash so that origin validation is reached.

`taking_an_abandon_preserves_original_identity_after_cache_loss` covers a remote record and
work created on the old history: both local rewrite paths keep durable canonical markers, and
rebuilding the translation cache returns the same originals. `coalesced_history_after_gc_is_refused_before_publishing_drops`
covers jj collecting the old local evidence before another command and sync: no drops are
published when the original intent is no longer recoverable.
`fresh_equal_time_operation_is_not_an_old_counterpart` checks that unpublished work with the
same time metadata as an old operation keeps its view after an abandon, even after jj gc,
cache loss and restart. Removing the durable evidence too causes a refusal before any drops.
`node::originals::tests::torn_rows_never_establish_an_identity` checks partial rows followed
by a complete append, and preserves multiple fingerprints per original and shared
fingerprints across originals. The existing repeated-abandon
restore tests also exercise a translation walk resuming on an old unmarked jj rewrite after
`check_abandon` moved the heads: that source keeps its established canonical correspondence.
`a_delayed_child_of_a_jj_rewrite_keeps_its_origin_after_cache_loss` checks that the source alias
survives cache loss and restart, that retaining a counted step while losing its head move
completes the physical rewrite, and that a delayed child keeps the original identity afterward.
`torn_steps_lose_only_themselves` generates the source rows too: no partial counted block can
silently omit an alias that records depend on. These local translation and crash boundaries
are tested runtime obligations, not additional theorems of the abstract protocol model.

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
| Node realizes an operation before its parents | invariants and conformance |
| Node realizes an operation before its objects arrive | invariants and conformance |
| Node learns a head whose `seq` equals the one it knows | conformance only: harmless, but not a model step |
| Node's `Push` uploads every operation since the root, not since `known.head` | conformance only: not `upOps` |
| Node with two heads pushes one of them before merging | conformance only: the push raises the other nodes' staleness, and the measure rises; the run still converges |
| Node that believes a head at the largest sequence number doesn't start over when its own request's reply says otherwise | `nodes_recover_from_false_replies`, and rarely `nodes_recover_from_wrong_replies` with real repositories: no honest hub gets there, and the node never converges |
| Hub accepts a `Push` whose records aren't its own | `a_push_without_the_hubs_records_is_refused` |
| Hub accepts a `Push` with its records to a head it dropped, or that the push drops | `a_push_to_a_dropped_head_is_refused`; rarely conformance, for the second, through `rogue_push` |
| Node advances to a head it dropped | `a_node_never_advances_to_a_head_it_dropped`, through the oracle (`HeadsOK`) |
| Hub ignores a `set_head` error and reports acceptance | `storage_boundaries::every_storage_boundary_recovers`: a successful reply/publication must match the actual store; the infallible tests cannot enter this boundary |

The storage-error experiment on 2026-11-02 changed only `hub::Push::answer` in a scratch
copy: replace `storage.set_head(...)?` with `let _ = storage.set_head(...)`. The countdown
sweep failed immediately. The first 50 generated cases missed it; a 500-case search found
and shrank it to six actions: make and push an operation, take a step, make a concurrent
operation on the root, merge, then exchange with a pre-effect failure at call 15. The hub
reported acceptance without installing that head, disagreeing with the oracle. Hegel's
stored failure replay failed again in 0.19 seconds; restoring the shipping handler made
the same six-action scenario pass. The catalogue sweep makes this boundary independent of random frequency.
The shared checkout was never mutated. This historical replay belongs to the original
`7b4ababc` snapshot (Hegel 0.50.2); later protocol/generator changes need that snapshot to
replay its draws. Its attribute is:

```rust
#[hegel::reproduce_failure("AXichYwxDgAgCAM54uTCJ/z/GyVBFmMjA9fk0i7Lm+TzgkGHIy60HwjhSvwWZTHexSiwAY98AWg=")]
```

"Invariants" is `protocol_invariants`, which checks the safety properties directly on the Rust
state, without the oracle. The random cases rarely reach the last three, which need a node behind
the hub's records to push from its head, a push to a head the hub dropped, which no node makes,
and a hub that goes back to a head a node dropped, so fixed tests make them. `just mutants` runs
cargo-mutants over `hub.rs` and `node.rs`; the property and conformance tests should kill every
mutant it makes.

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
and of `SAction` in `formal/Musubi/SupersedeExec.lean`. `node` is a node index below
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
| `hubForget` | `ops`, `objs` | `SyncStep.hubForget`: the hub keeps only `ops` and `objs`, which must be among what it stores and hold `closure(head)` |
| `hubRegress` | `seq` | `RStep`'s `State.regress` (`Regress.lean`), the hub going back: `seq ≤ hub.seq`; `head := hist seq`, `seq := seq`, its records, and how many of them it had pruned, go back to what they were then, and nothing else changes |
| `abandon` | `node`, `ops` | `SStep.abandon`: `ops` are below `node`'s heads, none of them, and not the root |
| `sendSup` | `node`, `new` | `SStep.sendSup`: a `supersede` message with the records `node` took, its dropped set, and `new`, the head of the push it rides on, which no record `node` took drops |
| `sendD` | `node` | `SStep.sendD`: a `dropped` message with the hub's records, and how many of them it has pruned |
| `adopt` | `node`, `records` | `SStep.adopt`: `records` were announced to `node`, which has held as many of them as the hub had pruned then (`heldPrefix`), and drop none of its heads; its dropped set gains theirs, and they become the records it took, and among those it has held |
| `hubSupAccept` | `node`, `ops`, `objs`, `expected`, `new`, `applied`, `dropped` | `SStep.sup` with the `hubPushAccept` it rides on: a `supersede` message of `applied`, `dropped` and `new` is in `net`, `applied` are the hub's records, and `new` is neither among the records the hub remembers nor among what `dropped` drops beyond `applied`; the hub adds a record of what `dropped` drops that it doesn't, if any |
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
and the `git` remote, such as `x@git`), and every `jj` command imports any difference as a change
made with git. musubi keeps that record per-machine ([design.md, "Per-machine state in a
replicated view"](design.md#per-machine-state-in-a-replicated-view)). `formal/Musubi/Refs.lean`
proves that an import changes a bookmark only if git moved the ref, whatever musubi realizes,
assuming jj's ref merge obeys three laws (`RefAlg`); that musubi realizes a merge as jj merges it;
that once musubi writes a conflicted remote bookmark's expected value, every machine's import
resolves it alike, a restore of the conflict included; and that `jj undo` and `jj op restore` keep
the invariant where jj's export can write what they restore, or restore a conflicted remote
bookmark ([formal/README.md, "Per-machine refs
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
   | A `jj` command moves `x`, `y` or `t` (`jj bookmark set`, `jj bookmark delete`, `jj tag set`, `jj tag delete`), or changes nothing (`jj status`) | `jjImport` of every ref; `jjExport` of every ref if that changed the view; then, if the command moves a bookmark, `set` and `jjExport` of every ref |
   | `y` moves in `origin`, and `jj git fetch` fetches it | as a `jj` command, whose change is `RStep.fetch` |
   | A `jj` command at the operation before the latest action (`--at-op`) moves `x` or `y`, and `jj status` follows | on the older operation's slots, `set` and `jjExport` of every ref (it imports nothing); then `TSlot.merge` of the head with them against the older operation's, in the order of the merge operation's parents, then as a `jj` command that changes nothing |
   | `jj undo`, or `jj op restore` to the operation before the latest action or to the one both machines last synced at | as a `jj` command that imports; then, if it restored an operation, which its description names, every ref's slot but `K` from that operation's view (`restoreLocal`, `restoreRemote`), the expected value the head's (`restoreC`), and `jjExport` of every ref |
   | The other machine moves `x` or `t` or fetches `y`, and both sync, with `refs/heads/x.lock` held here or not | `LStep.advance` of `x`, `y` and `t` and `CStep.advance` of `y@origin`, with this machine's expected value, then `jjExport` of every ref, except where the lock makes `x`'s update fail, then `exportConflicted` of `y@origin`; nothing if there was nothing to realize |
   | The other machine moves `x` or `t` or fetches `y` before it has this machine's latest operations, merges them with its own as it syncs, and this machine syncs | the other's operation realized from the slots both last synced at, and `realizeMerge` of it with the head, against those slots, in the order of the merge's parents, which is `TSlot.merge`; then the exports, as above. Two fetches that moved `y@origin` to different values merge to a conflict, whose expected value is its side; a conflict from one parent keeps that parent's, and a merge that resolves it has the remote bookmark itself |
   | Either of the last two, with a `jj` command here that moves `x`, `y` or `t` or fetches `y` after the other machine's operations and before this machine syncs | the command, as above; then the other's operation realized as above from this machine's slots before the command, and `jjExport` of every ref, against `.git` as the command left it, then `exportConflictedBeside` of `y@origin` against the command's record; then `TSlot.merge` of the two against the slots before the command, in the order of the merge's parents, and the exports, as above, with the merge's expected value: `LStep.beside` and `CStep.beside`. The other machine then syncs |

   The mapping follows what jj does. jj imports `x@git`, `y@git` and `y@origin` in that
   order, and the two refs of `y` share the bookmark, so an import of one that sets the
   bookmark is a `set` of the other. jj exports only a transaction with changes, which is
   why a `jj` command that imports nothing exports nothing, and a failed export waits for a
   command that changes something.

   After every action the test requires, for each ref, the bookmark, the remote bookmark
   and its tracking state, its `git_refs` entry and the git ref to be the model's, `LInv`
   (`CInv` for `y@origin`) to hold, and the repository to have one op head. A restore that
   isn't `Restorable` may leave a record behind `.git` until the next import, which only it
   may (the ghost `restored`). The test also checks that the other machine's command left its
   bookmarks and tag as the model says, its import resolving a conflicted `y@origin` as this
   machine's would (`conflicted_import_agrees`), so that its own refs reverted nothing
   either, and that its `.git` has the same expected value of a conflicted `y@origin`. Beside
   it, `undo_of_an_unexportable_bookmark_conflicts_it` shows `restore_reverts` with jj alone,
   and `restore_of_a_conflicted_remote_bookmark_resolves_alike` drives the state machine
   through `restore_import_agrees`: concurrent fetches conflict `y@origin`, a fetch here
   settles it, this machine restores the conflict, and both machines' commands resolve it to
   the fetched value. `realization_beside_a_fetch_keeps_the_fetch` is a run Hegel found:
   the other machine fetches a term of a restored conflict before realizing the restore,
   and the merge keeps its fetch, so musubi must not write the conflict's expected value to
   that machine's `.git` for the realization alone.
   `realization_beside_a_fetch_here_keeps_the_fetch` is the same on this machine, against the
   model (`beside_keeps_fetch`): the other machine merges its own operation with this one's
   restore of a conflict, keeping it, while this machine fetches a term of it.
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
  `git_refs`. Where jj's export can't write the restored bookmark, as for the root commit or
  a conflicted local bookmark, the record stays behind `.git`, and the next import takes the difference for a
  move made with git, though jj itself made it: a bookmark at the root, moved and undone,
  becomes a conflict (`restore_reverts`, and the test
  `undo_of_an_unexportable_bookmark_conflicts_it`, which runs only jj). That is jj's
  behaviour: no musubi step takes part, and other machines, which realize only the restored
  bookmark, keep their records. `jj undo` also refuses to undo a merge operation, or a
  realization of another machine's operation, which jj attributes to that machine's
  workspace.
- **Conflicted remote bookmarks.** Two machines' fetches merge to a conflicted `y@origin`,
  whose expected value is a side, which musubi writes to `.git`; a machine's next import
  resolves it to that side, as every other machine's does. A restore that brings such a
  conflict back writes nothing, so the restoring machine's `.git` keeps the value from before
  it, which is the restore's expected value, and every other machine keeps or writes that
  instead of the side. The slot model takes the expected value as given with each operation;
  this test computes it from the parents' as `export_conflicted_remote_bookmarks` does, and
  checks that both machines' `.git`s have it, but makes no joins. The separate history
  conformance below checks the shipping computation, including its join boundaries.
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
only a contiguous prefix ([protocol.md, "Chunked blobs"](protocol.md#chunked-blobs)). The chain
has two links:

1. **Refinement.** `Chunks.receive` is the prefix receiver, and `PStep` its steps: a chunk
   delivered with any claimed length, and a sweep of the partial blob or the stored one.
   For an injective hash, as `stored_identical` assumes, each is a run of the model's
   `CStep`s (`preach_abs`): a chunk taken is `recv`, one dropped no step, a hash match is
   `finishOk` then `crashRecv`, a mismatch is `crashRecv`, a chunk of a stored blob is
   `finishStored`, and the sweeps are `crashRecv` and `evict`. So `stored_identical` holds
   of it. A sender that resends from the prefix it reports finishes (`prefix_finishes`).
2. **The steps.** The Hegel test `receive_follows_the_prefix_model`, in
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

| `BlobStore` | Model |
| --- | --- |
| `partial/<id>` | `PState.pre` |
| `complete/<id>` | `PState.store` |
| `Received::Prefix(n)`, `Received::Complete` | `some n`, `none` |
| `sweep` of the partial blob, of the stored one | `sweepPartial` (`crashRecv`), `sweepStored` (`evict`) |
| A chunk in the middle of a write when the process dies | `inject` of the part written, claiming a length past it |

A model without `evict` fails the test, since the code sweeps stored blobs.

Not covered: a blob the receiver adds itself (`insert_file`, `insert_bytes`) during a
transfer, which only the uploading machine does; a stored blob a power cut left torn, which
`get` removes; and two receives of one blob at once, which the hub and the downloader don't
make. The proof's sender resends one chunk at a time, where musubi's senders send windows of
eight. A window from the prefix the receiver last reported starts with the proof's resend,
and the rest are chunks the safety proof allows any time. A window from a stale prefix, the
receiver having started over or swept the blob, puts nothing in the receiver, and its
replies give the real prefix: the test's extra resend.

```sh
cargo nextest run -p musubi-sync -E 'test(/^blobs::/)'
```

The test makes 200 cases, a few milliseconds each, one oracle serving them all. Dropping the
check that the prefix is the length the chunk claims, so that a blob is stored when a chunk
claims one byte too few, fails it at once, as does checking the hash a byte early.

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

The test checks the rule, not where musubi applies it: that `local_names` and `canonical_view`
pass it every machine the history has known, this one included, and this machine's own names is
for the race catalogue (`crates/musubi-sync/tests/races/forget.rs`) to check.

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

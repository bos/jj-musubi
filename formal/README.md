# Lean model of the musubi sync protocol

This directory holds machine-checked Lean 4 models of the following. Hive, node, hub and the
other terms are those of [design.md, "Vocabulary"](../docs/internals/design.md#vocabulary).

- The sync protocol of [protocol.md](../docs/internals/protocol.md), with its safety and
  liveness properties, and what still holds when the hub goes back to an earlier head.
- Replicated `jj op abandon`: contracting operations out of a history (`Musubi/Contract.lean`),
  and the protocol with dropped sets (`Musubi/Supersede.lean`; [design.md, "Abandoning
  operations"](../docs/internals/design.md#abandoning-operations)).
- Chunked blob transfer (`Musubi/Chunks.lean`), from the same document.
- The per-machine state of a replicated view, for one git ref (`Musubi/Refs.lean`; [design.md,
  "Per-machine state in a replicated
  view"](../docs/internals/design.md#per-machine-state-in-a-replicated-view)).
- Which copies a hive shows, one copy being one machine's repository (`Musubi/Presence.lean`;
  [design.md, "Copies that go away"](../docs/internals/design.md#copies-that-go-away)), and
  how a contraction keeps it (`Musubi/PresenceContract.lean`; [design.md, "Presence through an
  abandon"](../docs/internals/design.md#presence-through-an-abandon)).
- Which repository on a machine is the copy of a key, and which a duplicate made of its files
  (`Musubi/Copies.lean`; [copies.md](../docs/internals/copies.md)).
- The names a machine shows other machines' workspaces under (`Musubi/Names.lean`; [design.md,
  "Which workspaces are this machine's
  own"](../docs/internals/design.md#which-workspaces-are-this-machines-own)).

The last five are separate models, independent of the protocol model's state.

No proof is left unfinished (Lean's `sorry`) and the model adds no axioms. Every main theorem
depends only on Lean's standard `propext`, `Classical.choice` and `Quot.sound`, some on fewer;
`Musubi/Axioms.lean` prints each one's list.

The models are state machines, states and a step relation, except the presence model, which is
stated over any operation history. The protocol's is `Step N`, for `N` nodes, and `Reachable N s`
says that state `s` can be reached from `init`. Sets are predicates (`OSet`), so
`(s.node n).lops x` reads "`x ∈ local(n)`". *Ghost* state, such as each operation's creator,
exists only to state properties: no step reads it. [Correspondence with
protocol.md](#correspondence-with-protocolmd) maps the rest of the notation.

## Checking

Install Lean (for example, via `elan`) and put `lake` on `PATH`.

```sh
cd formal
lake build
```

The toolchain is pinned to `leanprover/lean4:v4.35.0` in `lean-toolchain`. The model uses only
core Lean: no Mathlib, no dependencies. A clean build of the proofs and the oracle takes about a
minute on 4 cores. It prints the axioms report of `Musubi/Axioms.lean` and runs the `#guard` smoke
tests in `Musubi/ExecTest.lean` and `Musubi/SupersedeExecTest.lean`.

`./test/run_smoke.sh` builds the conformance oracle alone (`lake build oracle`), replays
`test/smoke.jsonl` through it and diffs the output against `test/smoke.expected`. The binary
is `formal/.lake/build/bin/oracle`.

## Files

| File | Contents |
| --- | --- |
| `Musubi/Basic.lean` | Sets as predicates (`OSet`), point update `upd`, counting `cnt`, sums `sumN`. |
| `Musubi/Contract.lean` | Contracting dropped operations out of a history: parents (`cpar`), ids as terms (`cid`), composition, and when ids agree. |
| `Musubi/Dag.lean` | `Anc` (`anc*`), `ParLt` (parents have smaller ids, so the graph is acyclic), `maxSet` (`max`), and how `anc*` is preserved when a fresh op is created. |
| `Musubi/Model.lean` | The asynchronous model: state, messages, transitions, `EnvStep`, `SyncStep`, `Step`, `Reachable`. |
| `Musubi/Invariant.lean` | The inductive invariant `Inv` and the message invariant `MsgOK`. |
| `Musubi/PreserveEnv.lean` | `Inv` is preserved by `UserOp`, `Merge` and message sends. |
| `Musubi/PreserveSync.lean` | `Inv` is preserved by every sync, hub and crash step; `inv_reachable`. |
| `Musubi/Safety.lean` | The safety properties and no feedback. |
| `Musubi/Liveness.lean` | The policy model `PStep`, its simulation in the asynchronous model, the measure, progress, termination and convergence. |
| `Musubi/Merged.lean` | The merged `Push` and `Fetch` exchanges reach states that agree with policy steps on everything the measure and convergence read, with a hub that may have gone back too. |
| `Musubi/Regress.lean` | A hub that goes back to an earlier accepted head, as after a power cut or a remade hive: the extended system `RStep`, the invariant that survives, and convergence once the hub stops going back. |
| `Musubi/AbandonRefs.lean` | The boundary from contracted survivor heads and saved expected values to one-ref realization and merged publication. |
| `Musubi/Supersede.lean` | Replicated `jj op abandon`: the protocol over original operations with each party's dropped set (`SStep`, `SRStep`), its invariant, superseded ids never coming back, and liveness with supersedes (`SPStepR`). |
| `Musubi/Scenario.lean` | A concrete reachable run (a lost Cas race, then fetch, advance, merge, and the merge accepted), showing the model is not vacuous. |
| `Musubi/RegressScenario.lean` | A run of the executable model in which the hub goes back and two nodes then merge the same heads. |
| `Musubi/Chunks.lean` | The chunked-blob model, its safety and liveness; and musubi's receiver, which keeps only a prefix, proved a refinement of it, with its own liveness. |
| `Musubi/Exec.lean` | The executable model: finite `EState`, the `Action`s of [conformance.md](../docs/internals/conformance.md), `execStep`; and the liveness measures, convergence, and what a policy `Push` uploads, computed (`measureE`, `rmeasureE`, `convergedE`, `upOpsL`, `upObjsL`). |
| `Musubi/ExecSound.lean` | Soundness of `execStep` and of those computations ([below](#the-executable-model-and-the-conformance-oracle)). |
| `Musubi/ExecJson.lean` | The oracle's JSON codec and request handler (no protocol logic). |
| `Musubi/ExecTest.lean` | `#guard` smoke tests of `execStep`, checked at build time. |
| `Musubi/SupersedeExec.lean` | The executable model with supersedes: `SEState`, which adds the hub's records and each node's dropped set, the `SAction`s, `sexecStep`, and `smeasure` computed (`smeasureE`, `sconvergedE`). |
| `Musubi/SupersedeExecSound.lean` | Soundness of `sexecStep` against `SRStep`, and of those computations. |
| `Musubi/RecordLiveness.lean` | Record agreement and finite reconciliation after convergence. |
| `Musubi/AsyncLiveness.lean` | Progress at split exchange boundaries and hub stabilization on a constrained suffix; not yet the full retry bridge. |
| `Musubi/RetryControl.lean` | Finite pre-cut request-slot consumption and cached fix-up writes within an explicitly constrained epoch. |
| `Musubi/RecordStability.lean` | Finite record appends and pruning for bounded original drops, and pending shrink under record extension. |
| `Musubi/ContractOrder.lean` | Ancestry through a contracted expected head, including its difference from original ancestry. |
| `Musubi/SurvivorAdvance.lean` | The complete surviving-image frontier, preservation of local work, and its full-frontier merge. |
| `Musubi/ContractedSafety.lean` | Common store and frontier invariants without an original accepted-head chain; local primitive preservation and fixed-drop credit. |
| `Musubi/ContractedExec.lean` | The explicit executable union with survivor advance, atomic prepared adoption and contracted acceptance and rejection. |
| `Musubi/ContractedRecordCut.lean` | One record, pruning and node-drop stabilization cut for the executable recovery union, without assuming head stability. |
| `Musubi/PostCut.lean` | Strict hub movement after the record cut and finite influence of old ledger targets. |
| `Musubi/CutHistory.lean` | Survival of each saved hub head under its matching saved records, including rollback. |
| `Musubi/RecoveryEpoch.lean` | Composition of the record/drop cut with aligned acceptance witnesses. |
| `Musubi/PacketCoupling.lean` | One immutable push's full fields and actual send-time state, including actual-sender alignment. |
| `Musubi/PacketAcceptance.lean` | Upload coverage and actual packet checks force the executable hub's acceptance decision. |
| `Musubi/NodeReconcile.lean` | Surviving node heads throughout recovery and immediate adoption at an eligible node. |
| `Musubi/RecordReplies.lean` | Held-prefix custody and reconstruction of fresh serialized ordered-record replies. |
| `Musubi/SerialReply.lean` | Serialized calls, own-response recovery, shared request ids and notification scheduling between rounds. |
| `Musubi/RecordEpoch.lean` | Finite record adoptions and stale-plan reopens after current replies replace obsolete callbacks. |
| `Musubi/NotificationControl.lean` | Finite old notification handling, counting both in-flight logical frames and queued entries. |
| `Musubi/HubSuffix.lean` | Hub stabilization in raw graph space, with finite old-packet credit and a derived sender invariant. |
| `Musubi/HistoryWindow.lean` | Carry the raw accepted-head chain from the record cut to eligible nodes' later entry. |
| `Musubi/FreshObservation.lean` | Force an honest own response and repair obsolete initial knowledge without a whole-round premise. |
| `Musubi/EarlyEntry.lean` | Fair finite local bursts reach current records at eligible nodes before the hub settles. |
| `Musubi/EntryAssembly.lean` | Join eligible entry cuts and exclude core fix-ups/tips before hub stabilization. |
| `Musubi/NodeSettle.lean` | Finite local control after hub stabilization, from individual calls and local scheduling. |
| `Musubi/RecoveryBridge.lean` | Compose hub and local stabilization, with packet-specific handling and later response cuts. |
| `Musubi/CallBatch.lean` | Sequential finite call batches and injective virtual/wire-id correlation. |
| `Musubi/Expansion.lean` | Expand each actual event to a positive finite path and transfer stabilization back. |
| `Musubi/NodeSys.lean` | One joint graph, node controls, immutable calls, replies and notifications; scoped local embeddings. |
| `Musubi/NodeSysExec.lean` | Check structural writes with canonical id reuse. |
| `Musubi/NativeEvents.lean` | Replay event data and derive its eligible system run. |
| `Musubi/FineAssembly.lean` | Assemble the fine system from event replay and source bindings. |
| `Musubi/NodeSysEntry.lean` | Derive node entry and preserve the joint control invariants under individual-call fairness. |
| `Musubi/SysFreshCuts.lean` | Derive cutoffs for consumed old replies and processed old notifications without draining queues. |
| `Musubi/SysAcceptance.lean` | Compose actual hub stabilization and eligible-node settling, including raw head agreement. |
| `Musubi/HubSys.lean` | Read raw hub and node policy fields from that same joint system. |
| `Musubi/HubLedger.lean` | Retain actual send-time packet fields and prove coverage of outstanding eligible requests. |
| `Musubi/RawExpansion.lean`, `Musubi/RawMaintenance.lean` | Expand finite raw write batches, counting actual maintenance operations. |
| `Musubi/HubNodeSteps.lean` | Refine eligible node events to hub-suffix paths under explicit native primitive laws. |
| `Musubi/HubAnswers.lean` | Derive the suffix accept or frame from the actual immutable request and hub answer. |
| `Musubi/HubHistory.lean` | Derive the raw history window from the joint run before eligible-node entry. |
| `Musubi/RequestBounds.lean` | Derive request bounds, expand actual joint events, and prove the hub stabilizes. |
| `Musubi/HistoryReplies.lean` | Bind fresh replies and notifications to the actual hub history despite delayed delivery. |
| `Musubi/RawEvolution.lean`, `Musubi/GlobalRaw.lean` | Derive a single immutable raw graph and history window before fine control simulation starts. |
| `Musubi/PendingEpoch.lean` | Bound pending alias changes with partial normalization and per-original coherence. |
| `Musubi/ContractedMeasure.lean` | The record-aware executable progress check through surviving images; coincidence with the old check before drops. |
| `Musubi/ContractedExecTest.lean` | Build-time checks of independent recovery and mutually exclusive contracted outcomes. |
| `Musubi/SupersedeExecTest.lean` | `#guard` smoke tests of `sexecStep`, checked at build time. |
| `Musubi/Refs.lean` | Per-machine refs, for one git ref: imports, exports, merges, conflicted remote bookmarks, and `jj undo` and `jj op restore`. |
| `Musubi/Expected.lean` | The conflicted-ref history walk, agreement under operation renaming, termination and the import-agreement boundary. |
| `Musubi/ExpectedExec.lean` | Finite operation DAGs and commit-side selection for the history oracle. |
| `Musubi/Presence.lean` | Which copies a hive shows. |
| `Musubi/PresenceExec.lean` | The presence rule on a finite history, executable, for the oracle. |
| `Musubi/PresenceContract.lean` | Presence through a contraction: stamps, presence at what survives, and ids with stamps (`sid`) composing in either order. |
| `Musubi/RefsExec.lean` | `Refs.lean`'s slot functions on targets a test numbers, with jj's merges as a table, for the oracle. |
| `Musubi/Copies.lean` | Which repository is the copy of a key: musubi's decisions, jj's config-id rule, and a machine's repositories moved, copied, deleted and replaced. |
| `Musubi/Names.lean` | The names a machine shows other machines' workspaces under, and `#guard` tests of them. |
| `Musubi/Axioms.lean` | `#print axioms` for every main theorem. |
| `Oracle.lean` | The `oracle` executable: a stdin/stdout loop around `ExecJson.handle`, which also answers measure, upload, presence, copies, chunks, names, refs and expected-value requests. |
| `test/smoke.jsonl`, `test/smoke.expected`, `test/run_smoke.sh` | The oracle smoke test. |


## Correspondence with protocol.md

| protocol.md | Lean |
| --- | --- |
| `OpId`, `root` | `Nat`; `root = 0` |
| `parents(x)`, `objs(x)` | `s.U.par x`, `s.U.objs x` (`Univ`). Immutable: only the fresh id `s.U.next` is ever assigned. |
| `anc*(x)` | `Anc s.U.par · x` (`a ∈ anc*(x)` is `Anc par a x`) |
| `closure(x) ⊆ ops ∪ objects` | `ClosedAt s x` (built from `HubHas`) |
| `creator(x)` | ghost `s.U.creator x : Option Nat` (`none` for the root) |
| Hub `ops`, `objects`, `head`, `seq` | `s.hub.ops`, `s.hub.objs`, `s.hub.head`, `s.hub.seq` |
| History of accepted heads | ghost `s.hub.hist : Nat → Nat` (`hist i` = head accepted at `i`) |
| Node `local`, `heads`, `staged`, `known` | `(s.node n).lops`, `.heads`, `.sops`/`.sobj`, `.known`; `.lobj` is the local object store |
| `max(S)` | `maxSet par S` |
| `GetHead`/`Head`, `Accepted`, `Rejected`, `Incomplete`, publish | `Msg.getHead`, `Msg.head n k sq h` with `k : HeadKind` (`head`, `accepted`, `rejected`, `incomplete`, `notify`) |
| `PutOps`/`PutObjects`/`Stored` | `Msg.putOps n S`, `Msg.putObjs n S`, `Msg.stored` |
| `GetOps`/`Ops`, `GetObjects`/`Objects` | `Msg.getOps`, `Msg.ops`, `Msg.getObjs`, `Msg.objs` |
| `Cas(expected, new)` | `Msg.cas n e d`; hub steps `casIdem`, `casAccept`, `casReject` |
| `Push(operations, objects, expected, new)` | `Msg.push n S O e d`; node step `pushAll`; hub steps `hubPushIdem`, `hubPushAccept`, `hubPushReject`, `hubPushIncomplete`, each storing `S` and `O` first (`State.hubStore`) |
| `Fetch(base, haves)`/`Fetched` | `Msg.fetch n b H`; node step `fetchAll`; hub step `hubFetch`, which sends `head n head seq head`, `ops n (sinceOps b)` and `objs n (sinceObjs b H)` |
| `UserOp(p)` | `EnvStep.userOp` → `State.userOp` |
| `Merge` | `EnvStep.merge` → `State.mergeOp` |
| `Learn`, `Fetch`, `Realize`, `Advance`, `Upload`, `Push` | `SyncStep.learn`, `.fetchOps`/`.fetchObjs`/`.recvOps`/`.recvObjs`, `.realize`, `.advance`, `.uploadOps`/`.uploadObjs`, `.push` |
| Message loss, duplication, delay, reordering | `s.net` holds every message ever sent; any message in it may be handled any number of times, or never. |
| Node crash, hub crash | `crashNode`, `crashHub`, plus the relaxations `loseKnown`, `loseVolatile` and `hubForget` ([Modeling choices](#modeling-choices)) |
| Policy (reliable, atomic exchanges) | `PStep`: `learn`, `realize`, `advance`, `merge`, `pushAccept`, `pushIdem`, `pushReject` |
| Chunked blob session | `Chunks.CState`, `Chunks.CStep` (full model), `Chunks.LStep` (reliable delivery) |
| musubi's receiver (`BlobStore::receive`) | `Chunks.PState`, `Chunks.receive`, `Chunks.PStep`, `Chunks.PLStep` (resending from the prefix) |

## Main theorems

Unless it says otherwise, a protocol theorem holds in every state `Reachable N s`: every state of
the full asynchronous system with `N` nodes. The properties are stated in
[protocol.md, "Properties"](../docs/internals/protocol.md#properties).

### Safety (`Safety.lean`)

- `hubClosed`: `closure(hub.head) ⊆ ops ∪ objects`.
- `hubMonotone`: for every step `s → s'`, `s.hub.head ∈ anc*(s'.hub.head)`.
- `acceptedStays`: an operation in `anc*(hub.head)` stays there.
- `histStable`, `hubHistory`: the ghost history only grows, starts at the root, and each
  entry strictly descends from the previous one.
- `nodeClosed`: `local` is closed under parents, its operations' objects are present,
  `heads ⊆ local`, and `heads` is a nonempty antichain.
- `knownIsHubHistory`: `known.seq ≤ hub.seq` and `hist known.seq = known.head`.
- `headMsgsTruthful`: every head-carrying message carries a true `(seq, head)` pair.
- `locality`: `x ∈ local(n) → creator(x) = n ∨ x ∈ anc*(hub.head)`.
- `mergeOwnership`: whenever `Merge` is enabled on `n`, some parent was created by `n` and is
  not accepted.
- `mergeOwnershipGhost`: the same, recorded per merge in ghost state.
- `noDuplicateMerge`: merges created by different nodes have different parent sets.
- `mergeNeverRepeats`: a new merge never repeats the parent set of any earlier merge, from
  any node.
- `advance_result`: after `Advance`, `|heads| ≥ 2` or `heads = {known.head}`, as step 3 of
  [protocol.md, "Policy"](../docs/internals/protocol.md#policy) claims.

### No feedback

- `noFeedback` (`Safety.lean`): every `SyncStep`, including `Realize`, hub handling and
  crashes, leaves the operation universe unchanged. This is about the modeled step, not an
  entire repository call that also invokes jj's merge.
- `advance_merge_parents` and `advance_merge_refines` (`Safety.lean`): an advance that merges
  every concurrent head refines advance followed by `EnvStep.merge`; it retains the local
  operations, creates one merge, and leaves the hub and messages unchanged. The real-repository
  test `translation::advance_with_concurrent_heads_refines_advance_then_merge` checks the
  observed graph against those same oracle steps ([correspondence and
  limits](../docs/internals/conformance.md#a-repository-advance-that-also-merges)).
- `envCreatesOne` (`Safety.lean`): each environment step creates exactly one operation.
- `converged_quiescent` (`Liveness.lean`): a converged state enables no policy step.

### Liveness (`Liveness.lean`)

Liveness is proved for the policy model `PStep`: users have stopped (there is no `UserOp`), and
each node takes the policy's actions as atomic request/reply exchanges that succeed, nodes and
actions scheduled in any order. `Merge` is a policy step, because musubi loads the repository
and jj merges. [The asynchronous bridge](#the-asynchronous-liveness-bridge)
explains why this covers the real, lossy system.

`Converged N s` means that every node `n < N` has `heads = {hub.head}` and
`known = (hub.seq, hub.head)`.

- `pstep_reachable`: every policy step is a finite run of the asynchronous model.
- `progress`: if a reachable state is not converged, some policy step is enabled.
- `measure_decreases`: every policy step strictly decreases a lexicographic measure.
- `no_infinite_policy_run`: no policy run is infinite, under any schedule.
- `eventually_converges`: from every reachable state, policy steps reach a converged state.
- `maximal_run_converges`, `terminal_iff_converged`: a policy run that cannot be extended
  is converged, and a converged state cannot be extended.
- `converged_all_accepted`: once converged, every created operation is in `anc*(hub.head)`.

The measure is
`(dirty nodes, Σ staleness, Σ missing ops, Σ pending advances, Σ pending merges)`, compared
lexicographically. A node is dirty when one of its heads is not accepted; its staleness is
`hub.seq - known.seq`; its missing ops are the accepted operations it lacks; it has an advance
pending when `known.head` is below none of its heads, and a merge pending when it has two or
more heads. Contention is bounded by the first component: an accepted push cleans the pushing
node, a clean node never becomes dirty once users stop, and only accepted pushes move the hub
head, so the head moves at most once per dirty node, at most `N` times. Every lost Cas race
teaches the loser a newer head, which lowers its staleness.

### Merged requests (`Merged.lean`)

Policy steps exchange the fine-grained messages (`GetHead`, `PutOps`, `Cas` and the rest);
musubi sends the merged `Push` and `Fetch` instead. Each merged exchange is a run of the model
that ends in a state agreeing with the policy step's on everything but the network and what
is staged (`AgreeUpToStaging`).

- `pushAccept_merged`, `pushIdem_merged`, `pushReject_merged`: for a merged `Push` exchange
  and the corresponding policy step.
- `fetch_merged`: for a merged `Fetch` exchange and `PStep.learn`; it also stages every
  operation the node lacks below the head, with its objects at hand.
- `realize_agree`: realizing a staged operation agrees with `PStep.realize`.
- `measure_agree`, `converged_agree`: the measure and convergence see no difference.

The same holds with a hub that may have gone back, in the extended system of `Regress.lean`
(`RReachable`), against `PStepR` and `rmeasure`. There the node takes the head in a reply
whatever it knew (`learnUnfiltered`), as `PStepR` does.

- `pushAcceptR_merged`, `pushIdemR_merged`, `pushRejectR_merged`: for a merged `Push`
  exchange and the corresponding `PStepR` step.
- `fetchR_merged`: for a merged `Fetch` exchange and `PStepR.learn`, staging as
  `fetch_merged` does. `fetchR_current`: a `Fetch` by a node that knows the hub's head
  and `seq` already, for which `PStepR` has no step, ends agreeing with the state before it.
- `rmeasure_agree`: `rmeasure` sees no difference. `realize_agree` and `converged_agree` hold
  of any states.

### A hub that goes back (`Regress.lean`)

[protocol.md](../docs/internals/protocol.md) requires the hub to keep `head`, `seq` and
`closure(head)`, but musubi's hub syncs nothing to disk, so a power cut can lose the last heads it
accepted ([protocol.md, "Network and
failures"](../docs/internals/protocol.md#network-and-failures)). `State.regress s i` (the oracle's
action `hubRegress`) sets `head := hist i` and `seq := i` for any `i ≤ seq`. `RStep` is a `Step`
or such a regression, and `RReachable` its reachable states. Making a hive again, empty, is a
regression to 0 followed by `hubForget` (`remake_reachable`).

The invariant `InvR` keeps the universe, the hub's history and closure, and each node's
repository, but nothing relating nodes to the hub's history. So Locality, MergeOwnership,
HubMonotone and KnownIsHubHistory do not hold here: after the hub goes back, nodes can hold
operations the hub no longer has, know heads it has forgotten, and merge the same heads.

- `invR_reachable`: `InvR` holds in every `RReachable` state.
- `hubClosedR`, `hubHistoryR`, `nodeClosedR`, `noFeedbackR`: HubClosed, the history chain,
  NodeClosed and no feedback, with a hub that goes back.
- `duplicateMerge`, `rreachable_not_reachable` (`RegressScenario.lean`): two nodes can create
  merges with the same parents, which `noDuplicateMerge` rules out in every `Reachable` state.
- `pstepR_reachable`, `progressR`, `measureR_decreases`, `no_infinite_policy_runR`,
  `eventually_convergesR`, `maximal_run_convergesR`, `terminal_iff_convergedR`,
  `converged_all_acceptedR`: liveness once the hub stops going back, for the policy `PStepR`.
  Once converged, every operation any node created is in `anc*(hub.head)`: a hive made again
  fills from its machines.

`PStepR` differs from `PStep` in two steps, each as the Rust core takes it:

- A node learns the head in a reply to its own request whenever it differs from the one it
  knows, older or not (`learnUnfiltered`). `NodeCore::handle_reply` restarts the node and
  then takes the reply: `loseKnown`, then `learn`, to the same effect.
- A node realizes only below a head in the hub's current history (`Consistent`). The core
  drops its realization plan whenever `handle` changes `known`, and starts every sync with a
  `Fetch` whose reply sets `known`, so whatever it realizes is below the head the hub has just
  named.

The measure `rmeasure` is `(nodes not good, inconsistent nodes, Σ staleness of consistent
nodes, Σ missing ops, Σ pending advances, Σ pending merges)`. A node is good when its `known`
is in the hub's current history and it has one head, accepted and comparable with every head
in that history. The dirty count of `Liveness.lean` does not work here: after the hub goes
back, a node can hold two accepted heads that are not comparable, and merging them makes it
dirty. A good node stays good under every policy step of every node, and an accepted push
makes its node good, so the hub head moves at most once per node that is not good.

### Abandoned operations (`Contract.lean`, `Supersede.lean`)

`Contract.lean` is about any history (`ParLt par`) and a dropped set `D`. Ids are terms
(`CId`), so the hash they stand for is injective. `cid` takes an arbitrary immutable content
function, allowing equal content at different operations. `equal_content_recreates_id` proves
the three-operation counterexample when the content function is constant.

- `cpar_union`, `cid_union`: dropping `D₁`, then `D₂` from what is left, gives the parents and
  ids that dropping `D₁ ∪ D₂` gives; hence `cid_comm`, either order.
- `cid_eq`, assuming injective immutable content: two survivors' ids under two dropped sets
  are equal only for the same operation,
  with the sets agreeing on its proper ancestors. `superseded_ne`: an id from before a dropped
  set grew to include the operation or one of its ancestors is no survivor's id after.
- `anc_cpar_iff`: among survivors, contraction keeps ancestry; `cid_congr`: ids depend only on
  what is below.

Composition and ancestry need no content injectivity. `cid_eq`, `superseded_ne`, and the
protocol's never-return corollaries do. The protocol instantiates content with the original's
identity (`id`), representing the immutable original-parent material enforced by Rust's fresh
creation and contraction APIs. Runtime input-history and hub-publication checks reject duplicate
or explicitly dropped originals even when received with new current ids. Hash collision freedom
remains an assumption. These proofs do not authenticate a peer's claimed rewrite provenance or
infer which operation jj meant to retain when jj itself coalesces local ids; that ambiguous
case is refused. See the contraction correspondence in
[conformance.md](../docs/internals/conformance.md).

`AbandonRefs.lean` connects the survivor graph to a successful colocated publication with one
remote ref. Slots and expected-value snapshots are indexed by original operation identity.
`takeHeads` expands the current heads under the dropped set, adds the incoming
head, and takes the maximal survivors. `History.publish` contracts the graph and publishes one fresh
merge together with `Refs.cbeside`'s ref state. `publish_refines` proves surviving ancestry
and `CInv` together, and that the ref action is a `CStep.beside`. `fixup_retains` states the
fresh child/saved-expectation boundary: the new operation receives its parent's slot and the
saved expectation,
rather than inferred again from contracted ancestry. `abstraction_unique` uses the enforced
immutable identity premise above; `adoption_composes` connects sequential record contraction
to the union of dropped originals.

The oracle executes those definitions directly for the abandonment/ref race, checking every
survivor's parents, the normalized merge base, the published merge and its ref state before
convergence. It also checks the fix-up's saved expectation and translation immediately after
publication. [Conformance and limits](../docs/internals/conformance.md#abandonment-and-refs)
describes the observation points and premises. This boundary does not replace the network
model, derive expected values from all jj histories, or prove publication's lock discipline.

`Supersede.lean` models the protocol over each operation's original, so the states of
`Model.lean` stay as they are, and adds the hub's and each node's dropped sets, and which of the
hub's it has pruned (`SState`). `SStep` is a `Step` that gives each node no head of its own
dropped set, and the hub none it remembers dropping and, once it has pruned anything, none
whose push doesn't carry the hub's records; or one of `sup` (the hub takes a dropped set with
the push it rides on, to a head the push doesn't drop), `abandon`, `sendSup` (what the records a
node took drop, its dropped set, and the head of its push, which those records don't drop),
`sendD` (at least what the hub remembers), `adopt` and `prune` (the hub deletes the ids of some
of what it dropped); `SRStep` adds the hub going back, to the dropped and pruned sets it had
with that head.

- `SReachable.base`, `SRReachable.base`: every state is one of `Model.lean`, or of
  `Regress.lean` with the hub going back, so every theorem there holds as stated;
  `noDuplicateMergeS` restates one.
- `sinv_reachable`: the invariant `SInv`, whatever the hub prunes. No head is in its holder's
  dropped set, the root is in none, every dropped operation is below a head of a node that
  dropped it, and the records a supersede carries drop no head of its push.
- `dropped_never_head`: so, while the hub doesn't go back, it never takes a head it dropped,
  though it may have pruned it. `behind_not_carried`: a node that hasn't dropped an operation the
  hub pruned has no supersede the hub takes.
- `nodeD_grows`, `hubD_grows`: a node's dropped set only grows, and the hub's while it doesn't
  go back. `superseded_never_returns`, `superseded_never_returns_hub`: so, by `superseded_ne`,
  an id superseded on a node is never again an id of an operation it keeps, nor on the hub
  while it doesn't go back.
- `spstepR_reachable`, `smeasure_decreases`, `no_infinite_policy_runS`, `progressS`,
  `converged_quiescentS`, `terminal_iff_convergedS`, `eventually_convergesS`,
  `maximal_run_convergesS`: liveness once the hub stops going back, for the policy `SPStepR`,
  the steps of `PStepR` and `adopt`, `supPush` and `supFix`, from every reachable state where
  every node has dropped what the hub pruned (`AllPruned`), though the hub announces only what
  it remembers. `allPruned_step`: a step keeps `AllPruned` as long as what it prunes, every node
  had dropped; `Exec.sexec_allPruned`: the executable hub keeps it in every state it reaches.
- `converged_all_droppedS`, `converged_all_acceptedS`: once converged, the hub and every node
  have dropped every operation any node dropped, and every operation any node made is below the
  hub's head.

The measure puts `(drops not yet on the hub, drops not yet on each node)` before `rmeasure`. A
node can wait on another: with a head the hub dropped, or on a hub head it dropped and isn't
past. `progressS` shows the node with the newest head above the hub's head can always act, since
every dropped operation is below a newer head of a node that dropped it.

`Presence.lean`'s `fixup_present` and `pass_present` say what the fix-up chain does to which
copies are present; `PresenceContract.lean` that the rewrite itself changes nothing there.

### Presence through a contraction (`PresenceContract.lean`)

Presence is worked out from the history below an operation, and a contraction changes that
history while keeping every surviving operation's view. The model is abstract in the presence
values and the rule that works them out (`step`), so that it covers `Presence::merge` and
`apply` as they are: `val x` is presence at `x` before anything is dropped, and `step` asks
`seen c p` whether work `c` is below parent `p`. A history is the original parents and what is
gone; `seen` counts gone work as seen below every parent. A contraction stamps an operation
with `val x` where `step` on its new parents would give another value (`stamp`), and presence
at a stamped operation is its stamp (`pres`).

- `pres_eq`: presence at every surviving operation is what it was. It holds of any rule, as
  the stamp is defined to make it so; what it shows is that presence worked out from parents
  that are themselves stamped where needed is the original's.
- `stamp_union`, `sid_union`, `sid_comm`: stamps, and so ids, which hash them, are the same
  whichever order two dropped sets go in. Given the definitions, this is `cpar_union`: whether
  an operation is stamped, and with what, depends only on its contracted parents and on what
  is gone. `stamp_none`: a history nothing was dropped from has none.
- `sid_eq`, `sid_superseded_ne`: as `cid_eq` and `superseded_ne`, with stamps.

What the model leaves to tests: that the Rust's stamp is this definition, computed on the
history as it is after the drops before; and that the Rust, reading a stamp, finds the
operation standing for each work it names among its parents' presence. Presence values name
work by its original identity, which is what lets them stay as they are; the model numbers
operations by it. That `step` is `Presence::merge` then `Presence::apply`, and that these
compute `UMax` on a history nothing was dropped from, is `Presence.lean`'s (`umax_merge`,
`umax_work`, `umax_forget`). `presence::contraction_keeps_presence` compares each copy's latest
work at what every kept operation becomes with `PresenceExec.lean`'s at the operation, and
`dropping_twice_is_dropping_both` all of presence with presence worked out before the drops
([conformance.md, "Presence"](../docs/internals/conformance.md#presence)).

### Chunked blobs (`Chunks.lean`)

Each theorem assumes `hash` injective.

- `stored_identical`: in every reachable state, a finished (stored) blob equals the blob that
  was sent, even when the network injects arbitrary corrupt or stale chunks.
- `session_finishes`: from every reachable state, reliable delivery finishes the session and
  stores exactly the sent blob.
- `preach_abs`: every state musubi's prefix receiver reaches (`PReach`) stands for one the
  full model reaches, each of its steps a run of `CStep`s. Hence `prefix_stored_identical`: a
  blob it stores is the one sent.
- `prefix_finishes`: from every state the prefix receiver reaches, a sender that resends
  from the prefix it reports finishes, and the receiver stores exactly the sent blob.

### Per-machine refs (`Refs.lean`)

The model covers one git ref of a colocated repository: jj's import and export, with git an
adversary that can move the ref at any time, and jj's ref merge an abstract three-way merge
obeying three laws (`RefAlg`), which the test `ref_laws` checks against jj-lib.

- `noSpuriousRevert`: an import changes a local bookmark only if git moved its ref, whatever
  musubi realizes and whether or not its export succeeds. `remoteNoSpuriousRevert`: the same
  for a remote bookmark, as long as every realization is exported before a `jj` command can
  import. A tag's slot is a local bookmark's, so these hold for tags too.
- `conflictedNoSpuriousRevert`, `conflicted_import_agrees`: jj skips the export of a conflicted
  remote bookmark, which two machines' fetches merge to and `jj op restore` can bring back, so
  musubi writes its expected value to `.git` itself (`exportConflicted`): one of its sides
  where a merge made the conflict, and where a restore brought it, the value from before the
  restore, which the restoring machine's `.git` kept. Then an import changes nothing unless
  git moved the ref, or resolves the conflict to that value (not vacuously:
  `conflicted_resolves`), and every machine with the same expected value imports the same,
  the restoring machine included (`restore_import_agrees`), so a bookmark restored with its remote bookmark to a conflict
  goes back where it was (`restore_conflict_resolves_back`, `conflicted_restore_resolves`).
- `restoreLocal_inv`, `restoreRemote_inv`, `restoreRemote_cinv`: `jj undo` and `jj op restore`
  keep the invariant where jj's export can write the restored bookmark, or it restores a
  conflicted remote bookmark. Where it can't, as for the root commit or a conflicted local
  bookmark, the next import moves the bookmark with no `git` command
  having run (`restore_reverts`): jj's behaviour, in which no musubi step takes part.
- `verbatim_reverts`: replicating the per-machine record verbatim instead reverts another
  machine's move of a bookmark with no git move at all.
- `fork_merge_inv`, `fork_noSpuriousRevert`: a merge of concurrent op heads keeps the
  invariant unless both heads changed the record; if both did, the next import can move the
  bookmark (`concurrent_records_revert`), as jj does without musubi.
- `realizeMerge_eq`: musubi's realization of a merge, tracking states included, is jj's merge.
  Merging the per-machine fields against only the first of several closest common ancestors
  would leave a record the export can't correct, and the next import would move the bookmark
  (`firstBase_reverts`).
- `besideLocal_inv`, `cbeside_inv`: a realization beside the machine's own op head, which
  musubi exports, merges with that head and exports again, publishing only the merge, keeps
  the invariant whatever the head did (`LStep.beside`, `CStep.beside`), so the theorems about
  `LReach` and `CReach` hold of runs with it, given that the base's record agrees with itself
  (`LStep.agrees`). musubi's export of the realization leaves a conflicted remote bookmark
  alone where `.git` holds the head's record and the realization's differs
  (`exportConflictedBeside`); writing the expected value there moves the bookmark back after a
  fetch of a term of the conflict (`beside_keeps_fetch`). Published apart, the realization
  would be merged by a `jj` command, which doesn't export, and that machine would import a
  value other than the merge's expected value (`beside_published_apart_disagrees`).

Commit graphs, rebases and jj's conflict algebra are not modeled. The file's header lists
what else it leaves out: tracking in the linear steps; the tracking state of an absent
`x@git`, which musubi's realization keeps and jj would drop (`realize_not_WF`); as runs,
merges of more than two heads, criss-cross merges, and a remote bookmark's concurrent heads
that `jj` commands alone make; and the establishment of the history hypotheses below. The slot
model takes the expected value as given with each operation.

### Expected values from history (`Expected.lean`)

`Expected.decide` models the ordered history rule in `node/git.rs`: a cached value before a
recorded fix-up value; a deterministic side at a join; the first parent with the same target;
otherwise a single parent's resolved value or its own expectation; otherwise a deterministic
side. `ExpectedExec.latest` selects the latest committer time, then greatest commit id, among
positive present terms. The history walk does not choose merge bases: jj has already used
them to construct each operation's target.

- `eval_congr_on`: corresponding relevant observations under an operation renaming give
  equal expectations. Its domain need only contain the start and the parents the walk follows;
  history behind a join or checkpoint is not inspected. Parent order, target equality, join
  classification and effective checkpoint values must agree there.
- `eval_terminates`, `eval_stable`: a decreasing operation rank makes the walk finish, and
  extra fuel cannot change a successful answer. No expected value (`some none`) differs from
  fuel exhaustion (`none`).
- `eval_without_known_agrees`: removing correct memoized answers leaves successful walks
  equal, even with different fuel. It assumes each memoized answer is the uncached walk's
  result; pending pre-contraction values instead need authoritative history checkpoints.
- `conflicted_import_agrees_of_history`: two reachable slot states bound to the present results
  of those computations satisfy `conflicted_import_agrees`, without taking equality of `E`
  as an independent hypothesis. Matching bookmark targets, no external git move and successful
  exports remain the slot model's conditions.

`expected_history_conforms_to_model` runs the shipping history walk on operation DAGs in a
real jj store and compares it with the oracle, including joins, restored conflicts, effective
parents during contraction recognition, checkpoints, three parents and minimal criss-cross
ancestry. The finite oracle calls the same `eval` the theorems prove properties of, rather
than an unproved executable copy. jj's ref algebra remains tested laws in `ref_laws`.

This is a conditional history-computation theorem, not a proof that every translation or
fix-up supplies corresponding observations. In particular, the producer and persistence of
pre-contraction checkpoint values, and correspondence of merged targets and ordered parents,
remain obligations of the abandonment/realization bridge. Three-parent and criss-cross DAGs
are covered as inputs to this computation; their complete import/export runs and jj's
recursive merge-base construction remain outside the slot state machine. See
[conformance.md](../docs/internals/conformance.md#expected-values-from-history).

### Presence (`Presence.lean`)

A copy is present at an operation while some of its work in the operation's history was seen by no
forget of it ([design.md, "Copies that go away"](../docs/internals/design.md#copies-that-go-away)
defines work and forgets). For any operation graph:

- `present_local`, `present_congr`: presence depends only on the operation's history, so
  every machine agrees.
- `only_work_returns`, `absence_persists`: only work brings a copy back. Hence `leave_sticks`:
  `musubi leave` sticks however its forget is merged, given that the forget follows all of the
  copy's work and nothing made later is pushed.
- `unseen_work_survives`: work concurrent with a forget survives it.
- `forgets_need_fresh_work`, `no_forget_after_complete`, `forget_chain_bounded`: forgetting
  can't loop along a line of history.
- `redundant_forget_noop`, `concurrent_forget_noop`: duplicate forgets are harmless.
- `present_iff_latest`: presence can be decided from a copy's latest work and its forgets.
- `umax_merge`, `umax_work`, `umax_forget`, `present_iff_umax`: what musubi keeps of each
  copy, its latest work that no forget saw (`UMax`), follows from an operation's parents'
  alone, and says whether the copy is present.

### Workspace names (`Names.lean`)

Each machine, this one among them, takes the first of its candidate prefixes that no machine
before it took and that starts no name of this machine's own and `/`: its name, if no other
machine has it, then its name and the start of its key's suffix, its name and the whole suffix,
and that with ever more dashes ([conformance.md, "Workspace
names"](../docs/internals/conformance.md#workspace-names)). This machine shows the others under
theirs, as the hub, which names every machine, lists them.

- `choose_free`: one candidate is always free, one longer than every prefix taken and every
  name of this machine's own.
- `localName_injective`: the names of a view's workspaces, this machine's under their own
  names and the others' as `<prefix>/<workspace>`, are distinct, whatever the machines and the
  names of this machine's own, given machine names and suffixes without `/`, as musubi makes
  them; only a machine key edited by hand could have one.

## The asynchronous liveness bridge

The termination theorems concern successful atomic policy exchanges. `pstep_reachable`
embeds each policy step into the asynchronous safety model; it does not prove that an
asynchronous implementation run eventually takes policy steps. `Merged.lean` constructs
successful merged exchanges with the same measure and convergence result. The Rust
conformance test checks measure descent at completed, serialized exchanges. None alone
establishes convergence under arbitrary asynchronous delivery and retries.

`AsyncLiveness.lean` proves progress at the boundaries that the atomic exchanges hide:

- `bad_accept_before_reply` and `measureR_accept_before_reply`: a hub acceptance makes
  its pusher good before the acknowledgement, provided that node still has the single head
  it pushed and its old `known` belongs to the current hub history. Losing the reply leaves
  this progress intact. Stores and message bookkeeping do not affect the result.
- `measureR_delayed_learn`: learning a strictly newer pair from the current hub history
  decreases `rmeasure`, even when another acceptance has moved the hub beyond that pair.
  This does not cover a reply from a history the hub lost, or a recovery reset.
- `settling_hub_stabilizes`: every reachable run of `SettlingStep` eventually has a fixed
  hub head and sequence number. Its first measure component never increases, and every
  hub movement strictly decreases it. Local policy steps, including advance and merge,
  remain allowed, as do delayed consistent learning and bookkeeping. Fix-up creation,
  hub regression and obsolete-history recovery are excluded from this suffix relation.

`RetryControl.lean` proves two finite bounds, with executable boundary checks described in
[conformance.md](../docs/internals/conformance.md#liveness):

- `old_slots_eventually_stop`: after any finite request-id cut, only finitely many replies
  can consume a pre-cut live request slot. New requests cannot recharge the budget, and
  duplicate frames cannot consume a slot twice. This permits infinitely many unmatched
  duplicates. It assumes ids are never reused; production uses `u64`, so the correspondence
  excludes exhausting that counter. It does not bound queued notifications or prove that a
  still-live pre-cut call is eventually retired.
- `fixup_writes_le_one` and `fixups_eventually_stop`: at most one completed restoring write
  per node in an epoch with no new abandonment discovery, obsolete-prefix adoption or
  interrupted write. The first current-epoch adoption may replace pending drops; later
  adoptions must only remove them, in immutable original-operation names. Clearing the cache
  after alignment requires empty pending, which cannot then grow. A write produces a finite
  saved work list and final operation. No bound on network retries is assumed. The
  real-repository check pins cached reuse and reopening, but does not prove entry into this
  epoch or the monotonicity premise for all production adoptions. Neutral publication tips
  are additional work, outside this cached restoring-payload bound.

`Retry.Publication` distinguishes that cached restoring work from a neutral publication tip.
If pending is nonempty and the head equals the known head, `publication_progress` requires a
child above the current head even when the restoring work is cached. `publication_retry`
concerns the helper's result state, whose head is read as no longer known. A restoring write
can instead recreate the known body: the native post-write equality must be read separately,
and a neutral tip may follow without another learned head. `NodeSettle.write_known` counts
that restoring cache change in its rank rather than excluding the case by freshness.
`publication_tip_cached` proves the tip leaves the restoring cache untouched. These are local
decision/cache results, not a bound on tips across arbitrary later replies or adoptions.

`RecordStability.lean` derives part of the epoch argument. After rollback stops, every
changed full modeled record list appends a nonempty difference, spending a previously unseen
original drop. Bounded original drops therefore give an eventual fixed ordered list, without
assuming head stabilization. Pruning then spends a bounded prefix. The executable
`sexec_record_prefix_stabilizes` discharges the append and pruning premises from the existing
record constructors; its original-drop bound and cessation of rollback remain assumptions.
The independent `node_drop_sets_eventually_stabilize` gives a common cut for finitely many
monotone bounded node drop sets. `adopt_pending_subset` derives pending-original shrink from
`adoptR` when the new record list extends the old dropped union. These results neither prove
that every production adoption is such an extension nor repair the ancestry gap below.
`record_and_drop_sets_stabilize` combines those cuts using only their append, pruning and
persistent original-drop field effects. It does not require raw local realization, which may
contract parents, to be an original-history executable step.

`ContractedRecordCut.lean` extends that result to the full executable recovery relation.
`cexecAction_record_control` derives the same record and pruning effects for survivor
advancement, prepared adoption and contracted acceptance as for the legacy actions.
`contracted_step_node_drop_mono` also covers every added transition. Together with record
custody, `cexec_record_and_drop_sets_stabilize` gives one cut after which the ordered hub
records, pruning boundary and each participant's dropped set stay fixed. Bounded dropped
originals and cessation of rollback remain premises. The theorem does not assume head
stabilization, node record agreement, successful replies or a decreasing progress rank.

`CutHistory.lean` supplies the entry invariant that SEOK alone does not give. Each saved hub
head survives the record list saved at the same sequence. Acceptance updates both slots;
pruning preserves the current head; rollback restores that matching pair. This needs no
original-ancestry chain through the pre-cut accepted history.

`PostCut.lean` then derives strict original-ancestry movement in the finite executable model
after records stop changing, and a finite bound on moves to old ledger targets. A ledger
entry alone does not identify a request: `PacketCoupling.lean` instead ties every accepting
action to the immutable packet's records, drops, expected head and new head. Under the common
drop cut, `packet_sender_after_cut_aligned` identifies that packet's actual sender as
eligible throughout the suffix. Other nodes can keep sending packets; those cannot move
the hub. The native fixed-record counterpart uses the hub's raw graph, rather than a
universal projection from canonical versions to immutable originals.

`NodeReconcile.lean` proves that every reachable node head survives its own dropped set.
An eligible node, whose full drop set is the hub's, can therefore immediately adopt a
current announcement. With current ordered records it has no pending drops, before any
assumption of hub stabilization. `RecordReplies.lean` preserves held-prefix custody across
the full recovery union. A fresh response completes either from its matching request prefix
or from the held pruning boundary. `SerialReply.lean` proves that a live serialized call's
record snapshot has not changed, and models the actual own-response reset separately from
filtered notification learning. Other drivers' allocations advance the shared request
counter without adding a slot in this driver's projection. Notifications are handled only
outside a running sync round.

Notifications have no request id. `NotificationControl.lean` instead counts their finite
old logical frames in flight and in queues: arrival transfers credit and consumption spends
it. It assumes a consumptive stream/channel, with later publications from the current
history, rather than arbitrary infinite reinjection of obsolete frames. Fresh notifications
may continue forever. `FreshObservation.lean` separately forces an own response, because a
current notification can be ignored below an obsolete known sequence. That own response
repairs the pair; truthful later notifications preserve it.

`RecordEpoch.lean` accounts for the old announcement and persistent received-record debt
carried into a fixed-record suffix. Fresh Fetched replies announce only the fixed list, but
retain an equal-record announcement while receipts still need reconciliation. Preparing a
different list can retain its receipt without increasing the old-announcement credit; taking
it consumes every receipt, including when the applied list stays unchanged. Receipt debt
survives reopening, unlike the volatile announcement.
Adoption may invalidate a retained realization plan. A stale-plan error makes the daemon
reopen, clearing the plan and resetting knowledge. A finite credit bounds these adoptions
and stale-plan reopens without pretending that knowledge survives an error. Other failures
can reopen without increasing this credit; their eventual cessation has a separate argument.
Freshly surveyed realization still requires the adapter's scoped translation and
object-availability contract.

`EarlyEntry.lean` uses the driver's stronger round scheduling: knowledge cannot chase notices
inside a running round. Until current records are applied, a push is refused before its
expected head is read, and therefore cannot change knowledge either. A frozen known pair
has only finite local closure, plan, advance and merge work before the next RPC or idle.
A current fetch is reconstructible and adoption runs first at an eligible node.
`EntryAssembly.lean` joins their finitely many entry cuts. Shared ordered-record identity
and custody then derive empty pending and disable both core fix-ups and publication tips.
Finitely many automatic semantic writes remain an explicit premise, distinct from those
derived core-write bounds. This includes cleanup inside a busy call and writers in the
round's prelude, as well as idle housekeeping; the boundary is detailed below.
`HistoryWindow.lean` carries the strict raw history from the
earlier record cut to this later entry; nodes need not already know the latest sequence.

The separate `EarlyEntry.Burst` argument counts locality on the fixed raw known closure,
frontier coverage by the known images, heads, and queued plan entries. A fresh survey spends
a nonlocal raw operation; a queued realization may already be local because of batching,
but still dequeues an entry. Its executable `stepB`, proved sound, checks actual core
snapshots through `localBurst`; forgetting to pop the queue fails the fixed rollback trace.
`local_burst_conforms_across_a_pending_namespace` also checks the real adapter: it builds the
combined raw DAG from the hub and node stores, keeping the known operation and its renamed
node image distinct. This argument ends at the next RPC or core idle. It excludes
record-taking advances and does not bound subsequent daemon housekeeping. Finite immutable
metadata support derives fixed image names within a frozen-known prefix; append-only
successful realizations then derive locality monotonicity (`local_grows_after_inputs`).
`Control.Naming.settles` derives its cutoff inside the hypothetical unending prefix, using
partial pending-name normalization and immutable metadata on finite support. It assumes no
single finite support for all future moving heads. The normalizer's support and
mapping-retention laws remain native correspondence obligations.

`EarlyEntry.Control` extends that argument across complete metadata calls. Its raw survey
walks through nonlocal operations with bodies; readiness and missing bodies or objects are
computed from those inputs, with soundness proofs. `rawControl` checks the shipping core's
choice against this computation, and `callB` checks burst and completed-call field effects.
The six-part rank additionally counts missing bodies and per-operation objects, with unknown
bodies never considered object-ready. `raw_recovery_choices_and_calls_match_the_model` checks
the core's choices and consumed hub replies on a raw chain with independently missing bodies
and objects, different local frontiers, pending drops and record comparisons.
`raw_round_yields` reaches the next RPC or core idle before a first fresh observation, without
assuming current records, a stable hub or a single raw embedding. It excludes the finite
record-taking steps and checks the remaining local field effects. Driver fairness must still
schedule the next start-fetch after idle and complete individual calls.
`fresh_head_reached` uses that scheduling to derive a fresh own head reply: a refusal updates
heard records, preventing another push with the same stale record offer. It constrains heard
records only across non-idle core steps, allowing notices between rounds. After a fresh
fetch, `fresh_fetch_takes` uses canonical bodies at the next decision point, after preparation,
and lets `GetObjects` bring missing objects. The six-part rank forces record-taking or
already-current records, using only the active prefix of that round; whole raw-ancestry object
availability immediately after receipt is not assumed. Equal records can still need adoption
to consume custody; `RecordEpoch.needsRecords` and its active receipt guard distinguish that case.
`raw_entry_reached` joins fetch and push replies, excluding an incomplete push by its conditional
upload-closure law. `raw_entry_persists` retains entry after ordinary failures and their reopens
stop, deriving that an entered node's push cannot cause an incomplete-upload reopen. These are
still component results: their inputs must be the actual sampled daemon events and packet.

`HubSuffix.lean` works on raw operation vertices in a growing acyclic graph. Its packet
invariant derives, from policy guards, when a current-generation sender still holds the
head it sent. Every other move-capable packet belongs to a finite earlier list, whose
targets pay for its movements. Under finite eligible maintenance writes, the hub's head
and sequence stabilize; acceptance is not assumed finite. `NodeSettle.lean` gives the next
local-control argument: its branch-ordered rank falls until a node is settled or emits a
proper push from the settled hub head. `PacketAcceptance.lean` separates its primitive checks
from the hub's actual decision and rules out refusal, rejection, idempotence and incomplete
closure for the proper packet. Upload coverage uses the actual base-image frontier after
server-generated contraction bodies are present; the raw expected-head difference is only
the no-renaming case. `RecoveryBridge.lean` uses that packet's decision, allows a later local
response/reopen cut after hub stability, and joins all nodes' convergence cuts. These are
component theorems; the joint event replay and assembly below supply their common run.

The joint system now supplies per-event refinements. `NodeSys` keeps each node's scoped
embedding into the same raw graph and retains immutable requests while other nodes run.
`HubLedger` derives packet coverage from those actual request lists. `HubNodeSteps` expands
local events, including a full-frontier advance followed by its optional merge;
`HubAnswers` uses the actual accepted request and guards. `HubHistory` derives the history
window before node entry. `SysFreshCuts` derives both consumed-old-message cutoffs from the
joint transitions: later calls use fresh slots, and notifications leave their queues exactly
once. It does not require unread messages to disappear. `CallBatch` justifies sequential
native calls and interleaved physical request ids under injective correlation.
`RequestBounds.hub_stabilizes_sys` now constructs the expansion from those same joint events,
including finite maintenance: monotone generations cannot hide a maintenance write between
equal endpoint generations. Initial requests remain in the old-packet budget even if their
sender is ineligible; alignment is needed only for the actual moving answer's fresh request.
`SysAcceptance` couples the actual answered request to one executable decision, carrying the
conditional primitive laws of that same decision. It does not quantify over other executable
states that happen to have matching head and sequence fields. These primitive laws still need
their native correspondence; the theorem does not establish them by assuming acceptance.
`eligible_system_converges` composes the actual hub proof with local settling and retains
agreement of the physical raw heads with the hub. Only newly issued pushes must finish;
orphan requests from an old client session need never drain. This is the eligible-suffix
component; the assembly below derives entry, pending-name stabilization and eligibility of
every surviving machine. A node with pending drops translates hub operations into its own
namespace, so it cannot use the eligible node's single raw embedding unchanged.

`SysAcceptance.no_forever_pending` supplies the separate raw-control argument for such a
node on a stable hub. Finite local and completed-call work derives a pending push; the actual
raw publication decision would accept it and move the hub, a contradiction. The packet's
offered records, the records last heard and the hub's current records are bound separately:
the core's `differ = false` alone does not establish the hub's record comparison. The
`RawPublish` decision is checked through `rawPush` against all five shipping outcomes. The
assembly below derives the cuts' guards and uses actual fair-call sampling and the local
immutable-input and upload/naming contracts. The component theorem does not assume an
eventual push or identify original-operation ids with raw ids.

`NodeSysEntry.filt` constructs the eligible nodes' fine system from a coarser hive observation,
freezing the other node slots and omitting their fresh requests and replies. `filt_step` proves
each observed event becomes a fine-system event; noneligible writes become raw graph growth,
and their fresh answers become frames. Old requests remain in the finite initial budget.
The observation starts after eligible nodes have handled a fresh post-record-cut head and
taken current records: before then, even an eligible node's obsolete known head can have a
different node-space image. Ghost noneligible replies and notifications remain in the coarse
observation when native consumers take them; its virtual counter is distinct from physical
call ids. Native assembly must derive that entry cut and the noneligible-answer frame law
from fixed records and the actual packet decision, rather than hub stability.
The filter preserves the action label as well as the eligible slots. `hive_filtered` derives
its initial invariants with inactive root dummy slots for noneligible nodes; those machines
need no single raw embedding. It also derives the packet-owner alternative: an answered
packet is from an eligible node or was already in flight at entry. `hub_stabilizes_hive` and
`eligible_hive_converges` carry hub stability and eligible physical-head convergence back to
the coarse observation, transferring actual scheduling, push completion and packet decisions.

`raw_noneligible_answer_frame` derives the fresh noneligible answer's frame from native
packet/record effects. It splits on offered/current record equality; it does not assume that
noneligible nodes already applied the current records. In the accepted branch alone, matching
records, complete custody, unpublished pending originals and current pending-name coverage
make unchanged ordered records impossible. The coverage law matters: a superseded raw alias
can name a surviving rewritten original. This algebra needs no original-history executable
trace or noneligible node embedding. The source bindings below connect it to the actual
packet and the derived entry cut.

The conditional `SysAcceptance.hive_converges` assembly now joins record/drop stabilization,
record-credit cuts, entry and persistence, eligible-system convergence and the noneligible
contradiction. Its data are sampled from one observation, including the same actual push and
its handling time; hub stability then derives that decision's frame. A sampled step runs to
the completion of its request batch. A separate frame connects that result to the next
post-prelude reading, only where the derived naming cut makes the names and metadata stable.
It preserves available bodies, objects, locality, the canonical head readings and the retained
plan. Completing a saved rewrite can still move physical heads. Locality is not required to
grow while naming changes.

`NativeEvents` constructs the run recursively from event data. Each event's bindings name
the individual call's source obligations; `observed_hs` derives the eligible system's steps.
The filtered run's invariants are carried by induction, including the invariants a later
reply or notification needs, instead of assuming them separately at every callback.
`removed_eligible_push` identifies the exact request and packet of a push decision when an
eligible request leaves. An answer to another machine carries its actual post-answer hub
snapshot; its binding must establish that the snapshot stayed unchanged, using
`raw_noneligible_answer_frame`, before that event is filtered as a frame. Classifying its
sender alone does not supply that fact. Each binding is a local source contract; the replay
derives a system execution from those contracts and the initial snapshot.

`FineAssembly.fineAt_of` uses that replay to assemble the fine system. Its history invariant
keeps previously answered eligible replies and notifications tied to past hub snapshots as
the hub advances. `hive_converges_observed` supplies the lower assembly's fine-system premise
from event data, per-call laws and an initial snapshot. It derives the freshness of consumed
replies and notifications from the old-effects cutoff and completed request batches. A later
completed batch began after an earlier one completed, so its actual head-bearing reply was
requested after that cutoff. Notices name the state immediately after the acceptance that
published them. `NativeEvents.RecordView` connects the raw observer's applied identity, the
fine node's identity and the original-drop record view. Persistent raw entry fixes the applied
identity; eligibility and custody imply no raw pending names. A local record-effect binding
then derives stability of the fine hub's record identity from the original-record cut; it
does not identify different raw encodings of the same dropped-original set.

The resulting retry/response theorem is conditional on the explicit source contracts and
environment described below. It derives the progress cuts, eligible-system convergence and
entry of every remaining participant. Neither a stable hub, eventual eligibility, eventual
fresh knowledge nor a forever-successful round is a premise. A native fetch can update
knowledge before its following objects call finishes, while the system retains the
exchange's starting pair until the batch completes. The latch binding relates completed
observations; it does not equate every intermediate callback. Likewise, matching applied
records does not equate whole normalizers: one machine may have additional pending drops.
`Contract.cpar_absorbs_subset` and `cid_absorbs_subset` instead prove that a body already
contracted by a larger set stays unchanged under a subset. `image_absorbs_subset` gives the
singleton image of a surviving body; `anc_cpar_survives` covers its whole closure, including
the head. When drops name originals, `image_original_survives` and
`image_ne_dropped_original` exclude every version of a dropped original without assuming
originals distinguish raw versions. `PresenceContract.sid_absorbs_subset` also keeps the
presence stamp and the cumulative dropped set. Their native use still requires a complete
canonical-body construction and survival of the sent head. An incomplete metadata lookup's
identity fallback supplies neither. None of the source laws may substitute for the progress
the assembly is meant to derive.

The hub's remembered drops and cached renamings are separate too. A drop republished beside
the remade hub's current history can have no cached image: `is_superseded` recognizes it,
while `current` returns its input unchanged. The native store regression
`a_drop_outside_the_hub_head_is_remembered_without_a_cached_image` checks that case and its
reopening. The pending proof now uses `not_dropped_of`: whole-ancestry original survival
excludes remembered names and cached keys, through `NodeSys.Exec.unsuperseded_of_normal`.
A remembered raw name has a dropped original; a cache key has a dropped original in its raw
ancestry. With the hub's drops a subset of the node's, neither can mark a normal sent body.
This needs no equality between the cached lookup and full normalization, and accounts for
presence stamps without identifying a raw id with an unstamped structural term.
The earlier fixed-point lemma is retained separately.

The environmental premises are explicit: finitely many surviving participants and a bounded
dropped-original basis; an eventual record-safe suffix with no further hub remake, body loss,
gc invalidation or ordinary I/O failure; finite user activity and automatic semantic writes;
fair resumed rounds; correlated serial calls that complete; and consumptive old replies and
notices. Record identities identify their full ordered lists. The local source contracts
include canonical closure, object adequacy, custody, naming, metadata, individual call effects
and the initial snapshot. Focused native checks and executable component checks connect those
contracts to the code; the theorem does not formally verify every Rust execution.

Automatic semantic writes include settings reconciliation and workspace restoration before
a round; all five idle routines; working-copy replacement inside `advance_to`; delayed writes
that notice a user's operation abandonment; and late-operation reparenting after record
recovery. Protocol merges, realization and record adoption have their own model steps. Git
export copies keep their canonical form. An advance with no additional automatic write has
the full-frontier effect; the theorem uses that law only after the automatic-write cutoff.
It does not prove that finite user and configuration changes make these routines stop.
`workspaces::forgotten_working_copies_can_be_abandoned` pins why inline cleanup belongs in
this premise: the actual `Advanced(B)` endpoint is a new canonical child of the singleton
target B, written to replace this machine's abandoned working copy.

The hub-side event projection separates a push's writes, including generated contraction
bodies, from its decision. Read replies have a computable observation of the hub before and
after and the reply's fields: `checkAnswer`, with `HubAnswer.observed_step` proving its
soundness. The `hubRead` route compares that observation against the shipping `Fetch` and
`GetObjects` handlers in the native pending-namespace fixture. Full record states are interned
by equality, including their digests. This does not construct the node's labels, request slots,
or complete system trace.

Own writes need not create new global vertices. The native
`independent_merges_can_reuse_a_canonical_operation` case makes two copies merge the same
frontier with equal operation metadata: the second reuses the first copy's canonical id.
`GrowR` allows that reuse, and `NodeSysExec` checks both writes through the `nodeGrow` route.
One canonical body retains one raw id; a label is reused too when the node already has it.
The native case includes a receiver that realizes the merge detached before rollback, then
recreates that merge while advancing: neither a raw vertex nor a label is added.
The fine system and its suffix refinement allow fresh raw writes, global reuse, already
labelled merges and ancestor pruning. jj first removes heads below another head, then merges
those left; the local rank uses only that the retained heads cover the original frontier.
The native case also leaves an ancestor beside its merge through the shipping head-store
update, then checks that the core removes it without changing the complete canonical body set.
Constructing the full native event projection remains open. Labels for an unknown head's
ancestry are ghost structural exposure, with availability still false until bytes or
realizations arrive; receipt of a head alone does not supply its body.

Physical heads can alias a single canonical body too. The native
`interrupted_git_export_can_leave_aliased_operation_heads` case makes a real export
replacement and leaves both physical operations as heads through the shipping head store.
Reading them gives duplicate canonical heads; the next merge can write a new canonical child
with their one canonical parent. A native refinement must normalize these physical heads
before using unique canonical heads in the fine suffix; duplicate readings cannot simply be
discarded as an invisible step.

Native metadata custody is a separate boundary from local realization. Whole records retain
the canonical bodies, parent-operation closure and views of their names. Pending names are
matched by immutable identity to the raw known hub history after local abandon discovery;
an incoming record clears the same original under another name. The two native regressions
`record_bodies_keep_pending_drops_named_after_hub_rollback` and
`lost_records_follow_an_older_name_the_receiver_never_held` exercise both directions, including
republishing to a replacement hub. `PendingEpoch` proves the finite alias cutoff once pending
originals stop growing and known heads belong to the fixed-record history window. Its step
relation allows some originals to normalize while other bodies are still arriving, requiring
agreement only among aliases of an original whose name changes. `RawEvolution` and `GlobalRaw`
derive that window without assuming the later fine control trace.
`pending_names_settle_with_old_known` also handles an obsolete known pair: after old
observations and reopens stop, knowledge either remains fixed or enters the window. A fixed
head's own unique originals suffice, without comparing its ancestry to the new window or
assuming that a fresh observation ever arrives. Native assembly still must establish the
per-step known-source rule and partial-normalization correspondence. The source-indexed
variant reserves an index for the obsolete head and indexes the current history by observation
time; an obsolete native sequence can be higher than the current one after rollback.

The native receipt boundary now keeps records before preparation writes any local operation,
without counting them as applied or acknowledging them to the hub. Lost receipts become
pending together with contraction of their local versions. Their effects, once applied, also
justify retaining their readable prefixes among earlier records. The native departure
regression checks equal-record receipt recovery against `RecordEpoch.exec`, including its
decreasing credit, and exercises a successful departure and two rollbacks. Another native
regression stops before the publisher's fix-up: missing WORK timestamps are recovered from the
exact original in retained record metadata, without replaying stale shared settings.

Raw translation now normalizes known dropped originals through newly received ancestry,
including old names never previously mapped on this machine. It does not infer an unowned
abandonment from missing ancestry. The record identity and custody bindings feed the derived
record-control cutoff and suffix assembly described above.
The object-transfer contract also checks the saved raw fetch base's objects before using it:
a restore, abandonment and real jj gc can remove those objects while a local image remains.
`fetch_base::collected_objects_of_an_abandoned_fetch_base_are_fetched_again` covers a live and a
reopened adapter, including the initial fetch/import before head discovery. Without rechecking
before that fetch, the hub's omission claim prevents the missing objects from arriving.
An empty objects reply is also validated: a hub remake can leave a running sync requesting
an old head without another fetch. `objects::an_empty_object_reply_retries_from_the_remade_hub`
checks that this fails, reopens and completes a fresh round before another machine republishes.
The generic `Serial.object_recoveries_stop` credit lemma bounds obsolete-request recoveries
given preserved request adequacy and a reset that restores it; the source invariant includes
remaining calls in a batch and truthful have claims, not just the stored known head. It must
be established after old effects cease, rather than classifying protocol-induced failures as
ordinary I/O failures assumed to stop.
An incomplete upload ends a production driver round with its documented refusal; a bounded
retry trace in the lower-level hive harness alone does not show one endless driver round.

That gap has a real-repository counterexample:
`a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup`. After interrupted adoption and
hub rollback, the hub accepts a cached fix-up that does not originally descend from its
expected head: the push drops that head, whose surviving images are below the fix-up. The
trace converges. This is valid contracted ancestry, but `SStep.sup` and `SPStepR.supPush`
require original ancestry and cannot represent this acceptance. `ContractedExec.lean` now
extends the core harness's finite original-operation submodel with that comparison; it
does not change the meaning or claimed invariants of `SRStep`.

`ContractOrder.lean` models this comparison as `Below`: every surviving image of the expected
head is below the new head. `belowB` also checks that the image is nonempty, as the hub does.
`below_two_step` connects contraction of an already contracted history with contraction by
the union; `below_contracted_iff` connects original and current-graph ancestry of the images.
For a fixed drop set, `stable_suffix_chain` recovers a reflexive original-ancestry chain of
surviving heads. It does not repair the earlier history or establish strict changes, the
epoch projection, or the full protocol invariants. The real trace checks the accepted push
against `belowB` through the `contractedAncestry` oracle route, supplying its immutable DAG.
`RecordStability.lean`'s `eventual_original_chain` composes the record cut with that relational
argument: a trace of surviving hub heads compared under each resulting dropped set has an
eventual original-ancestry chain. It takes the immutable graph and contracted comparisons
as premises; it does not derive their physical-store projection or strict head changes.

`ContractedExec.cexecAction_sound` targets the explicit union `ContractedRStep`. Old checked
transitions remain available, with a tighter rejection guard where a contracted packet is
acceptable. Added advancement uses every surviving image, and preparation changes the
frontier and record custody in one boundary. `cexecAction_ok` preserves record custody;
`imageAdvance_safe`, `preparedAdvance_safe` and `imageAccept_safe` prove the new primitive
cases of `ContractedSafety.Safe`. They do not prove a global invariant of the union relation.
`old_expected_accepts_eventually_stop` gives a finite credit argument after dropped sets
stabilize, under its explicit local-step premises. This original-operation component does
not prove convergence of every network action. The raw-namespace assembly above handles
canonical versions and normalization in their birth parents through its explicit projection.

Cached restoring work alone does not imply that its drops are published. The real regression
`pending_drops_get_a_new_tip_when_the_hub_already_has_the_cached_fixup` reaches equal heads
and ordered records while an abandonment is still pending, after an orphan realization is
published without its lost record. Before the fix, both cores and idle maintenance stopped
there, violating dropped-set convergence. The core now requests a neutral child on the
current head; it preserves current state and gives the pending push a distinct id.
The test checks that acceptance publishes the drop, and that an unsubmitted request and a
restart reuse that child. `a_cached_fixup_publishes_pending_drops_even_when_its_head_is_known`
also requires the affected node to publish, without waiting for another node.

These boundaries motivate the retry/response bridge in
[#78](https://github.com/bos/jj-musubi/issues/78). A failed sync can leave an accepted hub
head, partially received data, or a newly written fix-up. `supFix` combines fix-up creation
with acceptance; a failed push leaves the creation without its compensating decrease.
The production cache may then return no new restoring operation. A neutral publication tip
now prevents that cache from causing an aligned node to idle with pending drops. The
raw-namespace model separates creation from acceptance and compares actual contracted ids;
the old policy's original-operation identities cannot represent every native transition.
The record-control, entry and accepted-history arguments above supply the bridge beyond
the retry bounds alone. Adopting an obsolete
ordered-record list can increase `recordLagE` even when no dropped set changes. The
record-aware theorem covers taking current hub records, not arbitrary old announcements.

The intended environmental assumptions are eventual cessation of user operations,
abandonments, hub regressions and disruptive crashes; resumed participating nodes; finite
influence from obsolete replies; eventually successful honest retries and transfers; and
fair scheduling of enabled local work. Permanent repository errors, unavailable objects or
unsupported jj merges do not satisfy those assumptions. Fairness must describe actual
work being scheduled, rather than assume that the rank eventually decreases. The assembly
connects the explicit assumptions to finite record/fix-up disturbances and completed
progress, with the composite repository source contracts described above. Automatic semantic
writes stopping remains a separate premise; it is not derived from user inactivity.

Request correlation is relevant but does not by itself supply that argument.
`StreamTransport` consumes the matching pending request, removes it on timeout and drains
pending requests on disconnect. `NodeDriver` processes one protocol call at a time, and
the daemon handles notifications outside `sync`. These facts exclude assigning a retired
call's late reply to a later request, assuming request ids are not reused. A still-live call
can nevertheless return a reply computed before a hub remake. The safety model allows
arbitrary replay, and `learnUnfiltered` permits `known` to move backwards during recovery;
neither finite obsolete delivery nor monotone `known.seq` follows from that model.

`lost_acceptance_and_delayed_fetch_make_progress` checks the two split-exchange lemmas
through the core and the oracle before quiescing. The transport contract checks a canceled
call's reply arriving after a fresh exchange and duplicates of a completed reply.
`replies_only_complete_the_matching_pending_call_once` also sends obsolete and duplicate
frames directly through the stream client's receiver in a fixed order, since service-side
reply inboxes may discard them before they become frames. These checks support the local
boundaries used by the conditional reverse refinement above; they do not by themselves
establish that refinement.

## Modeling choices

- **Operation universe.** Creating an operation assigns the fresh id `next` and fixes its
  parents and objects. The invariant keeps parents' ids smaller than their children's
  (`ParLt`), which makes the graph acyclic. `objs(x)` is taken as already closed under
  object reachability.
- **Sets** are predicates. The node and hub stores are sets of ids. Payload contents are
  global (`par`, `objs`), which models content addressing: equal ids have equal bytes.
- **Network.** `s.net` is the set of every message ever sent. Delivery does not remove a
  message, so it can be duplicated, delayed, reordered or lost. Requests and replies are
  separate messages. Request ids are not modeled: a node accepts any reply addressed to it,
  which over-approximates matching replies to outstanding requests, and also covers a node
  crash losing its in-flight requests.
- **Atomic payloads.** `Push`, `Fetched` and the other bulky payloads are atomic messages carrying
  sets, as [protocol.md](../docs/internals/protocol.md) specifies at this level. `Chunks.lean`
  justifies this: a finished blob is exactly the sent bytes, so a payload arrives whole or not at
  all.
- **The ancestry check** uses the global `parents`. It matters only once the closure check
  has passed, when every operation in `closure(new)` is stored, so it agrees with a check
  over the hub's stored operations.
- **Cas order.** `new = head` is answered `Accepted(seq, head)` before the other conditions
  are checked (`casIdem`).
- **Node-side guards are weakened where safety does not need them**, so the safety theorems
  also hold for a buggy node:
  - `Upload` may send any local operations and objects.
  - `Push` may send `Cas(e, d)` for any `e` and any local `d`, alone or in a merged `push`
    with any local operations and objects.
  - `GetObjects` and `Fetch` may ask for anything; `Fetch`'s operations are chosen by the
    hub from its own head.
  - `Learn` is also allowed without its staleness filter (`learnUnfiltered`), so `known`
    can move backwards.

  The policy's own actions are instances of these. Only one node-side guard of `Model.lean`
  carries weight: `GetOps` requests only operations in `anc*(known.head)`. The merged `Fetch`
  needs none, since the hub chooses the operations, all of them accepted. The model with
  supersedes adds one more: a node never names, as the head of its push, an operation that a
  record it took drops (`sendSup`). A hub that has pruned the record can't refuse that
  operation, so `dropped_never_head` doesn't hold of a buggy node that does.
- **Relaxations of durability, proved safe.** `loseKnown` lets a restarting node lose `known`
  (reset to `(0, root)`) while keeping `staged`, as the Rust node does. `loseVolatile` lets it
  lose `staged` as well. `hubForget` lets the hub lose or garbage-collect any operations and
  objects outside `closure(head)` in the original-ancestry relation. The extended executable
  model preserves operation bodies needed by retained historical heads: an older head can
  be outside the current closure after contracted acceptance. Historical-only objects may
  still be lost. A requested rollback to an incomplete target takes an explicit environment
  recovery choice, remaking the hive. This does not claim that native startup detects every
  damaged prefix or add a hub durability requirement; that physical interval remains open.
- **Ghost state.** `creator`, `isMerge` and `birth` record each op's creator, whether it is a
  merge, and the hub `seq` at its creation; `hist` records the history of accepted heads.
- **Original operations.** `Supersede.lean` identifies each canonical operation a drop renamed
  with its original. A node's operations there include the dropped ones it had, with their
  objects, as an abstraction of the real node, which keeps only survivors; the real hub's
  closure check, and a node's realization, are then taken over survivors, which contraction
  keeps in the same ancestry (`anc_cpar_iff`). Within this fixed-birth-graph abstraction,
  the names are `cid` under each dropped set. Arbitrary native versions can already carry
  normalization in their birth parents; an original label and a party's current drop set
  alone do not give a complete physical-store projection.
- **Translation layer.** It is not modeled. The model assumes what [protocol.md, "Translation
  layer"](../docs/internals/protocol.md#translation-layer) requires: `canon` is injective on
  reachable local operations, `canon(realize(C)) = C`, and realization never creates a canonical
  operation. Under those assumptions, the properties over canonical ids carry over to each node's
  local op log. The abandonment/ref boundary test checks selected properties before and immediately after
  publication; the generated end-to-end tests check all of them at every full convergence
  ([testing.md](../docs/internals/testing.md#generated-end-to-end-tests)).

## What the proofs assume of the implementation

The model takes some steps as atomic and some state as durable; the code must make them so.
[protocol.md](../docs/internals/protocol.md) states each rule
(["Hub"](../docs/internals/protocol.md#hub), ["Policy"](../docs/internals/protocol.md#policy),
["Chunked blobs"](../docs/internals/protocol.md#chunked-blobs)); these are the ones the proofs
rest on:

- **Hub:** a `Cas`'s checks and its update of `head` and `seq` form one critical section. The
  new `head` and `seq` are written before the reply or notification goes out, so that they
  survive the process crashing: replying first and then losing the update would break
  HubMonotone and KnownIsHubHistory. (A power cut can still lose them; that is
  [`Regress.lean`](#a-hub-that-goes-back-regresslean).) `closure(head)` is durable whenever
  `head` is. Every `Head`, `Accepted`, `Rejected` and `Incomplete` carries a `(seq, head)`
  the hub actually had.
- **Node:** stage and realize only operations in `anc*` of a head the hub accepted; push only
  local operations; `Merge` takes all current heads as parents. No other node-side check is
  needed for safety: the `Upload` and `Push` guards, the order of policy steps, and `Learn`'s
  filter matter only for liveness and efficiency.
- **Supersedes:** the hub refuses a push whose new head it has dropped, and takes a dropped set
  only with a push that leaves the new head; a node advances to no head it has dropped, and
  applies a dropped set only once none of its heads is in it. When the hub takes a dropped set,
  it holds the contraction of its history: it computes it, rather than taking a node's word.
- **Chunks:** use unique session ids, or tag chunks with the blob id; ignore duplicate and
  overlapping bytes; check `hash(assembled) = id` at `Finish`, and restart on a mismatch;
  treat a stored blob as finished. A receiver may instead keep only a contiguous prefix,
  report its length, and check the hash once it reaches the claimed length, as musubi's does
  (`preach_abs`).

The real repository's `advance` can also finish taking records. It holds them in the same
save that counts their renaming before moving heads; after an interrupted move, recovery
finishes the heads and workspace records. Holding them only in a later `Adopted` step lost
the responsibility to republish a drop if the hub rolled back in between, and the machine
could retry the same rejected push indefinitely. The real-repository races
`a_sync_stopped_while_taking_an_abandon_the_hub_then_loses` and
`taking_an_abandon_resumes_where_it_stopped` check the completed advance and its internal
save/head/workspace boundaries. They close that concrete implementation gap, not the full
retry/response refinement in [#78](https://github.com/bos/jj-musubi/issues/78).

## The executable model and the conformance oracle

The relational model can't be run, since its sets are predicates. To check the Rust core
against it, `Musubi/Exec.lean` gives a version that can, and `Oracle.lean` serves it as JSON.
[conformance.md](../docs/internals/conformance.md) is the contract, and describes the test
that checks the Rust core against the oracle.

1. **Relational to executable.** `EState` is a finite, computable state. Operations, nodes
   and the ghost history are association lists; sets are lists; `net` is a list read as a
   set. `abs : EState → State` maps it to the relational state.
   `execStep N es a : Except String EState` evaluates every guard of the matching relational
   step, and on failure returns `"<action>: <failed guard>"`. It decides `anc*` by one
   downward sweep from the descendant (`ancL`), exact because parents have smaller ids, and
   `ClosedAt`, `maxSet` and membership in `net` directly; set-valued message fields are
   compared as sets.
2. **Executable to oracle.** `Oracle.lean` reads requests and writes replies, one JSON object
   per line, flushing after each. A rejected or malformed request leaves the state unchanged.
   Decoding, encoding and the request loop are in `Musubi/ExecJson.lean`; all protocol
   logic is in `execStep`, `sexecStep` and the explicit extension `cexecAction`.

Theorems (`Musubi/ExecSound.lean`):

- `exec_sound : a.goesBack = false → execStep N es a = .ok es' → Step N (abs es) (abs es')`.
  Its only hypothesis is that the action is not `hubRegress`. `execStep` first checks the
  one well-formedness property its decision procedures rely on: every recorded operation's
  parents are below it (`parOK`).
- `abs_initE : abs initE = init`.
- `exec_reachable : ExecReachable N es → Reachable N (abs es)`: every state reached from
  `initE` through accepted actions other than `hubRegress` is relationally reachable, so
  every safety theorem holds in it.
- `exec_inv : ExecReachable N es → Inv N (abs es)`.
- `exec_rsound : execStep N es a = .ok es' → RStep N (abs es) (abs es')`, for every action.
- `exec_rreachable : ExecRReachable N es → RReachable N (abs es)` and
  `exec_invR : ExecRReachable N es → InvR N (abs es)`: with `hubRegress`, every state is a
  state of the extended system, and the theorems of `Regress.lean` hold in it.
- `exec_remake : ExecRReachable N es → run N es remakeActions = .ok es' →
  abs es' = (abs es).remake`. `remakeActions` is `hubRegress 0`, then `hubForget [root] []`:
  a hive made again, empty, as `HubDir::remake` makes one and as the conformance test's
  `remake` rule does. `remake_reachable` proves it a run of the extended system.
- `measureE_eq : es.parOK = true → es.measureE N = measure N (abs es)`, `rmeasureE_eq` the
  same for `rmeasure`, and `convergedE_iff : es.convergedE N = true ↔ Converged N (abs es)`.
  `mem_upOpsL` and `mem_upObjsL`: `upOpsL` and `upObjsL` list `upOps` and `upObjs`. The oracle
  answers `measure` and `upload` requests with them.

With supersedes (`Musubi/SupersedeExec.lean`, `Musubi/SupersedeExecSound.lean`), `SEState`
adds to an `EState` the hub's records, in the order it took them, and how many of the first it
has pruned, with a ghost copy of both as of each sequence number, each node's dropped set, the
records it took last and every list of records it has taken, and the supersedes and
announcements in flight, each announcement with how many of its records were pruned.
`sabs` maps it to an `SState`. `sexecStep` runs every action of `execStep`, checking `HeadOK`
and `HeadsOK` too, and the actions of `SStep`:

- `sexec_ok`: every action keeps `SEOK`, which holds of `initSE`: a node has dropped the
  operations of the records it took, and the hub has pruned no more records than it has.
- `sexec_allPruned`: every state reached has `AllPruned`, since the hub prunes only records
  every node has taken, now and as of any head it can go back to (`SEPruned`), so
  `eventually_convergesS` applies to it.
- `sexec_announced_held`: every node the hub waits for has held the records it pruned. Every
  announcement, however old, agrees on its pruned records with a list its node has taken
  (`SEHeld`), so `adopt` takes it: a node that took fewer records since takes the hub's all
  the same.
- `sexec_sound : SEOK ses → sexecStep N ses a = .ok ses' → SRStep N (sabs ses) (sabs ses') ∨
  sabs ses' = sabs ses`, for every action, and `sabs_initSE`. So `sexec_reachable` and
  `sexec_inv`: every state reached is `SRReachable`, and `SInv` holds in it, as do the
  theorems that superseded ids never come back.
- `smeasureE_eq` and `sconvergedE_iff`: the set-based `smeasure` and `SConverged`.
- `RecordLiveness.lean` adds `RecordConverged`, requiring the ordered applied records to
  match the hub's too, and `recordMeasure`: `(smeasure, recordLagE)`. `recordMeasureE_eq`
  and `recordConvergedE_iff` connect their computations to the original model. The extended
  oracle returns the record-aware `ContractedMeasure.rmeasureCE` suffix as part of
  `smeasure`, record debt as `recordLag`, and the stronger convergence check as `converged`.
  `rmeasureCE_without_drops` proves exact agreement before drops. Its new component facts
  and the generated strict-decrease checks do not establish full union termination.

The set abstraction alone does not establish record agreement: after a remake, a machine
may republish two old drops as one record while another retains two records with the same
union. `regrouped_records_conformance` reaches this through the core and oracle.
`recordMeasure_decreases` and `recordPolicy_wf` cover projected `SPStepR` progress and the
record-only adoption omitted by that policy. Set-based progress may increase record debt,
so it comes last. `recordLag_adopt_lt` and `recordLag_le` bound repairs by the number of
machines while the hub is fixed. `record_finish` proves finite completion from abstract
convergence where every node has dropped what the hub pruned (`AllPruned`, as
`sexec_allPruned` gives), preserving the entire abstract state. `reconcile_executable` checks
the announced-record adoption, its head guard and its pruned-prefix check. `NodeCore` already
follows this rule: it adopts differing record lists even with no missing drop, opening the
executable push guard.
The oracle/harness check both record debt and concrete convergence independently of the
set measure. This does not prove the asynchronous reply/retry scheduling bridge (#78) or
collision resistance of record digests; see [conformance.md, "Liveness"](
../docs/internals/conformance.md#liveness).

It is stricter than `SRStep` where the implementation is. The hub takes every push it
accepts as a supersede, carrying the node's dropped set and the records the node took last
(`sendSup`), and accepts it only if those are the hub's records (`hubSupAccept`); it adds a
record only for what the push drops that it hadn't. It refuses a push whose node's records
aren't its own, changing nothing (`hubPushRefuse`), since that node's ids aren't the hub's, and
one whose new head is among the records it remembers or the push drops beyond its records. A
node takes the hub's records as announced (`sendD`, to a node of the hive, `adopt`), and the
records it took last become those, if it has held the announced records as far as they were
pruned. The hub prunes its first records (`prune`) once every node has held them; `recs` stays
whole, standing for what a push's records must match, and the hub checks a head only against
the records after those.

`PresenceExec.lean` does the same for presence: `presentB` and `latestB` are proved to compute
`Present` and `UMax` (`presentB_iff`, `mem_latestB`), and the oracle answers presence requests
with them, as [conformance.md, "Presence"](../docs/internals/conformance.md#presence) describes.

Where the executable model differs from the relational one, or its JSON needs a note
([conformance.md](../docs/internals/conformance.md) gives the [wire
format](../docs/internals/conformance.md#wire-format), and what fakes of the model's state must
match, such as staging never being cleared):

- **Notifications.** The hub's publication of a new head is one internal `EMsg.notifyAll`,
  which stands for `head n notify seq head` for every node `n`, and appears in JSON as one
  such message per node.
- **Sorting.** State arrays are sorted ascending without duplicates, operation parent lists
  included (the order of parents never matters to the model), and `net` by
  `(msg, node, compact JSON of the whole message)`.
- **Extra guards.** `userOp` and `merge` also check that their parents are below `next`.
  The invariant implies these checks, so they never fire in a reachable state.
- **No bound on nodes.** The hub actions do not check `node < nodes`, just as the relational
  hub steps don't; a matching message in `net` already implies it.
- **The hub going back.** `hubRegress i` changes only the hub's `head` and `seq`: stores,
  nodes and `net` stay, and so does the ghost history, entries above `i` included. The next
  accept records entry `i + 1`, which then shadows the old one, as the relational
  `hubAccept` overwrites it. The ghost history is not part of the JSON state, so a test may
  equally truncate it to the entries up to `i`.
- **The hub forgetting.** `hubForget ops objs` names what the hub keeps, as
  `SyncStep.hubForget` does.

The oracle also answers with the prefix receiver of `Chunks.lean` and the naming rule of
`Names.lean`, whose definitions run as they are, so they need no executable form of their own
([conformance.md, "Chunked blobs"](../docs/internals/conformance.md#chunked-blobs) and
["Workspace names"](../docs/internals/conformance.md#workspace-names)). `Refs.lean`'s functions
are executable as they are too, over any `RefAlg`: `RefsExec.lean` runs them on numbered
targets, with jj's merges as a table each request carries, and the oracle answers refs requests
with them ([conformance.md, "Per-machine
refs"](../docs/internals/conformance.md#per-machine-refs)).

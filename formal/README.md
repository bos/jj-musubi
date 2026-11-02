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
new child even when the restoring work is cached. `publication_retry` proves that another
write without intervening head-equality or cache changes emits neither kind of work.
`publication_tip_cached` proves the tip leaves the restoring cache untouched. These are local
write-boundary results, not a bound on tips across arbitrary later replies or adoptions.

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

That gap has a real-repository counterexample:
`a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup`. After interrupted adoption and
hub rollback, the hub accepts a cached fix-up that does not originally descend from its
expected head: the push drops that head, whose surviving images are below the fix-up. The
trace converges. This is valid contracted ancestry, but `SStep.sup` and `SPStepR.supPush`
require original ancestry and cannot represent this acceptance. The core harness's fake
stores share that restriction, so their correspondence does not cover this real trace.

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

Cached restoring work alone does not imply that its drops are published. The real regression
`pending_drops_get_a_new_tip_when_the_hub_already_has_the_cached_fixup` reaches equal heads
and ordered records while an abandonment is still pending, after an orphan realization is
published without its lost record. Before the fix, both cores and idle maintenance stopped
there, violating dropped-set convergence. The core now requests a neutral child on the
current head; it preserves current state and gives the pending push a distinct id.
The test checks that acceptance publishes the drop, and that an unsubmitted request and a
restart reuse that child. `a_cached_fixup_publishes_pending_drops_even_when_its_head_is_known`
also requires the affected node to publish, without waiting for another node.

Establishing that the implementation eventually enters the settling suffix is still part
of [#78](https://github.com/bos/jj-musubi/issues/78). A failed sync can leave an accepted hub
head, partially received data, or a newly written fix-up. `supFix` combines fix-up creation
with acceptance; a failed push leaves the creation without its compensating decrease.
The production cache may then return no new restoring operation. A neutral publication tip
now prevents that cache from causing an aligned node to idle with pending drops, but
mapping its separate creation and acceptance to the policy remains necessary. Also, the
policy compares original-operation identities while the core compares their contracted ids.
The epoch and accepted-history correspondence is still needed; the retry bounds do not
supply it. Adopting an obsolete
ordered-record list can increase `recordLagE` even when no dropped set changes. The
record-aware theorem covers taking current hub records, not arbitrary old announcements.

The intended environmental assumptions are eventual cessation of user operations,
abandonments, hub regressions and disruptive crashes; resumed participating nodes; finite
influence from obsolete replies; eventually successful honest retries and transfers; and
fair scheduling of enabled local work. Permanent repository errors, unavailable objects or
unsupported jj merges do not satisfy those assumptions. Fairness must describe actual
work being scheduled, rather than assume that the rank eventually decreases. The proof
still needs to connect these assumptions to finite record/fix-up disturbances and completed
policy progress, with the composite repository correspondence described above.

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
reply inboxes may discard them before they become frames. These checks support the
boundaries; the full reverse refinement remains open.

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
  objects outside `closure(head)`. All safety theorems hold with these steps included.
- **Ghost state.** `creator`, `isMerge` and `birth` record each op's creator, whether it is a
  merge, and the hub `seq` at its creation; `hist` records the history of accepted heads.
- **Original operations.** `Supersede.lean` identifies each canonical operation a drop renamed
  with its original. A node's operations there include the dropped ones it had, with their
  objects, as an abstraction of the real node, which keeps only survivors; the real hub's
  closure check, and a node's realization, are then taken over survivors, which contraction
  keeps in the same ancestry (`anc_cpar_iff`). The ids each party shows are
  `cid` of its operations under its own dropped set.
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
   logic is in `execStep`.

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
  and `recordConvergedE_iff` connect their computations to the oracle, which returns the
  first eight components as `smeasure`, the last as `recordLag`, and the stronger
  convergence check as `converged`.

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

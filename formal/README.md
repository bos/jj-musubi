# Lean model of the musubi sync protocol

This directory holds machine-checked Lean 4 models of the following. Hive, node, hub and the
other terms are those of [design.md, "Vocabulary"](../docs/internals/design.md#vocabulary).

- The sync protocol of [protocol.md](../docs/internals/protocol.md), with its safety and
  liveness properties, and what still holds when the hub goes back to an earlier head.
- Contracting operations out of a history, as `musubi sync --prune` does (`Musubi/Contract.lean`,
  used by `Musubi/Publication.lean`).
- Chunked blob transfer (`Musubi/Chunks.lean`), from the same document.
- The per-machine state of a replicated view, for one git ref (`Musubi/Refs.lean`; [design.md,
  "Per-machine state in a replicated
  view"](../docs/internals/design.md#per-machine-state-in-a-replicated-view)).
- Which copies a hive shows, one copy being one machine's repository (`Musubi/Presence.lean`;
  [design.md, "Copies that go away"](../docs/internals/design.md#copies-that-go-away)).
- Which repository on a machine is the copy of a key, and which a duplicate made of its files
  (`Musubi/Copies.lean`; [copies.md](../docs/internals/copies.md)).
- The names a machine shows other machines' workspaces under (`Musubi/Names.lean`; [design.md,
  "Which workspaces are this machine's
  own"](../docs/internals/design.md#which-workspaces-are-this-machines-own)).
- How musubi moves the jj operation heads it read earlier while jj commands and the lockless
  `jj op abandon` race it (`Musubi/OpHeads.lean`, `Musubi/OpHeadsRace.lean`; [design.md, "Moving
  op heads"](../docs/internals/design.md#moving-op-heads)).
- [Snapshot publication budgets](#snapshot-publication-budgets), exact approval and cleanup of
  selected unpublished operations (`Musubi/Publication.lean`; [design.md, "Snapshot publication
  budgets"](../docs/internals/design.md#snapshot-publication-budgets)).

The models of chunked transfers, per-machine refs, presence, copies, workspace names, snapshot
publication and moving op heads are separate from the protocol model's
state.

No proof is left unfinished (Lean's `sorry`) and the model adds no axioms. Every main theorem
depends only on Lean's standard `propext`, `Classical.choice` and `Quot.sound`, some on fewer.
The build checks both: it treats the warning a `sorry` gives as an error, and
`Musubi/Axioms.lean` fails if a main theorem depends on any other axiom.

The protocol models are state machines, with states and a step relation. Other
models describe functions over histories or file sets. The protocol's step relation is `Step N`,
for `N` nodes, and `Reachable N s` says that state `s` can be reached from `init`.
Sets are predicates (`OSet`), so
`(s.node n).lops x` reads "`x ∈ local(n)`". *Ghost* state, such as each operation's creator,
exists only to state properties: no step reads it. [Correspondence with
protocol.md](#correspondence-with-protocolmd) maps the rest of the notation.

## Checking

For the contributor workflow, source-contract pitfalls and small Lean iterations, read
[Working on Lean proofs](../docs/internals/lean.md).

Install Lean (for example, via `elan`) and put `lake` on `PATH`.

```sh
cd formal
lake build
```

The toolchain is pinned to `leanprover/lean4:v4.35.0` in `lean-toolchain`. The model uses only
core Lean: no Mathlib, no dependencies. A clean build of the proofs and the oracle takes about a
minute on 4 cores. It checks the axioms of `Musubi/Axioms.lean` and runs the `#guard` smoke
tests in `Musubi/ExecTest.lean`.

`./test/run_smoke.sh` builds the conformance oracle alone (`lake build oracle`), replays
`test/smoke.jsonl` through it and diffs the output against `test/smoke.expected`. The binary
is `formal/.lake/build/bin/oracle`.

## What is proved of convergence, and what is tested

`Safety.lean` proves the protocol's safety properties of every reachable state of the
asynchronous model: lost, duplicated, delayed and reordered messages, and crashes. `Liveness.lean`,
`Merged.lean` and `Regress.lean` prove that the policy converges: every atomic policy exchange
that succeeds lowers a measure, so a run of them ends with every node at the hub's head, also
when the hub goes back to an earlier head. `Merged.lean` shows that merged exchanges have the same
measure, and `pstep_reachable` embeds each policy step in the asynchronous model.

None of this says that an asynchronous run, with its retries and replies that arrive late or
never, takes those policy steps. Convergence of the running system is tested, not proved: the
e2e search checks it at the end of every generated case, and the races and the fault tests check
the parts. The proofs of that bridge, built on the replicated `jj op abandon` records, were
deleted with them. Rebuilding one on `Exec` is a separate project.

## Files

| File | Contents |
| --- | --- |
| `Musubi/Basic.lean` | Sets as predicates (`OSet`), point update `upd`, counting `cnt`, sums `sumN`, indicators `ind`, shared termination/progress facts (`Steps`, `eventually_done_of_progress`), and traces that stop changing (`nat_trace_stabilizes`, `lex_stabilizes`). |
| `Musubi/Contract.lean` | Contracting dropped operations out of a history, as `musubi sync --prune` does: parents (`cpar`) and the ancestry of survivors. |
| `Musubi/Dag.lean` | `Anc` (`anc*`), `ParLt` (parents have smaller ids, so the graph is acyclic), `maxSet` (`max`), and how `anc*` is preserved when a fresh op is created. |
| `Musubi/Model.lean` | The asynchronous model: state, messages, transitions, `EnvStep`, `SyncStep`, `Step`, `Reachable`. |
| `Musubi/Invariant.lean` | `Base`, what every state satisfies, whether or not the hub goes back; `Core`, which adds the original history chain and every node's work below its heads; the inductive invariant `Inv`, which extends `Core`; and the message invariant `MsgOK`. |
| `Musubi/PreserveEnv.lean` | `Base`, `Core` and `Inv` are preserved by `UserOp`, `Merge` and message sends. |
| `Musubi/PreserveSync.lean` | `Base` and `Core` are preserved by replacing one node (`Base.setNode`, `Core.setNode`); `Inv` is preserved by every sync, hub and crash step; `inv_reachable`. |
| `Musubi/Safety.lean` | The safety properties and no feedback. |
| `Musubi/Liveness.lean` | The policy model `PStep`, its simulation in the asynchronous model, the measure, progress, termination and convergence. |
| `Musubi/Merged.lean` | The merged `Push` and `Fetch` exchanges reach states that agree with policy steps on everything the measure and convergence read, with a hub that may have gone back too. |
| `Musubi/Regress.lean` | A hub that goes back to an earlier accepted head, as after a power cut or a remade hive: the extended system `RStep`, the invariant that survives (`InvR`: `Core` with `InvC`, what every step keeps, history chain or not), and convergence once the hub stops going back. |
| `Musubi/Scenario.lean` | A concrete reachable run (a lost Cas race, then fetch, advance, merge, and the merge accepted), showing the model is not vacuous. |
| `Musubi/RegressScenario.lean` | A run of the executable model in which the hub goes back and two nodes then merge the same heads. |
| `Musubi/Chunks.lean` | The chunked-blob model, its safety and liveness; musubi's receiver, which keeps only a prefix, proved a refinement of it, with its own liveness; and its senders, attempt by attempt under a deadline, and in time, with sweeps of what has gone untouched. |
| `Musubi/Exec.lean` | The executable model: finite `EState`, the `Action`s of [conformance.md](../docs/internals/conformance.md), `execStep`; and the liveness measures, convergence, and what a policy `Push` uploads, computed (`measureE`, `rmeasureE`, `convergedE`, `upOpsL`, `upObjsL`). |
| `Musubi/ExecSound.lean` | Soundness of `execStep` and of those computations ([below](#the-executable-model-and-the-conformance-oracle)). |
| `Musubi/ExecJson.lean` | The oracle's JSON codec and request handler, which also checks the preconditions of the model functions it calls. |
| `Musubi/ExecTest.lean` | `#guard` smoke tests of `execStep`, checked at build time. |
| `Musubi/Refs.lean` | Per-machine refs, for one git ref: imports, exports, merges, conflicted remote bookmarks, and `jj undo` and `jj op restore`. |
| `Musubi/Expected.lean` | The conflicted-ref history walk, agreement under operation renaming, termination and the import-agreement boundary. |
| `Musubi/ExpectedExec.lean` | Finite operation DAGs and commit-side selection for the history oracle. |
| `Musubi/Presence.lean` | Which copies a hive shows. |
| `Musubi/PresenceExec.lean` | The presence rule on a finite history, executable, for the oracle. |
| `Musubi/RefsExec.lean` | `Refs.lean`'s slot functions on targets a test numbers, with jj's merges as a table, for the oracle. |
| `Musubi/Copies.lean` | Which repository is the copy of a key: musubi's decisions, jj's config-id rule, and a machine's repositories moved, copied, deleted and replaced. |
| `Musubi/Names.lean` | The names a machine shows other machines' workspaces under, and `#guard` tests of them. |
| `Musubi/Publication.lean` | Cumulative snapshot accounting, exact approval, selected operation cleanup, and checks of the prepared result before installation. |
| `Musubi/OpHeads.lean` | What musubi decides about op heads it moves, as a pure function for the oracle and the code: `same` (`plan::same`); and what it reads of operations. |
| `Musubi/OpHeadsJson.lean` | The oracle's `opHeads` request. |
| `Musubi/OpHeadsRace.lean` | A small model of the op heads among jj commands, `jj op abandon`, `jj op integrate` and musubi's moves, and its theorems. |
| `Musubi/Axioms.lean` | `#assert_axioms`, which fails unless a theorem uses only the standard axioms, for every main theorem. |
| `Oracle.lean` | The `oracle` executable: a stdin/stdout loop around `ExecJson.handle`, which also answers measure, upload, presence, copies, chunks, attempts, names, refs, expected-value, publication and op-head requests. |
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
| musubi's senders (`RemoteHub::upload`, `download`) | `Chunks.attempt` (a window, `m` chunks delivered, `k` replies heard), `Chunks.next`, `Chunks.ARun` (attempts, and chunks arriving late) |
| Time, renewal and sweeps of blobs | `Chunks.TState`, `Chunks.TStep`, `Chunks.refresh`, `Chunks.FairRun` (fair runs, without sweeps) |

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
and jj merges. [What is proved of convergence, and what is
tested](#what-is-proved-of-convergence-and-what-is-tested) says what is known of the real,
lossy system.

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

### Contracting operations (`Contract.lean`)

`musubi sync --prune` removes selected unpublished operations from the history it publishes.
`Publication.lean` contracts the operations' parents with `Contract.cpar`: a dropped parent is
replaced, in place, by the expansion of its own parents, and then duplicates are removed, keeping
each one's first occurrence.

- `anc_cpar_survives`, `anc_cpar_iff`: among survivors, contraction keeps ancestry exactly.
- `anc_congr`: `anc*(x)` depends only on the parents of `x` and what is below it.

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

Attempts under a deadline: a sender sends a window of chunks from an offset; the receiver takes
the first `m`, the sender hears its replies to the first `k`, and goes on from the furthest
prefix they report (`attempt`, `next`). Chunks of a window whose replies it never heard may
reach the receiver later (`ARun.late`), and a downloader goes on from the receiver's prefix,
being the receiver (`ARun.reread`).

- `attempt_progress`: an attempt from within the receiver's prefix, short of the end, that
  hears `k` replies takes the prefix at least `k` chunks on from where it started, or to the
  end, and the sender goes on from there; or the receiver stores the blob.
- `restart_stalls`: an attempt from the beginning, once the prefix holds the chunks it
  delivers, leaves the prefix as it was, however many replies it hears: a sender that starts
  every attempt there never finishes.
- `attempt_decreases`: from any state, an attempt that hears a reply takes `ameasure` down; a
  chunk arriving late (`late_le`), and going on from the receiver's prefix
  (`ameasure_reread`), never take it up.
- `attempts_finish`, `attempts_bounded`: from every state the prefix receiver reaches, a run
  whose receiver hasn't the blob yet has made fewer attempts that heard a reply than
  `ameasure`; one of `ameasure` such attempts has stored exactly the sent blob.

In time (`TStep`), a sweep takes the sender's blob, or what the receiver has of it, only once no
chunk has touched it for `life`, and a chunk renews what it touches at most every `renew`
(`refresh`): an attempt, a chunk that moves nothing (`touch`), and, at the receiver, a chunk
arriving late. A fair run (`FairRun`) takes `TStep`s but sweeps (`fair_tsteps`), with no more than
`gap` passing without an attempt that delivers a chunk, or a touch.

- `fair_unswept`: every state a fair run reaches from a state renewed within `renew`, with
  `renew + gap ≤ life`, has gone untouched for less than `life`, so that no sweep can take
  place there.
- `fair_arun`, `fair_finishes`: a fair run's attempts that hear a reply are a run of `ARun`,
  so that one with `ameasure` of them, from a state the prefix receiver reaches, ends with the
  receiver storing exactly the sent blob.
- `swept_source_stalls`: once a sweep has taken the sender's blob, the receiver never stores
  it.

That attempts which hear a reply keep coming, `ameasure` of them, is an assumption about the
network. On a real link it depends too on how much of the sender's own timed-out windows is
still ahead of it, which the code bounds by narrowing its window and the model doesn't count.

### Per-machine refs (`Refs.lean`)

The model covers one git ref of a colocated repository: jj's import and export, with git an
adversary that can move the ref at any time, and jj's ref merge an abstract three-way merge
obeying three laws (`RefAlg`), which the test `ref_laws` checks against jj-lib.

The model's import is the update of a selected ref. jj 0.47 selects it for an ordinary
command only when the physical ref differs from `git_refs`; otherwise it is an identity
step. An explicit fetch selects its returned target even when the physical ref is unchanged.
Thus the theorems about resolving a conflicted remote bookmark or `restore_reverts` describe
an actual import, not an unconditional effect of the next ordinary command. The conformance
harness applies that selection and tests unchanged refs too.

For an explicit fetch after an ambiguous join, `TSlot.import_remote` and `import_record`
establish that the selected observation becomes the remote target and its record, even when
the physical ref did not move. `TSlot.import_following` establishes that a tracked local
bookmark equal to its remote follows that observation. Local differences remain jj's merge
(`import_L`). These are properties of the selected-ref computation already checked through
the oracle, not claims that every fetch succeeds, that a failed call has no completed effects,
or that cached observations have a total order. The CLI and generated join regressions listed
in [conformance](../docs/internals/conformance.md#per-machine-refs) check the command boundary.

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
  the restoring machine included (`restore_import_agrees`). An explicit import of the expected
  value resolves a restored conflict (`restore_conflict_resolves_back`,
  `conflicted_restore_resolves`).
- `restoreLocal_inv`, `restoreRemote_inv`, `restoreRemote_cinv`: `jj undo` and `jj op restore`
  keep the invariant where jj's export can write the restored bookmark, or it restores a
  conflicted remote bookmark. Where it can't, as for the root commit or a conflicted local
  bookmark, the next import moves the bookmark with no `git` command
  having run (`restore_reverts`) if that ref is selected for import. An ordinary command
  leaves it alone when `git_refs` still matches the physical ref.
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
  would be merged by a `jj` command without exporting before its import, so that machine
  would import a value other than the merge's expected value (`beside_published_apart_disagrees`).

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
remain obligations of the realization. Three-parent and criss-cross DAGs
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

### Moving op heads (`OpHeads.lean`, `OpHeadsRace.lean`)

musubi replaces op heads it read earlier, while jj commands, which publish under jj's op-heads
lock, and `jj op abandon` and `jj op integrate`, which take no lock, change them. The model has
the op heads, the operations (their parents) and the lock; a command loads an operation and later
publishes its own in place of it, or merges several op heads; `jj op abandon` and `jj op
integrate` write an operation and later land it, adding it and removing what it replaces with no
lock; musubi plans a move, locks, checks the op heads are those it read, writes each head, and
lets go. [Conformance, "Moving op heads"](../docs/internals/conformance.md#moving-op-heads) says
which code each step is and how it is checked.

- `Inv.step`, `Reachable.inv`: the invariants of the race model, in every reachable state.
- `locked_blocks_commands`, `held_has_lock`, `writing_has_lock`: from taking the lock to letting
  it go, which covers the check and every write, no command publishes or merges.
- `check_no_event`, `check_step`: where musubi's check, under the lock, finds the op heads those
  it read, no command has published or merged, and no `jj op abandon` or `jj op integrate` has
  landed, since it read them. The lock and the check keep commands out of the whole of a move, so
  that no operation a command wrote is among those musubi takes out.
- `Trace.landing_before_the_lock`: a landing between musubi's read and its lock makes the check
  fail, and musubi moves nothing. `Trace.landing_during_the_move`: one between musubi's two
  writes stays among the op heads.

The model assumes of jj what `heads_laws.rs` pins, and of musubi nothing but what the conformance
test checks of `same` and the order of steps `heads.rs` reads as. It says nothing of what is in a
view, whether musubi's rewrite of an operation is the right one, or the hub. The theorems leave
out how the local moves refine the protocol model's steps, which are on canonical operations: a
command's publish and merge have the shape of `EnvStep.userOp` and `EnvStep.merge` on the heads,
but relating a local op head to its canonical operation is the translation, which this model
abstracts away.

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
  needs none, since the hub chooses the operations, all of them accepted.
- **Relaxations of durability, proved safe.** `loseKnown` lets a restarting node lose `known`
  (reset to `(0, root)`) while keeping `staged`, as the Rust node does. `loseVolatile` lets it
  lose `staged` as well. `hubForget` lets the hub lose or garbage-collect any operations and
  objects outside `closure(head)` in the original-ancestry relation. The executable
  model preserves operation bodies needed by retained historical heads: an older head can
  be outside the current closure after the hub goes back. Historical-only objects may still be
  lost. A requested rollback to an incomplete target is an explicit environment choice
  that remakes the hive. Whether native startup detects every damaged prefix is not modeled, and
  the model adds no hub durability requirement.
- **Ghost state.** `creator`, `isMerge` and `birth` record each op's creator, whether it is a
  merge, and the hub `seq` at its creation; `hist` records the history of accepted heads.
- **Translation layer.** It is not modeled. The model assumes what [protocol.md, "Translation
  layer"](../docs/internals/protocol.md#translation-layer) requires: `canon` is injective on
  reachable local operations, `canon(realize(C)) = C`, and realization never creates a canonical
  operation. Under those assumptions, the properties over canonical ids carry over to each node's
  local op log. The generated end-to-end tests check all of them at every full
  convergence ([testing.md](../docs/internals/testing.md#generated-end-to-end-tests)).

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
- **Chunks:** use unique session ids, or tag chunks with the blob id; ignore duplicate and
  overlapping bytes; check `hash(assembled) = id` at `Finish`, and restart on a mismatch;
  treat a stored blob as finished. A receiver may instead keep only a contiguous prefix,
  report its length, and check the hash once it reaches the claimed length, as musubi's does
  (`preach_abs`). For liveness under deadlines, start each attempt where the receiver last
  said it was, or, for a downloader, from what it has, not from the beginning
  (`attempts_finish`, `restart_stalls`); sweep a blob only once no chunk has touched it for
  `life`, renew one a chunk touches at most every `renew`, and touch every blob a transfer
  still needs, with `renew` plus the longest wait between touches within `life`
  (`fair_unswept`, `fair_finishes`).

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
   `Musubi/ExecJson.lean` decodes requests, encodes replies and dispatches them. It also checks
   the preconditions of the model functions it calls, and answers a request that fails them with
   `bad request: <reason>`: operations' parents must come before them, and heads and indices
   must be in range. The protocol decisions are made by `execStep`, not by the codec.

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

The oracle also answers with the prefix receiver of `Chunks.lean`, its senders' attempts and the
naming rule of `Names.lean`, whose definitions run as they are, so they need no executable form of
their own ([conformance.md, "Chunked blobs"](../docs/internals/conformance.md#chunked-blobs) and
["Workspace names"](../docs/internals/conformance.md#workspace-names)). `Refs.lean`'s functions are
executable as they are too, over any `RefAlg`: `RefsExec.lean` runs them on numbered targets, with
jj's merges as a table each request carries, and the oracle answers refs requests with them
([conformance.md, "Per-machine refs"](../docs/internals/conformance.md#per-machine-refs)).

## Snapshot publication budgets

`Publication.lean` counts the unique extra paths and content bytes that outgoing operation
history adds, excluding files in commits the hub already knows and files of intentional
commits, and decides whether a plan may be sent (`maySend`).

- `protected_not_charged`, `known_not_charged`, `protected_content_free`: no file of an
  intentional or known commit is charged.
- `changed_plan_held`: a plan over the limits cannot be sent under the approval of a different
  plan.
- Cleanup freezes source intent, contracts operation parents with `Contract.cpar` and adds a
  checkpoint that references every intentional commit version. `cleanup_keeps_current_view`,
  `cleanup_keeps_context` and `cleanup_keeps_unselected` (a surviving operation keeps its
  required commits and intent) say what stays. `cleanup_requires_intentional` and
  `cleanup_keeps_intentional_files`: every intentional commit and its files are still
  referenced. `survivor_parent_survives`, `survivor_ancestry`: contraction keeps survivor
  ancestry.
- `applyCleanup` installs a prepared result only if its checks pass: `stale_cleanup_refused`
  (the expected heads differ), `uncertain_cleanup_refused` (`intentKnown` is false), and
  `installed_keeps_view_context`, `installed_keeps_intentional_files` for what it installs.

The oracle evaluates these same definitions, with native jj fixtures comparing exact sets and
applied effects; see [conformance](../docs/internals/conformance.md#snapshot-publication).

An unknown native command record sets `intentKnown` false, which refuses cleanup and still allows
exact publication approval. The full object closure, jj transaction facts, selected revision
decoding, opaque canonical context and guarded physical identity mapping are native contracts,
not theorems about jj. The convergence results require publication holds to be resolved,
disabled or approved eventually; they do not prove progress through a deliberate hold.

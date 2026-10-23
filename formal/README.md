# Lean model of the musubi sync protocol

This directory is a machine-checked Lean 4 model of [`docs/protocol.md`](../docs/protocol.md),
and, in `Musubi/Refs.lean`, of the per-machine view state of [`docs/design.md`](../docs/design.md).
It contains no `sorry` and adds no axioms. Every main theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. Some depend on fewer, and `Musubi/Axioms.lean` prints
the exact list.

## Checking

Install Lean (for example, via `elan`) and put `lake` on `PATH`.

```sh
cd formal
lake build
```

The toolchain is pinned to `leanprover/lean4:v4.35.0` in `lean-toolchain`. The model uses
only core Lean: there is no Mathlib and there are no dependencies. A clean build of the proofs
and the oracle takes about 5 seconds. The build prints the `#print axioms` report from
`Musubi/Axioms.lean` and runs the `#guard` smoke tests in `Musubi/ExecTest.lean`.

To build and run only the conformance oracle:

```sh
cd formal
lake build oracle
.lake/build/bin/oracle < test/smoke.jsonl
./test/run_smoke.sh   # replays test/smoke.jsonl and diffs against test/smoke.expected
```

The binary is `formal/.lake/build/bin/oracle`.

## Files

| File | Contents |
| --- | --- |
| `Musubi/Basic.lean` | Sets as predicates (`OSet`), point update `upd`, counting `cnt`, sums `sumN`. |
| `Musubi/Dag.lean` | `Anc` (`anc*`), `ParLt` (acyclicity), `maxSet` (`max`), and how `anc*` is preserved when a fresh op is created. |
| `Musubi/Model.lean` | The asynchronous model: state, messages, transitions, `EnvStep`, `SyncStep`, `Step`, `Reachable`. |
| `Musubi/Invariant.lean` | The inductive invariant `Inv` and the message invariant `MsgOK`. |
| `Musubi/PreserveEnv.lean` | `Inv` is preserved by `UserOp`, `Merge` and message sends. |
| `Musubi/PreserveSync.lean` | `Inv` is preserved by every sync, hub and crash step; `inv_reachable`. |
| `Musubi/Safety.lean` | The safety properties and no-feedback. |
| `Musubi/Liveness.lean` | The reliable policy model `PStep`, simulation into the async model, the measure, progress, termination and convergence. |
| `Musubi/Merged.lean` | The merged `Push` and `Fetch` exchanges reach states that agree with policy steps on everything the measure and convergence depend on. |
| `Musubi/Regress.lean` | A hub that goes back to an earlier accepted head, as a power cut or a remade hive makes it: the extended system `RStep`, the invariant that survives, and convergence once the hub stops going back. |
| `Musubi/Chunks.lean` | The chunked-blob model, its safety and its liveness. |
| `Musubi/Scenario.lean` | A concrete reachable run: a lost Cas race, then fetch, advance, merge, and the merge accepted. It shows the model is not vacuous. |
| `Musubi/Exec.lean` | The executable model: finite `EState`, the `Action` vocabulary of `docs/conformance.md`, and `execStep`. |
| `Musubi/ExecSound.lean` | `exec_sound`, `abs_initE`, `exec_reachable`, `exec_inv`, and with the hub going back `exec_rsound`, `exec_rreachable`, `exec_invR`. |
| `Musubi/ExecJson.lean` | The oracle's JSON codec and request handler (no protocol logic). |
| `Musubi/ExecTest.lean` | `#guard` smoke tests of `execStep`, checked at build time. |
| `Musubi/RegressScenario.lean` | A run of the executable model in which the hub goes back and two nodes then merge the same heads (`duplicateMerge`), so the extended system reaches states the durable one does not (`rreachable_not_reachable`). |
| `Oracle.lean` | The `oracle` executable: a stdin/stdout loop around `ExecJson.handle`. |
| `test/smoke.jsonl`, `test/smoke.expected`, `test/run_smoke.sh` | The oracle smoke test. |
| `Musubi/Refs.lean` | Per-machine and shared state of a replicated view, for one git ref: jj's ref import and export against an adversarial `.git`, no spurious revert for local and remote bookmarks, and the verbatim-replication counterexample (docs/design.md, "Per-machine state in a replicated view"). Independent of the protocol model. |
| `Musubi/Axioms.lean` | `#print axioms` for every main theorem. |

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
| Node crash, hub crash | `crashNode`, `crashHub`, plus the relaxations `loseKnown`, `loseVolatile` and `hubForget` (see below) |
| Policy (reliable, atomic exchanges) | `PStep`: `learn`, `realize`, `advance`, `merge`, `pushAccept`, `pushIdem`, `pushReject` |
| Chunked blob session | `Chunks.CState`, `Chunks.CStep` (full model), `Chunks.LStep` (reliable delivery) |

## Main theorems

All quantify over `Reachable N s`: every state of the full asynchronous system with `N`
nodes reachable from `init`.

Safety (`Safety.lean`):

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
- `advance_result`: after `Advance`, `|heads| ≥ 2` or `heads = {known.head}`. This is the
  claim in policy step 3.

No feedback:

- `noFeedback`: every `SyncStep`, including `Realize`, hub handling and crashes, leaves the
  operation universe unchanged.
- `envCreatesOne`: each environment step creates exactly one operation.
- `converged_quiescent`: a converged state enables no policy step.

Liveness (`Liveness.lean`):

- `pstep_reachable`: every policy step is a finite run of the asynchronous model.
- `progress`: if a reachable state is not converged, some policy step is enabled.
- `measure_decreases`: every policy step strictly decreases a lexicographic measure.
- `no_infinite_policy_run`: no policy run is infinite, under any schedule.
- `eventually_converges`: from every reachable state, policy steps reach a converged state.
- `maximal_run_converges`, `terminal_iff_converged`: a policy run that cannot be extended
  is converged, and a converged state cannot be extended.
- `converged_all_accepted`: once converged, every created operation is in `anc*(hub.head)`.

Merged requests (`Merged.lean`):

- `pushAccept_merged`, `pushIdem_merged`, `pushReject_merged`: a merged `Push` exchange
  reaches a state that agrees with the corresponding policy step's up to the network and
  staging.
- `fetch_merged`: a merged `Fetch` exchange does the same for `PStep.learn`, and stages
  every operation the node lacks below the head, with its objects at hand.
- `realize_agree`: realizing a staged operation agrees with `PStep.realize`.
- `measure_agree`, `converged_agree`: the measure and convergence see no difference.

`Converged N s` means that every node `n < N` has `heads = {hub.head}` and
`known = (hub.seq, hub.head)`.

A hub that goes back (`Regress.lean`). `protocol.md` requires the hub to keep `head`, `seq` and
`closure(head)`; musubi's hub syncs nothing to disk, so it may not. `State.regress s i` (the
oracle's action `hubRegress`) sets `head := hist i` and `seq := i` for any `i ≤ seq`;
`RStep` is a `Step` or such a regression, and `RReachable` its reachable states. Making a
hive again, empty, is a regression to 0 followed by `hubForget` (`remake_reachable`). The
invariant `InvR` keeps the universe, the hub's history and closure, and each node's
repository, but not what relates nodes to the hub's history, so Locality, MergeOwnership,
HubMonotone and KnownIsHubHistory do not hold there: after the hub goes back, nodes can hold
operations the hub no longer has, know heads it has forgotten, and merge the same heads
(`duplicateMerge`, in `RegressScenario.lean`).

- `invR_reachable`: `InvR` holds in every `RReachable` state.
- `hubClosedR`, `hubHistoryR`, `nodeClosedR`, `noFeedbackR`: HubClosed, the history chain,
  NodeClosed and no feedback, with a hub that goes back.
- `duplicateMerge`, `rreachable_not_reachable`: two nodes can create merges with the same
  parents, which `noDuplicateMerge` rules out in every `Reachable` state.
- `pstepR_reachable`, `progressR`, `measureR_decreases`, `no_infinite_policy_runR`,
  `eventually_convergesR`, `maximal_run_convergesR`, `terminal_iff_convergedR`,
  `converged_all_acceptedR`: liveness once the hub stops going back, for the policy `PStepR`.
  Once converged, every operation any node created is in `anc*(hub.head)`: a hive made again
  fills from its machines.

`PStepR` differs from `PStep` in two steps:

- A node learns the head in a reply to its own request whenever it differs from the one it
  knows, older or not. In the Rust core, `NodeCore::handle_reply` restarts the node and then
  takes the reply, which is `loseKnown` then `learn`; `PStepR` uses `learnUnfiltered`, which
  has the same effect.
- A node realizes only below a head in the hub's current history (`Consistent`). The Rust
  core clears its realization plan whenever `handle` changes `known`, so a plan never
  outlives the head it was made for, and every sync starts with a `Fetch` whose reply sets
  `known`: whatever a node realizes is below the head the hub has just named.

The measure is `(nodes not good, inconsistent nodes, Σ staleness of consistent nodes,
Σ missing ops, Σ pending advances, Σ pending merges)`. A node is good when its `known` is in
the hub's current history and it has one head, accepted and comparable with every head in
that history. The dirty count of `Liveness.lean` does not work here: after the hub goes
back, a node can hold two accepted heads that are not comparable, and merging them makes it
dirty. A good node stays good under every policy step of every node, and an accepted push
makes its node good, so the hub head moves at most once per node that is not good.

Chunked blobs (`Chunks.lean`, with `hash` assumed injective):

- `stored_identical`: in every reachable state, a finished (stored) blob equals the blob that
  was sent. This holds even when the network injects arbitrary corrupt or stale chunks.
- `session_finishes`: from every reachable state, reliable delivery finishes the session and
  stores exactly the sent blob.

## Modeling choices

- **Operation universe.** Op ids are `Nat`s. Creating an operation assigns the fresh id
  `next` and fixes its parents and objects. The invariant keeps parents' ids smaller than
  their children's (`ParLt`), which makes the graph acyclic. `objs(x)` is taken as already
  closed under object reachability.
- **Sets** are predicates. The node and hub stores are sets of ids. Payload contents are
  global (`par`, `objs`), which models content addressing: equal ids have equal bytes.
- **Network.** `s.net` is the set of every message ever sent. Delivery does not remove a
  message, so it can be duplicated, delayed, reordered or lost. Requests and replies are
  separate messages. Request ids are not modeled: a node accepts any reply addressed to it,
  which over-approximates matching replies to outstanding requests. This over-approximation
  also covers a node crash losing its in-flight requests.
- **Atomic payloads.** `Push`, `Fetched` and the other bulky payloads are atomic messages
  carrying sets, as `protocol.md` specifies at this level. `Chunks.lean` justifies the
  atomicity: a finished blob is exactly the sent bytes, so a payload arrives whole or not at
  all.
- **The ancestry check** uses the global `parents`. It matters only once the closure check
  has passed, which means every operation in `closure(new)` is stored, so this agrees with a
  check over the hub's stored operations.
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

  The policy's own actions are instances of these weakened ones. Only one node-side guard
  carries weight: `GetOps` requests only operations in `anc*(known.head)`. The merged
  `Fetch` needs none, since the hub chooses the operations, all of them accepted.
- **Proven-safe relaxations of durability.** `loseKnown` lets a restarting node lose `known`
  (reset to `(0, root)`) while keeping `staged`, which is what the Rust node does.
  `loseVolatile` lets it lose `staged` as well. `hubForget` lets the hub lose or garbage-collect any
  operations and objects outside `closure(head)`. All safety theorems hold with these steps
  included.
- **Ghost state.** `creator`, `isMerge` and `birth` record each op's creator, whether it is a
  merge, and the hub `seq` at its creation. `hist` records the history of accepted heads.
  None of them affects any transition.
- **Translation layer.** It is not modeled. As `protocol.md` requires, the model assumes
  that `canon` is injective on reachable local operations, that `canon(realize(C)) = C`, and
  that realization never creates a canonical operation. Under those assumptions, the
  properties over canonical ids carry over to each node's local op log.

## The executable model and the conformance oracle

`docs/conformance.md` is the contract. The chain from the proofs to the Rust core is:

1. **Relational to executable.** `Musubi/Exec.lean` defines a finite, computable state
   `EState`. Operations, nodes and the ghost history are association lists; sets are lists;
   `net` is a list read as a set. `abs : EState → State` maps it to the relational state.
   `execStep N es a : Except String EState` evaluates every guard of the matching relational
   step:
   - `anc*` is decided by one downward sweep from the descendant (`ancL`), which is exact
     because parents have smaller ids;
   - `ClosedAt`, `maxSet` and membership in `net` are decided directly; set-valued message
     fields are compared as sets.

   On failure, `execStep` returns `"<action>: <failed guard>"`.
2. **Executable to oracle.** `Oracle.lean` reads requests and writes replies, one JSON object
   per line, flushing after each. A rejected or malformed request leaves the state unchanged.
   Decoding, encoding and the request loop are in `Musubi/ExecJson.lean`; all protocol
   logic is in `execStep`.

Theorems (`Musubi/ExecSound.lean`):

- `exec_sound : a.goesBack = false → execStep N es a = .ok es' → Step N (abs es) (abs es')`.
  Its only hypothesis is that the action is not `hubRegress`. `execStep` first checks the
  one well-formedness property the decision procedures rely on, that every recorded
  operation's parents are below it (`parOK`).
- `abs_initE : abs initE = init`.
- `exec_reachable : ExecReachable N es → Reachable N (abs es)`. Every state reached through
  accepted actions other than `hubRegress` from `initE` is relationally reachable, so every
  safety theorem holds in it.
- `exec_inv : ExecReachable N es → Inv N (abs es)`.
- `exec_rsound : execStep N es a = .ok es' → RStep N (abs es) (abs es')`, for every action.
- `exec_rreachable : ExecRReachable N es → RReachable N (abs es)` and
  `exec_invR : ExecRReachable N es → InvR N (abs es)`: with `hubRegress`, every state is a
  state of the extended system, and `InvR` and the theorems of `Regress.lean` hold in it.

Encoding choices:

- **Notifications.** The hub's publication of a new head is one internal `EMsg.notifyAll`,
  which denotes `head n notify seq head` for every node `n`. In JSON it appears as one
  `head` message with `headKind: "notify"` per node `n < nodes`.
- **Sorting.** State arrays are sorted ascending without duplicates. Operation parent lists
  are also sorted; the order of parents never matters to the model. `net` is sorted by
  `(msg, node, compact JSON of the whole message)`.
- **Extra guards.** `userOp` and `merge` also check that their parents are below `next`.
  These checks are implied by the invariant, so they never fire in a reachable state.
- **Staging is never cleared.** `realize` adds the op to `lops` and its objects to `lobj`,
  but leaves them in `sops`/`sobj`, and only `loseVolatile` empties staging. A fake repo
  that deletes staged entries on realize will differ from the oracle's `sops`/`sobj`.
- **No well-formedness bound on nodes.** The hub actions do not check `node < nodes`, just
  as the relational hub steps don't; a matching message in `net` already implies it.
- **The hub going back.** `hubRegress i` sets the hub's `head` to the head it accepted at
  `i` and its `seq` to `i`, and changes nothing else: stores, nodes and `net` stay, and so
  does the ghost history, entries above `i` included. The next accept records entry
  `i + 1`, which then shadows the old one, as the relational `hubAccept` overwrites it. The
  ghost history is not part of the JSON state, so a test may equally truncate it to the
  entries up to `i`.

## Why the reliable policy model is a sound abstraction for liveness

`PStep` lets a node perform one policy action as an atomic, successful request/reply
exchange. Nodes and actions may be scheduled in any order; the policy's priority order is
one particular schedule. `Merge` is a policy action, because musubi loads the repo and jj
merges. `UserOp` is absent, because environment activity has stopped.

1. **Each `PStep` is a run of the real system** (`pstep_reachable`). So every policy run
   stays inside the reachable states, and all safety invariants hold along it. The
   implementation exchanges the merged requests instead, and `Merged.lean` shows that
   those runs end in states that agree with the policy step's on the universe, the hub, and
   each node's operations, objects, heads and `known`, differing only in the network and in
   what is staged (`AgreeUpToStaging`). The measure and `Converged` read nothing else
   (`measure_agree`, `converged_agree`). `pushAccept_merged`, `pushIdem_merged` and
   `pushReject_merged` cover pushes. `fetch_merged` covers `PStep.learn`, and leaves every
   operation the node lacks below the head staged with its objects at hand, so that
   `Realize` takes each in turn with the effect of `PStep.realize` (`realize_agree`).
2. **Failures only delay.** A failed exchange (lost request or reply, crash, hub restart)
   leaves persistent state unchanged, or changes it in a way that a retry absorbs:
   - Storing is idempotent.
   - `Learn` ignores stale and duplicate sequence numbers.
   - `Cas` with `new = head` answers `Accepted` and changes nothing.
   - Realizing an operation that is already local adds nothing.
   - A `Cas` that was accepted but whose reply was lost has exactly the hub-side effect of
     `pushAccept`. The node's next `Fetch` performs the remaining `Learn`.
   - Stored-but-unacknowledged uploads only grow hub stores, which the measure ignores.

   With eventual delivery, each retried exchange eventually completes. The run of
   persistent-state changes is then a `PStep` run, interleaved with steps the measure
   ignores.
3. **Stale in-flight messages are finitely many** when environment activity stops:
   - A stale `Cas(e, d)` can change the hub at most once, because the head never returns to
     `e`, and it can only move the head forward.
   - Stale head-carrying replies only raise `known.seq`, which is bounded by `hub.seq`.
   - Stale `Fetched` and `Ops` replies only stage accepted operations, and stale uploads
     only grow hub stores.

   After them, `eventually_converges` applies again from the then-current state, because it
   holds from every reachable state, whatever messages are still in flight.
4. **Termination does not depend on fairness among nodes.** `measure_decreases` holds for
   every policy step, so no schedule runs forever. `progress` guarantees that a node
   following the policy always has something to do until convergence.

**Contention.** The measure is
`(dirty nodes, Σ staleness, Σ missing ops, Σ pending advances, Σ pending merges)`, ordered
lexicographically. A node is dirty when one of its heads is not accepted. An accepted push
cleans the pushing node. Without `UserOp`, a clean node never becomes dirty, and only
accepted pushes move the hub head. So once environment activity stops, the hub head changes
at most once per dirty node, at most `N` times. Every lost Cas race teaches the loser a
newer head, which decreases its staleness.

## Obligations for the Rust implementation

- **Hub:**
  - A `Cas`'s checks and the update of `head` and `seq` form one critical section.
  - The new `head` and `seq` are written before the reply or notification is sent, so that
    they survive the hub's process crashing. If the hub replied first and then lost the
    update in a crash, HubMonotone and KnownIsHubHistory would fail. (A power cut can still
    lose them, since musubi's hub syncs nothing to disk; `Regress.lean` covers a hub that
    goes back.)
  - `closure(head)` is durable whenever `head` is.
  - Every `Head`, `Accepted`, `Rejected` and `Incomplete` message carries a pair
    `(seq, head)` that the hub actually had.
- **Node:**
  - Stage and realize only operations in `anc*` of a head the hub accepted.
  - Push only local operations.
  - `Merge` takes all current heads as parents.
  - No other node-side check is needed for safety. The Upload and Push guards, the order of
    policy steps, and `Learn`'s filter matter only for liveness and efficiency.
- **Chunks:**
  - Use unique session ids, or tag chunks with the blob id.
  - Ignore duplicate and overlapping bytes.
  - Check `hash(assembled) = id` at `Finish`, and restart on a mismatch.
  - Treat a stored blob as finished.

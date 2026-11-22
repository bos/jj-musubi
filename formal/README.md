# Lean model of the musubi sync protocol

This directory holds machine-checked Lean 4 models of the following. Hive, node, hub and the
other terms are those of [design.md, "Vocabulary"](../docs/internals/design.md#vocabulary).

- The sync protocol of [protocol.md](../docs/internals/protocol.md), with its safety and
  liveness properties, and what still holds when the hub goes back to an earlier head.
- Convergence of the asynchronous system with loss, retries and abandoned operations in flight,
  from explicit premises about the native code ([the trusted
  base](#the-trusted-base-of-convergence); [the bridge](#the-asynchronous-liveness-bridge)).
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
- How musubi moves the jj operation heads it read earlier while jj commands and the lockless
  `jj op abandon` race it (`Musubi/OpHeads.lean`, `Musubi/OpHeadsRace.lean`; [design.md, "Moving
  op heads"](../docs/internals/design.md#moving-op-heads)).
- [Snapshot publication budgets](#snapshot-publication-budgets), exact approval and cleanup of
  selected unpublished operations (`Musubi/Publication.lean`; [design.md, "Snapshot publication
  budgets"](../docs/internals/design.md#snapshot-publication-budgets)).
- A finite executable model of native preparation and publication (`Musubi/NativeLifecycle/`),
  with construction and record-custody proofs. Its native evidence and correspondence limits
  are described in
  [conformance.md](../docs/internals/conformance.md#native-lifecycle-inputs-and-events).

The models of chunked transfers, per-machine refs, presence, copies, workspace names, snapshot
publication, native preparation and moving op heads are separate from the protocol model's
state.

No proof is left unfinished (Lean's `sorry`) and the model adds no axioms. Every main theorem
depends only on Lean's standard `propext`, `Classical.choice` and `Quot.sound`, some on fewer.
The build checks both: it treats the warning a `sorry` gives as an error, and
`Musubi/Axioms.lean` fails if a main theorem depends on any other axiom.

The protocol and lifecycle models are state machines, with states and a step relation. Other
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
tests in `Musubi/ExecTest.lean` and `Musubi/SupersedeExecTest.lean`.

`./test/run_smoke.sh` builds the conformance oracle alone (`lake build oracle`), replays
`test/smoke.jsonl` through it and diffs the output against `test/smoke.expected`. The binary
is `formal/.lake/build/bin/oracle`.

## Reading the integration proofs

The convergence argument proves one statement, and the assumptions it rests on are listed in one
place. Start there:

1. The statement of `FineAssembly.hive_converges_observed` in `FineAssembly.lean`. Its conclusion
   is `SysAcceptance.Converges` (`Acceptance.lean`): the hub stops moving and every node settles
   at its head.
2. [The trusted base of convergence](#the-trusted-base-of-convergence), every premise of that
   theorem, field by field.
3. `SysAcceptance/Convergence.lean`, where `hive_converges` composes the derived phases. It
   shows which fact each phase supplies to the next.
4. `Musubi/SysAcceptance.lean`, the map of the layers, then the interfaces in this order:
   1. `SysAcceptance/Observations.lean` groups the readings of one actual hive run by
      responsibility. Its sampled views use those same readings for entry, fetch and pending
      runs.
   2. `SysAcceptance/Cuts.lean` names record stabilization, quiet suffixes and old-effect
      cutoffs.
   3. `SysAcceptance/Contracts.lean` groups source effects, environment, transport, knowledge,
      entry, scheduling and system bindings. Completion and fairness obligations stay explicit.
   4. `SysAcceptance/Phases.lean` derives quiet records, persistent entry, a completed active
      sample and final eligibility.
   5. `SysAcceptance/Eligible.lean` owns `FineSnapshot`, `FineStart` and `FineAt`, and
      `Acceptance.lean` owns `eligible_system_converges`.
   6. `FineAssembly.lean` builds `FineAt` from the event replay and `FineSource`;
      `FineAssembly/Honesty.lean` proves the invariant on replies and notifications that
      assembly uses.

The nodes of a hive may differ in which originals they have dropped. The *eligible* nodes
(`EligibleAt`) drop exactly what the hub's records drop. The *fine system* is the hive's run
filtered to those nodes (`NodeSysEntry.filt`, `hiveSys`): the other nodes' slots are frozen, and
their fresh requests and the replies to them are left out. Each observed event of the hive
becomes a step of the fine system, to which the hub and node proofs apply. The *fine cut*
(`FineCut`) is the time from which every node has entered and has completed an active sample
after old effects stopped; the fine system starts there. Three names derive from it:

* `FineSnapshot` is the fine system's starting snapshot at the fine cut, and `FineStart` adds
  the hub's history window to it;
* `FineAt` is the fine system's interface from that cut: `FineStart`, its steps, graph law,
  fixed records, decisions and fairness. `FineAt.converges` concludes `Converges` for it;
* `FineSource` is the same interface read from native event replay, on `FineSnapshot`.
  `FineAssembly.fineAt_of` builds `FineAt` from it and the window;
* `hive_converges_observed` takes a `FineSource` for every fine cut, derives the history window
  (`history_window_from_record_cut`) and the rest of `FineAt`.

`Pending/Contracts.lean` separates the abstract round's control and publication laws from
survival facts derived from native naming. `known_after` in `Phases.lean` supplies the shared
knowledge-tail argument, including the stable-head corollary. The two `SysStep` effect interfaces
hide constructor bookkeeping from the honesty invariant.

For local control, `NodeSettle.Settled` names the final state's properties and `NodeSettle.rank`
orders the remaining work by priority. `NodeSys.SysStep.nonanswer_effect` describes the
unchanged hub and shrinking traffic of a step outside hub answering. `Schedule.lean` owns the
shared bounds on event order and batch completion. `HiveFilter.lean` owns the eligible-system
observation and projection used by native-event replay.

## The trusted base of convergence

`FineAssembly.hive_converges_observed` takes the premises below and nothing else. A stable hub,
entry, eventual eligibility, fresh knowledge and a successful round are not among them: the
proof derives them, along with the record, quiet and old-effect cuts, the empty pending drops,
the fixed hub records and the honesty of traffic sent after the fine cut.

The premises, in the order of the statement:

* `label`, `decodeR` and `origin` are the adapter's data: they read a native record identity as
  a model id and as executable records, and name each operation's original.
* `C : HiveContracts` has 8 groups and 43 fields.
* `views`, `hubRecs` and `hubRecsStep` tie the records of the native observer, the hub and the
  fine nodes together.
* `fine` yields a `FineSource` (12 fields) and its `FineSnapshot` (9 fields). It is asked at every
  `recordCut` and `cut` that satisfy `CutAt`, `QuietAt` and `FineCut`, not only at the pair the
  proof picks, which it chooses by existence.

Each field carries a tag, except data fields:

* **correspondence**: the native code, or the adapter's reading of it, behaves this way. It is
  checked against the implementation, and the proof cannot establish it;
* **progress/fairness**: something eventually happens: a failure stops, a call completes, a node
  is scheduled;
* **invariant at a cut**: a property of a state, assumed at a time the proof derives, because no
  bound step leads to that time from the start to derive it.

Most laws are asked only from a record cut `k` (`CutAt`: records and drops fixed, no adopt or
fail) in a quiet environment (`QuietAt`: no I/O or object failure, automatic write, user work or
loss). Those are the rows with a reason in the last column. The proof derives such a `k`, and
the premise is the law on the suffix after it. That is natural for one reason: before `k` a
remade hub, a gc, a user write or a record set still moving can legitimately break a law about
undisturbed native code, and nothing here needs the law there.

Check these specially:

* `Entry.pending`: see [below](#the-pending-premise).
* `Environment.autoWritesStop` is a progress assumption that the proof cannot derive from
  finitely many user and configuration changes.
* `FineSource.binds` and `Entry.entry` are the largest correspondence obligations: the first is
  one binding for each kind of replayed event, whose node-side fields the source says no checker
  of this exact relation tests (`decide`, `handle`); the second is 28 per-call laws of a node's
  pre-entry run (`EntryLaws`), including `objects_step` and `idle_restarts`, which require
  eventual round restarts.
* `FineSource.inFlight` is the one part of the honesty invariant that is not derived. Its
  window, head and clock parts follow from the derived history window and `clock`; the replay
  proves honesty of traffic sent after the cut. A reply or notice already in flight at the cut
  has a snapshot that no contract constrains: `ownHead`, `noteHead` and `replyBind` bind the
  observer's times, and only replies consumed after the cut. So `inFlight` cannot be derived
  from the other premises.
* `HubHandling.answer` joins an eventual-handling assumption to a correspondence.
* `HubHandling.climbs` holds natively when no new drop is taken, which `CutAt` ensures, and the
  hub's head at the cut survives the hub's records. The native hub keeps the second condition:
  `HubStore::set_head` appends each accepted head on one line of its `heads` file together with
  the record taken with it, and `Push::answer` refuses a push whose new head the records it
  remembers or the push's own drops supersede (once it has pruned, the push's records keep such a
  head out, as a node never pushes one a record it took drops), so no record the hub keeps drops
  its head. A power cut leaves a prefix of the file, an older consistent state, or a torn line,
  which the hub treats as corrupt and remakes. The shipping hub's accept by contracted ancestry
  ([below](#contracted-ancestry)) brings a new drop of its head, so it falls before the cut. This
  is an argument about the native code, not a Lean proof.

### Record effects (`Source.RecordEffects`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `recStep` | at each step the native records stay or take drops (`takeRecs`) | **correspondence** | |
| `prune` | the pruned count never falls | **correspondence** | |
| `pruneLe` | the pruned count is at most the record count | **correspondence** | |
| `dropsGrow` | a node's dropped originals only grow | **correspondence** | |
| `hubBound`, `nodeBound` | every dropped original is below the bound `B` | **correspondence** | |
| `epochStep` | each node's record bookkeeping steps by `Retry.Records.Step` (fetch, adopt, reopen) | **correspondence** | asked once records are fixed and old replies and notices have stopped; an old `Fetched` may announce old records before then |

### Environment (`Source.Environment`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `envFinal` | nothing is lost (hub remade, objects lost, gc) from some time on | **progress/fairness** | |
| `readyKeep` | object credit survives a step that loses nothing | **correspondence** | |
| `readyFail` | a missing-object reply spends the credit and the node is then ready | **correspondence** | |
| `failFinal` | I/O failures stop | **progress/fairness** | |
| `autoWritesStop` | a node's automatic writes stop (housekeeping, prelude, cleanup, abandon pass-on, reparenting) | **progress/fairness** | |
| `userFinal` | user work in the nodes' repositories stops | **progress/fairness** | |

### Transport (`Source.Transport`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `inboxStep` | for every call id `c`, a node's inbox steps by `Retry.InboxStep c`, whose flag says the step finished a pending call with an id below `c`; the flag is set whenever the step handles an own reply to a call below `c` | **correspondence** | |
| `callIds` | call ids are never reset: for a call id with an own reply, if the inbox's next id at `t` is at most the id, the call is made at or after `t` | **correspondence** | |
| `notesOld` | notices published before a cut are finitely many, in flight or queued, and handling one uses it up | **correspondence** | |

### Knowledge (`Source.Knowledge`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `ownHead` | an own reply names a hub state between its call and its handling, and `handleHead` updates the known pair | **correspondence** | |
| `noteHead` | a notice names a state no later than its handling, and `handleHead` updates the known pair | **correspondence** | |
| `quietKnown` | with no reply, notice or reopen, the known pair stays | **correspondence** | |
| `rootSeq` | the hub at sequence 0 has the root as its head | **correspondence** | |
| `hubSeqStep` | the hub's sequence does not fall at a step that loses nothing | **correspondence** | |
| `histBind` | when nothing is lost from `a`, the history at the hub's sequence is the hub's head | **correspondence** | |

### Entry (`Source.Entry`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `entry` | each node's run from a sample after the cut obeys `EntryLaws` | **correspondence** and **progress/fairness** | entry is argued on undisturbed calls: no object failure, no change of records |
| `reopenWhy` | a reopen follows `Incomplete` or a missing-object reply not yet recovered | **correspondence** | I/O failure, loss or user work can reopen a node before the cut |
| `incHead` | an `Incomplete` push is from the hub's head, and its upload is not closed | **correspondence** | asked only once the records are fixed |
| `closure` | an entered node's push from the hub's head is closed | **correspondence** | a lost hub object or cached have would leave the upload short |
| `keep` | raw entry persists unless the node reopens | **correspondence** | a loss, failure or automatic write can undo entry before the cut |
| `pending` | see [below](#the-pending-premise) | **correspondence** | asked of a hub that stays, after the cut |

### Scheduling (`Source.Scheduling`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `schedMono` | each node has infinitely many sampled events, in order | **progress/fairness** | |
| `doneIn` | a sampled call batch completes before the next sample | **progress/fairness** | |
| `idleStart` | a node between rounds eventually starts one | **progress/fairness** | fairness is asked of the quiet suffix, where nothing keeps restarting it |
| `startActive` | the sample after a started round is active | **progress/fairness** | as `idleStart` |

### System bindings (`Source.SystemBindings`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `clock` | the system's time is the hive time | **correspondence** | |
| `maintBind` | a maintenance step is an automatic write | **correspondence** | |
| `noteBind` | a notice a node takes is the observer's, at its publishing time | **correspondence** | |
| `replyBind` | a head-bearing reply consumed after the cut belongs to a completed sampled batch and a call made no later than the reply | **correspondence** | replies from before a loss or reconnect need not match a sampled batch |
| `freshOwn` | a fresh reply at `t` has an own reply by the batch's completion, to the call made at `t` | **correspondence** | |
| `latchKnown` | the system's known pair is the observer's at the latch time | **correspondence** | |
| `latchLe`, `latchMono`, `latchAtSample` | the latch is no later than `t`, monotone, and at a sample is that sample | **correspondence** | |

### Hub handling (`Source.HubHandling`)

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `answer` | a push is handled at or after it is sent, and the hub then is `RawPublish.after` its packet and checks | **correspondence** and **progress/fairness** | a remade hub can drop a push before the cut |
| `climbs` | from the record cut `k`, the hub's head exists; the raw graph only grows; and each step leaves the hub's sequence number and head as they are, or moves to the next sequence number and a different existing head with the old head among its raw ancestors (`HubClimb`); its `RawGrow` clause rests on `QuietAt.noLoss`: no remade hub, object loss or gc after the cut | **correspondence** | no new drop is taken, so an accept compares raw ancestry (`HubLaw.guards`), and the hub's head at `k` survives the hub's records, as the native hub keeps it (see above); an accept that drops the head brings a new drop and compares contracted ancestry, which can jump the raw history |

### The starting snapshot (`FineSnapshot`)

`rawRoot` is data: the id of the raw root. Every other field is an **invariant at a cut**, at the
fine cut `k` and for the eligible nodes. Each holds of a well-formed state and is kept by every
step after `k`, but no bound step leads to `k` from the start, so the proof cannot derive it at
`k`.

| Field | Says |
| --- | --- |
| `rawRoot`, `rootBound`, `rootParents` | `rawRoot` is data; the raw root it names exists and has no parents |
| `nodes` | each eligible node is well-formed (`NodeOK`: local invariant, scoped embedding, wait), and its object requests and replies match (`ObjsOK`) |
| `system` | request and reply slots are below the counter, a reply to a fetch is `fetched`, a reply to a push is `refused` or `head` with constraints on its records, and the hub law's `dropped` holds of no push request in flight (`SysOK`) |
| `time` | every reply and notice was made in the past (`TimeOK`) |
| `objectReplies` | a reply to an objects request is objects |
| `requestBounds` | a push in flight names an existing operation |
| `distinctHeads` | each eligible node's heads, and those of its step in flight, are distinct |

The hub's history window is not among them. `FineStart` adds it, and `hive_converges_observed`
derives it (`history_window_from_record_cut`) from `HubHandling.climbs`, `Knowledge.histBind`
and `FineSource.parentsFirst`: from the record cut `w`, nothing is lost, so the history holds the
head at each time, and each move to the next sequence number is a step up raw ancestry. That gives
parents with smaller ids (`parLt`); the hub's head an existing operation (`headLt`) and the
history's entry at the hub's sequence (`histHead`); `w`, the record cut's sequence, at most that
sequence (`window`); and from `w` the hub's history a chain of ancestors (`chain`) with strictly
increasing ids (`strict`).

### Replay and fairness (`FineSource`)

Asked of the fine cut and its run.

| Field | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `decisionNodes`, `decodeRecords`, `events` | data: the executable hub's node count and record decoder, and the native events | | |
| `replay` | the run from the cut is the replay of `events` | **correspondence** | the events are the actual ones |
| `replayActs` | each step's action is its event's | **correspondence** | |
| `binds` | each event obeys its bindings: a node's call and its handling obey the core's laws (`NodeIssue.Binds` and the other kinds), the hub's answer is its decision | **correspondence** | |
| `inFlight` | replies to eligible nodes and notices in flight at the cut, from the record cut on, carry honest snapshots | **invariant at a cut** | the replay derives it for later traffic only |
| `parentsFirst` | an operation's parents have smaller ids | **correspondence** | |
| `advance` | an eligible node's busy step with the advance guard and no automatic write is a full-frontier advance | **correspondence** | an advance's cleanup writes nothing once no automatic write happens |
| `pushDecisions` | each push event's handling is a decision of the executable hub, with its primitive laws | **correspondence** | |
| `fair` | each eligible node's rounds start, its steps happen and its replies are taken | **progress/fairness** | |
| `pushFair` | a push an eligible node sends is handled eventually | **progress/fairness** | |

### The loose premises

| Premise | Says | Tag | Why from the cut |
| --- | --- | --- | --- |
| `views` | a node's applied records in the system are the label of the observer's, the native applied records decode them, and its pending originals are in custody (`RecordView`) | **correspondence** | records are fixed |
| `hubRecs` | the native hub's records at the cut are what the observer's records identity decodes to | **correspondence** | records are fixed |
| `hubRecsStep` | the system hub's records change only when the native records or the pruned count do | **correspondence** | records are fixed and the environment quiet |
| `fine` | gives `FineSource` above | | |

### The pending premise

`Source.Entry.pending` assumes, for each node that is not `EligibleAt`, all 29 fields of
`PendingLaws` for that node's frozen round, on a hub that stays and a node that knows its head:
control, publication checks and naming laws of the push the node would send. Its only use is
`all_eligible` (`Phases.lean`), which passes it to `PendingLaws.absurd`: a node that stays
ineligible on a stable hub would stay pending forever, and its push, accepted by the hub, would
move the hub.

The premise is used only by refutation. In a run that satisfies every premise no node is ever in
that state, so the 29 laws are never exercised on an actual execution, and a test of the whole
system or of the conclusion does not check them. They are claims about what the native code
would do for an ineligible node on a hub that stays. An auditor checks each against the native
round, as for any correspondence. A law the native code violates there does not falsify the
conclusion for runs without such a node. It removes the guarantee for the runs where a node
could stay ineligible, the case the premise exists to exclude. The laws to read closely are
`hguard` (the round's guard bits), `hdropsSub` (a node that offers the hub's records drops at
least what they drop), `hnormalDef` and `hsend`.

## Files

| File | Contents |
| --- | --- |
| `Musubi/Basic.lean` | Sets as predicates (`OSet`), point update `upd`, counting `cnt`, sums `sumN`, indicators `ind`, shared termination/progress facts (`Steps`, `eventually_done_of_progress`), and traces that stop changing (`nat_trace_stabilizes`, `lex_stabilizes`). |
| `Musubi/Contract.lean` | Contracting dropped operations out of a history: parents (`cpar`), ids as terms (`cid`), composition, and when ids agree; comparing through surviving images (`Below`), and the frontier of heads under a dropped set (`frontierSet`). |
| `Musubi/Dag.lean` | `Anc` (`anc*`), `ParLt` (parents have smaller ids, so the graph is acyclic), `maxSet` (`max`), and how `anc*` is preserved when a fresh op is created. |
| `Musubi/Model.lean` | The asynchronous model: state, messages, transitions, `EnvStep`, `SyncStep`, `Step`, `Reachable`. |
| `Musubi/Invariant.lean` | `Base`, what every state satisfies, whatever goes back or is dropped; `Core`, which adds the original history chain and every node's work below its heads; the inductive invariant `Inv`, which extends `Core`; and the message invariant `MsgOK`. |
| `Musubi/PreserveEnv.lean` | `Base`, `Core` and `Inv` are preserved by `UserOp`, `Merge` and message sends. |
| `Musubi/PreserveSync.lean` | `Base` and `Core` are preserved by replacing one node (`Base.setNode`, `Core.setNode`); `Inv` is preserved by every sync, hub and crash step; `inv_reachable`. |
| `Musubi/Safety.lean` | The safety properties and no feedback. |
| `Musubi/Liveness.lean` | The policy model `PStep`, its simulation in the asynchronous model, the measure, progress, termination and convergence. |
| `Musubi/Merged.lean` | The merged `Push` and `Fetch` exchanges reach states that agree with policy steps on everything the measure and convergence read, with a hub that may have gone back too. |
| `Musubi/Regress.lean` | A hub that goes back to an earlier accepted head, as after a power cut or a remade hive: the extended system `RStep`, the invariant that survives (`InvR`: `Core` with `InvC`, what every step keeps, history chain or not), and convergence once the hub stops going back. |
| `Musubi/AbandonRefs.lean` | The boundary from contracted survivor heads and saved expected values to one-ref realization and merged publication. |
| `Musubi/Supersede.lean` | Replicated `jj op abandon`: the protocol over original operations with each party's dropped set (`SStep`, `SRStep`), accepting a push through the surviving images of the hub's head, advancing to what survives of a dropped head and adopting records with their frontier; its invariant, superseded ids never coming back, and liveness with supersedes (`SPStepR`) from states whose history is an original chain (`SChain`). |
| `Musubi/Scenario.lean` | A concrete reachable run (a lost Cas race, then fetch, advance, merge, and the merge accepted), showing the model is not vacuous. |
| `Musubi/RegressScenario.lean` | A run of the executable model in which the hub goes back and two nodes then merge the same heads. |
| `Musubi/Chunks.lean` | The chunked-blob model, its safety and liveness; musubi's receiver, which keeps only a prefix, proved a refinement of it, with its own liveness; and its senders, attempt by attempt under a deadline, and in time, with sweeps of what has gone untouched. |
| `Musubi/Exec.lean` | The executable model: finite `EState`, the `Action`s of [conformance.md](../docs/internals/conformance.md), `execStep`; and the liveness measures, convergence, and what a policy `Push` uploads, computed (`measureE`, `rmeasureE`, `convergedE`, `upOpsL`, `upObjsL`). |
| `Musubi/ExecSound.lean` | Soundness of `execStep` and of those computations ([below](#the-executable-model-and-the-conformance-oracle)). |
| `Musubi/ExecJson.lean` | The oracle's JSON codec and request handler, which also checks the preconditions of the model functions it calls. |
| `Musubi/ExecTest.lean` | `#guard` smoke tests of `execStep`, checked at build time. |
| `Musubi/SupersedeExec.lean` | The executable model with supersedes: `SEState`, which adds the hub's records and each node's dropped set, the `SAction`s, `sexecStep`, and the measures computed (`smeasureE`, `sconvergedE`, and `rmeasureCE` through surviving images). |
| `Musubi/SupersedeExecSound.lean` | Soundness of `sexecStep` against `SRStep`, and of those computations. |
| `Musubi/RecordLiveness.lean` | Record agreement and finite reconciliation after convergence. |
| `Musubi/AsyncLiveness.lean` | Progress at split exchange boundaries and hub stabilization on a constrained suffix. The convergence proof does not use it. |
| `Musubi/RetryControl.lean` | Finite pre-cut request-slot consumption and cached fix-up writes within an explicitly constrained epoch. |
| `Musubi/RecordStability.lean` | Finite record appends and pruning for bounded original drops, and pending shrink under record extension. |
| `Musubi/ContractOrder.lean` | The hub's comparison computed (`belowB`) and the frontier computed (`frontier`), with the frontier's covering, merge and survival facts. |
| `Musubi/BaseImages.lean` | Every image of the accepted base stays below an op head, through each step that changes the base, the drops or the heads, as stated, unchecked against the code (#138). |
| `Musubi/PacketAcceptance.lean` | One immutable push's fields and send-time state, upload coverage, and actual packet checks that force the executable hub's acceptance decision. |
| `Musubi/SerialReply.lean` | Serialized calls, own-response recovery, shared request ids and notification scheduling between rounds. |
| `Musubi/RecordEpoch.lean` | Finite record adoptions and stale-plan reopens after current replies replace obsolete callbacks. |
| `Musubi/NotificationControl.lean` | Finite old notification handling, counting both in-flight logical frames and queued entries. |
| `Musubi/HubSuffix.lean` | Hub stabilization in raw graph space, with finite old-packet credit and a derived sender invariant. |
| `Musubi/HistoryWindow.lean` | The raw accepted-head chain from the record cut, and its entry into the hub suffix. |
| `Musubi/EarlyEntry.lean` | Entry API: imports all six layers below. |
| `Musubi/EarlyEntry/Abstract.lean` | The invariant a burst of node steps needs of a state. |
| `Musubi/EarlyEntry/Burst.lean` | Finite bursts with the known pair frozen. |
| `Musubi/EarlyEntry/Control.lean` | Raw control, choice guards, surveys and progress ranks. |
| `Musubi/EarlyEntry/FreshHead.lean` | Naming stabilization and a first fresh head-bearing reply. |
| `Musubi/EarlyEntry/FreshFetch.lean` | Taking current records through a fresh fetch. |
| `Musubi/EarlyEntry/RawEntry.lean` | Source laws, round restarts and assembled raw entry. |
| `Musubi/EntryAssembly.lean` | Pending-name custody and the native packet and record algebra for fixed records. |
| `Musubi/NodeSettle.lean` | Finite local control after hub stabilization, from individual calls and local scheduling. |
| `Musubi/CallBatch.lean` | Sequential finite call batches and injective virtual/wire-id correlation. Not used by the convergence proof. |
| `Musubi/Expansion.lean` | Expand each actual event to a positive finite path and transfer stabilization back. |
| `Musubi/NodeSys.lean` | Joint graph/control model, named request guards, hub-answer law and the raw-ancestry climb (`HubClimb`), invariants and shared scheduling facts. |
| `Musubi/NodeSysExec.lean` | Check structural writes with canonical id reuse. |
| `Musubi/NativeEvents.lean` | Replay event data and derive its eligible system run. |
| `Musubi/FineAssembly.lean` | Assemble the fine system from event replay, a starting snapshot, the derived history window and source bindings. |
| `Musubi/FineAssembly/Honesty.lean` | Preserve honest replies and notifications along the actual replay. |
| `Musubi/Schedule.lean` | Shared bounds on event indices, sampling order and batch completion. |
| `Musubi/NodeSysEntry.lean` | Derive node entry and preserve the joint control invariants under individual-call fairness. |
| `Musubi/HiveFilter.lean` | Observe eligible-node events, project the hive run and preserve its initial invariants. |
| `Musubi/SysFreshCuts.lean` | Derive cutoffs after which no old reply is consumed and no old notification processed; queues need not drain. |
| `Musubi/SysAcceptance.lean` | Convergence API: imports all nine layers below. |
| `Musubi/SysAcceptance/Acceptance.lean` | Actual request decisions and stable-hub acceptance. |
| `Musubi/SysAcceptance/Pending.lean` | The control/publication contradiction for a node that stays pending. |
| `Musubi/SysAcceptance/Pending/Contracts.lean` | Shared round, control and publication interfaces; native naming laws derive survival. |
| `Musubi/SysAcceptance/Eligible.lean` | Filtering and convergence of eligible nodes, with the starting snapshot, its history window and the fine-run interface. |
| `Musubi/SysAcceptance/Events.lean` | Individual hub and node observations projected into system steps. |
| `Musubi/SysAcceptance/Observations.lean` | Grouped hive observations and their sampled entry, fetch and pending views. |
| `Musubi/SysAcceptance/Cuts.lean` | Named phase boundaries and quiet-suffix conditions. |
| `Musubi/SysAcceptance/Contracts.lean` | Source laws grouped by responsibility, with completion and fairness assumptions, and the hub's climb from the record cut. |
| `Musubi/SysAcceptance/Phases.lean` | Derive old-effect, recovery, entry and fine cuts, the hub's history window at the fine cut, truthful knowledge and final eligibility. |
| `Musubi/SysAcceptance/Convergence.lean` | Compose the derived phases into hive convergence. |
| `Musubi/HubSys.lean` | Reads the hub's and nodes' policy fields out of the one joint system as a `Musubi.State`, with `parents`, which is acyclic when every operation's parents are smaller than it. |
| `Musubi/HubLedger.lean` | Retain actual send-time packet fields and prove coverage of outstanding eligible requests. |
| `Musubi/RawExpansion.lean`, `Musubi/RawMaintenance.lean` | Expand finite raw write batches, counting actual maintenance operations. |
| `Musubi/HubNodeSteps.lean` | Refine eligible node events to hub-suffix paths under explicit native primitive laws. |
| `Musubi/HubAnswers.lean` | Derive the suffix accept or frame from the actual immutable request and hub answer. |
| `Musubi/HubHistory.lean` | The hub's history of the joint run, by sequence number, and its history window from a climbing hub. |
| `Musubi/RequestBounds.lean` | Derive request bounds, expand actual joint events, and prove the hub stabilizes. |
| `Musubi/PendingEpoch.lean` | Bound pending alias changes with partial normalization and per-original coherence. |
| `Musubi/SupersedeExecTest.lean` | `#guard` smoke tests of `sexecStep`, including contracted acceptance, survivor advance and prepared adoption, checked at build time. |
| `Musubi/Refs.lean` | Per-machine refs, for one git ref: imports, exports, merges, conflicted remote bookmarks, and `jj undo` and `jj op restore`. |
| `Musubi/Expected.lean` | The conflicted-ref history walk, agreement under operation renaming, termination and the import-agreement boundary. |
| `Musubi/ExpectedExec.lean` | Finite operation DAGs and commit-side selection for the history oracle. |
| `Musubi/Presence.lean` | Which copies a hive shows. |
| `Musubi/PresenceExec.lean` | The presence rule on a finite history, executable, for the oracle. |
| `Musubi/PresenceContract.lean` | Presence through a contraction: stamps, presence at what survives, and ids with stamps (`sid`) composing in either order. |
| `Musubi/RefsExec.lean` | `Refs.lean`'s slot functions on targets a test numbers, with jj's merges as a table, for the oracle. |
| `Musubi/Copies.lean` | Which repository is the copy of a key: musubi's decisions, jj's config-id rule, and a machine's repositories moved, copied, deleted and replaced. |
| `Musubi/Names.lean` | The names a machine shows other machines' workspaces under, and `#guard` tests of them. |
| `Musubi/Publication.lean` | Cumulative snapshot accounting, exact approval, selected operation cleanup, and checks of the prepared result before installation. |
| `Musubi/OpHeads.lean` | What musubi decides about op heads it moves, as a pure function for the oracle and the code: `same` (`plan::same`); and what it reads of operations. |
| `Musubi/OpHeadsJson.lean` | The oracle's `opHeads` request. |
| `Musubi/OpHeadsRace.lean` | A small model of the op heads among jj commands, `jj op abandon`, `jj op integrate` and musubi's moves, and its theorems. |
| `Musubi/NativeLifecycle.lean` | Entry point for the finite native lifecycle model. |
| `Musubi/NativeLifecycle/Types.lean`, `Musubi/NativeLifecycle/Graph.lean`, `Musubi/NativeLifecycle/Selectors.lean` | Raw observations, finite graph queries, and source selection with explicit evidence gaps. |
| `Musubi/NativeLifecycle/NativeFacts.lean`, `Musubi/NativeLifecycle/Construction.lean` | Native observation tables and executable receipt and render construction. |
| `Musubi/NativeLifecycle/Steps.lean` | Executable preparation, revalidation and publication actions. |
| `Musubi/NativeLifecycle/ConstructionSound.lean`, `Musubi/NativeLifecycle/RunSound.lean` | Conditional construction facts and record custody along executable traces. |
| `Musubi/NativeLifecycle/Json.lean`, `Musubi/NativeLifecycleTest.lean` | Finite fixture codec and model examples. They do not authenticate native observations. |
| `Musubi/Axioms.lean` | `#assert_axioms`, which fails unless a theorem uses only the standard axioms, for every main theorem. |
| `Oracle.lean` | The `oracle` executable: a stdin/stdout loop around `ExecJson.handle`, which also answers measure, upload, presence, copies, chunks, attempts, names, refs, expected-value, publication and native lifecycle requests. |
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
and jj merges. [The asynchronous bridge](#the-asynchronous-liveness-bridge) states what is
proved of the real, lossy system.

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
(`IdTerm`, with content of any type; `CId` is `IdTerm Nat`), so the hash they stand for is
injective. `cid` takes an arbitrary immutable content function, allowing equal content at
different operations. `equal_content_recreates_id` proves
the three-operation counterexample when the content function is constant.

- `cpar_union`, `cid_union`: dropping `D₁`, then `D₂` from what is left, gives the parents and
  ids that dropping `D₁ ∪ D₂` gives; hence `cid_comm`, either order.
- `cid_eq`, assuming injective immutable content: two survivors' ids under two dropped sets
  are equal only for the same operation,
  with the sets agreeing on its proper ancestors. `superseded_ne`: an id from before a dropped
  set grew to include the operation or one of its ancestors is no survivor's id after. Both
  are instances of `idTerm_cpar_eq` and `idTerm_superseded_ne`, for content of any type.
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
`takeHeads` is the frontier of the incoming head and the current heads under the dropped set
(`Contract.frontier`): their surviving images, less those below another. `History.publish`
contracts the graph and publishes one fresh merge together with `Refs.cbeside`'s ref state.
`publish_refines` proves surviving ancestry and `CInv` together, and that the ref action is a
`CStep.beside`. `fixup_retains` states the fresh child/saved-expectation boundary: the new
operation receives its parent's slot and the saved expectation, rather than inferred again from
contracted ancestry. `abstraction_unique` uses the enforced immutable identity premise above;
`adoption_composes` connects sequential record contraction to the union of dropped originals.

The oracle executes those definitions directly for the abandonment/ref race, checking every
survivor's parents, the normalized merge base, the published merge and its ref state before
convergence. It also checks the fix-up's saved expectation and translation immediately after
publication. [Conformance and limits](../docs/internals/conformance.md#abandonment-and-refs)
describes the observation points and premises. This boundary does not replace the network
model, derive expected values from all jj histories, or prove publication's lock discipline.

`Supersede.lean` models the protocol over each operation's original, and adds the hub's and each
node's dropped sets, and which of the hub's it has pruned (`SState`). `SStep` is a `Step` of
`Model.lean` that gives each node no head of its own dropped set, and the hub none it remembers
dropping and, once it has pruned anything, none whose push doesn't carry the hub's records; or
one of:

- `sup`: the hub takes a dropped set with the `Cas` or `Push` it rides on, from its head to a
  new head the request doesn't drop, when every surviving image of its head, under its drops and
  the request's, is below the new head (`Contract.Below`), whether or not its head itself is;
- `advance`: a node advances to what survives of the head it knows, its heads becoming their
  frontier with that head under its dropped set (`Contract.frontierSet`), all of it local;
- `abandon`; `sendSup` (what the records a node took drop, its dropped set, and the head of its
  push, which those records don't drop); `sendD` (at least what the hub remembers); `adopt`;
- `adoptPrepared`: a node takes announced records and, at once, the frontier of its heads and
  known head under what it then drops, so it can take records that drop a head of its own;
- `prune`: the hub deletes the ids of some of what it dropped.

`SRStep` adds the hub going back to a head it still holds the closure of, and to the dropped and
pruned sets it had then. A hub that lost part of that closure is made again instead.

- `sinv_reachable`: the invariant `SInv`, for every step and whatever the hub prunes. The universe
  is a DAG, the hub holds its head's closure and every node its store's (`InvC`). The hub's
  history is a chain in its own comparison: each head's surviving images, under the drops the
  hub took the next head with, are below the next (`histBelow`). No head is in its holder's
  dropped set, the root is in none, every operation a node made and kept is below one of its
  heads, and the records a supersede carries drop no head of its push.
- `hub_moves_original`: a step that accepts a head without adding to the hub's drops moves the
  hub's head strictly up original ancestry. The hub's head can fail to be below the new head
  only if the push drops it.
- `dropped_never_head`: so, while the hub doesn't go back, it never takes a head it dropped,
  though it may have pruned it. `behind_not_carried`: a node that hasn't dropped an operation the
  hub pruned has no supersede the hub takes.
- `nodeD_grows`, `hubD_grows`: a node's dropped set only grows, and the hub's while it doesn't
  go back. `superseded_never_returns`, `superseded_never_returns_hub`: so, by `superseded_ne`,
  an id superseded on a node is never again an id of an operation it keeps, nor on the hub
  while it doesn't go back.
- `SChain`: what the liveness argument needs beyond `SInv`. The hub's history is a chain in
  original ancestry and every operation a node made is below one of its heads, which with `SInv`
  is `Regress.lean`'s `InvR` (`SChain.invR`); and every dropped operation is below a head of a
  node that dropped it (`Kept`). `schain_rstep`: a step keeps it when it moves the hub's head up
  original ancestry and each node's heads keep what they reached (`ChainOK`), as every policy step
  does; `schain_of_run`: every state reached by such steps satisfies it. An acceptance whose push
  dropped the hub's head, or an advance or prepared adoption that leaves work below no head, can
  reach a state where it fails: liveness from such a state is not proved here, though the
  asynchronous convergence theorem covers it under its premises ([Contracted
  ancestry](#contracted-ancestry)).
- `spstepR_reachable`, `smeasure_decreases`, `no_infinite_policy_runS`, `progressS`,
  `converged_quiescentS`, `terminal_iff_convergedS`, `eventually_convergesS`,
  `maximal_run_convergesS`: liveness once the hub stops going back, for the policy `SPStepR`,
  the steps of `PStepR` and `adopt`, `supPush` and `supFix`, from every reachable state that
  satisfies `SChain` and where every node has dropped what the hub pruned (`AllPruned`), though
  the hub announces only what it remembers. `allPruned_step`: a step keeps `AllPruned` as long as
  what it prunes, every node had dropped; `Exec.sexec_allPruned`: the executable hub keeps it in
  every state it reaches.
- `converged_all_droppedS`, `converged_all_acceptedS`: once converged, the hub and every node
  have dropped every operation any node dropped, and every operation any node made is below the
  hub's head.

The executable hub waits for every node, which gives `AllPruned`; the model has no clock, no
joining machines and no forgotten copies. The native hub waits for the copies present at its head,
for machines its history doesn't know and for those that asked it to join, that have said what
they took in the last day, and prunes nothing for an hour after it opens a store, as after a
restart, when it no longer knows which machines were joining. A machine it stops waiting for, a
copy the hive forgot, one whose join stalled for over a day, or one joining that was away when the
hub restarted and for over an hour after, is covered for safety by the relational `prune`, which
may prune anything the hub dropped, and its refusal by `behind_not_carried`: the hub takes no
supersede from it. The liveness theorems assume `AllPruned` of every node, so they say nothing of
a run with such a machine, not even that the others converge.
`history::a_joining_machine_back_within_an_hour_of_a_hub_restart_carries_on` and
`history::a_copy_joining_again_is_waited_for` check the native wait and successful recovery.
`hub::tests::pruning_waits_for_recent_joins_and_restart_grace` checks restart grace, join/rejoin
expiry and renewal with synthetic presence and reports. The native
`history::a_forgotten_copy_behind_pruned_records_stops` retains the stranded copy's refusal and
checks that none of its work is uploaded.

The measure puts `(drops not yet on the hub, drops not yet on each node)` before `rmeasure`. A
node can wait on another: with a head the hub dropped, or on a hub head it dropped and isn't
past. `progressS` shows the node with the newest head above the hub's head can always act, since
in an `SChain` state every dropped operation is below a newer head of a node that dropped it.

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
- `sid_eq`, `sid_superseded_ne`: as `cid_eq` and `superseded_ne`, with stamps; both are
  instances of `idTerm_cpar_eq` and `idTerm_superseded_ne`.

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

Selecting the surviving original from native jj history is also a test obligation.
`history::a_trim_below_an_accepted_push_keeps_the_other_copy_present` covers an accepted push
above a saved fetch base that a trim drops in full. Discovery must match against both
accepted histories together before `pres_eq` applies to the survivor. The pruning model
waits for its fixed participants; it does not prove the native presence-based wait set is
correct. The regression checks that set and that pruning waits for the other copy.
For unpublished surviving work, selecting its pre-trim state is another native obligation:
`history::a_trim_below_an_accepted_forget_keeps_the_copy_forgotten` checks a maximal accepted
frontier in both orders of saved base and own push. `pres_eq` does not select that frontier.

Root-based native publication, and publication while taking records that drop a current op
head (`NativeLifecycle` `dropsHead`), also select current local Git state independently of the
contracted shared ancestry. `Refs.lean` preserves supplied local slots, and
`AbandonRefs.publish_refines` uses its normalized common-base slot; neither proves this
native source selection, cache refresh, or Git HEAD handling. The trim, concurrent bookmark
change, cached-root and dropped-head regressions described in
[conformance](../docs/internals/conformance.md#presence)
check those boundaries against real repositories and the independent import checker.
The within-step forward-bookmark regression also compares immediate native publication with
the existing `realizeLocal` and `exportLocal` functions through the oracle. This covers the
root transition's current-state ref input; it does not extend the normalized-base theorem.

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

### Native preparation and publication (`NativeLifecycle/`)

This finite executable model selects sources from raw graph, namespace and record observations,
constructs receipts and rendered operations, and revalidates prepared work before publication.
Its proofs cover construction origins and record responsibility along the executable action
trace. Missing or ambiguous evidence stays explicit.

These results do not authenticate arbitrary native observations or establish a complete Rust
refinement. The native fixtures compare the model with the shipping code through the first retry
after a changed head; retry canonicalization beyond it and the whole publication are not
simulated. The real adapter fixtures and their schedule restrictions are described in
[conformance.md](../docs/internals/conformance.md#native-lifecycle-inputs-and-events), which owns
the correspondence and remaining gaps.

## The asynchronous liveness bridge

The liveness theorems of `Liveness.lean`, `Regress.lean` and `Supersede.lean` cover atomic policy
exchanges that succeed. `pstep_reachable` embeds each policy step in the asynchronous model, and
`Merged.lean` shows that merged exchanges give the same measure and convergence. Neither says
that an asynchronous run, with lost, duplicated and delayed messages and with retries, takes
policy steps. This section covers the proofs that do, tracked in
[#78](https://github.com/bos/jj-musubi/issues/78). They end in
`FineAssembly.hive_converges_observed`, whose premises [the trusted
base](#the-trusted-base-of-convergence) lists.

**Assumes.** The premises of the trusted base. The **correspondence** rows are checked against the
Rust by tests and not proved, so the result does not verify every Rust execution. The
environment rows say that the surviving participants are finite and their dropped originals
bounded; that from some point the hub is not remade, no body is lost or gc'd and no ordinary I/O
fails; that finitely many user changes happen; and that rounds resume fairly and serial calls
complete. The correspondence rows also take finite obsolete delivery, that old replies and
notices are consumed (`inboxStep`, `notesOld`). Permanent repository errors,
unavailable objects and jj merges the code does not support do not satisfy them. Fairness is
stated of enabled local work being scheduled (`fair`, `pushFair`); no premise says the progress
rank decreases.

**Scope limits.** The Rust conformance test checks measure descent only at completed, serialized
exchanges. `autoWritesStop` assumes a node's automatic writes stop; finitely many user and
configuration changes do not imply it. The writes include those a node makes outside a protocol
step (housekeeping, the round's prelude) and cleanup inside a busy call, such as working-copy
replacement inside `advance_to`: its `Advanced(B)` endpoint is a new canonical child of the
singleton target B, written to replace this machine's abandoned working copy
(`workspaces::forgotten_working_copies_can_be_abandoned`). An advance with no
further automatic write has the full-frontier effect, a law the proof uses only after the cutoff.

### Split exchanges (`AsyncLiveness.lean`)

- `bad_accept_before_reply`, `measureR_accept_before_reply`: a hub acceptance makes its pusher
  good before the acknowledgement arrives, if the node still has the single head it pushed and
  its `known` belongs to the current hub history. Losing the reply keeps the progress.
- `measureR_delayed_learn`: learning a strictly newer pair from the current hub history lowers
  `rmeasure`, even when another acceptance has moved the hub past that pair. A reply from a
  history the hub lost, and a recovery reset, are not covered.
- `settling_hub_stabilizes`: every reachable run of `SettlingStep` has a fixed hub head and
  sequence number from some point. Local policy steps, delayed consistent learning and
  bookkeeping are allowed; fix-up creation, hub regression and recovery from an obsolete history
  are excluded, so a concrete run must still be shown to have this form.

`lost_acceptance_and_delayed_fetch_make_progress` checks the first two lemmas
(`bad_accept_before_reply`, `measureR_delayed_learn`) through the core and the oracle.

### Request slots and fix-up writes (`RetryControl.lean`)

Executable boundary checks are in [conformance.md](../docs/internals/conformance.md#liveness).

- `old_slots_eventually_stop`: after any finite request-id cut, only finitely many replies can
  consume a pre-cut live request slot, even with infinitely many unmatched duplicates. It assumes
  ids are never reused; production ids are `u64`, so the correspondence excludes exhausting the
  counter. It does not bound queued notifications or show that a pre-cut call still live is
  eventually retired.
- `fixup_writes_le_one`, `fixups_eventually_stop`: in an epoch with no new abandonment
  discovery, obsolete-prefix adoption or interrupted write, a node completes at most one
  restoring write. The first adoption of the epoch may replace pending drops; later ones only
  remove them, in immutable original-operation names. No bound on network retries is needed.
  Neutral publication tips are extra work, outside this cached restoring-payload bound. Nothing
  proves that a run enters such an epoch, or that every production adoption only removes
  pending drops; the real-repository check pins cached reuse and reopening.
- `publication_progress`: with pending drops and the head equal to the known head, a child above
  the current head is required even when the restoring work is cached. `publication_tip_cached`:
  such a neutral tip leaves the restoring cache untouched. `publication_retry` concerns the
  helper's result state, where the head reads as no longer known; a restoring write can instead
  recreate the known body, which the native equality after the write must settle, and
  `NodeSettle.write_known` counts that cache change in its rank. These are local results, not a
  bound on tips across later replies or adoptions.

### Records

When rollback has stopped, every change to the hub's ordered record list appends a nonempty
difference that spends a previously unseen original drop. With original drops bounded, the list
is eventually fixed, and pruning then spends a bounded prefix.

- `RecordStability.lean`: `record_and_drop_sets_stabilize` gives one cut after which the ordered
  records, the pruning boundary and each node's dropped set stay fixed. It needs only the
  append, pruning and persistent-drop effects, not that raw local realization, which may contract
  parents, is a step of the original-history model. `sexec_record_prefix_stabilizes` derives
  those effects from the executable record constructors, leaving the bound on original drops and
  the end of rollback as assumptions. `adopt_pending_subset`: pending originals shrink under
  `adoptR` when the new record list extends the old dropped union; nothing proves that every
  production adoption extends it.
- `sexec_record_and_drop_sets_stabilize` (`RecordStability.lean`): the same cut for every
  executable run, survivor advance, prepared adoption and contracted acceptance included, by
  `sexec_record_control` and `sexec_node_drop_mono`. It assumes bounded dropped originals and
  no rollback, and needs no head stability, node record agreement, successful reply or
  decreasing rank.
- `RecordEpoch.lean`: counts the old announcement and received-record debt carried into a
  fixed-record suffix. A fresh `Fetched` announces only the fixed list, taking a list consumes
  every receipt, and receipt debt survives a reopen while the announcement does not. Adoption can
  invalidate a retained realization plan; the stale-plan error reopens the daemon, and a finite
  credit bounds these reopens. Other failures reopen without spending it, and their stopping is
  the premise `failFinal`. The projection omits knowledge, so it makes no claim that a restart
  preserves the local progress rank.
- `NotificationControl.lean`: notifications carry no request id, so the slot bound does not
  apply. The file counts old logical frames in flight and queued; arrival transfers credit and
  consumption spends it. It assumes that each frame is delivered once and receipt removes its
  queue entry, and that later publications come from the current history. Fresh notifications
  may continue forever.
- `SerialReply.lean`: `handleHead` models a node's known pair on a head-bearing reply: an own
  reply that is older or changed first resets knowledge, then `filteredLearn` takes a reply only
  if it is newer, as for a notification. `own_reply_learns`: an own reply that satisfies `hroot`
  (sequence 0 names the root) sets the known pair to the reply. `object_recoveries_stop` bounds
  the recoveries from obsolete requests, given preserved request adequacy and a reset that
  restores it. That adequacy covers the remaining calls of a batch and the truthful have claims,
  not only the stored known head, and must be established after old effects stop.

### Entry

These proofs use the driver's round scheduling: knowledge cannot chase notices inside a running
round, and until current records are applied a push is refused before its expected head is read.
`EntryAssembly.eligible_pending_empty` derives an eligible node's empty pending list from
ordered-record identity and custody, which disables core fix-ups and publication tips.
`HistoryWindow.lean` carries the strict raw history from the record cut to an eligible node's
entry; the node need not already know the latest sequence.

- `EarlyEntry/Burst.lean`: between RPCs or idle, a node with a frozen known pair has finite local
  work (closure, plan, advance, merge), ranked by locality and frontier coverage. The executable
  `stepB` is proved sound and checks the actual core through `localBurst`;
  `local_burst_conforms_across_a_pending_namespace` checks the real adapter. A burst excludes
  record-taking advances and does not bound later daemon housekeeping, which the automatic-write
  premise covers.
- `Control.Naming.settles`: pending-name changes cease inside a prefix that need not end. Each
  head has its own finite support, and none is shared by all future heads. The normalizer's
  support and mapping-retention laws are native correspondence obligations.
- `EarlyEntry/Control.lean`: extends this across complete metadata calls. `rawControl` and
  `callB` check the raw survey and the call effects against the shipping core, and
  `raw_recovery_choices_and_calls_match_the_model` does so on a raw chain with independently
  missing bodies and objects, different local frontiers, pending drops and record comparisons.
  The driver must still schedule the next start-fetch after idle and complete each call
  (`idleStart`, `doneIn`).
- `fresh_head_reached`: with that scheduling, a node gets a fresh reply to its own head request,
  and a refusal updates the heard records, so the node does not push again with the same stale
  record offer. `fresh_fetch_takes`: after a fresh fetch, a six-part rank (counting missing
  bodies and per-operation objects) forces record-taking or already-current records, using only
  the active prefix of the round. Equal records can still need adoption to consume custody
  (`RecordEpoch.needsRecords`).
- `raw_entry_reached`, `raw_entry_persists`: a node enters on fetch and push replies, and keeps
  entry once ordinary failures and their reopens stop. An entered node's push cannot cause an
  incomplete-upload reopen.

`fresh_fetch_takes` takes the premise `hserve` (`EarlyEntry/FreshFetch.lean`) and
`raw_entry_reached` takes `hroundServe` (`EarlyEntry/RawEntry.lean`): no `GetObjects` of the round
after a fresh fetch fails. Neither is a law of the run; each is to be derived from the hub keeping
what it can serve. All of the entry results are component results. Their inputs must be the
actual sampled daemon events and packet.

### Hub stabilization

- `HubSuffix.lean` (`hub_suffix_stabilizes`): in a growing acyclic raw graph, the hub's head and
  sequence stabilize if eligible maintenance writes are finite; acceptances need not be. A packet
  invariant shows that a sender of the current generation still holds the head it sent, and every
  other packet that can move the hub belongs to a finite earlier list whose targets pay for it.
- `NodeSettle.lean`: a rank falls until a node is settled or emits a proper push from the
  settled hub head. `PacketAcceptance.lean`: the proper packet meets no refusal, rejection,
  idempotence or incomplete closure; upload coverage uses the actual base-image frontier once
  server-generated contraction bodies are present.
- `Supersede.hub_moves_original`: once records stop changing, the hub moves strictly along
  original ancestry, and from every reachable state each step the executable hub takes is a step
  of `SRStep` (`Exec.sexec_sound`). `packet_sender_after_cut_aligned` (`PacketAcceptance.lean`):
  an accepted packet's sender is eligible throughout the suffix, so other nodes' packets cannot
  move the hub. The native counterpart works on the hub's raw graph, with no projection from
  canonical versions to immutable originals.
- The joint system: `NodeSys` keeps each node's scoped embedding into one raw graph and retains
  immutable requests; `HubLedger`, `HubNodeSteps` and `HubAnswers` derive packet coverage, expand
  local events and use the actual accepted request; `SysFreshCuts` derives the cutoffs for
  consumed old replies and processed old notifications; `RequestBounds.hub_stabilizes_sys`
  builds the expansion from these events, finite maintenance included. Initial requests stay in
  the old-packet budget even when their sender is ineligible.
- `SysAcceptance` couples the actual answered request to one executable decision with its
  conditional primitive laws. Those laws need native correspondence; the theorem does not
  establish them by assuming acceptance. `eligible_system_converges`
  composes the hub proof with local settling and keeps the physical raw heads in agreement with
  the hub. Only newly issued pushes must finish; orphan requests of an old client session need
  not drain.

### Ineligible nodes

A node with pending drops translates hub operations into its own namespace, so it cannot use the
eligible node's single raw embedding. `SysAcceptance.no_forever_pending`: on a stable hub such a
node cannot stay pending forever, since finite local and completed-call work yields a pending
push that the raw publication decision would accept, moving the hub. It takes the control,
publication and `survival` interfaces and the premises `hstable` and `hserve`
(`SysAcceptance/Pending.lean`). The offered records, the
records last heard and the hub's current records are bound separately, because the core's
`differ = false` alone does not give the hub's record comparison. `RawPublish` is checked through
`rawPush` against all five shipping outcomes. No eventual push is a premise, and original-
operation ids are not identified with raw ids.

`raw_noneligible_answer_frame`: from native packet and record effects, a fresh answer to an
ineligible node leaves the hub unchanged, without assuming the node applied the current records.
In the accepted branch, matching records, complete custody, unpublished pending originals and
current pending-name coverage make unchanged ordered records impossible; the coverage matters
because a superseded raw alias can name a surviving rewritten original.

### The assembly

- `NodeSysEntry.filt` builds the eligible nodes' fine system from the hive observation,
  freezing the other nodes' slots and omitting their fresh requests and replies. `filt_step`
  turns each observed event into a fine-system event, ineligible writes into raw graph growth
  and their fresh answers into frames. The observation starts once eligible nodes have handled
  a fresh head after the record cut and taken current records, since before that an eligible
  node's obsolete known head can have a different node-space image. `hive_filtered` derives
  the initial invariants.
- `NativeEvents` builds the run recursively from event data. Each event's bindings state that
  call's source obligations, and `observed_hs` derives the eligible system's steps; invariants
  that a later reply or notification needs are carried by induction (`FineAssembly/Honesty.lean`).
  An answer to another machine carries its post-answer hub snapshot, and its binding must show it
  unchanged, using `raw_noneligible_answer_frame`, before the event is filtered as a frame.
- `FineAssembly.fineAt_of` assembles the fine system from the replay, and
  `hive_converges_observed` derives the freshness of consumed replies and notices from the
  old-effects cutoff and the completed batches: a later completed batch began after an earlier
  one completed, so its head-bearing reply was requested after the cutoff.
  `NativeEvents.RecordView` ties the raw observer's applied identity to the fine node's and the
  original-drop view. Different raw encodings of one dropped-original set are not identified.
- `SysAcceptance.hive_converges` joins record and drop stabilization, entry, eligible-system
  convergence and the contradiction for ineligible nodes, on data sampled from one observation,
  including the same push and its handling time. A sampled step runs to the completion of its
  request batch.

[Reading the integration proofs](#reading-the-integration-proofs) gives the order of the proof.
`finite_common_cut` (`Basic.lean`) joins every node's cut, and stable-head knowledge with
`PendingLaws.absurd` excludes the ineligible nodes.

Two limits of the premises: a native fetch can update knowledge before its following objects
call finishes, while the system keeps the exchange's starting pair until the batch completes,
so the latch binding relates completed observations, not every intermediate callback; and
matching applied records does not make whole normalizers equal, since one machine may have extra
pending drops. The completion and scheduling premises (`doneIn`, `answer`,
`EntryLaws.objects_step`, `idle_restarts`) are obligations on the sampled execution, not derived.

### Contraction and canonical bodies

Because a machine may have more pending drops than another, the assembly needs contracting by a
subset to leave a body unchanged.

- `Contract.cpar_absorbs_subset`, `cid_absorbs_subset`, `PresenceContract.sid_absorbs_subset`: a
  history or body already contracted by a larger set keeps its parents and canonical id, with
  its presence stamp, when a subset is dropped again.
- `image_absorbs_subset`: a surviving body's singleton image is unchanged. `anc_cpar_survives`:
  its whole closure, head included, consists of survivors.
- `image_original_survives`, `image_ne_dropped_original`: when drops name originals, no image is
  any version of a dropped original, whether or not originals distinguish raw versions.

Their native use still requires a complete canonical-body construction and survival of the sent
head; a metadata lookup that falls back to the identity supplies neither.

The hub's remembered drops and its cached renamings are separate: a drop republished beside the
remade hub's current history can have no cached image, so `is_superseded` recognizes it while
`current` returns its input unchanged
(`a_drop_outside_the_hub_head_is_remembered_without_a_cached_image`). `not_dropped_of` shows that
survival of every original in a body's ancestry excludes remembered names and cached keys
(`NodeSys.Exec.unsuperseded_of_normal`), so with the hub's drops a subset of the node's, neither
can mark a normal sent body.

### Contracted ancestry

The shipping hub accepts a cached fix-up that drops its expected head, when the head's surviving
images are below the fix-up (`a_push_can_drop_its_expected_head_and_reuse_a_cached_fixup`, after
an interrupted adoption and a hub rollback, with the hub holding no records: the push brings the
drop). `SStep.sup` accepts by that comparison, so this is
a step of the one relation, and `SInv` holds after it. The hub's history is then a chain only in
the hub's own comparison (`SInv.histBelow`), and the liveness theorems, which need an original
chain (`SChain`), say nothing of the states that follow. `FineAssembly.hive_converges_observed`
covers them, under its premises. Those are assumed only from a record cut on (`climbs` and the
history window it gives start at the hub's sequence there), and an acceptance like this one adds
to the hub's drops, so it comes before the records stop changing; from then on every acceptance
is in original ancestry (`hub_moves_original`), as `HubLaw.guards` requires. The executable hub
decision there checks `belowB` (`Exec.PacketPrimitives.descends` in `PacketAcceptance.lean`).

- `Contract.lean`: `Below` says every surviving image of the expected head is below the new
  head, and `belowB` (`ContractOrder.lean`) also checks that the image is nonempty, as the hub
  does. `below_two_step`, `below_contracted_iff`: contracting a contracted history equals
  contracting by the union, and original and current-graph ancestry of the images agree. For a
  fixed drop set, `stable_suffix_chain` gives a reflexive original-ancestry chain of surviving
  heads, and `Supersede.hub_moves_original` a strict one once the hub's drops stop growing. The
  real trace checks the accepted push against `belowB` through the `contractedAncestry` route.
- `RecordStability.eventual_original_chain`: a trace of surviving hub heads compared under each
  resulting dropped set has an eventual original-ancestry chain. The immutable graph and the
  contracted comparisons are premises; their projection onto the physical store and strict head
  changes are not derived.
- `Exec.sexec_sound`: every step the executable model takes, advance through every surviving
  image and preparation changing frontier and record custody in one boundary included, is a
  step of `SRStep` or none. The model does not prove convergence of every network action; the
  raw-namespace assembly handles canonical versions and normalization in their birth parents
  through its explicit projection.

A failed sync can leave an accepted hub head, partially received data or a newly written fix-up.
`supFix` combines fix-up creation with acceptance, so a failed push leaves the creation without
its compensating decrease, and the production cache may return no new restoring operation. The
raw-namespace model separates creation from acceptance and compares actual contracted ids, which
the original-operation policy cannot do for every native transition. Cached restoring work does
not by itself publish its drops: when the hub already has the cached fix-up and an abandonment
is pending, the core requests a neutral child on the current head
(`pending_drops_get_a_new_tip_when_the_hub_already_has_the_cached_fixup`,
`a_cached_fixup_publishes_pending_drops_even_when_its_head_is_known`). Adopting an obsolete
ordered-record list can raise `recordLagE` even when no dropped set changes; the record-aware
theorem covers taking current hub records, not arbitrary old announcements.

### Native correspondence

The hub-side event projection separates a push's writes from its decision. A read reply has a
computable observation of the hub before and after (`checkAnswer`, sound by
`HubAnswer.observed_step`), which the `hubRead` route compares against the shipping `Fetch` and
`GetObjects` handlers in the native pending-namespace fixture. The assembly does not use
`checkAnswer` or `HubAnswer.observed_step`: they are the soundness proof of the oracle's `hubRead`
check. Nothing constructs the whole native event projection, including the node's labels and
request slots. No checker tests the exact relation that `FineSource.replay` and `binds` state,
and none tests the node-side fields of `binds`; these routes cover parts of the projection.

| Native behavior the model leaves to tests | Check |
| --- | --- |
| Own writes can reuse a canonical operation: two copies merge the same frontier with equal metadata and the second reuses the first's id. `GrowR` allows it and `NodeSysExec` checks both writes through `nodeGrow`. | `independent_merges_can_reuse_a_canonical_operation` |
| Physical heads can alias one canonical body: an interrupted Git export leaves both as heads, and the next merge writes a child with their one canonical parent. | `interrupted_git_export_can_leave_aliased_operation_heads` |
| Pending names match the raw known hub history by immutable identity, and an incoming record clears the same original under another name, including on a replacement hub. | `record_bodies_keep_pending_drops_named_after_hub_rollback`, `lost_records_follow_an_older_name_the_receiver_never_held` |
| The saved raw fetch base's objects are checked before use, since a restore, abandonment and jj gc can remove them while a local image remains. | `fetch_base::collected_objects_of_an_abandoned_fetch_base_are_fetched_again` |
| An empty objects reply fails, reopens and completes a fresh round, since a hub remake can leave a sync requesting an old head. | `objects::an_empty_object_reply_retries_from_the_remade_hub` |
| Records received before preparation writes a local operation are kept without counting as applied or being acknowledged; lost receipts become pending together with the contraction of their local versions. Missing WORK timestamps are recovered from the exact original in retained record metadata. | `received_records_survive_departure_and_drop_local_aliases` (checks equal-record receipt recovery against `RecordEpoch.exec`), `lost_received_records_preserve_work_before_the_fixup_arrives` |

Open obligations for a native refinement:

- Aliased physical heads must be normalized before the fine suffix uses unique canonical heads;
  duplicate readings cannot be dropped as an invisible step.
- `PendingEpoch.lean` proves a finite cutoff for pending-name aliases once pending originals
  stop growing and known heads belong to the fixed-record window; the native code must still be
  shown to meet its per-step known-source rule and partial-normalization steps.
- Labels for an unknown head's ancestry are ghost structural exposure: availability stays false
  until bytes or realizations arrive. Raw translation does not infer an abandonment this machine
  does not own from missing ancestry.
- A bounded retry trace in the lower-level hive harness alone does not show one endless driver
  round; production ends a round on an incomplete upload with its documented refusal.

### Transport

`StreamTransport` consumes the matching pending request, removes it on timeout and drains pending
requests on disconnect, `NodeDriver` processes one protocol call at a time, and the daemon
handles notifications outside `sync`. So, with ids never reused, a retired call's late reply is
never assigned to a later request. A call still live can return a reply computed before a hub
remake, and the safety model allows arbitrary replay and a `known` that moves backwards
(`learnUnfiltered`). Neither finite obsolete delivery nor monotone `known.seq` follows from it;
the trusted base takes finite obsolete delivery as the premises `inboxStep` and `notesOld`.
`replies_only_complete_the_matching_pending_call_once` checks the client's correlation against
`Retry.Inbox.finish` with obsolete and duplicate frames delivered directly, since service-side
reply inboxes may discard them first. The transport contract also checks a canceled call's reply
arriving after a fresh exchange and duplicates of a completed reply. These checks support the
local boundaries of the conditional refinement; they do not by themselves establish it.

### Results the convergence proof does not use

The whole of `AsyncLiveness.lean` and `CallBatch.lean` (which justifies sequential native calls
and interleaved physical request ids under injective correlation) is not used, nor are these
parts of other files:

| File | Not used |
| --- | --- |
| `RetryControl.lean` | `fixup_writes_le_one`, `fixups_eventually_stop`, `publication_retry`, `publication_tip_cached` |
| `RecordStability.lean` | `sexec_record_prefix_stabilizes`, `adopt_pending_subset` |
| `SerialReply.lean` | the serialized-call model and its invariant (the proof uses `handleHead`, `filteredLearn`, `own_reply_learns`, `object_recoveries_stop`, `wentBack`) |
| `RecordEpoch.lean` | `exec_sound` and the `Guard` facts |
| `SysAcceptance/Events.lean` | the answer-observation check (`expectAnswer`, `checkAnswer_expect`, `HubAnswer.observed_step`), `HubAnswer.push_handled`, `NodeIssue.raw_step`, `learn_new_bare` |
| `PacketAcceptance.lean` | `packet_checks_accept`, `packet_upload_closes`, the packet-coupling theorems (`packet_sender_aligned` and the rest), and their helpers |
| `EntryAssembly.lean` | everything except `PendingOriginals`, `eligible_pending_empty` |
| `PendingEpoch.lean` | `pending_names_settle_with_old_known` (an obsolete known pair), `pending_names_settle_from_sources`, `finite_metadata_output_stabilizes` |
| `RequestBounds.lean` | `hub_stabilizes_hive` |
| `EarlyEntry/Burst.lean` | `no_infinite_burst`, `localFromImages`, `local_grows_after_inputs` |
| `EarlyEntry/Control.lean` | `no_infinite_calls`, `raw_round_yields` |

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
  objects outside `closure(head)` in the original-ancestry relation. The executable
  model preserves operation bodies needed by retained historical heads: an older head can
  be outside the current closure after contracted acceptance. Historical-only objects may
  still be lost. A requested rollback to an incomplete target is an explicit environment choice
  that remakes the hive. Whether native startup detects every damaged prefix is not modeled, and
  the model adds no hub durability requirement.
- **Ghost state.** `creator`, `isMerge` and `birth` record each op's creator, whether it is a
  merge, and the hub `seq` at its creation; `hist` records the history of accepted heads.
- **Original operations.** `Supersede.lean` identifies each canonical operation a drop renamed
  with its original. A node's operations there include the dropped ones it had, with their
  objects, as an abstraction of the real node, which keeps only survivors; the real hub's
  closure check, and a node's realization, are then taken over survivors, which contraction
  keeps in the same ancestry (`anc_cpar_iff`). Within this fixed-birth-graph abstraction,
  the names are `cid` under each dropped set. A native version can carry normalization in its
  birth parents, so an original label and a party's current drop set do not by themselves give a
  complete physical-store projection.
- **Translation layer.** It is not modeled. The model assumes what [protocol.md, "Translation
  layer"](../docs/internals/protocol.md#translation-layer) requires: `canon` is injective on
  reachable local operations, `canon(realize(C)) = C`, and realization never creates a canonical
  operation. Under those assumptions, the properties over canonical ids carry over to each node's
  local op log. The abandonment/ref boundary test checks selected properties before and
  immediately after publication; the generated end-to-end tests check all of them at every full
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
- **Supersedes:** the hub refuses a push whose new head it has dropped, and takes a dropped set
  only with a push that leaves the new head; a node advances to no head it has dropped, and
  applies a dropped set only once none of its heads is in it. When the hub takes a dropped set,
  it holds the contraction of its history: it computes it, rather than taking a node's word.
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

The real repository's `advance` can also finish taking records. It holds them in the same save
that counts their renaming, before moving heads, and after an interrupted move recovery finishes
the heads and workspace records. Holding them only in a later `Adopted` step would lose the
responsibility to republish a drop if the hub rolled back in between, and the machine could
retry the same rejected push forever. The real-repository races
`a_sync_stopped_while_taking_an_abandon_the_hub_then_loses` and
`taking_an_abandon_resumes_where_it_stopped` check the completed advance and its internal
save, head and workspace boundaries.

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
   `bad request: <reason>`: operations' parents must come before them, heads and indices must be
   in range, current heads must survive the dropped set, and a requested control action must be
   enabled. The protocol decisions are made by `execStep` and `sexecStep`, not by the codec.

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
  and `recordConvergedE_iff` connect their computations to the original model. The oracle
  returns `rmeasureCE` (`SupersedeExec.lean`), the measure counted through surviving images, as
  the suffix of `smeasure`, record debt as `recordLag`, and the stronger convergence check as
  `converged`. `rmeasureCE_without_drops` proves exact agreement with `rmeasureE` when nothing
  is dropped. That it decreases from states past a contracted acceptance is not proved; the
  generated strict-decrease checks test it.

The set abstraction alone does not establish record agreement: after a remake, a machine
may republish two old drops as one record while another retains two records with the same
union. `regrouped_records_conformance` reaches this through the core and oracle.
`recordMeasure_decreases` and `recordPolicy_wf` cover projected `SPStepR` progress and the
record-only adoption omitted by that policy. Set-based progress may increase record debt,
so it comes last. `recordLag_adopt_lt` and `recordLag_le` bound repairs by the number of
machines while the hub is fixed. `record_finish` proves finite completion from abstract
convergence where every node has dropped what the hub pruned (`AllPruned`, as
`sexec_allPruned` gives), preserving the entire abstract state. `reconcile_executable` checks
the announced-record adoption, its head guard and its pruned-prefix check. `NodeCore` follows
this rule: it adopts differing record lists even with no missing drop, opening the
executable push guard. The oracle and harness check record debt and concrete convergence
independently of the set measure. Collision resistance of record digests is not proved, and
asynchronous reply and retry scheduling is covered by [the
bridge](#the-asynchronous-liveness-bridge) under its premises; see [conformance.md,
"Liveness"](../docs/internals/conformance.md#liveness).

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

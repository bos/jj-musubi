/-
Source, completion and scheduling contracts of one actual hive run. Each group owns one kind
of obligation; `HiveContracts` assembles them.

The observation begins after the last destructive fault that loses records, drops or recent
local writes. Convergence on this suffix transfers to the whole execution by its time offset.
The cuts, truthful knowledge, entry, hub stability and eligibility are derived in `Convergence`.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance.Cuts
import Musubi.SysAcceptance.Events

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts Musubi.EarlyEntry.Control

namespace Source

variable {ρ α : Type}

/-- Record effects and bounded original drops, on the suffix after the last destructive fault.
Append, prune and custody laws hold from the start. `epochStep` applies only once records and
drops are fixed and old replies and notifications have stopped taking effect; before that, an
old `Fetched` may still announce old records. -/
structure RecordEffects (N : Nat) (recs : Nat → Exec.SEState) (B : Nat)
    (epoch : Nat → Nat → Retry.Records.State) (adopts fails : Nat → Nat → Bool)
    (recLabel : Nat → Nat) (O : HiveObs ρ α) : Prop where
  /-- Each step leaves the records as they are or takes some of them off (`takeRecs`). -/
  recStep : ∀ i, (recs (i + 1)).recs = (recs i).recs ∨
    ∃ D, (recs (i + 1)).recs = (recs i).takeRecs D
  /-- The pruned count never decreases. -/
  prune : ∀ i, (recs i).pruned ≤ (recs (i + 1)).pruned
  /-- The pruned count is at most the number of records. -/
  pruneLe : ∀ i, (recs i).pruned ≤ (recs i).recs.length
  /-- A node's dropped originals only grow. -/
  dropsGrow : ∀ i n, n < N → ∀ x, x ∈ (recs i).nodeDF n → x ∈ (recs (i + 1)).nodeDF n
  /-- The hub's drops are all below `B`. -/
  hubBound : ∀ i x, x ∈ (recs i).hubDL → x < B
  /-- Every node's drops are all below `B`. -/
  nodeBound : ∀ i n, n < N → ∀ x, x ∈ (recs i).nodeDF n → x < B
  /-- After the records are fixed at `kR` and old effects are gone at `k`, each node's retry
  epoch follows `Retry.Records.Step`, with the adopts and fails of the run. -/
  epochStep : ∀ kR k, RecordsFixedFrom N recs kR → kR ≤ k → OldGone N O kR k → ∀ n, n < N →
    ∀ i, k ≤ i →
    Retry.Records.Step (recLabel kR) (epoch n i) (epoch n (i + 1)) (adopts n i) (fails n i)

/-- Environment assumptions and object-credit effects. Failures, losses, user work and automatic
semantic writes eventually stop. Termination of automatic writes (housekeeping, prelude, inline
cleanup, passed-on abandon, late reparenting) is assumed, not derived.

A missing-object reply consumes the node's credit and begins recovery; the credit is kept
otherwise. So missing-object failures eventually stop, and that cutoff is derived. -/
structure Environment (N : Nat) (O : Observation.Environment) : Prop where
  /-- Loss eventually stops. -/
  envFinal : ∃ kE, ∀ t, kE ≤ t → ¬ O.lost t
  /-- While nothing is lost, `objReady` stays true. -/
  readyKeep : ∀ n t, n < N → ¬ O.lost t → O.objReady n t = true → O.objReady n (t + 1) = true
  /-- While nothing is lost, an object failure occurs only with `objReady` false, and sets it. -/
  readyFail : ∀ n t, n < N → ¬ O.lost t → O.objFail n t →
    O.objReady n t = false ∧ O.objReady n (t + 1) = true
  /-- I/O failure eventually stops. -/
  failFinal : ∃ kF, ∀ t, kF ≤ t → ¬ O.ioFail t
  /-- Native automatic writes eventually stop. -/
  autoWritesStop : ∀ n, n < N → ∃ kA, ∀ t, kA ≤ t → ¬ O.autoWrite n t
  /-- User work in node repositories eventually stops. -/
  userFinal : ∃ kU, ∀ t, kU ≤ t → ∀ n, n < N → ¬ O.userWork n t

/-- Finite old effects. Replies consume live call slots or reopens retire them; the shared id
counter is never reset. Notices have a separate finite in-flight and queued lifetime, including
across reconnects. Old traffic need not drain fairly: only these finite lifetimes are assumed. -/
structure Transport (N : Nat) (O : Observation.Transport) : Prop where
  /-- Each node's call-slot inbox follows `Retry.InboxStep`; below the cut `c`, a handled own
  reply is a retirement. -/
  inboxStep : ∀ c n t, n < N →
    ∃ b, Retry.InboxStep c (O.inbox n t) (O.inbox n (t + 1)) b ∧
      ∀ id a, O.own n t = some (id, a) → id < c → b = true
  /-- If an own reply carries call id `id` and the inbox's next id at `t` is at most `id`, the
  call was made at or after `t`, so ids are not reused. -/
  callIds : ∀ n t u id a, n < N → O.own n u = some (id, a) → (O.inbox n t).next ≤ id →
    t ≤ O.callAt n id
  /-- Notices published before `c` have a finite lifetime (`Retry.Notifications.Step`). -/
  notesOld : ∀ c n t, n < N → c ≤ t → ∃ h, Retry.Notifications.Step (O.oldNotes c n t)
    (O.oldNotes c n (t + 1)) h ∧ ∀ a, O.note n t = some a → a < c → h = true

/-- Native knowledge and history effects. An own reply names a hub state between call and
handling; a notice names a state no later than handling. Both use `handleHead`, and nothing
else changes the known pair without reopening. Sequence monotonicity and history bindings
hold once loss has stopped, whether or not the hub is stable. -/
structure Knowledge (N : Nat) (run : Nat → Sys) (O : HiveObs ρ α) : Prop where
  /-- An own reply handled at `t` updates the known pair by `handleHead` with a hub state `a`
  between its call and `t`. -/
  ownHead : ∀ n t id a, n < N → ¬ O.reopen n t → O.own n t = some (id, a) →
    O.callAt n id ≤ a ∧ a ≤ t ∧
    ⟨O.seq n (t + 1), O.known n (t + 1)⟩ = Retry.Serial.handleHead O.root true false
      ⟨O.seq n t, O.known n t⟩ ⟨(run a).hub.seq, (run a).hub.head⟩
  /-- A notice handled at `t` updates the known pair by `handleHead` with a hub state `a ≤ t`. -/
  noteHead : ∀ n t a, n < N → ¬ O.reopen n t → O.note n t = some a →
    a ≤ t ∧ ⟨O.seq n (t + 1), O.known n (t + 1)⟩ = Retry.Serial.handleHead O.root false true
      ⟨O.seq n t, O.known n t⟩ ⟨(run a).hub.seq, (run a).hub.head⟩
  /-- With no reopen, own reply or notice, the known pair is unchanged. -/
  quietKnown : ∀ n t, n < N → ¬ O.reopen n t → O.own n t = none → O.note n t = none →
    (⟨O.seq n (t + 1), O.known n (t + 1)⟩ : Known) = ⟨O.seq n t, O.known n t⟩
  /-- A hub at sequence 0 has the root as its head. -/
  rootSeq : ∀ a, (run a).hub.seq = 0 → (run a).hub.head = O.root
  /-- While nothing is lost, the hub's sequence does not decrease. -/
  hubSeqStep : ∀ t, ¬ O.lost t → (run t).hub.seq ≤ (run (t + 1)).hub.seq
  /-- From a time with no later loss, the history maps the hub's sequence to its head. -/
  histBind : ∀ a, (∀ s, a ≤ s → ¬ O.lost s) → O.hist ((run a).hub.seq) = (run a).hub.head

/-- Local source laws scoped to their phase. Entry laws read each actual sampled event through
its completed batch, then frame that result to the next post-prelude reading. Their object
and restart laws include completion assumptions.

Past the cut, a reopen follows `Incomplete` or an unrecovered missing-object reply. An entered
push from the hub head is closed, and entry persists otherwise. Once the hub stays and a node
knows it, `pending` supplies that node's own frozen-round laws for samples past the cut;
`PendingLaws.absurd` later rules out ineligibility. -/
structure Entry [DecidableEq ρ] (N : Nat) (run : Nat → Sys) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (Rof : Nat → ρ) (wOf : Nat → Nat) (O : HiveObs ρ α) : Prop where
  /-- Each sampled event from the cut on satisfies `EntryLaws`. -/
  entry : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n, n < N → ∀ p,
    k ≤ O.sched n p → EntryLaws (Rof k) (wOf k) (O.entryData n p)
  /-- A reopen is due to `Incomplete`, or to an object failure not yet recovered from. -/
  reopenWhy : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    O.reopen n i → O.incomplete n i = true ∨
      ∃ t, t ≤ i ∧ O.objFail n t ∧ ∀ s, t < s → s < i → ¬ O.reopen n s
  /-- An incomplete push expects the hub's head and is not closed. -/
  incHead : ∀ k, CutAt N recs adopts fails k → ∀ n i, n < N → k ≤ i →
    O.incomplete n i = true → O.expectedIsHead n i = true ∧ O.closed n i = false
  /-- An entered node that expects the hub's head has a closed push. -/
  closure : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    RawEntry (Rof k) (wOf k) (O.rawAt n i) → O.expectedIsHead n i = true →
    O.closed n i = true
  /-- Entry persists across a step with no reopen. -/
  keep : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    RawEntry (Rof k) (wOf k) (O.rawAt n i) → ¬ O.reopen n i →
    RawEntry (Rof k) (wOf k) (O.rawAt n (i + 1))
  /-- A node that is ineligible, entered, and knows the stable hub's head satisfies
  `PendingLaws` on its samples. -/
  pending : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n p, n < N →
    k ≤ O.sched n p →
    (∀ i, O.sched n p ≤ i → (run i).hub = (run (O.sched n p)).hub) →
    (∀ i, O.sched n p ≤ i → O.known n i = (run (O.sched n p)).hub.head) →
    (∀ i, O.sched n p ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
    ¬ EligibleAt N recs k n →
    PendingLaws ⟨(run (O.sched n p)).hub.seq, (run (O.sched n p)).hub.head⟩
      (O.pendingData n p (Rof k))

/-- Scheduling and batch completion. Each node has infinitely many ordered samples. Its batch
completes before the next sample, whose prelude has its own hive times. A node between rounds
eventually starts a round, followed by an active sample. These are progress assumptions;
an active sample does not by itself make the sampled event a core step. -/
structure Scheduling (N : Nat) (recs : Nat → Exec.SEState) (adopts fails : Nat → Nat → Bool)
    (O : HiveObs ρ α) : Prop where
  /-- A node's sample times strictly increase. -/
  schedMono : ∀ n p, O.sched n p < O.sched n (p + 1)
  /-- A sample's batch completes at or after it and before the next sample's prelude. -/
  doneIn : ∀ n p, n < N → O.sched n p ≤ O.doneAt n (O.sched n p) ∧
    O.doneAt n (O.sched n p) + 1 < O.sched n (p + 1)
  /-- An inactive node eventually starts a round. -/
  idleStart : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n p, n < N →
    k ≤ O.sched n p → O.active n (O.sched n p) = false → ∃ q, p ≤ q ∧ O.starts n (O.sched n q)
  /-- The sample after a started round is active. -/
  startActive : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n q, n < N →
    k ≤ O.sched n q → O.starts n (O.sched n q) → O.active n (O.sched n (q + 1)) = true

/-- Correspondence between native observations and the fine system. Its clock is hive time;
maintenance and notifications name the actual native effects. A consumed head-bearing reply
belongs to the completed sampled batch and its own call. The system holds the last completed
or post-prelude snapshot, through the latch laws. -/
structure SystemBindings (N : Nat) (run : Nat → Sys) (acts : Nat → Act) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (O : HiveObs ρ α) : Prop where
  /-- The system's clock is hive time. -/
  clock : ∀ i, (run i).time = i
  /-- A maintenance step of the system is an automatic write of the node. -/
  maintBind : ∀ n i, n < N → acts i = .core n .maint → O.autoWrite n i
  /-- A notice step of the system is the observed notice, published at the notice's time. -/
  noteBind : ∀ n i nt, n < N → acts i = .notice n nt → O.note n i = some (nt.time + 1)
  /-- A consumed head-bearing reply belongs to a completed sampled batch and the reply's own
  call. -/
  replyBind : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ i r, k ≤ i →
    r ∈ (run i).reps → r ∉ (run (i + 1)).reps → r.node < N →
    (∃ s, r.ans = .fetched s ∨ r.ans = .head s) →
    ∃ p t id a, O.doneAt r.node (O.sched r.node p) = i ∧ O.sched r.node p ≤ t ∧
      O.own r.node t = some (id, a) ∧ O.callAt r.node id ≤ r.time
  /-- A fresh reply at a sample was consumed within its batch, by a call made at the sample. -/
  freshOwn : ∀ n t, n < N → O.reply n t = .fresh → ∃ u id a, t ≤ u ∧ u ≤ O.doneAt n t ∧
    O.own n u = some (id, a) ∧ O.callAt n id = t
  /-- The system's known pair at `t` is the observed pair at the latch time. -/
  latchKnown : ∀ n t, n < N →
    Recovery.HubSys.known (run t) n = ⟨O.seq n (O.latch n t), O.known n (O.latch n t)⟩
  /-- The latch time is no later than `t`. -/
  latchLe : ∀ n t, n < N → O.latch n t ≤ t
  /-- The latch time is monotone. -/
  latchMono : ∀ n t t', n < N → t ≤ t' → O.latch n t ≤ O.latch n t'
  /-- At a sample, the latch is the sample time. -/
  latchAtSample : ∀ n p, n < N → O.latch n (O.sched n p) = O.sched n p

/-- Two laws of the hub. `answer`: each push is eventually handled, one request at a time, with
the effect of that same immutable packet and its checks; it combines native correspondence with
an eventual-handling assumption. `climbs`: from the record cut the hub's every step climbs raw
ancestry. That the hub stays fixed through the handling is derived after stabilization. -/
structure HubHandling (N : Nat) (run : Nat → Sys) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (O : HiveObs ρ α) : Prop where
  /-- A push at `t` is answered at or after `t`, and the answer moves the hub as
  `RawPublish.after` does for its packet and checks. -/
  answer : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n t, n < N → k ≤ t →
    O.pushes n t →
    t ≤ O.answerAt n t ∧
    (⟨(run (O.answerAt n t + 1)).hub.seq, (run (O.answerAt n t + 1)).hub.head⟩ :
        RawPublish.Hub) =
      RawPublish.after ⟨(run (O.answerAt n t)).hub.seq, (run (O.answerAt n t)).hub.head⟩
        (O.pkt n t) (O.checks n t)
  /-- The raw-ancestry hub law of `HubLaw`, read from the record cut `k`: the hub's head exists
  there, the raw graph only grows, and each step leaves the hub as it is or accepts, moving to
  the next sequence number and a different existing head that has the old head in its raw
  ancestry (`HubClimb`). Natively it holds when no new drop is taken, which `CutAt` ensures by
  fixing the records and drops, and the hub's head at `k` survives the hub's records. The second
  condition is not derived: a hub rollback may leave the head dropped by records the hub keeps,
  and a push can then be accepted by contracted ancestry without a new drop, off raw ancestry.
  It is what native checking must cover. The earlier `historyWindow` premise assumed the same
  chain over the same interval, so the trust is no wider. The `RawGrow` clause rests on
  `QuietAt.noLoss`. -/
  climbs : ∀ k, CutAt N recs adopts fails k → QuietAt N O k →
    (run k).hub.head < (run k).next ∧
    ∀ i, k ≤ i → RawGrow (run i) (run (i + 1)) ∧ HubClimb (run i) (run (i + 1))

end Source

/-- The native obligations of one hive execution. Grouping preserves their individual fields:
record effects, environment, transport, knowledge, entry, scheduling, system bindings and hub
handling. Every sampled view comes from the same `HiveObs`.

`hive_converges` takes the fine-system refinement as a separate premise, for the point where
nodes have entered and completed an active sample, past the old-effects cut.
`FineAssembly.hive_converges_observed` derives it from native event replay. Fairness within
that system (`fair`, `pushFair`) is a premise of `FineAssembly.FineSource`, which
`hive_converges_observed` asks of every fine cut. Termination of automatic writes is the premise
`autoWritesStop` in `Source.Environment`. -/
structure HiveContracts {ρ α : Type} [DecidableEq ρ] (N : Nat) (run : Nat → Sys)
    (acts : Nat → Act) (recs : Nat → Exec.SEState) (B : Nat)
    (epoch : Nat → Nat → Retry.Records.State) (adopts fails : Nat → Nat → Bool)
    (recLabel : Nat → Nat) (Rof : Nat → ρ) (wOf : Nat → Nat) (O : HiveObs ρ α) : Prop
    extends Source.RecordEffects N recs B epoch adopts fails recLabel O,
      Source.Environment N O.toEnvironment, Source.Transport N O.toTransport, Source.Knowledge N run O,
      Source.Entry N run recs adopts fails Rof wOf O,
      Source.Scheduling N recs adopts fails O,
      Source.SystemBindings N run acts recs adopts fails O,
      Source.HubHandling N run recs adopts fails O

end Musubi.SysAcceptance

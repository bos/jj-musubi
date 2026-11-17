/-
Source, completion and scheduling contracts of one actual hive run. Each group owns one kind
of obligation; `HiveContracts` assembles them without adding a premise.

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
Append, prune and custody laws hold from the start. `epochStep` is asked only after records
and drops are fixed and old replies and notifications have stopped taking effect; an old
`Fetched` may still announce old records before that cut. -/
structure RecordEffects (N : Nat) (recs : Nat → Exec.SEState) (B : Nat)
    (epoch : Nat → Nat → Retry.Records.State) (adopts fails : Nat → Nat → Bool)
    (recLabel : Nat → Nat) (O : HiveObs ρ α) : Prop where
  recStep : ∀ i, (recs (i + 1)).recs = (recs i).recs ∨
    ∃ D, (recs (i + 1)).recs = (recs i).takeRecs D
  prune : ∀ i, (recs i).pruned ≤ (recs (i + 1)).pruned
  pruneLe : ∀ i, (recs i).pruned ≤ (recs i).recs.length
  dropsGrow : ∀ i n, n < N → ∀ x, x ∈ (recs i).nodeDF n → x ∈ (recs (i + 1)).nodeDF n
  hubBound : ∀ i x, x ∈ (recs i).hubDL → x < B
  nodeBound : ∀ i n, n < N → ∀ x, x ∈ (recs i).nodeDF n → x < B
  epochStep : ∀ kR k, RecordsFixedFrom N recs kR → kR ≤ k → OldGone N O kR k → ∀ n, n < N →
    ∀ i, k ≤ i →
    Retry.Records.Step (recLabel kR) (epoch n i) (epoch n (i + 1)) (adopts n i) (fails n i)

/-- Environment assumptions and object-credit effects. Failures, losses, user work and automatic
semantic writes eventually stop. Automatic-write termination is an assumption, including
housekeeping, prelude, inline cleanup, passed-on abandon and late reparenting.

A missing-object reply consumes the node's credit and begins recovery. Keeping that credit
otherwise implies that missing-object failures eventually stop; that cutoff is derived. -/
structure Environment (N : Nat) (O : Observation.Environment) : Prop where
  envFinal : ∃ kE, ∀ t, kE ≤ t → ¬ O.lost t
  readyKeep : ∀ n t, n < N → ¬ O.lost t → O.objReady n t = true → O.objReady n (t + 1) = true
  readyFail : ∀ n t, n < N → ¬ O.lost t → O.objFail n t →
    O.objReady n t = false ∧ O.objReady n (t + 1) = true
  failFinal : ∃ kF, ∀ t, kF ≤ t → ¬ O.ioFail t
  /-- Termination of native automatic writes remains unproved. -/
  autoWritesStop : ∀ n, n < N → ∃ kA, ∀ t, kA ≤ t → ¬ O.autoWrite n t
  userFinal : ∃ kU, ∀ t, kU ≤ t → ∀ n, n < N → ¬ O.userWork n t

/-- Finite old effects. Replies consume live call slots or reopens retire them; the shared id
counter is never reset. Notices have a separate finite in-flight and queued lifetime, including
across reconnects. These laws do not require fair draining of old traffic. -/
structure Transport (N : Nat) (O : Observation.Transport) : Prop where
  inboxStep : ∀ c n t, n < N →
    ∃ b, Retry.InboxStep c (O.inbox n t) (O.inbox n (t + 1)) b ∧
      ∀ id a, O.own n t = some (id, a) → id < c → b = true
  callIds : ∀ n t u id a, n < N → O.own n u = some (id, a) → (O.inbox n t).next ≤ id →
    t ≤ O.callAt n id
  notesOld : ∀ c n t, n < N → c ≤ t → ∃ h, Retry.Notifications.Step (O.oldNotes c n t)
    (O.oldNotes c n (t + 1)) h ∧ ∀ a, O.note n t = some a → a < c → h = true

/-- Native knowledge and history effects. An own reply names a hub state between call and
handling; a notice names a state no later than handling. Both use `handleHead`, and nothing
else changes the known pair without reopening. Sequence monotonicity and history bindings
are conditional on loss having stopped, not on the hub already being stable. -/
structure Knowledge (N : Nat) (run : Nat → Sys) (O : HiveObs ρ α) : Prop where
  ownHead : ∀ n t id a, n < N → ¬ O.reopen n t → O.own n t = some (id, a) →
    O.callAt n id ≤ a ∧ a ≤ t ∧
    (O.seq n (t + 1), O.known n (t + 1)) = Retry.Serial.handleHead O.root true false
      (O.seq n t, O.known n t) ((run a).hub.seq, (run a).hub.head)
  noteHead : ∀ n t a, n < N → ¬ O.reopen n t → O.note n t = some a →
    a ≤ t ∧ (O.seq n (t + 1), O.known n (t + 1)) = Retry.Serial.handleHead O.root false true
      (O.seq n t, O.known n t) ((run a).hub.seq, (run a).hub.head)
  quietKnown : ∀ n t, n < N → ¬ O.reopen n t → O.own n t = none → O.note n t = none →
    (O.seq n (t + 1), O.known n (t + 1)) = (O.seq n t, O.known n t)
  rootSeq : ∀ a, (run a).hub.seq = 0 → (run a).hub.head = O.root
  hubSeqStep : ∀ t, ¬ O.lost t → (run t).hub.seq ≤ (run (t + 1)).hub.seq
  histBind : ∀ a, (∀ s, a ≤ s → ¬ O.lost s) → O.hist ((run a).hub.seq) = (run a).hub.head

/-- Local source laws scoped to their phase. Entry laws read each actual sampled event through
its completed batch, then frame that result to the next post-prelude reading. Their object
and restart laws include completion assumptions.

Past the cut, a reopen follows `Incomplete` or an unrecovered missing-object reply. An entered
push from the hub head is closed, and entry persists otherwise. Once the hub stays and a node
knows it, `pending` supplies that node's own frozen-round laws for samples past the cut; `PendingLaws.absurd` later rules
out ineligibility. No field assumes entry, an end to recovering reopens, or eligibility. -/
structure Entry [DecidableEq ρ] (N : Nat) (run : Nat → Sys) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (Rof : Nat → ρ) (wOf : Nat → Nat) (O : HiveObs ρ α) : Prop where
  entry : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n, n < N → ∀ p,
    k ≤ O.sched n p → EntryLaws (Rof k) (wOf k) (O.entryData n p)
  reopenWhy : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    O.reopen n i → O.incomplete n i = true ∨
      ∃ t, t ≤ i ∧ O.objFail n t ∧ ∀ s, t < s → s < i → ¬ O.reopen n s
  incHead : ∀ k, CutAt N recs adopts fails k → ∀ n i, n < N → k ≤ i →
    O.incomplete n i = true → O.expectedIsHead n i = true ∧ O.closed n i = false
  closure : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    RawEntry (Rof k) (wOf k) (O.rawAt n i) → O.expectedIsHead n i = true →
    O.closed n i = true
  keep : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    RawEntry (Rof k) (wOf k) (O.rawAt n i) → ¬ O.reopen n i →
    RawEntry (Rof k) (wOf k) (O.rawAt n (i + 1))
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
activity alone does not assert that the sampled event is a core step. -/
structure Scheduling (N : Nat) (recs : Nat → Exec.SEState) (adopts fails : Nat → Nat → Bool)
    (O : HiveObs ρ α) : Prop where
  schedMono : ∀ n p, O.sched n p < O.sched n (p + 1)
  doneIn : ∀ n p, n < N → O.sched n p ≤ O.doneAt n (O.sched n p) ∧
    O.doneAt n (O.sched n p) + 1 < O.sched n (p + 1)
  idleStart : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n p, n < N →
    k ≤ O.sched n p → O.active n (O.sched n p) = false → ∃ q, p ≤ q ∧ O.starts n (O.sched n q)
  startActive : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n q, n < N →
    k ≤ O.sched n q → O.starts n (O.sched n q) → O.active n (O.sched n (q + 1)) = true

/-- Correspondence between native observations and the fine system. Its clock is hive time;
maintenance and notifications name the actual native effects. A consumed head-bearing reply
belongs to the completed sampled batch and its own call. The system holds the last completed
or post-prelude snapshot, through the latch laws. -/
structure SystemBindings (N : Nat) (run : Nat → Sys) (acts : Nat → Act) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (O : HiveObs ρ α) : Prop where
  clock : ∀ i, (run i).time = i
  maintBind : ∀ n i, n < N → acts i = .core n .maint → O.autoWrite n i
  noteBind : ∀ n i nt, n < N → acts i = .notice n nt → O.note n i = some (nt.time + 1)
  replyBind : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ i r, k ≤ i →
    r ∈ (run i).reps → r ∉ (run (i + 1)).reps → r.node < N →
    (∃ s, r.ans = .fetched s ∨ r.ans = .head s) →
    ∃ p t id a, O.doneAt r.node (O.sched r.node p) = i ∧ O.sched r.node p ≤ t ∧
      O.own r.node t = some (id, a) ∧ O.callAt r.node id ≤ r.time
  freshOwn : ∀ n t, n < N → O.reply n t = .fresh → ∃ u id a, t ≤ u ∧ u ≤ O.doneAt n t ∧
    O.own n u = some (id, a) ∧ O.callAt n id = t
  latchKnown : ∀ n t, n < N →
    Recovery.HubSys.known (run t) n = (O.seq n (O.latch n t), O.known n (O.latch n t))
  latchLe : ∀ n t, n < N → O.latch n t ≤ t
  latchMono : ∀ n t t', n < N → t ≤ t' → O.latch n t ≤ O.latch n t'
  latchAtSample : ∀ n p, n < N → O.latch n (O.sched n p) = O.sched n p

/-- A push is eventually handled, one request at a time, with the effect of that same immutable
packet and its checks. This combines native correspondence with an eventual-handling
assumption. The hub staying fixed through the handling is derived only after stabilization. -/
structure HubHandling (N : Nat) (run : Nat → Sys) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (O : HiveObs ρ α) : Prop where
  answer : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n t, n < N → k ≤ t →
    O.pushes n t →
    t ≤ O.answerAt n t ∧
    (⟨(run (O.answerAt n t + 1)).hub.seq, (run (O.answerAt n t + 1)).hub.head⟩ :
        RawPublish.Hub) =
      RawPublish.after ⟨(run (O.answerAt n t)).hub.seq, (run (O.answerAt n t)).hub.head⟩
        (O.pkt n t) (O.checks n t)

end Source

/-- The native obligations of one hive execution. Grouping preserves their individual fields:
record effects, environment, transport, knowledge, entry, scheduling, system bindings and hub
handling. Every sampled view comes from the same `HiveObs`.

The fine-system refinement is supplied separately to `hive_converges`, once nodes have entered
and completed an active sample, past the old-effects cut. `FineAssembly.hive_converges_observed`
derives that interface from native event replay. Fairness within that system remains explicit
in `FineAt`. Automatic-write termination is the explicit premise in `Source.Environment`. -/
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

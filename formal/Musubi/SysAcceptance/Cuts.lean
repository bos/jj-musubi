/-
The phase boundaries of hive convergence. Record cuts and quiet suffixes are derived by
`Convergence`; the source contracts take them only to scope the laws of each phase.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance.Observations

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSys

/-- The records and every node's dropped originals stay as they are from `k`. -/
def RecordsFixedFrom (N : Nat) (recs : Nat → Exec.SEState) (k : Nat) : Prop :=
  ∀ i, k ≤ i → ((recs i).recs, (recs i).pruned) = ((recs k).recs, (recs k).pruned) ∧
    ∀ n, n < N → ∀ x, x ∈ (recs i).nodeDF n ↔ x ∈ (recs k).nodeDF n

/-- The cut: records and drops fixed, and no node adopts or fails for a stale plan, from `k`. -/
structure CutAt (N : Nat) (recs : Nat → Exec.SEState) (adopts fails : Nat → Nat → Bool)
    (k : Nat) : Prop where
  records : RecordsFixedFrom N recs k
  control : ∀ n, n < N → ∀ i, k ≤ i → adopts n i = false ∧ fails n i = false

/-- A node is eligible at the cut `k`: it drops exactly what the hub's records drop. -/
def EligibleAt (N : Nat) (recs : Nat → Exec.SEState) (k : Nat) (n : Nat) : Prop :=
  n < N ∧ Exec.seteq ((recs k).nodeDF n) (recs k).hubDL = true

instance (N : Nat) (recs : Nat → Exec.SEState) (k : Nat) :
    DecidablePred (EligibleAt N recs k) := fun n => by
  unfold EligibleAt; infer_instance

/-- From `k` on the environment is quiet and loses nothing, so no per-cut law faces a hub
regression. Each field covers one kind of event:
* `noIOFailure`: no ordinary I/O or transport failure.
* `noAutomaticWrite`: no node's own code makes an automatic write (`autoWrite`: idle
  housekeeping, the prelude's, `advance_to`'s cleanup, a `jj op abandon` passed on, a late
  reparenting).
* `noUserWork`: no user works in a node's repository.
* `noObjectFailure`: no `GetObjects` reply lacks what it asked for, so no batch fails on one.
* `noLoss`: the environment loses nothing (`lost`: no hub remade, no hub losing objects, no
  node's own gc, no cached have that has stopped being true). -/
structure QuietAt {ρ α : Type} (N : Nat) (O : HiveObs ρ α) (k : Nat) : Prop where
  noIOFailure : ∀ t, k ≤ t → ¬ O.ioFail t
  noAutomaticWrite : ∀ n, n < N → ∀ t, k ≤ t → ¬ O.autoWrite n t
  noUserWork : ∀ n, n < N → ∀ t, k ≤ t → ¬ O.userWork n t
  noObjectFailure : ∀ n, n < N → ∀ t, k ≤ t → ¬ O.objFail n t
  noLoss : ∀ t, k ≤ t → ¬ O.lost t

/-- From `k` on, no node handles an own head-bearing reply to a call it made before hive time
`c`, nor a notice published before `c`. -/
def OldGone {ρ α : Type} (N : Nat) (O : HiveObs ρ α) (c k : Nat) : Prop :=
  ∀ n, n < N → ∀ t, k ≤ t → (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
    ∀ a, O.note n t = some a → c ≤ a

/-- Node `n`'s known pair at `i` is one the hub had at a hive time from `k` on, by `i`. -/
def KnownTrue {ρ α : Type} (run : Nat → Sys) (O : HiveObs ρ α) (k n i : Nat) : Prop :=
  ∃ a, k ≤ a ∧ a ≤ i ∧ (⟨O.seq n i, O.known n i⟩ : Known) = ⟨(run a).hub.seq, (run a).hub.head⟩

/-- A record/control cut holds at every later time, with the frozen snapshot rebased to it. -/
theorem CutAt.mono {N : Nat} {recs : Nat → Exec.SEState}
    {adopts fails : Nat → Nat → Bool} {k later : Nat}
    (cut : CutAt N recs adopts fails k) (afterCut : k ≤ later) :
    CutAt N recs adopts fails later where
  records := by
    intro i hi
    obtain ⟨records, drops⟩ := cut.records i (by omega)
    obtain ⟨atLater, dropsAtLater⟩ := cut.records later afterCut
    exact ⟨records.trans atLater.symm,
      fun n hn x => (drops n hn x).trans (dropsAtLater n hn x).symm⟩
  control := fun n hn i hi => cut.control n hn i (by omega)

/-- At the entry phase, records are fixed, the environment is quiet, and only `Incomplete`
can reopen a node. Recovering reopens have spent their last object-failure credit. -/
structure EntryPhase {ρ α : Type} (N : Nat) (recs : Nat → Exec.SEState)
    (adopts fails : Nat → Nat → Bool) (O : HiveObs ρ α) (time : Nat) : Prop where
  cut : CutAt N recs adopts fails time
  quiet : QuietAt N O time
  reopenIncomplete : ∀ n, n < N → ∀ i, time ≤ i →
    O.reopen n i → O.incomplete n i = true

/-- Every node has entered and stays entered. Its closed push rules out the only reason left
for reopening. `recordCut` identifies the frozen records; `cut` starts this suffix. -/
structure EnteredPhase {ρ α : Type} (N : Nat) (Rof : Nat → ρ) (wOf : Nat → Nat)
    (O : HiveObs ρ α) (recordCut cut : Nat) : Prop where
  afterRecord : recordCut ≤ cut
  entry : ∀ n, n < N → ∀ i, cut ≤ i →
    EarlyEntry.Control.RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n i)
  noReopen : ∀ n, n < N → ∀ i, cut ≤ i → ¬ O.reopen n i

/-- The observed boundary supplied to native replay: every node is entered and has completed
an active sample after old effects stopped. The snapshot correspondence laws are in
`FineSnapshot`; activity alone identifies no core event and proves no normalized heads. -/
structure FineCut {ρ α : Type} (N : Nat) (Rof : Nat → ρ) (wOf : Nat → Nat)
    (O : HiveObs ρ α) (recordCut cut : Nat) : Prop where
  afterRecord : recordCut ≤ cut
  entry : ∀ n, n < N → ∀ i, cut ≤ i →
    EarlyEntry.Control.RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n i)
  completed : ∃ oldCut, OldGone N O recordCut oldCut ∧ ∀ n, n < N → ∃ q,
    oldCut ≤ O.sched n q ∧ O.doneAt n (O.sched n q) < cut ∧
    O.active n (O.sched n q) = true ∧ ∀ i, O.sched n q ≤ i →
      EarlyEntry.Control.RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n i)

end Musubi.SysAcceptance

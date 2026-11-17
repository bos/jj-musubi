/-
Assemble fine-system convergence from the replay of actual native events. `FineSource.steps`
derives system steps, and the honesty invariant supplies truthful replies and notifications.
Each removed push is tied to its own decision event; maintenance is excluded after the cut.

The primitive boundaries have separate owners:
- `HiveContracts`: grouped source effects, environment, completion and scheduling obligations.
- `FineStart`: the starting snapshot shared by `FineAt` and `FineSource`.
- `FineSource`: event replay and bindings, graph acyclicity, native advance, lawful decisions
  and fine-system fairness.
- `hive_converges_observed`: native record identity and custody (`views`), the hub's records
  at the cut (`hubRecs`), and their change only with native records or pruning (`hubRecsStep`).

Entry, old-effect cutoffs and stabilization are derived. Eventual handling and restarts are
source obligations, as is the termination of automatic native writes (`autoWritesStop`).

The convergence proof uses this file.
-/
import Musubi.FineAssembly.Honesty

namespace Musubi.FineAssembly

open Musubi NodeSettle NodeSys NodeSysEntry SysAcceptance NativeEvents Recovery.HubSys
  Recovery.HubNodeSteps

/-! ## The fine system, assembled -/

/-- Native replay and its laws at the fine cut. `FineStart` owns the initial snapshot;
`inFlight` supplies honesty of the eligible nodes' replies and notifications already in flight
from `t0`.

The remaining obligations have distinct sources:
* `events`, `replay`, `replayActs` and `binds` describe the same observed execution;
* `parentsFirst` is the native graph contract;
* `advance` describes a native full-frontier advance whose cleanup makes no automatic write;
* `pushDecisions` binds each immutable packet to its own lawful handling event;
* `fair` and `pushFair` state scheduling and completion assumptions.

`fineAt_of` derives the fine steps, preserved honesty and maintenance laws. The hive assembly
supplies its quietness, fixed records, empty pending drops and old-effect cutoff. -/
structure FineSource (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    [DecidablePred E] (run : Nat → Sys) (acts : Nat → Act) (k w : Nat) (initial : Nat → Nat)
    (t0 : Nat) (auto : Nat → Nat → Prop)
    extends FineStart D law E run k w initial where
  /-- Node count used by the executable packet-decision model. -/
  decisionNodes : Nat
  decodeRecords : Nat → List Exec.Rec
  events : Nat → Event
  replay : ∀ i, run (k + i) = observedRun N law (run k) events i
  replayActs : ∀ i, acts (k + i) = (events i).act
  binds : ∀ i, (events i).Binds N D law E (run k).reqs (run (k + i))
  inFlight : InFlightHonest E w t0 initial (run k)
  parentsFirst : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x
  advance : ∀ i, k ≤ i → ∀ n, E n → acts i = .core n .busy → ¬ auto n i →
    AdvGuard ((run i).node n).ns → FullAdv ((run i).node n).ns ((run (i + 1)).node n).ns
  pushDecisions : ∀ j q P c, events j = .push q P c →
    Nonempty (LawfulDecision decisionNodes decodeRecords (run (k + j)) (run (k + j + 1)) P)
  fair : ∀ n, E n → ∃ kf, Fair (fun j => run (k + j)) (fun j => acts (k + j)) n kf
  pushFair : ∀ n, E n → PushFair (fun j => run (k + j)) (fun j => acts (k + j)) n 0

/-- The replay's steps, read on the actual run. -/
theorem FineSource.steps {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {run : Nat → Sys} {acts : Nat → Act} {k w : Nat}
    {initial : Nat → Nat} {t0 : Nat} {auto : Nat → Nat → Prop}
    (S : FineSource N D law E run acts k w initial t0 auto) :
    ∀ j, HiveStep N D law E (run k).reqs (acts (k + j)) (run (k + j)) (run (k + j + 1)) := by
  have h0 := runOK_filt_init (E := E) (old := (run k).reqs) S.nodes S.system S.time S.objectReplies
    S.rootBound S.rootParents
  have hb : ∀ i, (S.events i).Binds N D law E (run k).reqs
      (observedRun N law (run k) S.events i) := fun i => S.replay i ▸ S.binds i
  intro j
  rw [S.replayActs j, S.replay j, show k + j + 1 = k + (j + 1) from rfl, S.replay (j + 1)]
  exact observed_hs (run k) S.events (fun _ => dummy S.rawRoot) h0 hb j

/-- The fine system's premises, from the replay and the laws `FineSource` names. Assumes, from
the cut on:
* no eligible node makes an automatic write (`hnoAuto`), so each advance's cleanup writes
  nothing;
* the hub's records stay (`hr`);
* no eligible node has pending drops (`pending`), adopts (`applied`) or does housekeeping
  (`hm`);
* the clock is at least `t0` at the cut (`time`);
* an eligible node takes only head-bearing replies answered from `t0` on, and only
  notifications naming a state from `t0` on (`takes`, `notes`). -/
def fineAt_of {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {run : Nat → Sys} {acts : Nat → Act} {k w : Nat}
    {initial : Nat → Nat} {t0 : Nat} {auto : Nat → Nat → Prop}
    (S : FineSource N D law E run acts k w initial t0 auto)
    (hnoAuto : ∀ i, k ≤ i → ∀ n, E n → ¬ auto n i) (time : t0 ≤ (run k).time)
    (hr : ∀ i, k ≤ i → (run i).hub.recs = (run k).hub.recs)
    (pending : ∀ i, k ≤ i → ∀ n, E n → ((run i).node n).ns.pending = [])
    (applied : ∀ i, k ≤ i → ∀ n, E n → ((run (i + 1)).node n).ns.ap = ((run i).node n).ns.ap)
    (hm : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint)
    (takes : ∀ i, k ≤ i → ∀ r ∈ (run i).reps, r ∉ (run (i + 1)).reps → E r.node →
      (∃ s, r.ans = .fetched s ∨ r.ans = .head s) → t0 ≤ r.time)
    (notes : ∀ i, k ≤ i → ∀ n nt, acts i = .notice n nt → E n → t0 ≤ nt.time + 1) :
    FineAt N D law E run acts k w initial := by
  have hsteps := S.steps
  have honest := honest_run (fun j => run (k + j)) (fun j => acts (k + j)) initial hsteps
    (S.inFlight.honest S.historyWindow.window S.historyWindow.histHead time)
  refine {
    toFineStart := S.toFineStart
    decisionNodes := S.decisionNodes
    decodeRecords := S.decodeRecords
    steps := ?_
    parentsFirst := S.parentsFirst
    nodeLaws := ?_
    noMaintenance := hm
    recordsFixed := hr
    fair := S.fair
    pushFair := S.pushFair
    pushDecisions := ?_
  }
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    exact hsteps j
  · intro i
    refine {
      pending := fun n hE => pending (k + i) (by omega) n hE
      applied := fun n hE _ => applied (k + i) (by omega) n hE
      advance := fun n hE ha hg =>
        S.advance (k + i) (by omega) n hE ha (hnoAuto (k + i) (by omega) n hE) hg
      maintain := fun n hE ha => absurd ha (hm (k + i) (by omega) n hE)
      replies := ?_
      notices := ?_
    }
    · intro n hE r hr hr' hn s hs
      have hEr : E r.node := hn ▸ hE
      exact (honest i).reps r hr hEr (takes (k + i) (by omega) r hr hr' hEr ⟨s, hs⟩) s hs
    · intro n hE nt ha
      obtain ⟨hin, hnn⟩ := notice_mem (ha ▸ hsteps i)
      exact (honest i).notes nt hin (hnn ▸ hE) (notes (k + i) (by omega) n nt ha hE)
  · -- every removed push is its decision event's (`observed_decisions`)
    intro n hE j q hq hq' hn P hP
    have hb : ∀ i, (S.events i).Binds N D law E (run k).reqs
        (observedRun N law (run k) S.events i) := fun i => S.replay i ▸ S.binds i
    have hd : ∀ i q P c, S.events i = .push q P c →
        Nonempty (LawfulDecision S.decisionNodes S.decodeRecords
          (observedRun N law (run k) S.events i) (observedRun N law (run k) S.events (i + 1)) P) := by
      intro i q P c he
      rw [← S.replay i, ← S.replay (i + 1)]
      exact S.pushDecisions i q P c he
    have h := observed_decisions (run k) S.events S.decisionNodes S.decodeRecords hb hd n hE j q
      (by rw [← S.replay j]; exact hq) (by rw [← S.replay (j + 1)]; exact hq') hn P hP
    rw [S.replay j, show k + j + 1 = k + (j + 1) from rfl, S.replay (j + 1)]
    exact h

open Musubi.EarlyEntry.Control in
/-- Convergence from observed native events. At the derived `FineCut`, the replay supplies
`FineSource`; assembly derives the remaining `FineAt` laws:

* quietness excludes maintenance and advance cleanup writes;
* the completed active sample and old-effects cutoff exclude stale replies and notifications;
* native record identity and custody give empty pending drops and unchanged applied records;
* fixed native records keep the fine system's hub records fixed.

The replay, native correspondence and fairness obligations remain explicit premises. -/
theorem hive_converges_observed {ρ α : Type} [DecidableEq ρ] {N : Nat}
    {D : Nat → Nat → Nat → Prop} {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act}
    {recs : Nat → Exec.SEState} {B : Nat} {epoch : Nat → Nat → Retry.Records.State}
    {adopts fails : Nat → Nat → Bool} {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat}
    {O : HiveObs ρ α}
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    (label : ρ → Nat) (decodeR : Nat → List Exec.Rec) (origin : Nat → Nat → Nat → Nat)
    (views : ∀ recordCut, CutAt N recs adopts fails recordCut →
      RecordView N recordCut run recs O label decodeR origin)
    (hubRecs : ∀ recordCut, CutAt N recs adopts fails recordCut →
      (recs recordCut).recs = decodeR (label (Rof recordCut)))
    (hubRecsStep : ∀ recordCut, CutAt N recs adopts fails recordCut → QuietAt N O recordCut →
      ∀ i, recordCut ≤ i →
      (run (i + 1)).hub.recs = (run i).hub.recs ∨
        ((recs (i + 1)).recs, (recs (i + 1)).pruned) ≠ ((recs i).recs, (recs i).pruned))
    (fine : ∀ recordCut cut, CutAt N recs adopts fails recordCut → QuietAt N O recordCut →
      FineCut N Rof wOf O recordCut cut →
      FineSource N D law (EligibleAt N recs recordCut) run acts cut
        (run recordCut).hub.seq O.hist recordCut O.autoWrite) :
    Converges D (fun n => n < N) run := by
  refine hive_converges (D := D) (law := law) C fun recordCut fineCut cutLaws quiet boundary => ?_
  have afterRecord := boundary.afterRecord
  have entry := boundary.entry
  obtain ⟨oldCut, oldGone, completed⟩ := boundary.completed
  -- no eligible node does housekeeping from the cut, an automatic write
  have hm : ∀ i, fineCut ≤ i → ∀ n, EligibleAt N recs recordCut n → acts i ≠ .core n .maint :=
    fun i hi n hE ha => quiet.noAutomaticWrite n hE.1 i (by omega) (C.maintBind n i hE.1 ha)
  -- no automatic write from the cut, inline cleanup and prelude writes included
  have hnoAuto : ∀ i, fineCut ≤ i → ∀ n, EligibleAt N recs recordCut n → ¬ O.autoWrite n i :=
    fun i hi n hE => quiet.noAutomaticWrite n hE.1 i (by omega)
  -- the old-effects cut is before each node's completed event, so before `fineCut`
  have oldCutBefore : ∀ n, n < N → oldCut < fineCut := by
    intro n hn
    obtain ⟨q, h1, h2, -⟩ := completed n hn
    have := (C.doneIn n q hn).1
    omega
  have notes : ∀ i, fineCut ≤ i → ∀ n nt, acts i = .notice n nt → EligibleAt N recs recordCut n →
      recordCut ≤ nt.time + 1 := by
    intro i hi n nt ha hE
    exact (oldGone n hE.1 i (by have := oldCutBefore n hE.1; omega)).2 _ (C.noteBind n i nt hE.1 ha)
  have takes : ∀ i, fineCut ≤ i → ∀ r ∈ (run i).reps, r ∉ (run (i + 1)).reps →
      EligibleAt N recs recordCut r.node → (∃ s, r.ans = .fetched s ∨ r.ans = .head s) →
      recordCut ≤ r.time := by
    intro i hi r hr hr' hE hhd
    obtain ⟨p, t, id, a, hdone, hpt, hown, hcall⟩ :=
      C.replyBind recordCut cutLaws quiet i r (by omega) hr hr' hE.1 hhd
    obtain ⟨q, hGq, beforeFine, -, -⟩ := completed r.node hE.1
    have hlt : O.sched r.node q < O.sched r.node p :=
      Schedule.before_of_done_before (C.schedMono r.node) (fun p => C.doneIn r.node p hE.1) (by omega)
    exact Nat.le_trans ((oldGone r.node hE.1 t (by omega)).1 id a hown) hcall
  -- the hub's records stay: each step past the cut keeps them, the native records being fixed
  have hstep : ∀ i, recordCut ≤ i → (run (i + 1)).hub.recs = (run i).hub.recs := by
    intro i hi
    refine (hubRecsStep recordCut cutLaws quiet i hi).resolve_right fun hne => hne ?_
    rw [(cutLaws.records (i + 1) (by omega)).1, (cutLaws.records i hi).1]
  have hr : ∀ i, fineCut ≤ i → (run i).hub.recs = (run fineCut).hub.recs := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction d with
    | zero => rfl
    | succ d ih => rw [← Nat.add_assoc, hstep _ (by omega), ih (by omega)]
  -- no pending drops and no adoption, through the native records' view
  have V := (views recordCut cutLaws).mono afterRecord
  have pending := V.pending_empty afterRecord cutLaws.records (hubRecs recordCut cutLaws) entry
  have applied := V.applied_stays entry
  exact ⟨fineAt_of (fine recordCut fineCut cutLaws quiet boundary) hnoAuto
    (by rw [C.clock fineCut]; exact afterRecord) hr
    (fun i hi n hE => pending n hE i hi) (fun i hi n hE => applied n hE.1 i hi) hm takes notes⟩

end Musubi.FineAssembly

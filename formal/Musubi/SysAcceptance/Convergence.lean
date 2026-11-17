/-
Convergence of the actual hive run, composed from the derived phases. The fine-system
interface is a premise at the native boundary; `FineAssembly` builds it from event replay.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance.Phases

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.NodeSys Musubi.NodeSysEntry

/-- Every node of the hive settles at the same raw head on the loss-free suffix of the run.

The proof: records and recovery settle, every node enters and completes an active sample, and
the eligible system stabilizes the hub. The native pending laws then rule out ineligible nodes.

Assumptions:
* `C : HiveContracts`: the source, completion and scheduling contracts, including fairness and
  termination of automatic writes.
* `fine`: the eligible-system interface at the derived fine cut, separate from `HiveContracts`;
  `FineAssembly.hive_converges_observed` constructs it from native replay. -/
theorem hive_converges {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    (fine : ∀ recordCut cut, CutAt N recs adopts fails recordCut → QuietAt N O recordCut →
      FineCut N Rof wOf O recordCut cut →
      Nonempty (FineAt N D law (EligibleAt N recs recordCut) run acts cut
        (run recordCut).hub.seq O.hist)) :
    Converges D (fun n => n < N) run := by
  obtain ⟨recordCut, phase⟩ := entry_phase C
  obtain ⟨entryCut, entered⟩ := entered_phase C phase
  obtain ⟨fineCut, boundary, truthful⟩ := fine_cut C phase entered
  obtain ⟨system⟩ := fine recordCut fineCut phase.cut phase.quiet boundary
  have honest := honest_latched_known C phase.quiet truthful
  obtain ⟨K, cut, ordered, stable, settled⟩ := system.converges honest (fun n h => h.1)
  have eligible := all_eligible C phase entered stable
  unfold Converges
  exact ⟨K, cut, ordered, stable, fun n hn => settled n (eligible n hn)⟩

end Musubi.SysAcceptance

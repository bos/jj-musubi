/-
Convergence of the actual hive run, composed from the derived phases. The fine-system
interface is supplied at the native boundary; `FineAssembly` builds it from event replay.
-/
import Musubi.SysAcceptance.Phases

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.NodeSys Musubi.NodeSysEntry

/-- The hive converges on its loss-free suffix. Records and recovery settle, every node enters
and completes an active sample, and the eligible system stabilizes the hub. The native pending
laws then rule out ineligible nodes, so every node settles at the same raw head.

`fine` supplies the eligible-system interface at the derived fine cut. It remains separate
from `HiveContracts`; `FineAssembly.hive_converges_observed` constructs it from native replay.
Completion, fairness and automatic-write termination remain explicit source obligations. -/
theorem hive_converges {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    (fine : ∀ recordCut cut, CutAt N recs adopts fails recordCut → QuietAt N O recordCut →
      FineCut N Rof wOf O recordCut cut →
      Nonempty (FineAt N D law (EligibleAt N recs recordCut) run acts cut
        (run recordCut).hub.seq O.hist)) :
    ∃ K cut, K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, n < N → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, Recovery.HubSys.heads (run i) n x ↔ x = (run K).hub.head := by
  obtain ⟨recordCut, phase⟩ := entry_phase C
  obtain ⟨entryCut, entered⟩ := entered_phase C phase
  obtain ⟨fineCut, boundary, truthful⟩ := fine_cut C phase entered
  obtain ⟨system⟩ := fine recordCut fineCut phase.cut phase.quiet boundary
  have honest := honest_latched_known C phase.quiet truthful
  obtain ⟨K, cut, -, ordered, stable, settled⟩ := system.converges honest (fun n h => h.1)
  have eligible := all_eligible C phase entered stable
  exact ⟨K, cut, ordered, stable, fun n hn => settled n (eligible n hn)⟩

end Musubi.SysAcceptance

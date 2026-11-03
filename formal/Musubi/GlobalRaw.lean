/-
One immutable raw graph for a growing joint-system run. A vertex's parents are chosen when
it exists; every later state has those same parents. Future writes need not stop, and a
vertex that is never created has no parents. The raw history indexed by actual system time
then supplies PendingEpoch's window, without assuming the hub has already stabilized.
-/
import Musubi.RawEvolution
import Musubi.PendingEpoch

namespace Musubi.Recovery.HubSys

open Musubi NodeSys

theorem raw_run_grows {run : Nat → Sys}
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    {i j : Nat} (hij : i ≤ j) : RawGrow (run i) (run j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | succ d ih =>
    have step := (hs (i + d)).grows
    exact ⟨Nat.le_trans ih.1 step.1, fun x hx =>
      (step.2 x (Nat.lt_of_lt_of_le hx ih.1)).trans (ih.2 x hx)⟩

noncomputable def globalParents (run : Nat → Sys) (x : Nat) : List Nat := by
  classical
  exact if h : ∃ i, x < (run i).next then (run (Classical.choose h)).par x else []

theorem globalParents_agrees {run : Nat → Sys}
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    {i x : Nat} (hx : x < (run i).next) : globalParents run x = (run i).par x := by
  classical
  unfold globalParents
  split
  · rename_i h
    have ht := Classical.choose_spec h
    rcases Nat.le_total (Classical.choose h) i with hi | hi
    · exact ((raw_run_grows hs hi).2 x ht).symm
    · exact (raw_run_grows hs hi).2 x hx
  · exact False.elim (‹¬ ∃ j, x < (run j).next› ⟨i, hx⟩)

theorem globalParents_parLt (run : Nat → Sys)
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x) :
    ParLt (globalParents run) := by
  classical
  intro x p hp
  unfold globalParents at hp
  split at hp
  · rename_i h
    exact hdag _ x (Classical.choose_spec h) p hp
  · simp at hp

theorem global_anc_of_local {run : Nat → Sys}
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    {i a b : Nat} (h : Anc (parents (run i)) a b) (hb : b < (run i).next) :
    Anc (globalParents run) a b := by
  induction h with
  | refl => exact Anc.refl
  | @step p x hp _ ih =>
    have hraw : p ∈ (run i).par x := by simpa [parents, hb] using hp
    have hpx := hdag i x hb p hraw
    exact Anc.step (by rw [globalParents_agrees hs hb]; exact hraw) (ih (by omega))

theorem local_anc_of_global {run : Nat → Sys}
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    {i a b : Nat} (h : Anc (globalParents run) a b) (hb : b < (run i).next) :
    Anc (parents (run i)) a b := by
  induction h with
  | refl => exact Anc.refl
  | @step p x hp _ ih =>
    have hpx := globalParents_parLt run hdag x p hp
    exact Anc.step (by simpa [parents, hb, globalParents_agrees hs hb] using hp)
      (ih (by omega))

/-- The actual-time raw heads form the window's chain in the global graph. This derives
the static graph used for pending-name credit from finite-prefix histories. -/
theorem global_history_chain {run : Nat → Sys} (initial : Nat → Nat)
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hw : ∀ i, HistoryWindow (run 0).hub.seq (state (run i) (histories run initial i)))
    {i j : Nat} (hij : i ≤ j) :
    Anc (globalParents run) (run i).hub.head (run j).hub.head := by
  have ha := (hw j).chain (run i).hub.seq (run j).hub.seq (hw i).window
    (raw_seq_mono hs hij) (Nat.le_refl _)
  change Anc (parents (run j))
    (histories run initial j (run i).hub.seq) (histories run initial j (run j).hub.seq) at ha
  have hi : histories run initial i (run i).hub.seq = (run i).hub.head := (hw i).histHead
  have hj : histories run initial j (run j).hub.seq = (run j).hub.head := (hw j).histHead
  rw [raw_histories_saved hs initial hij (Nat.le_refl _), hi, hj] at ha
  exact global_anc_of_local hs hdag ha (hw j).headLt

theorem pending_history_of_sys {run : Nat → Sys} (initial : Nat → Nat) (origin : Nat → Nat)
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hw : ∀ i, HistoryWindow (run 0).hub.seq (state (run i) (histories run initial i)))
    (hunique : ∀ i x y, Anc (parents (run i)) x (run i).hub.head →
      Anc (parents (run i)) y (run i).hub.head → origin x = origin y → x = y) :
    PendingEpoch.History (globalParents run) (fun i => (run i).hub.head) 0 origin := by
  constructor
  · intro i j _ hij; exact global_history_chain initial hs hdag hw hij
  · intro i _ x y hx hy ho
    exact hunique i x y (local_anc_of_global hs hdag hx (hw i).headLt)
      (local_anc_of_global hs hdag hy (hw i).headLt) ho

end Musubi.Recovery.HubSys

/-
The hub's history of the joint system, indexed by sequence number: the head each sequence
number had when the hub last moved to it. From a time `a` on, where the hub only climbs raw
ancestry (`HubClimb`), the history is a window: strictly increasing heads along ancestry. The
convergence proof uses this file.
-/
import Musubi.HubAnswers

namespace Musubi.Recovery.HubSys

open Musubi NodeSys HubSuffix

/-- `histories run initial i s` is the head that sequence number `s` had after `i` steps of
`run`, starting from `initial`; it is updated whenever the hub's sequence number advances. -/
noncomputable def histories (run : Nat → Sys) (initial : Nat → Nat) : Nat → Nat → Nat
  | 0 => initial
  | i + 1 => nextHistory (run i) (run (i + 1)) (histories run initial i)

/-! ## The window from a climbing hub

From `a` on the raw graph only grows and the hub climbs (`HubClimb`). Then the history at the
sequence numbers the hub passes through is a chain of ancestors with strictly increasing
heads. -/

/-- Raw growth across a range of steps. -/
theorem rawGrow_range {run : Nat → Sys} {a : Nat}
    (grows : ∀ i, a ≤ i → RawGrow (run i) (run (i + 1))) {i : Nat} (hi : a ≤ i) :
    ∀ d, RawGrow (run i) (run (i + d)) := by
  intro d
  induction d with
  | zero => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | succ d ih =>
    have h := grows (i + d) (by omega)
    have e : i + (d + 1) = i + d + 1 := rfl
    rw [e]
    exact ⟨Nat.le_trans ih.1 h.1, fun y hy => by
      rw [h.2 y (Nat.lt_of_lt_of_le hy ih.1), ih.2 y hy]⟩

/-- Ancestry below `b` in a graph is ancestry in any graph that grows from it. -/
theorem anc_grow {g g' : Sys} (hg : RawGrow g g')
    (hdag : ∀ x, x < g.next → ∀ p ∈ g.par x, p < x) {a b : Nat} (h : Anc g.par a b)
    (hb : b < g.next) : Anc g'.par a b := by
  induction h with
  | refl => exact Anc.refl
  | @step p x hp _ ih =>
    exact Anc.step (by rw [hg.2 x hb]; exact hp) (ih (Nat.lt_trans (hdag x hb p hp) hb))

/-- Every sequence number between the hub's at `a` and at `a + d` is the hub's just before a
step that moves to the next one, since a step adds at most one. -/
theorem seq_step_exists {run : Nat → Sys} {a : Nat}
    (climbs : ∀ i, a ≤ i → HubClimb (run i) (run (i + 1))) :
    ∀ d q, (run a).hub.seq ≤ q → q < (run (a + d)).hub.seq →
      ∃ i, a ≤ i ∧ i < a + d ∧ (run i).hub.seq = q ∧ (run (i + 1)).hub.seq = q + 1 := by
  intro d
  induction d with
  | zero => intro q h1 h2; rw [Nat.add_zero] at h2; exact absurd h2 (by omega)
  | succ d ih =>
    intro q h1 h2
    have e : a + (d + 1) = a + d + 1 := rfl
    rw [e] at h2
    have hs := (climbs (a + d) (by omega)).seq_le_succ
    have hm := (climbs (a + d) (by omega)).seq_le
    by_cases hq : q < (run (a + d)).hub.seq
    · obtain ⟨i, hi, hid, e1, e2⟩ := ih q h1 hq
      exact ⟨i, hi, by omega, e1, e2⟩
    · exact ⟨a + d, by omega, by omega, by omega, by omega⟩

/-- A relation `R` that holds between consecutive numbers of `f` on `[lo, hi]` and is transitive
holds from `f i` to `f j` for `lo ≤ i < j ≤ hi`. -/
theorem chain_trans {R : Nat → Nat → Prop} (tr : ∀ x y z, R x y → R y z → R x z)
    {f : Nat → Nat} {lo hi : Nat}
    (step : ∀ q, lo ≤ q → q + 1 ≤ hi → R (f q) (f (q + 1))) :
    ∀ i j, lo ≤ i → i < j → j ≤ hi → R (f i) (f j) := by
  intro i j hi hij hj
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ j by omega)
  clear hij
  induction e with
  | zero => exact step i hi (by omega)
  | succ e ih => exact tr _ _ _ (ih (by omega)) (step (i + 1 + e) (by omega) (by omega))

/-- The history at `b` is a window from the hub's sequence number at `a` (`HistoryWindow`): its
heads from there on climb strictly along raw ancestry, and the hub's head at `b` is the last.
Here `a` is where the climbs start, `b` is the state's time, `dag` is the parents-first law of
every graph from `a` to `b`, and `bind` says the history holds the hub's head at each time from
`a` to `b`. The sequence number never falls and moves one at a time, so each sequence number
from the window's start is the hub's at some time, and the step to the next is a climb: the old
head is a raw ancestor of the new one and different from it, so below it. -/
theorem history_window_of_climbs {run : Nat → Sys} {hist : Nat → Nat} {a b : Nat}
    (hab : a ≤ b) (head : (run a).hub.head < (run a).next)
    (grows : ∀ i, a ≤ i → RawGrow (run i) (run (i + 1)))
    (climbs : ∀ i, a ≤ i → HubClimb (run i) (run (i + 1)))
    (dag : ∀ i, a ≤ i → i ≤ b →
      ∀ x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (bind : ∀ i, a ≤ i → i ≤ b → hist (run i).hub.seq = (run i).hub.head) :
    Recovery.HistoryWindow (run a).hub.seq (state (run b) hist) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  have seqMono : ∀ d, (run a).hub.seq ≤ (run (a + d)).hub.seq := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans ih (climbs (a + d) (by omega)).seq_le
  have headLt : ∀ d, (run (a + d)).hub.head < (run (a + d)).next := by
    intro d
    induction d with
    | zero => exact head
    | succ d ih =>
      have hg := (grows (a + d) (by omega)).1
      cases climbs (a + d) (by omega) with
      | stay | climb => show (run (a + d + 1)).hub.head < (run (a + d + 1)).next; omega
  have dagB := dag (a + d) hab (Nat.le_refl _)
  have hpar := parents_parLt dagB
  -- each step of the history is a climb, seen from the last graph
  have consec : ∀ q, (run a).hub.seq ≤ q → q + 1 ≤ (run (a + d)).hub.seq →
      Anc (parents (run (a + d))) (hist q) (hist (q + 1)) ∧ hist q < hist (q + 1) := by
    intro q h1 h2
    obtain ⟨i, hai, hid, e1, e2⟩ := seq_step_exists climbs d q h1 (by omega)
    have b1 := bind i hai (by omega)
    have b2 := bind (i + 1) (by omega) (by omega)
    rw [e1] at b1
    rw [e2] at b2
    cases climbs i hai with
    | stay => omega
    | climb _ hdiff hb habove =>
      have hgi : RawGrow (run i) (run (a + d)) := by
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (show i ≤ a + d by omega)
        rw [he]; exact rawGrow_range grows hai e
      have hdagi := dag i hai (by omega)
      have hanc := anc_grow hgi hdagi habove hb
      have hbn : (run (i + 1)).hub.head < (run (a + d)).next :=
        Nat.lt_of_lt_of_le hb hgi.1
      have hanc' := anc_parents dagB hanc hbn
      rw [b1, b2]
      exact ⟨hanc', Anc.lt_of_ne hpar hanc' (Ne.symm hdiff)⟩
  refine ⟨hpar, headLt d, bind (a + d) hab (Nat.le_refl _), seqMono d, ?_, ?_⟩
  · intro i j hi hij hj
    change j ≤ (run (a + d)).hub.seq at hj
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · exact Anc.refl
    · exact chain_trans (R := Anc (parents (run (a + d)))) (f := hist) (fun _ _ _ => Anc.trans)
        (fun q h1 h2 => (consec q h1 h2).1) i j hi hlt hj
  · intro i j hi hij hj
    change j ≤ (run (a + d)).hub.seq at hj
    exact chain_trans (R := (· < ·)) (f := hist) (fun _ _ _ => Nat.lt_trans)
      (fun q h1 h2 => (consec q h1 h2).2) i j hi hij hj

end Musubi.Recovery.HubSys

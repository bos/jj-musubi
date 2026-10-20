/-
The operation DAG: `anc*`, its order properties, transport across creation of a fresh
operation, and the `max` operator on sets of heads.
-/
import Musubi.Basic

namespace Musubi

/-- `Anc par a x` means `a ∈ anc*(x)`: `a` is `x` or an ancestor of `x`, following the
`par` (parents) function. -/
inductive Anc (par : Nat → List Nat) (a : Nat) : Nat → Prop
  | refl : Anc par a a
  | step {p x : Nat} : p ∈ par x → Anc par a p → Anc par a x

/-- Parents have strictly smaller ids. Fresh ids are allocated in increasing order, so this
holds of every reachable universe and makes the graph acyclic. -/
def ParLt (par : Nat → List Nat) : Prop := ∀ y p, p ∈ par y → p < y

/-- `max(S)`: the elements of `S` that are not ancestors of another element of `S`. -/
def maxSet (par : Nat → List Nat) (S : OSet) : OSet :=
  fun x => S x ∧ ∀ y, S y → Anc par x y → x = y

namespace Anc

variable {par : Nat → List Nat}

theorem parent {p x : Nat} (h : p ∈ par x) : Anc par p x := step h refl

theorem trans {a b c : Nat} (hab : Anc par a b) (hbc : Anc par b c) : Anc par a c := by
  induction hbc with
  | refl => exact hab
  | step hp _ ih => exact step hp ih

theorem le (hlt : ParLt par) {a x : Nat} (h : Anc par a x) : a ≤ x := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hp _ ih => exact Nat.le_of_lt (Nat.lt_of_le_of_lt ih (hlt _ _ hp))

theorem lt_of_ne (hlt : ParLt par) {a x : Nat} (h : Anc par a x) (hne : a ≠ x) : a < x :=
  Nat.lt_of_le_of_ne (h.le hlt) hne

theorem antisymm (hlt : ParLt par) {a b : Nat} (hab : Anc par a b) (hba : Anc par b a) :
    a = b := Nat.le_antisymm (hab.le hlt) (hba.le hlt)

/-- A set closed under parents is closed under ancestors. -/
theorem closed {S : OSet} (hS : ∀ x p, S x → p ∈ par x → S p) {a x : Nat}
    (h : Anc par a x) (hx : S x) : S a := by
  induction h with
  | refl => exact hx
  | step hp _ ih => exact ih (hS _ _ hx hp)

/-- `x ∉ anc*(y)` when `x > y`. -/
theorem not_of_lt (hlt : ParLt par) {a x : Nat} (h : x < a) : ¬ Anc par a x :=
  fun hA => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (hA.le hlt) h)

end Anc

/-! ## Transport across the creation of a fresh operation -/

theorem parLt_upd {par : Nat → List Nat} (hlt : ParLt par) {o : Nat} {L : List Nat}
    (hL : ∀ p ∈ L, p < o) : ParLt (upd par o L) := by
  intro y p hp
  by_cases hy : y = o
  · subst hy; simp at hp; exact hL p hp
  · rw [upd_ne _ _ hy] at hp; exact hlt y p hp

/-- Creating operation `o` with parents `L` does not change `anc*` of older operations. -/
theorem anc_upd_iff {par : Nat → List Nat} (hlt : ParLt par) {o : Nat} {L : List Nat}
    (hL : ∀ p ∈ L, p < o) {a x : Nat} (hx : x < o) :
    Anc (upd par o L) a x ↔ Anc par a x := by
  have hlt' := parLt_upd hlt hL
  constructor
  · intro h
    induction h with
    | refl => exact Anc.refl
    | @step p y hp _ ih =>
      have hy : y ≠ o := Nat.ne_of_lt hx
      rw [upd_ne _ _ hy] at hp
      exact Anc.step hp (ih (Nat.lt_trans (hlt _ _ hp) hx))
  · intro h
    induction h with
    | refl => exact Anc.refl
    | @step p y hp _ ih =>
      have hy : y ≠ o := Nat.ne_of_lt hx
      have hp' : p ∈ upd par o L y := by rw [upd_ne _ _ hy]; exact hp
      exact Anc.step hp' (ih (Nat.lt_trans (hlt _ _ hp) hx))

/-- `anc*` of the fresh operation itself. -/
theorem anc_upd_new {par : Nat → List Nat} (hlt : ParLt par) {o : Nat} {L : List Nat}
    (hL : ∀ p ∈ L, p < o) {a : Nat} :
    Anc (upd par o L) a o ↔ a = o ∨ ∃ p ∈ L, Anc par a p := by
  constructor
  · intro h
    cases h with
    | refl => exact Or.inl rfl
    | step hp hA =>
      simp at hp
      exact Or.inr ⟨_, hp, (anc_upd_iff hlt hL (hL _ hp)).1 hA⟩
  · rintro (rfl | ⟨p, hp, hA⟩)
    · exact Anc.refl
    · exact Anc.step (by simp; exact hp) ((anc_upd_iff hlt hL (hL _ hp)).2 hA)

end Musubi

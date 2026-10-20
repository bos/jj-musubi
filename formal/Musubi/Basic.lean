/-
Basic utilities: sets as predicates, point updates of functions, and finite counting
over `Nat` ranges (used by the liveness measure).
-/

namespace Musubi

/-- Sets of identifiers (operation ids, object ids) are predicates. -/
abbrev OSet := Nat → Prop

/-- Point update of a function on `Nat`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (a : α) : Nat → α :=
  fun j => if j = i then a else f j

@[simp] theorem upd_same {α : Type} (f : Nat → α) (i : Nat) (a : α) : upd f i a i = a := by
  simp [upd]

@[simp] theorem upd_ne {α : Type} (f : Nat → α) {i j : Nat} (a : α) (h : j ≠ i) :
    upd f i a j = f j := by
  simp [upd, h]

theorem upd_lt {α : Type} (f : Nat → α) {i j : Nat} (a : α) (h : j < i) :
    upd f i a j = f j := upd_ne f a (Nat.ne_of_lt h)

/-! ## Counting -/

open Classical in
/-- `cnt B P` is the number of `x < B` satisfying `P`. -/
noncomputable def cnt : Nat → (Nat → Prop) → Nat
  | 0, _ => 0
  | B + 1, P => cnt B P + (if P B then 1 else 0)

theorem cnt_congr {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → (P x ↔ Q x)) :
    cnt B P = cnt B Q := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [cnt]
    rw [ih (fun x hx => h x (Nat.lt_succ_of_lt hx))]
    have := h B (Nat.lt_succ_self B)
    by_cases hP : P B
    · have hQ : Q B := this.1 hP
      simp [hP, hQ]
    · have hQ : ¬ Q B := fun hq => hP (this.2 hq)
      simp [hP, hQ]

theorem cnt_le {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x) :
    cnt B Q ≤ cnt B P := by
  induction B with
  | zero => exact Nat.le_refl _
  | succ B ih =>
    simp only [cnt]
    have ih' := ih (fun x hx => h x (Nat.lt_succ_of_lt hx))
    have hB := h B (Nat.lt_succ_self B)
    by_cases hQ : Q B
    · simp [hQ, hB hQ]; omega
    · by_cases hP : P B
      · simp [hQ, hP]; omega
      · simp [hQ, hP]; omega

theorem cnt_lt {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x)
    (w : ∃ x, x < B ∧ P x ∧ ¬ Q x) : cnt B Q < cnt B P := by
  induction B with
  | zero => obtain ⟨x, hx, -⟩ := w; exact absurd hx (Nat.not_lt_zero _)
  | succ B ih =>
    simp only [cnt]
    have hle := cnt_le (B := B) (P := P) (Q := Q) (fun x hx => h x (Nat.lt_succ_of_lt hx))
    obtain ⟨x, hx, hPx, hQx⟩ := w
    by_cases hxB : x = B
    · subst hxB
      simp [hPx, hQx]; omega
    · have hlt : x < B := by omega
      have ih' := ih (fun y hy => h y (Nat.lt_succ_of_lt hy)) ⟨x, hlt, hPx, hQx⟩
      have hB := h B (Nat.lt_succ_self B)
      by_cases hQ : Q B
      · simp [hQ, hB hQ]; omega
      · by_cases hP : P B
        · simp [hQ, hP]; omega
        · simp [hQ, hP]; omega

/-! ## Sums over `n < N` -/

/-- `sumN N f = f 0 + ... + f (N-1)`. -/
def sumN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | N + 1, f => sumN N f + f N

theorem sumN_congr {N : Nat} {f g : Nat → Nat} (h : ∀ n, n < N → f n = g n) :
    sumN N f = sumN N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [sumN]
    rw [ih (fun n hn => h n (Nat.lt_succ_of_lt hn)), h N (Nat.lt_succ_self N)]

theorem sumN_lt {N : Nat} {f g : Nat → Nat} {i : Nat} (hi : i < N)
    (hlt : f i < g i) (heq : ∀ n, n < N → n ≠ i → f n = g n) : sumN N f < sumN N g := by
  induction N with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ N ih =>
    simp only [sumN]
    by_cases h : i = N
    · subst h
      have := sumN_congr (N := i) (f := f) (g := g)
        (fun n hn => heq n (Nat.lt_succ_of_lt hn) (Nat.ne_of_lt hn))
      omega
    · have hi' : i < N := by omega
      have := ih hi' (fun n hn hne => heq n (Nat.lt_succ_of_lt hn) hne)
      have := heq N (Nat.lt_succ_self N) (Ne.symm h)
      omega

/-! ## Minimal elements -/

theorem exists_min (P : Nat → Prop) {a : Nat} (ha : P a) :
    ∃ x, P x ∧ ∀ y, y < x → ¬ P y := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases h : ∃ y, y < a ∧ P y
    · obtain ⟨y, hy, hPy⟩ := h
      exact ih y hy hPy
    · exact ⟨a, ha, fun y hy hPy => h ⟨y, hy, hPy⟩⟩

end Musubi

/-
Basic utilities: sets as predicates, point updates of functions, and finite counting
over `Nat` ranges (used by the liveness measure), and termination of runs.
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
    rw [ih (fun x hx => h x (Nat.lt_succ_of_lt hx)), h B (Nat.lt_succ_self B)]

theorem cnt_le {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x) :
    cnt B Q ≤ cnt B P := by
  induction B with
  | zero => exact Nat.le_refl _
  | succ B ih =>
    simp only [cnt]
    have ih' := ih (fun x hx => h x (Nat.lt_succ_of_lt hx))
    have hB := h B (Nat.lt_succ_self B)
    grind only

theorem cnt_lt {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x)
    (w : ∃ x, x < B ∧ P x ∧ ¬ Q x) : cnt B Q < cnt B P := by
  induction B with
  | zero => obtain ⟨x, hx, -⟩ := w; omega
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
      grind only

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
  | zero => omega
  | succ N ih =>
    simp only [sumN]
    by_cases h : i = N
    · subst h
      have := sumN_congr (N := i) (f := f) (g := g)
        (fun n hn => heq n (Nat.lt_succ_of_lt hn) (Nat.ne_of_lt hn))
      omega
    · have := ih (by omega) (fun n hn hne => heq n (Nat.lt_succ_of_lt hn) hne)
      have := heq N (Nat.lt_succ_self N) (Ne.symm h)
      omega

/-! ## Runs -/

/-- An accessible state cannot start an infinite descending chain. -/
theorem acc_no_infinite_chain {α : Sort u} {r : α → α → Prop} {a : α} (ha : Acc r a) :
    ∀ f : Nat → α, f 0 = a → ¬ ∀ i, r (f (i + 1)) (f i) := by
  induction ha with
  | intro a _ ih =>
    intro f hf hall
    exact ih (f 1) (hf ▸ hall 0) (fun i => f (i + 1)) rfl (fun i => hall (i + 1))

/-- A well-founded step relation on an invariant admits no infinite run from that invariant.
The relation is reversed in `wf` because each forward step descends. -/
theorem no_infinite_run_of_invariant {α : Sort u} {step : α → α → Prop} {inv : α → Prop}
    (wf : WellFounded (fun t s => inv s ∧ step s t))
    (preserve : ∀ {s t}, inv s → step s t → inv t) {s : α} (hs : inv s) :
    ¬ ∃ f : Nat → α, f 0 = s ∧ ∀ i, step (f i) (f (i + 1)) := by
  rintro ⟨f, hf0, hf⟩
  have hinv : ∀ i, inv (f i) := by
    intro i
    induction i with
    | zero => exact hf0 ▸ hs
    | succ i ih => exact preserve ih (hf i)
  exact acc_no_infinite_chain (wf.apply s) f hf0 (fun i => ⟨hinv i, hf i⟩)

/-- Progress and quiescence characterize terminal states. -/
theorem terminal_iff_of_progress {α : Sort u} {step : α → α → Prop} {s : α} {done : Prop}
    (progress : ¬ done → ∃ t, step s t) (quiescent : done → ∀ t, ¬ step s t) :
    (∀ t, ¬ step s t) ↔ done := by
  constructor
  · intro ht
    refine Classical.byContradiction fun hd => ?_
    obtain ⟨t, hst⟩ := progress hd
    exact ht t hst
  · exact quiescent

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

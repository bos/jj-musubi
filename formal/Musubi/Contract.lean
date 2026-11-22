/-
Contracting operations out of a history, as `musubi sync --prune` does when it removes selected
unpublished operations (`Publication.lean`; docs/internals/design.md, "Snapshot publication
budgets").

A history is a parent function `par` whose parents have smaller ids (`ParLt`), and a set `D`
of operations to drop. Each surviving operation's parents become the expansion of its parent
list: a dropped parent is replaced, in place, by the expansion of its own parents, and then
duplicates are removed, keeping each one's first occurrence (`cpar`).

- `anc_cpar_iff`: among survivors, contraction keeps ancestry exactly.
- `anc_congr`: `anc*(x)` depends only on the parents of `x` and what is below it.
-/
import Musubi.Dag

namespace Musubi.Contract

/-! ## Removing duplicates -/

/-- The elements of `l` not in `seen`, each at its first occurrence. -/
def ddAux : List Nat → List Nat → List Nat
  | _, [] => []
  | seen, a :: l => if a ∈ seen then ddAux seen l else a :: ddAux (a :: seen) l

/-- `l` without duplicates, keeping each element's first occurrence. -/
def dd (l : List Nat) : List Nat := ddAux [] l

theorem ddAux_congr {s₁ s₂ : List Nat} (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) (l : List Nat) :
    ddAux s₁ l = ddAux s₂ l := by
  induction l generalizing s₁ s₂ with
  | nil => rfl
  | cons a l ih =>
    simp only [ddAux]
    by_cases ha : a ∈ s₁
    · have : a ∈ s₂ := (h a).1 ha
      simp [ha, this, ih h]
    · have : a ∉ s₂ := fun h₂ => ha ((h a).2 h₂)
      simp only [ha, this, ite_false]
      congr 1
      exact ih (fun b => by simp [h b])

theorem mem_ddAux {s l : List Nat} {a : Nat} : a ∈ ddAux s l ↔ a ∈ l ∧ a ∉ s := by
  induction l generalizing s with
  | nil => simp [ddAux]
  | cons b l ih =>
    simp only [ddAux]
    by_cases hb : b ∈ s
    · simp only [hb, ite_true, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact absurd hb h2
        · exact ⟨h1, h2⟩
    · simp only [hb, ite_false, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨Or.inl rfl, hb⟩
        · exact ⟨Or.inr h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · by_cases hab : a = b
          · exact Or.inl hab
          · exact Or.inr ⟨h1, fun h => h.elim hab h2⟩

theorem mem_dd {l : List Nat} {a : Nat} : a ∈ dd l ↔ a ∈ l := by
  simp [dd, mem_ddAux]

/-- `flatMap` needs `f` and `g` to agree only on the list's members. -/
theorem flatMap_congr_mem {l : List Nat} {f g : Nat → List Nat} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-! ## Contraction -/

variable (par : Nat → List Nat) (D : Nat → Bool)

/-- The expansion of `p` with fuel: `[p]` if it survives, otherwise its parents' expansions. -/
def expF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, p => if D p then (par p).flatMap (expF f) else [p]

/-- The expansion of `p`: `[p]` if `p` survives, and otherwise what its parents expand to. -/
def exp (p : Nat) : List Nat := expF par D (p + 1) p

/-- The parents of `x` once `D` is dropped: its parent list expanded, without duplicates. -/
def cpar (x : Nat) : List Nat := dd ((par x).flatMap (exp par D))

variable {par D}

theorem expF_fuel (hlt : ParLt par) {f g p : Nat} (hf : p < f) (hg : p < g) :
    expF par D f p = expF par D g p := by
  induction f generalizing g p with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [expF]
      split
      · apply flatMap_congr_mem
        intro q hq
        have := hlt p q hq
        exact ih (by omega) (by omega)
      · rfl

theorem exp_eq (hlt : ParLt par) (p : Nat) :
    exp par D p = if D p then (par p).flatMap (exp par D) else [p] := by
  simp only [exp, expF]
  split
  · apply flatMap_congr_mem
    intro q hq
    have := hlt p q hq
    exact expF_fuel hlt (by omega) (by omega)
  · rfl

/-- What `p` expands to survives, and is `p` or one of its ancestors. -/
theorem mem_exp (hlt : ParLt par) {p q : Nat} (h : q ∈ exp par D p) :
    D q = false ∧ Anc par q p := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    rw [exp_eq hlt] at h
    split at h
    · obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 h
      obtain ⟨hD, hA⟩ := ih r (hlt p r hr) hq
      exact ⟨hD, Anc.step hr hA⟩
    · simp at h
      subst h
      rename_i hD
      exact ⟨by simpa using hD, Anc.refl⟩

/-- A survivor that is `p` or an ancestor of `p` is reached from what `p` expands to. -/
theorem exp_covers (hlt : ParLt par) {a p : Nat} (hA : Anc par a p) (ha : D a = false) :
    ∃ q ∈ exp par D p, Anc par a q := by
  induction hA with
  | refl => exact ⟨a, by rw [exp_eq hlt]; simp [ha], Anc.refl⟩
  | @step r x hr hA ih =>
    rw [exp_eq hlt]
    by_cases hx : D x
    · obtain ⟨q, hq, hAq⟩ := ih
      exact ⟨q, by simp only [hx, ite_true]; exact List.mem_flatMap.2 ⟨r, hr, hq⟩, hAq⟩
    · exact ⟨x, by simp [hx], Anc.step hr hA⟩

theorem mem_cpar (hlt : ParLt par) {x q : Nat} (h : q ∈ cpar par D x) :
    D q = false ∧ Anc par q x ∧ q ≠ x := by
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 (mem_dd.1 h)
  obtain ⟨hD, hA⟩ := mem_exp hlt hq
  have hlt' : q < x := Nat.lt_of_le_of_lt (hA.le hlt) (hlt x p hp)
  exact ⟨hD, Anc.step hp hA, Nat.ne_of_lt hlt'⟩

/-- A surviving proper ancestor of `x` is reached from `x`'s contracted parents. -/
theorem cpar_covers (hlt : ParLt par) {a x : Nat} (hA : Anc par a x) (hne : a ≠ x)
    (ha : D a = false) : ∃ q ∈ cpar par D x, Anc par a q := by
  cases hA with
  | refl => exact absurd rfl hne
  | @step p _ hp hA =>
    obtain ⟨q, hq, hAq⟩ := exp_covers hlt hA ha
    exact ⟨q, mem_dd.2 (List.mem_flatMap.2 ⟨p, hp, hq⟩), hAq⟩

theorem parLt_cpar (hlt : ParLt par) : ParLt (cpar par D) := by
  intro y q hq
  obtain ⟨-, hA, hne⟩ := mem_cpar hlt hq
  exact Anc.lt_of_ne hlt hA hne

/-- The whole contracted closure of a survivor contains only survivors. This includes its
head, unlike the fact that each contracted parent survives. -/
theorem anc_cpar_survives (hlt : ParLt par) {x y : Nat} (hx : D x = false)
    (ha : Anc (cpar par D) y x) : D y = false := by
  induction ha with
  | refl => exact hx
  | step hp _ ih => exact ih (mem_cpar hlt hp).1

/-- Among survivors, contraction keeps ancestry exactly. -/
theorem anc_cpar_iff (hlt : ParLt par) {a x : Nat} (ha : D a = false) :
    Anc (cpar par D) a x ↔ Anc par a x := by
  constructor
  · intro h
    induction h with
    | refl => exact Anc.refl
    | step hq _ ih => exact ih.trans (mem_cpar hlt hq).2.1
  · intro h
    induction x using Nat.strongRecOn with
    | ind x ih =>
      by_cases hax : a = x
      · subst hax; exact Anc.refl
      · obtain ⟨q, hq, hAq⟩ := cpar_covers hlt h hax ha
        have hlt' := (parLt_cpar hlt) x q hq
        exact Anc.step hq (ih q hlt' hAq)


/-! ## Ids depend only on what is below -/

/-- `anc*(x)` depends only on the parents of `x` and what is below it. -/
theorem anc_congr {par par' : Nat → List Nat} (hlt : ParLt par) {x : Nat}
    (h : ∀ y, y ≤ x → par y = par' y) {a : Nat} : Anc par a x ↔ Anc par' a x := by
  have hlt' : ∀ y p, y ≤ x → p ∈ par' y → p < y := by
    intro y p hy hp; rw [← h y hy] at hp; exact hlt y p hp
  constructor
  · intro hA
    have : ∀ z, Anc par a z → z ≤ x → Anc par' a z := by
      intro z hz
      induction hz with
      | refl => intro _; exact Anc.refl
      | @step p z hp _ ih =>
        intro hzx
        have hpz := hlt z p hp
        exact Anc.step (by rw [← h z hzx]; exact hp) (ih (by omega))
    exact this x hA (Nat.le_refl _)
  · intro hA
    have : ∀ z, Anc par' a z → z ≤ x → Anc par a z := by
      intro z hz
      induction hz with
      | refl => intro _; exact Anc.refl
      | @step p z hp _ ih =>
        intro hzx
        have hpz := hlt' z p hzx hp
        exact Anc.step (by rw [h z hzx]; exact hp) (ih (by omega))
    exact this x hA (Nat.le_refl _)

end Musubi.Contract

/-
Which copies a hive shows, when copies go away without leaving (issue #47).

Each copy of a repository has its own identity in the hive (`laptop#1a2b3c4d`), and every
machine shows the other copies' working copies. A copy that goes away should stop being shown.
Here an operation in the hive's history may be *work* by a copy, an operation that copy's own
`jj` made, or a *forget* of a copy, written by `musubi forget`, by `musubi leave` for its own
copy, or by a daemon that finds a copy idle for longer than its `forget-after`. Merges, and the
operations musubi writes, are neither. The rule:

  copy `k` is present at operation `x` when some work by `k` in `anc*(x)` is in `anc*` of no
  forget of `k` in `anc*(x)`.

A forget removes the work it saw, and only work brings a copy back. For any operation DAG:

- presence at `x` depends only on `x`'s history (`present_local`), so every machine that has
  `x` agrees; and operations whose histories have the same work and forgets agree, as merges
  of the same heads do, in any order or grouping (`present_congr`);
- work makes its copy present, and a forget makes it absent (`work_present`,
  `forget_absent`);
- only work brings a copy back. An operation that isn't the copy's work, all of whose parents
  have the copy absent, has it absent (`only_work_returns`), and absence lasts until the
  history has work by the copy that it lacked (`absence_persists`). So `musubi leave`, if it
  forgets its copy after all the copy's work and pushes nothing made later, sticks however
  its forget is merged (`leave_sticks`);
- a forget removes only the work it saw, so work concurrent with it survives the merge
  (`unseen_work_survives`);
- forgetting can't loop along a line of history. Of forgets made only where the copy is
  present (`Guarded`), one that follows another saw work the other didn't
  (`forgets_need_fresh_work`); none follows a forget that saw all the copy's work
  (`no_forget_after_complete`); and a chain of them is no longer than the copy's work
  (`forget_chain_bounded`). Forgets made side by side, each before the others arrived, aren't
  bounded here: the implementation keeps them few by forgetting only just after fetching.
  They are harmless: of two that saw the same work, wherever one is, the other changes nothing
  (`concurrent_forget_noop`), and a forget made where its copy is already absent changes
  nothing (`redundant_forget_noop`);
- presence can be decided from the copy's latest work and its forgets
  (`present_iff_latest`);
- what a machine keeps of each copy present, its latest work that no forget saw (`UMax`),
  follows from an operation's parents' alone (`umax_merge`, `umax_work`, `umax_forget`), and
  says whether the copy is present (`present_iff_umax`). `crates/musubi-jj/src/presence.rs`
  computes it so, and `PresenceExec.lean` checks it, through the oracle.

Not modeled: where the working copies are (presence decides only whether a copy's working
copies are in the view), how a daemon judges a copy idle (the theorems hold whatever it
decides, given `Guarded` where stated), and the sync protocol, which `Model.lean` models.
-/
import Musubi.Dag

namespace Musubi.Presence

/-- `anc*(x)` is `x` and what its parents reach. -/
theorem anc_cases {par : Nat → List Nat} {a x : Nat} (hA : Anc par a x) :
    a = x ∨ ∃ p ∈ par x, Anc par a p := by
  cases hA with
  | refl => exact Or.inl rfl
  | step hp hA => exact Or.inr ⟨_, hp, hA⟩

/-- A predicate that holds somewhere, and only at numbers up to `x`, holds at a largest one. -/
theorem exists_max_le {Q : Nat → Prop} {x a : Nat} (ha : Q a) (hle : ∀ m, Q m → m ≤ x) :
    ∃ m, Q m ∧ ∀ m', Q m' → m' ≤ m := by
  have hP : x - a ≤ x ∧ Q (x - (x - a)) :=
    ⟨Nat.sub_le x a, by rw [Nat.sub_sub_self (hle a ha)]; exact ha⟩
  obtain ⟨d, ⟨hd, hQd⟩, hmin⟩ := exists_min (fun d => d ≤ x ∧ Q (x - d)) hP
  refine ⟨x - d, hQd, fun m' hm' => ?_⟩
  have hm'x := hle m' hm'
  apply Classical.byContradiction
  intro hgt
  have hlt : x - m' < d := by omega
  exact hmin (x - m') hlt ⟨Nat.sub_le x m', by rw [Nat.sub_sub_self hm'x]; exact hm'⟩

/-- Two parent functions that agree throughout `anc*(x)` give `x` the same `anc*`. -/
theorem anc_local {p₁ p₂ : Nat → List Nat} {x : Nat} (hpar : ∀ b, Anc p₁ b x → p₁ b = p₂ b)
    {a : Nat} : Anc p₁ a x ↔ Anc p₂ a x := by
  constructor
  · intro hA
    have : ∀ y, Anc p₁ a y → (∀ b, Anc p₁ b y → p₁ b = p₂ b) → Anc p₂ a y := by
      intro y hy
      induction hy with
      | refl => intro _; exact Anc.refl
      | @step p y hp _ ih =>
        intro hb
        have hp₂ : p ∈ p₂ y := by rw [← hb y Anc.refl]; exact hp
        exact Anc.step hp₂ (ih (fun b hb' => hb b (Anc.trans hb' (Anc.parent hp))))
    exact this x hA hpar
  · intro hA
    have : ∀ y, Anc p₂ a y → Anc p₁ y x → Anc p₁ a y := by
      intro y hy
      induction hy with
      | refl => intro _; exact Anc.refl
      | @step p y hp _ ih =>
        intro hyx
        have hp₁ : p ∈ p₁ y := by rw [hpar y hyx]; exact hp
        exact Anc.step hp₁ (ih (Anc.trans (Anc.parent hp₁) hyx))
    exact this x hA Anc.refl

/-- A hive's operation history: each operation's parents, and which operations are work by,
or forgets of, which copies. Copies are numbered too. -/
structure Hist where
  par : Nat → List Nat
  /-- `work x k`: copy `k`'s own `jj` made operation `x`. -/
  work : Nat → Nat → Prop
  /-- `forget x k`: operation `x` forgets copy `k`. -/
  forget : Nat → Nat → Prop

namespace Hist

variable (h : Hist)

/-- `anc*(x)`. -/
abbrev AncOf (x : Nat) : OSet := fun a => Anc h.par a x

/-- What `x`'s parents reach: `anc*(x)` without `x`, the history an operation is made on. -/
abbrev Below (x : Nat) : OSet := fun a => ∃ p ∈ h.par x, Anc h.par a p

/-- Work `w` by `k` is covered in `S` when a forget of `k` in `S` saw it. -/
def Covered (S : OSet) (k w : Nat) : Prop :=
  ∃ f, S f ∧ h.forget f k ∧ Anc h.par w f

/-- `k` is present in a set of operations `S`: some work by `k` in `S` is not covered there. -/
def PresentIn (S : OSet) (k : Nat) : Prop :=
  ∃ w, S w ∧ h.work w k ∧ ¬ h.Covered S k w

/-- `k` is present at operation `x`: its working copies are in `x`'s view. -/
def Present (x k : Nat) : Prop := h.PresentIn (h.AncOf x) k

/-- Operations as musubi makes them: work by at most one copy, and never both work and a
forget. -/
def WellFormed : Prop :=
  (∀ x k j, h.work x k → h.work x j → k = j) ∧ (∀ x k j, h.work x k → ¬ h.forget x j)

/-- Every forget of `k` is made where `k` is present. A daemon forgets only a copy it shows,
and `musubi forget` and `musubi leave` write nothing for a copy already absent. -/
def Guarded (k : Nat) : Prop := ∀ f, h.forget f k → h.PresentIn (h.Below f) k

/-- `m` is latest work by `k` in `anc*(x)`: no other work by `k` there has `m` in its `anc*`. -/
def Latest (x k m : Nat) : Prop :=
  Anc h.par m x ∧ h.work m k ∧ ∀ m', Anc h.par m' x → h.work m' k → Anc h.par m m' → m' = m

/-- `h`, but with operation `f` forgetting `k` too. -/
def addForget (f k : Nat) : Hist :=
  { h with forget := fun y j => h.forget y j ∨ (y = f ∧ j = k) }

theorem below_anc {x a : Nat} (hb : h.Below x a) : Anc h.par a x := by
  obtain ⟨p, hp, hA⟩ := hb
  exact Anc.trans hA (Anc.parent hp)

theorem covered_mono {y x k w : Nat} (hyx : Anc h.par y x) (hc : h.Covered (h.AncOf y) k w) :
    h.Covered (h.AncOf x) k w := by
  obtain ⟨f, hf, hF, hA⟩ := hc
  exact ⟨f, Anc.trans hf hyx, hF, hA⟩

/-- Where `k` is absent, every work by it is covered. -/
theorem covered_of_absent {y k w : Nat} (hy : ¬ h.Present y k) (hw : Anc h.par w y)
    (hW : h.work w k) : h.Covered (h.AncOf y) k w :=
  Classical.byContradiction fun hn => hy ⟨w, hw, hW, hn⟩

/-! ## Agreement -/

/-- Operations whose histories have the same work by, and forgets of, `k` agree on it: merges
of the same heads, in any order or grouping, by any machine. -/
theorem present_congr {x y k : Nat}
    (hxy : ∀ a, (h.work a k ∨ h.forget a k) → (Anc h.par a x ↔ Anc h.par a y)) :
    h.Present x k ↔ h.Present y k := by
  have hc : ∀ w, h.Covered (h.AncOf x) k w ↔ h.Covered (h.AncOf y) k w := fun w =>
    ⟨fun ⟨f, hf, hF, hA⟩ => ⟨f, (hxy f (Or.inr hF)).1 hf, hF, hA⟩,
     fun ⟨f, hf, hF, hA⟩ => ⟨f, (hxy f (Or.inr hF)).2 hf, hF, hA⟩⟩
  constructor
  · rintro ⟨w, hw, hW, hn⟩
    exact ⟨w, (hxy w (Or.inl hW)).1 hw, hW, fun c => hn ((hc w).2 c)⟩
  · rintro ⟨w, hw, hW, hn⟩
    exact ⟨w, (hxy w (Or.inl hW)).2 hw, hW, fun c => hn ((hc w).1 c)⟩

/-- An operation that is neither work by `k` nor a forget of it has `k` present exactly when
its parents' history, taken together, does. -/
theorem present_iff_below {x k : Nat} (hW : ¬ h.work x k) (hF : ¬ h.forget x k) :
    h.Present x k ↔ h.PresentIn (h.Below x) k := by
  constructor
  · rintro ⟨w, hw, hWk, hn⟩
    have hb : h.Below x w := by
      rcases anc_cases hw with rfl | hb
      · exact absurd hWk hW
      · exact hb
    exact ⟨w, hb, hWk, fun ⟨f, hf, hFk, hA⟩ => hn ⟨f, h.below_anc hf, hFk, hA⟩⟩
  · rintro ⟨w, hw, hWk, hn⟩
    refine ⟨w, h.below_anc hw, hWk, fun ⟨f, hf, hFk, hA⟩ => hn ⟨f, ?_, hFk, hA⟩⟩
    rcases anc_cases hf with rfl | hb
    · exact absurd hFk hF
    · exact hb

/-- Presence at `x` depends only on `x`'s history: two histories that agree there, as every
machine that has `x` does, agree on it. -/
theorem present_local (h₁ h₂ : Hist) {x k : Nat}
    (hpar : ∀ b, Anc h₁.par b x → h₁.par b = h₂.par b)
    (hw : ∀ b, Anc h₁.par b x → (h₁.work b k ↔ h₂.work b k))
    (hfg : ∀ b, Anc h₁.par b x → (h₁.forget b k ↔ h₂.forget b k)) :
    h₁.Present x k ↔ h₂.Present x k := by
  have hanc : ∀ a, Anc h₁.par a x ↔ Anc h₂.par a x := fun _ => anc_local hpar
  have hanc' : ∀ f, Anc h₁.par f x → ∀ a, (Anc h₁.par a f ↔ Anc h₂.par a f) :=
    fun f hfx _ => anc_local (fun b hb => hpar b (Anc.trans hb hfx))
  constructor
  · rintro ⟨w, hwx, hW, hn⟩
    refine ⟨w, (hanc w).1 hwx, (hw w hwx).1 hW, ?_⟩
    rintro ⟨f, hfx, hF, hA⟩
    have hfx₁ : Anc h₁.par f x := (hanc f).2 hfx
    exact hn ⟨f, hfx₁, (hfg f hfx₁).2 hF, (hanc' f hfx₁ w).2 hA⟩
  · rintro ⟨w, hwx, hW, hn⟩
    have hwx₁ : Anc h₁.par w x := (hanc w).2 hwx
    refine ⟨w, hwx₁, (hw w hwx₁).2 hW, ?_⟩
    rintro ⟨f, hfx, hF, hA⟩
    exact hn ⟨f, (hanc f).1 hfx, (hfg f hfx).1 hF, (hanc' f hfx w).1 hA⟩

/-! ## Work and forgets -/

theorem work_present (hlt : ParLt h.par) (hwf : h.WellFormed) {x k : Nat} (hW : h.work x k) :
    h.Present x k := by
  refine ⟨x, Anc.refl, hW, fun ⟨f, hf, hFk, hA⟩ => hwf.2 x k k hW ?_⟩
  have := Anc.antisymm hlt hf hA
  subst this
  exact hFk

theorem forget_absent {f k : Nat} (hF : h.forget f k) : ¬ h.Present f k :=
  fun ⟨_, hw, _, hn⟩ => hn ⟨f, Anc.refl, hF, hw⟩

/-- Only work brings a copy back: an operation that isn't `k`'s work, made where every parent
has `k` absent, has `k` absent. Merges and the operations musubi writes are such operations. -/
theorem only_work_returns {x k : Nat} (hW : ¬ h.work x k)
    (hpar : ∀ p ∈ h.par x, ¬ h.Present p k) : ¬ h.Present x k := by
  rintro ⟨w, hw, hWk, hn⟩
  rcases anc_cases hw with rfl | ⟨p, hp, hA⟩
  · exact hW hWk
  · exact hn (h.covered_mono (Anc.parent hp) (h.covered_of_absent (hpar p hp) hA hWk))

/-- Absence lasts: `k`, absent at `y`, stays absent at a later `x` unless `x`'s history has
work by `k` that `y`'s lacks. -/
theorem absence_persists {y x k : Nat} (hy : ¬ h.Present y k) (hyx : Anc h.par y x)
    (hnew : ∀ w, Anc h.par w x → h.work w k → Anc h.par w y) : ¬ h.Present x k :=
  fun ⟨w, hw, hWk, hn⟩ => hn (h.covered_mono hyx (h.covered_of_absent hy (hnew w hw hWk) hWk))

/-- `musubi leave` sticks, if it writes its forget after all of its copy's work and pushes
nothing made later (a `jj` command run in the copy as it leaves stays there, unpushed): the
copy is absent at every operation that has the forget, whatever it is merged with. -/
theorem leave_sticks {f x k : Nat} (hF : h.forget f k) (hall : ∀ w, h.work w k → Anc h.par w f)
    (hfx : Anc h.par f x) : ¬ h.Present x k :=
  h.absence_persists (h.forget_absent hF) hfx (fun w _ hW => hall w hW)

/-- A forget removes only the work it saw: work that no forget saw keeps its copy present,
as when a copy works while a daemon that hasn't seen that work forgets it. -/
theorem unseen_work_survives {w x k : Nat} (hW : h.work w k) (hwx : Anc h.par w x)
    (hunseen : ∀ f, Anc h.par f x → h.forget f k → ¬ Anc h.par w f) : h.Present x k :=
  ⟨w, hwx, hW, fun ⟨f, hf, hF, hA⟩ => hunseen f hf hF hA⟩

/-! ## No loop -/

/-- Of two guarded forgets of `k`, one after the other, the later saw work by `k` that the
earlier didn't. -/
theorem forgets_need_fresh_work {f₁ f₂ k : Nat} (hg : h.Guarded k) (h₁ : h.forget f₁ k)
    (h₂ : h.forget f₂ k) (h12 : Anc h.par f₁ f₂) (hne : f₁ ≠ f₂) :
    ∃ w, h.work w k ∧ Anc h.par w f₂ ∧ ¬ Anc h.par w f₁ := by
  obtain ⟨w, hw, hW, hn⟩ := hg f₂ h₂
  have hb : h.Below f₂ f₁ := by
    rcases anc_cases h12 with heq | hb
    · exact absurd heq hne
    · exact hb
  exact ⟨w, hW, h.below_anc hw, fun hA => hn ⟨f₁, hb, h₁, hA⟩⟩

/-- Once a forget of `k` has seen all of `k`'s work, no guarded forget of `k` follows it. -/
theorem no_forget_after_complete {f₁ f₂ k : Nat} (hg : h.Guarded k) (h₁ : h.forget f₁ k)
    (hall : ∀ w, h.work w k → Anc h.par w f₁) (h12 : Anc h.par f₁ f₂) (h₂ : h.forget f₂ k) :
    f₂ = f₁ := by
  apply Classical.byContradiction
  intro hne
  obtain ⟨w, hW, _, hn⟩ := h.forgets_need_fresh_work hg h₁ h₂ h12 (fun e => hne e.symm)
  exact hn (hall w hW)

theorem chain_anc {c : Nat → Nat} {n : Nat}
    (hstep : ∀ i, i < n → Anc h.par (c i) (c (i + 1))) :
    ∀ j, j ≤ n → ∀ i, i ≤ j → Anc h.par (c i) (c j) := by
  intro j
  induction j with
  | zero =>
    intro _ i hi
    have : i = 0 := by omega
    subst this
    exact Anc.refl
  | succ j ih =>
    intro hj i hi
    by_cases hij : i = j + 1
    · subst hij; exact Anc.refl
    · exact Anc.trans (ih (by omega) i (by omega)) (hstep j (by omega))

/-- A chain of `n + 1` guarded forgets of `k`, each after the one before, has at least `n + 1`
operations of `k`'s work in the history of its last. -/
theorem forget_chain_bounded (hlt : ParLt h.par) {k n : Nat} (hg : h.Guarded k) {c : Nat → Nat}
    (hF : ∀ i, i ≤ n → h.forget (c i) k)
    (hstep : ∀ i, i < n → Anc h.par (c i) (c (i + 1)) ∧ c i ≠ c (i + 1)) :
    n + 1 ≤ cnt (c n + 1) (fun w => h.work w k ∧ Anc h.par w (c n)) := by
  have hanc := h.chain_anc (c := c) (n := n) (fun i hi => (hstep i hi).1)
  have key : ∀ i, i ≤ n → i + 1 ≤ cnt (c n + 1) (fun w => h.work w k ∧ Anc h.par w (c i)) := by
    intro i
    induction i with
    | zero =>
      intro _
      obtain ⟨w, hw, hW, _⟩ := hg (c 0) (hF 0 (Nat.zero_le n))
      have hA := h.below_anc hw
      have hwle : w ≤ c n :=
        Nat.le_trans (hA.le hlt) ((hanc n (Nat.le_refl n) 0 (Nat.zero_le n)).le hlt)
      have := cnt_lt (B := c n + 1) (P := fun w => h.work w k ∧ Anc h.par w (c 0))
        (Q := fun _ => False) (fun _ _ hq => hq.elim) ⟨w, by omega, ⟨hW, hA⟩, id⟩
      omega
    | succ i ih =>
      intro hi
      have hlt' : cnt (c n + 1) (fun w => h.work w k ∧ Anc h.par w (c i)) <
          cnt (c n + 1) (fun w => h.work w k ∧ Anc h.par w (c (i + 1))) := by
        apply cnt_lt
        · intro w _ ⟨hW, hA⟩
          exact ⟨hW, Anc.trans hA (hstep i (by omega)).1⟩
        · obtain ⟨w, hW, hA, hn⟩ := h.forgets_need_fresh_work hg (hF i (by omega))
            (hF (i + 1) hi) (hstep i (by omega)).1 (hstep i (by omega)).2
          have hwle : w ≤ c n := Nat.le_trans (hA.le hlt) ((hanc n (Nat.le_refl n) (i + 1) hi).le hlt)
          exact ⟨w, by omega, ⟨hW, hA⟩, fun ⟨_, hA'⟩ => hn hA'⟩
      have := ih (by omega)
      omega
  exact key n (Nat.le_refl n)

/-- A forget written where its copy is already absent, as by a `musubi forget` racing a
daemon, changes nothing anywhere. -/
theorem redundant_forget_noop {f k : Nat} (hW : ¬ h.work f k)
    (habs : ¬ h.PresentIn (h.Below f) k) (x j : Nat) :
    (h.addForget f k).Present x j ↔ h.Present x j := by
  have key : ∀ w, h.work w j → ((h.addForget f k).Covered ((h.addForget f k).AncOf x) j w ↔
      h.Covered (h.AncOf x) j w) := by
    intro w hWj
    constructor
    · rintro ⟨g, hg, hF | ⟨rfl, rfl⟩, hA⟩
      · exact ⟨g, hg, hF, hA⟩
      · have hb : h.Below g w := by
          rcases anc_cases hA with rfl | hb
          · exact absurd hWj hW
          · exact hb
        obtain ⟨g', hg', hF', hA'⟩ :=
          Classical.byContradiction fun hn => habs ⟨w, hb, hWj, hn⟩
        exact ⟨g', Anc.trans (h.below_anc hg') hg, hF', hA'⟩
    · rintro ⟨g, hg, hF, hA⟩
      exact ⟨g, hg, Or.inl hF, hA⟩
  constructor
  · rintro ⟨w, hw, hWj, hn⟩
    exact ⟨w, hw, hWj, fun c => hn ((key w hWj).2 c)⟩
  · rintro ⟨w, hw, hWj, hn⟩
    exact ⟨w, hw, hWj, fun c => hn ((key w hWj).1 c)⟩

/-- Two forgets of `k` that saw the same work, as two daemons that fetched the same state
write: wherever the first is, the second changes nothing. -/
theorem concurrent_forget_noop {f₁ f₂ k x : Nat} (h₁ : h.forget f₁ k)
    (hsaw : ∀ w, h.work w k → Anc h.par w f₂ → Anc h.par w f₁) (hx : Anc h.par f₁ x)
    (j : Nat) : (h.addForget f₂ k).Present x j ↔ h.Present x j := by
  have key : ∀ w, h.work w j → ((h.addForget f₂ k).Covered ((h.addForget f₂ k).AncOf x) j w ↔
      h.Covered (h.AncOf x) j w) := by
    intro w hWj
    constructor
    · rintro ⟨g, hg, hF | ⟨rfl, rfl⟩, hA⟩
      · exact ⟨g, hg, hF, hA⟩
      · exact ⟨f₁, hx, h₁, hsaw w hWj hA⟩
    · rintro ⟨g, hg, hF, hA⟩
      exact ⟨g, hg, Or.inl hF, hA⟩
  constructor
  · rintro ⟨w, hw, hWj, hn⟩
    exact ⟨w, hw, hWj, fun c => hn ((key w hWj).2 c)⟩
  · rintro ⟨w, hw, hWj, hn⟩
    exact ⟨w, hw, hWj, fun c => hn ((key w hWj).1 c)⟩

/-! ## Deciding presence -/

/-- `k` is present exactly when some latest work by it is seen by no forget of it: a machine
need check only `k`'s latest work, usually one operation, against `k`'s forgets in `anc*(x)`. -/
theorem present_iff_latest (hlt : ParLt h.par) {x k : Nat} :
    h.Present x k ↔
      ∃ m, h.Latest x k m ∧ ∀ f, Anc h.par f x → h.forget f k → ¬ Anc h.par m f := by
  constructor
  · rintro ⟨w, hw, hW, hn⟩
    obtain ⟨m, ⟨hmx, hmW, hwm⟩, hmax⟩ :=
      exists_max_le (Q := fun m => Anc h.par m x ∧ h.work m k ∧ Anc h.par w m)
        ⟨hw, hW, Anc.refl⟩ (fun m hm => hm.1.le hlt)
    refine ⟨m, ⟨hmx, hmW, fun m' hm'x hm'W hmm' => ?_⟩, fun f hf hF hmf => ?_⟩
    · exact Nat.le_antisymm (hmax m' ⟨hm'x, hm'W, Anc.trans hwm hmm'⟩) (hmm'.le hlt)
    · exact hn ⟨f, hf, hF, Anc.trans hwm hmf⟩
  · rintro ⟨m, ⟨hmx, hmW, _⟩, hno⟩
    exact ⟨m, hmx, hmW, fun ⟨f, hf, hF, hA⟩ => hno f hf hF hA⟩

/-! ## What a machine keeps

Each machine keeps, for every copy present at an operation, its latest work there that no
forget saw (`UMax`), and computes it for an operation from its parents' alone
(`umax_merge`, `umax_work`, `umax_forget`): `Presence::merge` and `Presence::apply` in
`crates/musubi-jj/src/presence.rs`. A copy is present exactly where it has some
(`present_iff_umax`). -/

/-- Work `w` by `k` in `anc*(x)` that no forget of `k` there saw. -/
def Uncov (x k w : Nat) : Prop := Anc h.par w x ∧ h.work w k ∧ ¬ h.Covered (h.AncOf x) k w

/-- `c` is latest such work: no other has `c` in its `anc*`. -/
def UMax (x k c : Nat) : Prop := h.Uncov x k c ∧ ∀ c', h.Uncov x k c' → Anc h.par c c' → c' = c

theorem exists_umax_above (hlt : ParLt h.par) {y k w : Nat} (hu : h.Uncov y k w) :
    ∃ m, h.UMax y k m ∧ Anc h.par w m := by
  obtain ⟨m, ⟨hmu, hwm⟩, hmax⟩ :=
    exists_max_le (Q := fun m => h.Uncov y k m ∧ Anc h.par w m) ⟨hu, Anc.refl⟩
      (fun m hm => hm.1.1.le hlt)
  refine ⟨m, ⟨hmu, fun c' hc' hmc' => ?_⟩, hwm⟩
  exact Nat.le_antisymm (hmax c' ⟨hc', Anc.trans hwm hmc'⟩) (hmc'.le hlt)

theorem present_iff_umax (hlt : ParLt h.par) {x k : Nat} :
    h.Present x k ↔ ∃ c, h.UMax x k c := by
  constructor
  · rintro ⟨w, hw, hW, hn⟩
    obtain ⟨m, hm, -⟩ := h.exists_umax_above hlt ⟨hw, hW, hn⟩
    exact ⟨m, hm⟩
  · rintro ⟨c, ⟨hcx, hW, hn⟩, -⟩
    exact ⟨c, hcx, hW, hn⟩

theorem uncov_work (hlt : ParLt h.par) (hwf : h.WellFormed) {x k : Nat} (hW : h.work x k) :
    h.Uncov x k x := by
  refine ⟨Anc.refl, hW, fun ⟨f, hf, hFk, hA⟩ => hwf.2 x k k hW ?_⟩
  have := Anc.antisymm hlt hf hA
  subst this
  exact hFk

/-- A copy's work is its own latest. -/
theorem umax_work (hlt : ParLt h.par) (hwf : h.WellFormed) {x k c : Nat} (hW : h.work x k) :
    h.UMax x k c ↔ c = x := by
  constructor
  · rintro ⟨⟨hcx, -, -⟩, hmax⟩
    exact (hmax x (h.uncov_work hlt hwf hW) hcx).symm
  · rintro rfl
    exact ⟨h.uncov_work hlt hwf hW, fun c' hc' hcc' => Anc.antisymm hlt hc'.1 hcc'⟩

/-- A forget leaves its copy nothing. -/
theorem umax_forget {x k c : Nat} (hF : h.forget x k) : ¬ h.UMax x k c :=
  fun ⟨⟨hcx, _, hn⟩, _⟩ => hn ⟨x, Anc.refl, hF, hcx⟩

/-- Coverage at an operation that doesn't forget `k` is coverage at one of its parents. -/
theorem covered_parents {x k w : Nat} (hF : ¬ h.forget x k)
    (hc : h.Covered (h.AncOf x) k w) : ∃ p ∈ h.par x, h.Covered (h.AncOf p) k w := by
  obtain ⟨f, hf, hFk, hA⟩ := hc
  rcases anc_cases hf with rfl | ⟨p, hp, hfp⟩
  · exact absurd hFk hF
  · exact ⟨p, hp, f, hfp, hFk, hA⟩

theorem uncov_parent {x p k w : Nat} (hp : p ∈ h.par x) (hwp : Anc h.par w p)
    (hu : h.Uncov x k w) : h.Uncov p k w :=
  ⟨hwp, hu.2.1, fun hc => hu.2.2 (h.covered_mono (Anc.parent hp) hc)⟩

/-- Work after work that no forget saw, in the same history, no forget saw either. -/
theorem uncov_above {x k w w' : Nat} (hu : h.Uncov x k w) (hW : h.work w' k)
    (hww' : Anc h.par w w') (hw'x : Anc h.par w' x) : h.Uncov x k w' :=
  ⟨hw'x, hW, fun ⟨f, hf, hFk, hA⟩ => hu.2.2 ⟨f, hf, hFk, Anc.trans hww' hA⟩⟩

theorem umax_parent {x p k c : Nat} (hp : p ∈ h.par x) (hcp : Anc h.par c p)
    (hm : h.UMax x k c) : h.UMax p k c :=
  ⟨h.uncov_parent hp hcp hm.1, fun c' hc' hcc' =>
    hm.2 c' (h.uncov_above hm.1 hc'.2.1 hcc' (Anc.trans hc'.1 (Anc.parent hp))) hcc'⟩

/-- An operation that is neither work by `k` nor a forget of it keeps the latest work its
parents keep for `k`, each unless a parent whose history has it doesn't keep it: a forget
there saw it, or later work there followed it. -/
theorem umax_merge (hlt : ParLt h.par) {x k c : Nat} (hW : ¬ h.work x k)
    (hF : ¬ h.forget x k) :
    h.UMax x k c ↔
      (∃ p ∈ h.par x, h.UMax p k c) ∧ (∀ p ∈ h.par x, Anc h.par c p → h.UMax p k c) := by
  constructor
  · intro hm
    have hne : c ≠ x := fun e => hW (e ▸ hm.1.2.1)
    obtain ⟨p, hp, hcp⟩ : ∃ p ∈ h.par x, Anc h.par c p := by
      rcases anc_cases hm.1.1 with e | hb
      · exact absurd e hne
      · exact hb
    exact ⟨⟨p, hp, h.umax_parent hp hcp hm⟩, fun p' hp' hcp' => h.umax_parent hp' hcp' hm⟩
  · rintro ⟨⟨p₀, hp₀, hm₀⟩, hclose⟩
    have hu : h.Uncov x k c := by
      refine ⟨Anc.trans hm₀.1.1 (Anc.parent hp₀), hm₀.1.2.1, fun hc => ?_⟩
      obtain ⟨p, hp, f, hfp, hFk, hcf⟩ := h.covered_parents hF hc
      exact (hclose p hp (Anc.trans hcf hfp)).1.2.2 ⟨f, hfp, hFk, hcf⟩
    refine ⟨hu, fun c' hc' hcc' => ?_⟩
    have hne : c' ≠ x := fun e => hW (e ▸ hc'.2.1)
    obtain ⟨p', hp', hc'p'⟩ : ∃ p ∈ h.par x, Anc h.par c' p := by
      rcases anc_cases hc'.1 with e | hb
      · exact absurd e hne
      · exact hb
    obtain ⟨m, hm, hc'm⟩ := h.exists_umax_above hlt (h.uncov_parent hp' hc'p' hc')
    have hmc : m = c :=
      (hclose p' hp' (Anc.trans hcc' hc'p')).2 m hm.1 (Anc.trans hcc' hc'm)
    subst hmc
    exact Anc.antisymm hlt hc'm hcc'

end Hist

end Musubi.Presence

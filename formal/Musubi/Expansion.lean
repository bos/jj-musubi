/-
An implementation that refines a model only after expanding steps: one actual step stands for a
finite, nonempty path of model steps, as an advance that publishes a merge stands for an advance
and a merge, or a write of several operations for several. A step that changes nothing the model
sees is a path of one frame. Concatenating the paths gives a model run whose states at strictly
increasing indices are the actual ones (`concat`), so whatever the model run settles to, the
actual run settles to as well (`stabilizes_of_expansion`), and whatever holds of every model step
from some path on holds of every model step from that path's index on (`concat_tail`).
-/
import Musubi.Basic

namespace Musubi.Expansion

/-- A path of model states `st 0 = a`, …, `st len = b`, each related to the next. -/
structure Path {G : Type} (R : G → G → Prop) (a b : G) where
  len : Nat
  pos : 0 < len
  st : Nat → G
  first : st 0 = a
  last : st len = b
  step : ∀ j, j < len → R (st j) (st (j + 1))

theorem Path.invariant {G : Type} {R : G → G → Prop} {a b : G}
    (p : Path R a b) (P : G → Prop)
    (preserve : ∀ s t, P s → R s t → P t) (ha : P a) : P b := by
  have along : ∀ j, j ≤ p.len → P (p.st j) := by
    intro j
    induction j with
    | zero => intro _; rw [p.first]; exact ha
    | succ j ih => intro hj; exact preserve _ _ (ih (by omega)) (p.step j (by omega))
  rw [← p.last]
  exact along p.len (Nat.le_refl _)

section Concat

variable {G : Type} {R : G → G → Prop} {α : Nat → G} (p : ∀ i, Path R (α i) (α (i + 1)))

/-- One state on: further along the path, or the start of the next. -/
def nextPlace (q : Nat × Nat) : Nat × Nat :=
  if q.2 + 1 < (p q.1).len then (q.1, q.2 + 1) else (q.1 + 1, 0)

/-- Where the `j`th model state is: which path, and how far along it. -/
def place : Nat → Nat × Nat
  | 0 => (0, 0)
  | j + 1 => nextPlace p (place j)

theorem place_succ (j : Nat) : place p (j + 1) = nextPlace p (place p j) := rfl

theorem nextPlace_cases (q : Nat × Nat) :
    (q.2 + 1 < (p q.1).len ∧ nextPlace p q = (q.1, q.2 + 1)) ∨
      (¬ q.2 + 1 < (p q.1).len ∧ nextPlace p q = (q.1 + 1, 0)) := by
  unfold nextPlace
  by_cases h : q.2 + 1 < (p q.1).len
  · left; exact ⟨h, by simp [h]⟩
  · right; exact ⟨h, by simp [h]⟩

/-- The model run: the paths, one after another. -/
def concat (j : Nat) : G := (p (place p j).1).st (place p j).2

/-- Where the `i`th actual state is in the model run. -/
def index : Nat → Nat
  | 0 => 0
  | i + 1 => index i + (p i).len

theorem place_lt (j : Nat) : (place p j).2 < (p (place p j).1).len := by
  induction j with
  | zero => exact (p 0).pos
  | succ j _ =>
    rw [place_succ]
    rcases nextPlace_cases p (place p j) with ⟨h, he⟩ | ⟨_, he⟩ <;> rw [he]
    · exact h
    · exact (p _).pos

theorem place_index (i : Nat) : ∀ o, o < (p i).len → place p (index p i + o) = (i, o) := by
  have along : ∀ i o, o + 1 < (p i).len → place p (index p i + o) = (i, o) →
      place p (index p i + (o + 1)) = (i, o + 1) := by
    intro i o ho h
    rw [show index p i + (o + 1) = index p i + o + 1 by omega, place_succ, h]
    rcases nextPlace_cases p (i, o) with ⟨_, he⟩ | ⟨hn, _⟩
    · exact he
    · exact absurd ho hn
  induction i with
  | zero =>
    intro o
    induction o with
    | zero => intro _; rfl
    | succ o ih => intro ho; exact along 0 o ho (ih (by omega))
  | succ i ih =>
    have hpos := (p i).pos
    have hlast : place p (index p i + ((p i).len - 1)) = (i, (p i).len - 1) :=
      ih _ (by omega)
    have hstart : place p (index p (i + 1)) = (i + 1, 0) := by
      show place p (index p i + (p i).len) = (i + 1, 0)
      rw [show index p i + (p i).len = index p i + ((p i).len - 1) + 1 by omega, place_succ,
        hlast]
      rcases nextPlace_cases p (i, (p i).len - 1) with ⟨h, _⟩ | ⟨_, he⟩
      · exact absurd h (by simp only; omega)
      · exact he
    intro o
    induction o with
    | zero => intro _; exact hstart
    | succ o ih' => intro ho; exact along (i + 1) o ho (ih' (by omega))

theorem concat_index (i : Nat) : concat p (index p i) = α i := by
  have h := place_index p i 0 (p i).pos
  simp only [Nat.add_zero] at h
  unfold concat
  rw [h]
  exact (p i).first

theorem index_lt (i : Nat) : index p i < index p (i + 1) := by
  show index p i < index p i + (p i).len
  have := (p i).pos
  omega

theorem le_index (i : Nat) : i ≤ index p i := by
  induction i with
  | zero => exact Nat.le_refl _
  | succ i ih => have := index_lt p i; omega

/-- A model step of the concatenation is the step of a path from where it is. -/
theorem concat_step_of (S : G → G → Prop) (j : Nat)
    (hS : ∀ o, o < (p (place p j).1).len →
      S ((p (place p j).1).st o) ((p (place p j).1).st (o + 1))) :
    S (concat p j) (concat p (j + 1)) := by
  have hl := place_lt p j
  unfold concat
  rw [place_succ]
  rcases nextPlace_cases p (place p j) with ⟨_, he⟩ | ⟨hn, he⟩ <;> rw [he]
  · exact hS _ hl
  · have heq : (place p j).2 + 1 = (p (place p j).1).len := by omega
    have h := hS _ hl
    rw [heq, (p _).last] at h
    simp only
    rw [(p _).first]
    exact h

/-- Every model step of the concatenation is a step of one of the paths. -/
theorem concat_step (j : Nat) : R (concat p j) (concat p (j + 1)) :=
  concat_step_of p R j fun o ho => (p _).step o ho

theorem place_mono (j : Nat) : (place p j).1 ≤ (place p (j + 1)).1 := by
  rw [place_succ]
  rcases nextPlace_cases p (place p j) with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he]
  · exact Nat.le_refl _
  · exact Nat.le_succ _

theorem place_ge (K : Nat) : ∀ j, index p K ≤ j → K ≤ (place p j).1 := by
  intro j hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction d with
  | zero =>
    have h := place_index p K 0 (p K).pos
    rw [h]
    exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (Nat.le_add_right _ _)) (place_mono p _)

/-- What every step of every path from the `K`th on satisfies, every model step from that
path's index on satisfies. -/
theorem concat_tail (S : G → G → Prop) (K : Nat)
    (hS : ∀ i, K ≤ i → ∀ j, j < (p i).len → S ((p i).st j) ((p i).st (j + 1))) :
    ∀ j, index p K ≤ j → S (concat p j) (concat p (j + 1)) :=
  fun j hj => concat_step_of p S j (hS _ (place_ge p K j hj))

end Concat

/-- An expansion of an actual run into a model run. -/
theorem expand {G : Type} (R : G → G → Prop) (α : Nat → G)
    (hp : ∀ i, Nonempty (Path R (α i) (α (i + 1)))) :
    ∃ (a : Nat → G) (m : Nat → Nat), m 0 = 0 ∧ (∀ i, m i < m (i + 1)) ∧
      (∀ i, a (m i) = α i) ∧ ∀ j, R (a j) (a (j + 1)) := by
  let p : ∀ i, Path R (α i) (α (i + 1)) := fun i => Classical.choice (hp i)
  exact ⟨concat p, index p, rfl, index_lt p, concat_index p, concat_step p⟩

/-- Whatever an expanded model run settles to, the actual run does. -/
theorem stabilizes_of_expansion {G O : Type} (obs : G → O) (α a : Nat → G) (m : Nat → Nat)
    (hm : ∀ i, m i < m (i + 1)) (ha : ∀ i, a (m i) = α i)
    (hs : ∃ k, ∀ j, k ≤ j → obs (a j) = obs (a k)) :
    ∃ k, ∀ i, k ≤ i → obs (α i) = obs (α k) := by
  obtain ⟨K, hK⟩ := hs
  have hindex : ∀ i, i ≤ m i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := hm i; omega
  refine ⟨K, fun i hi => ?_⟩
  rw [← ha i, ← ha K, hK (m i) (by have := hindex i; omega), hK (m K) (hindex K)]

end Musubi.Expansion

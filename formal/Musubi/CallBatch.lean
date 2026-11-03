/-
The driver's finite request list is sent sequentially, not allocated as one physical-id
batch. Virtual slots identify its already planned calls; wire ids are attached only when
each call starts, and other callers or subscriptions may allocate between them. Correlation
needs an injective relabelling of the actual live ids, not order preservation or equality of
the physical and virtual counters. A finite batch completes from fairness of starting and
finishing each individual call; no sync-round completion is assumed.
-/
import Musubi.RetryControl

namespace Musubi.Retry.Batch

/-- Injectivity is required only on actual bound calls plus the reply being checked.
Unsent virtual slots have no wire id and need not extend to a global counter renaming. -/
def InjectiveOn (f : Nat → Nat) (xs : List Nat) : Prop :=
  ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b

theorem finish_relabel (f : Nat → Nat) (xs : List Nat) (id : Nat)
    (hinj : InjectiveOn f (id :: xs)) :
    (xs.filter (· != id)).map f = (xs.map f).filter (· != f id) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have sub : ∀ a, a ∈ id :: xs → a ∈ id :: x :: xs := by
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ha)
    have ht : InjectiveOn f (id :: xs) := fun a ha b hb he => hinj a (sub a ha) b (sub b hb) he
    have he : f x = f id ↔ x = id :=
      ⟨fun h => hinj x (by simp) id (by simp) h, congrArg f⟩
    by_cases hx : x = id
    · subst x; simp [ih ht]
    · have hf : f x ≠ f id := fun h => hx (he.1 h)
      simp [hx, hf, ih ht]

theorem match_relabel (f : Nat → Nat) (xs : List Nat) (id : Nat)
    (hinj : InjectiveOn f (id :: xs)) : (xs.map f).contains (f id) = xs.contains id := by
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem, List.mem_map]
  constructor
  · rintro ⟨x, hx, he⟩
    have hi : x = id := hinj x (by simp [hx]) id (by simp) he
    exact hi ▸ hx
  · intro hi
    exact ⟨id, hi, rfl⟩

structure State where
  remaining : Nat
  active : Bool
  deriving DecidableEq, Repr

def Inv (s : State) : Prop := s.active = true → 0 < s.remaining

inductive Event
  | start
  | finish
  | wait
  deriving DecidableEq

inductive Step : Event → State → State → Prop
  | start (left : Nat) : Step .start ⟨left + 1, false⟩ ⟨left + 1, true⟩
  | finish (left : Nat) : Step .finish ⟨left + 1, true⟩ ⟨left, false⟩
  | wait (s : State) : Step .wait s s

theorem inv_step {e : Event} {s t : State} (hi : Inv s) (hs : Step e s t) : Inv t := by
  cases hs with
  | start => simp [Inv]
  | finish => simp [Inv]
  | wait => exact hi

theorem remaining_mono {e : Event} {s t : State} (hs : Step e s t) :
    t.remaining ≤ s.remaining := by
  cases hs <;> simp

theorem finish_decreases {s t : State} (h : Step .finish s t) :
    t.remaining < s.remaining := by
  cases h
  exact Nat.lt_succ_self _

theorem start_active {s t : State} (h : Step .start s t) : t.active = true := by
  cases h
  rfl

/-- The list may contain one or two calls in the driver, but any finite initial count
works. Completing one call enables starting the next. Shared wire-id interleaving is free. -/
theorem finite_batch_completes (run : Nat → State) (events : Nat → Event)
    (hs : ∀ i, Step (events i) (run i) (run (i + 1)))
    (hstart : ∀ i, 0 < (run i).remaining → (run i).active = false →
      ∃ j, i ≤ j ∧ events j = .start)
    (hfinish : ∀ i, (run i).active = true → ∃ j, i ≤ j ∧ events j = .finish) :
    ∃ k, ∀ i, k ≤ i → (run i).remaining = 0 ∧ (run i).active = false := by
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => (run i).remaining)
    (fun i => remaining_mono (hs i))
  have nofinish : ∀ i, k ≤ i → events i ≠ .finish := by
    intro i hit he
    have h := hs i
    rw [he] at h
    have hlt := finish_decreases h
    rw [hk i hit, hk (i + 1) (by omega)] at hlt
    exact Nat.lt_irrefl _ hlt
  have inactive : ∀ i, k ≤ i → (run i).active = false := by
    intro i hit
    cases ha : (run i).active with
    | false => rfl
    | true =>
      obtain ⟨j, hj, he⟩ := hfinish i ha
      exact False.elim (nofinish j (by omega) he)
  refine ⟨k, fun i hit => ⟨?_, inactive i hit⟩⟩
  apply Classical.byContradiction
  intro hn
  obtain ⟨j, hj, he⟩ := hstart i (by omega) (inactive i hit)
  have h := hs j
  rw [he] at h
  have ha := start_active h
  rw [inactive (j + 1) (by omega)] at ha
  contradiction

end Musubi.Retry.Batch

/-
Time bounds shared by sampled-event proofs. A strictly increasing schedule cannot lag its
index; completing each batch before the next sample also orders events by completion time.

The convergence proof uses this file.
-/
import Musubi.Basic

namespace Musubi.Schedule

variable {sched doneAt : Nat → Nat}

/-- Each sampled event occurs no earlier than its index. -/
theorem index_le (increasing : ∀ p, sched p < sched (p + 1)) : ∀ p, p ≤ sched p
  | 0 => Nat.zero_le _
  | p + 1 => Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (index_le increasing p) (increasing p))

/-- Event order is preserved by the schedule. -/
theorem monotone (increasing : ∀ p, sched p < sched (p + 1)) {p q : Nat} (h : p ≤ q) :
    sched p ≤ sched q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (Nat.le_of_lt (increasing (p + d)))

/-- If one batch completes later, its event started later: each batch completes before the
next event, and no batch completes before its own start. -/
theorem before_of_done_before (increasing : ∀ p, sched p < sched (p + 1))
    (completes : ∀ p, sched p ≤ doneAt (sched p) ∧ doneAt (sched p) + 1 < sched (p + 1))
    {p q : Nat} (h : doneAt (sched q) < doneAt (sched p)) : sched q < sched p := by
  have hqp : q < p := by
    apply Nat.lt_of_not_ge
    intro hpq
    rcases Nat.eq_or_lt_of_le hpq with rfl | hpq
    · exact Nat.lt_irrefl _ h
    · have hnext := monotone increasing (show p + 1 ≤ q by omega)
      have hp := (completes p).2
      have hq := (completes q).1
      omega
  exact Nat.lt_of_lt_of_le (increasing q) (monotone increasing hqp)

end Musubi.Schedule

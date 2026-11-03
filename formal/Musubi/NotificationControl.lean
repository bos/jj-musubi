/-
Old notifications have no request id, so the live-slot theorem does not apply to them.
Instead count the finite logical frames already in flight and queued at the cut. A stream
reader delivers each logical frame once, and a channel receive removes its queue entry.
Receiving an in-flight old frame transfers credit rather than creating it. Later published
notifications come from the current history. No fairness or queue-draining assumption is
needed to bound OLD notification handling, even if fresh notices keep arriving forever.
-/
import Musubi.RetryControl

namespace Musubi.Retry.Notifications

structure State where
  inFlight : Nat
  queued : Nat
  deriving DecidableEq, Repr

def State.credit (s : State) : Nat := s.inFlight + s.queued

inductive Step : State → State → Bool → Prop
  | arrive (flight queued : Nat) :
      Step ⟨flight + 1, queued⟩ ⟨flight, queued + 1⟩ false
  | handle (flight queued : Nat) :
      Step ⟨flight, queued + 1⟩ ⟨flight, queued⟩ true
  | loseFlight (flight queued : Nat) :
      Step ⟨flight + 1, queued⟩ ⟨flight, queued⟩ false
  | loseQueued (flight queued : Nat) :
      Step ⟨flight, queued + 1⟩ ⟨flight, queued⟩ false
  | clear (s : State) : Step s ⟨0, 0⟩ false
  /-- Fresh arrival/handling and unrelated work have no old-frame credit. -/
  | fresh (s : State) : Step s s false

theorem step_credit {s t : State} {handled : Bool} (h : Step s t handled) :
    t.credit + (if handled then 1 else 0) ≤ s.credit := by
  cases h <;> simp [State.credit] <;> omega

theorem old_notifications_stop (run : Nat → State) (handled : Nat → Bool)
    (hs : ∀ i, Step (run i) (run (i + 1)) (handled i)) :
    ∃ k, ∀ i, k ≤ i → handled i = false := by
  have hle : ∀ i, (run (i + 1)).credit ≤ (run i).credit := by
    intro i
    have := step_credit (hs i)
    split at this <;> omega
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => (run i).credit) hle
  refine ⟨k, fun i hi => ?_⟩
  have h := step_credit (hs i)
  rw [hk i hi, hk (i + 1) (by omega)] at h
  cases he : handled i <;> simp_all <;> omega

end Musubi.Retry.Notifications

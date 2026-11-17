/-
Notifications already sent when the cut is taken carry no request id, so the live-slot
theorem does not cover them. Instead, count the finite logical frames in flight or queued at
the cut as credit. A stream reader delivers each logical frame once, and a channel receive
removes its queue entry, so receiving an in-flight frame moves credit from `inFlight` to
`queued` and handling one spends it. Notifications published after the cut come from the
current history and carry no credit. Hence only finitely many pre-cut notifications are
ever handled, however many fresh notices keep arriving.

The convergence proof uses this file.
-/
import Musubi.RetryControl

namespace Musubi.Retry.Notifications

/-- Credit: the pre-cut frames still in flight or queued. -/
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
  /-- Fresh arrival or handling, and unrelated work; these touch no pre-cut frame. -/
  | fresh (s : State) : Step s s false

/-- A step never raises credit, and a handling step lowers it by one. -/
theorem step_credit {s t : State} {handled : Bool} (h : Step s t handled) :
    t.credit + (if handled then 1 else 0) ≤ s.credit := by
  cases h <;> simp [State.credit] <;> omega

/-- Pre-cut notifications are handled only finitely often. -/
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

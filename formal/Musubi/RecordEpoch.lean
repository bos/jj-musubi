/-
Finite record adoptions and stale-plan restarts once the hub's ordered records stop changing
and obsolete callbacks stop. A carried old announcement or persistent receipt may still
require reconciliation; every subsequent fresh Fetched announces the fixed list. Adoption may
invalidate a retained realization plan. A stale-plan error reopens the daemon, clearing its
plan and announcement, and resetting knowledge in the full control state. This projection
forgets knowledge, so it does not pretend that restart preserves the local progress rank.
-/
import Musubi.RetryControl

namespace Musubi.Retry.Records

/-- Record identities stand for complete ordered lists, rather than flattened drop sets.
`stalePlan` is conservative: adoption can invalidate a retained plan; a fresh survey under
unchanged records cannot. Ordinary I/O failures are outside this successful local suffix. -/
structure State where
  applied : Nat
  announced : Option Nat
  stalePlan : Bool
  receipts : Bool
  deriving DecidableEq, Repr

def State.recordCredit (R : Nat) (s : State) : Nat :=
  if ∃ A, s.announced = some A ∧ A ≠ R then 2
  else if s.applied ≠ R ∨ s.receipts = true then 1 else 0

def State.credit (R : Nat) (s : State) : Nat :=
  2 * s.recordCredit R + if s.stalePlan then 1 else 0

def State.fetched (s : State) (R : Nat) : State :=
  { s with announced := if R = s.applied ∧ s.receipts = false then none else some R }

def State.adopt (_s : State) (A : Nat) : State :=
  ⟨A, none, true, false⟩

def State.reopen (s : State) : State := ⟨s.applied, none, false, s.receipts⟩

inductive Step (R : Nat) : State → State → Bool → Bool → Prop
  | fetched (s : State) : Step R s (s.fetched R) false false
  | keepReceipt (s : State) (A : Nat) (ha : s.announced = some A) (hne : A ≠ s.applied) :
      Step R s { s with receipts := true } false false
  | adopt (s : State) (A : Nat) (ha : s.announced = some A)
      (hne : A ≠ s.applied ∨ s.receipts = true) :
      Step R s (s.adopt A) true false
  | staleFailure (s : State) (hp : s.stalePlan = true) :
      Step R s s.reopen false true
  | clearPlan (s : State) : Step R s { s with stalePlan := false } false false
  | wait (s : State) : Step R s s false false

/-- Executable control at the native receipt boundary, including an equal-record adoption.
The flags count actual adoptions and stale-plan failures. -/
inductive Action
  | fetched | keepReceipt (records : Nat) | adopt (records : Nat)
  | staleFailure | clearPlan | wait
  deriving Repr

def exec (R : Nat) (s : State) : Action → Option (State × Bool × Bool)
  | .fetched => some (s.fetched R, false, false)
  | .keepReceipt A =>
    if s.announced = some A ∧ A ≠ s.applied then
      some ({ s with receipts := true }, false, false) else none
  | .adopt A =>
    if s.announced = some A ∧ (A ≠ s.applied ∨ s.receipts = true) then
      some (s.adopt A, true, false) else none
  | .staleFailure => if s.stalePlan then some (s.reopen, false, true) else none
  | .clearPlan => some ({ s with stalePlan := false }, false, false)
  | .wait => some (s, false, false)

theorem exec_sound {R : Nat} {s t : State} {a : Action} {adopts fails : Bool}
    (h : exec R s a = some (t, adopts, fails)) : Step R s t adopts fails := by
  cases a with
  | fetched => cases h; exact .fetched _
  | keepReceipt A =>
    simp only [exec] at h
    split at h
    · rename_i hg; cases h; exact .keepReceipt _ A hg.1 hg.2
    · contradiction
  | adopt A =>
    simp only [exec] at h
    split at h
    · rename_i hg; cases h; exact .adopt _ A hg.1 hg.2
    · contradiction
  | staleFailure =>
    simp only [exec] at h
    split at h
    · rename_i hg; cases h; exact .staleFailure _ hg
    · contradiction
  | clearPlan => cases h; exact .clearPlan _
  | wait => cases h; exact .wait _

theorem adopt_record_credit {R A : Nat} {s : State}
    (ha : s.announced = some A) (hne : A ≠ s.applied ∨ s.receipts = true) :
    (s.adopt A).recordCredit R + 1 ≤ s.recordCredit R := by
  by_cases hA : A = R <;> by_cases hap : s.applied = R <;> cases hr : s.receipts <;>
    simp [State.recordCredit, State.adopt, ha, hA, hap, hr] at * <;> omega

/-- Both adoption and an error/reopen spend finite debt. In particular the error may reset
known and discard the whole plan in the full state; no unchanged-known premise is used. -/
theorem step_credit {R : Nat} {s t : State} {adopts fails : Bool}
    (h : Step R s t adopts fails) :
    t.credit R + (if adopts then 1 else 0) + (if fails then 1 else 0) ≤ s.credit R := by
  cases h with
  | fetched =>
    have hpa : (R = s.applied) ↔ s.applied = R := eq_comm
    by_cases hap : s.applied = R <;>
      by_cases ho : ∃ A, s.announced = some A ∧ A ≠ R <;>
      cases hp : s.stalePlan <;> cases hr : s.receipts <;>
      simp [State.credit, State.recordCredit, State.fetched, hap, ho, hr, hp, hpa]
  | keepReceipt A ha hne =>
    by_cases hA : A = R <;> by_cases hap : s.applied = R <;>
      cases hr : s.receipts <;> cases hp : s.stalePlan <;>
      simp [State.credit, State.recordCredit, ha, hA, hap, hr, hp] at * <;> omega
  | adopt A ha hne =>
    have hc := adopt_record_credit (R := R) ha hne
    change 2 * (s.adopt A).recordCredit R + 1 + 1 + 0 ≤
      2 * s.recordCredit R + (if s.stalePlan then 1 else 0)
    cases s.stalePlan <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  | staleFailure hp =>
    have hr : s.reopen.recordCredit R ≤ s.recordCredit R := by
      by_cases hap : s.applied = R <;>
        by_cases ha : ∃ A, s.announced = some A ∧ A ≠ R <;> cases hr : s.receipts <;>
        simp [State.recordCredit, State.reopen, hap, ha, hr]
    change 2 * s.reopen.recordCredit R + 0 + 0 + 1 ≤
      2 * s.recordCredit R + (if s.stalePlan then 1 else 0)
    simp only [hp, ↓reduceIte]
    omega
  | clearPlan =>
    simp only [State.credit, State.recordCredit, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    split <;> omega
  | wait => simp

/-- The finite prefix may leave an old announcement and an invalid retained plan. Fresh
replies cannot recharge that old-record debt, and each stale-plan reopen clears its cause.
Consequently both kinds of disturbance stop, without assuming any sync round completes. -/
theorem record_disturbances_stop (R : Nat) (run : Nat → State)
    (adopts fails : Nat → Bool)
    (hs : ∀ i, Step R (run i) (run (i + 1)) (adopts i) (fails i)) :
    ∃ k, ∀ i, k ≤ i → adopts i = false ∧ fails i = false := by
  have hle : ∀ i, (run (i + 1)).credit R ≤ (run i).credit R := by
    intro i
    have := step_credit (hs i)
    split at this <;> split at this <;> omega
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => (run i).credit R) hle
  refine ⟨k, fun i hi => ?_⟩
  have h := step_credit (hs i)
  rw [hk i hi, hk (i + 1) (by omega)] at h
  cases ha : adopts i <;> cases hf : fails i <;> simp_all <;> omega

end Musubi.Retry.Records

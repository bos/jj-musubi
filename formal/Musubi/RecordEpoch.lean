/-
A node's record adoptions and stale-plan restarts are finite once the hub's ordered record
list `R` stops changing and obsolete callbacks stop. A carried-over old announcement or a
persistent receipt may still need reconciling; every fresh Fetched announces `R`. Adopting
records may invalidate the node's retained realization plan. A stale-plan error reopens the
daemon, clearing its plan and announcement; in the full control state it also resets the
node's knowledge. This projection omits knowledge, so it makes no claim that a restart
preserves the local progress rank.

The convergence proof uses this file except `exec_sound` and the `Guard` facts.
-/
import Musubi.RetryControl

namespace Musubi.Retry.Records

/-- The core's effective announcement guard: an announcement needs action if it differs from
the applied list, or if receipts are held even when the lists are equal. It reads the stored
announcement, before `NodeCore::step` takes it. -/
def needsRecords {α : Type} [DecidableEq α] (applied : α) (announced : Option α)
    (receipts : Bool) : Bool :=
  match announced with
  | none => false
  | some A => decide (A ≠ applied) || receipts

/-- In an active round, receipts are held only with an announcement. So if the guard is false,
no receipts are held, even when the announced records equal the applied ones. -/
theorem no_receipts_when_quiet {α : Type} [DecidableEq α] (applied : α)
    (announced : Option α) (receipts : Bool)
    (hguard : receipts = true → announced ≠ none)
    (hquiet : needsRecords applied announced receipts = false) : receipts = false := by
  cases hr : receipts
  · rfl
  · cases ha : announced with
    | none => exact False.elim (hguard hr ha)
    | some A => simp [needsRecords, ha, hr] at hquiet

/-- A node's record state. A `Nat` identifies a complete ordered record list. `stalePlan` is
conservative: adoption can invalidate a retained plan, and a fresh survey under unchanged
records cannot. Other failures may reset control without spending stale-plan debt. -/
structure State where
  /-- The record list the node has applied. -/
  applied : Nat
  /-- The list the hub last announced to the node, if any. -/
  announced : Option Nat
  /-- The retained realization plan may be invalid. -/
  stalePlan : Bool
  /-- The node holds custody of a prepared adoption (a persistent receipt). -/
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
  /-- An ordinary failure or an unsatisfied object reply can reopen with no stale plan. It
  never raises the debt and is not counted as a stale-plan failure. -/
  | reopen (s : State) : Step R s s.reopen false false
  | clearPlan (s : State) : Step R s { s with stalePlan := false } false false
  | wait (s : State) : Step R s s false false

/-- Executable control actions at the native receipt boundary, including adoption of an equal
record list. `exec` reports whether an action adopted records and whether it was a stale-plan
failure. -/
inductive Action
  | fetched | keepReceipt (records : Nat) | adopt (records : Nat)
  | staleFailure | reopen | clearPlan | wait
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
  | .reopen => some (s.reopen, false, false)
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
  | reopen => cases h; exact .reopen _
  | clearPlan => cases h; exact .clearPlan _
  | wait => cases h; exact .wait _

theorem adopt_record_credit {R A : Nat} {s : State}
    (ha : s.announced = some A) (hne : A ≠ s.applied ∨ s.receipts = true) :
    (s.adopt A).recordCredit R + 1 ≤ s.recordCredit R := by
  by_cases hA : A = R <;> by_cases hap : s.applied = R <;> cases hr : s.receipts <;>
    simp [State.recordCredit, State.adopt, ha, hA, hap, hr] at * <;> omega

/-- Adoptions and stale-plan failures each spend one unit of a finite credit. Other reopens may
leave it as it was but never raise it; that they eventually stop is not shown here. A reopen
may reset knowledge and discard the whole plan. -/
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
  | reopen =>
    have hr : s.reopen.recordCredit R ≤ s.recordCredit R := by
      by_cases hap : s.applied = R <;>
        by_cases ha : ∃ A, s.announced = some A ∧ A ≠ R <;> cases hr : s.receipts <;>
        simp [State.recordCredit, State.reopen, hap, ha, hr]
    change 2 * s.reopen.recordCredit R + 0 + 0 ≤
      2 * s.recordCredit R + (if s.stalePlan then 1 else 0)
    split <;> omega
  | clearPlan =>
    simp only [State.credit, State.recordCredit, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    split <;> omega
  | wait => simp

/-- Adoptions and stale-plan failures both eventually stop. The finite prefix before the cut
may leave an old announcement and an invalid plan. Fresh replies cannot add to that debt, and
each stale-plan reopen clears its cause. No sync round is assumed to complete. -/
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

/-- A reopened core is inactive until its first Fetch reply. Once active, it holds a receipt
only with an announcement: preparing keeps the announcement until taking consumes the
receipt. -/
def State.Guard (s : State) (active : Bool) : Prop :=
  active = true → s.receipts = true → s.announced ≠ none

theorem State.guard_fetched (s : State) (R : Nat) (active : Bool) :
    (s.fetched R).Guard active := by
  intro _ hr
  simp [State.fetched] at hr ⊢
  simp [hr]

/-- The native round-phase law: a round activates only after its first Fetch, and a reopen
leaves it inactive. The premise `hreopen` is stated on the action, because a reopen's output
state can equal that of a quiet wait, so states alone cannot tell them apart. Every other
reply and local step preserves the guard. -/
theorem step_guard {R : Nat} {s t : State} {a : Action} {adopts fails active active' : Bool}
    (hs : exec R s a = some (t, adopts, fails)) (hi : s.Guard active)
    (hactivate : active' = true → active = true ∨ t = s.fetched R)
    (hreopen : a = .staleFailure ∨ a = .reopen → active' = false) : t.Guard active' := by
  have same (hr : t.receipts = s.receipts) (ha : t.announced = s.announced) :
      t.Guard active' := by
    intro hact hreceipt
    rcases hactivate hact with hact | ht
    · rw [ha]
      apply hi hact
      rwa [hr] at hreceipt
    · rw [ht] at hreceipt ⊢
      exact State.guard_fetched s R active' hact hreceipt
  cases a with
  | fetched => cases hs; exact State.guard_fetched _ _ _
  | keepReceipt A =>
    simp only [exec] at hs
    split at hs
    · rename_i hg
      cases hs
      intro _ _
      change s.announced ≠ none
      simp [hg.1]
    · contradiction
  | adopt A =>
    simp only [exec] at hs
    split at hs
    · cases hs; intro _ h; simp [State.adopt] at h
    · contradiction
  | staleFailure =>
    simp only [exec] at hs
    split at hs
    · cases hs
      intro hact _
      rw [hreopen (Or.inl rfl)] at hact
      cases hact
    · contradiction
  | reopen =>
    cases hs
    intro hact _
    rw [hreopen (Or.inr rfl)] at hact
    cases hact
  | clearPlan => cases hs; exact same rfl rfl
  | wait => cases hs; exact same rfl rfl

end Musubi.Retry.Records

/-
The actual executable action list, not a separately chosen abstract run. These results
derive complete-record responsibility at every constructed body write. Native observation
simulation and preservation of ConstructionInvariant along this same trace remain distinct.
-/
import Musubi.NativeLifecycle.ConstructionSound

namespace Musubi.NativeLifecycle

inductive Runs : State → List Action → State → Prop where
  | nil (s : State) : Runs s [] s
  | cons {s t u : State} {action : Action} {actions : List Action} :
      step s action = .ok t → Runs t actions u → Runs s (action :: actions) u

theorem run_has_trace {initial final : State} {actions : List Action}
    (success : run initial actions = .ok final) : Runs initial actions final := by
  induction actions generalizing initial with
  | nil => cases success; exact .nil _
  | cons action actions ih =>
    simp only [run, List.foldlM_cons] at success
    cases next : step initial action with
    | error gap => simp [next, bind, Except.bind] at success
    | ok intermediate =>
      simp only [next, bind, Except.bind] at success
      exact .cons next (ih success)

def responsible (s : State) (records : List Record) : Prop :=
  ∀ record, record ∈ records → record ∈ s.saved.applied ++ s.saved.custody

theorem writeReceiptCanonical_records {s t : State} {index : Nat} {plan : ReceiptBuild}
    (success : step s (.writeReceiptCanonical index) = .ok t)
    (bound : s.receiptPlan = some plan) : responsible s plan.computed.records := by
  cases held : plan.computed.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    cases body : plan.canonicalWrites[index]? <;>
      simp only [step, bound, body, held, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Bool.not_false] at success
    all_goals repeat (split at success <;> simp_all)
    all_goals cases success

theorem writeReceiptNative_records {s t : State} {index : Nat} {plan : ReceiptBuild}
    (success : step s (.writeReceiptNative index) = .ok t)
    (bound : s.receiptPlan = some plan) : responsible s plan.computed.records := by
  cases held : plan.computed.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    cases body : plan.nativeWrites[index]? <;>
      simp only [step, bound, body, held, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Bool.not_false] at success
    all_goals repeat (split at success <;> simp_all)
    all_goals cases success

def NamedWriteCustody (s : State) : Action → Prop
  | .writeReceiptCanonical _ | .writeReceiptNative _ =>
      ∀ plan, s.receiptPlan = some plan → responsible s plan.computed.records
  | .writeRender _ => ∀ plan receipt, s.renderPlan = some plan →
      plan.receipt = some receipt → responsible s receipt.records
  | _ => True

theorem step_named_custody {s t : State} {action : Action}
    (success : step s action = .ok t) : NamedWriteCustody s action := by
  cases action <;> try exact True.intro
  · intro plan bound; exact writeReceiptCanonical_records success bound
  · intro plan bound; exact writeReceiptNative_records success bound
  · intro plan receipt bound captured; exact writeRender_captured_records success bound captured

inductive CustodyAlong : State → List Action → State → Prop where
  | nil (s : State) : CustodyAlong s [] s
  | cons {s t u : State} {action : Action} {actions : List Action} :
      step s action = .ok t → NamedWriteCustody s action →
      CustodyAlong t actions u → CustodyAlong s (action :: actions) u

theorem runs_named_custody {s t : State} {actions : List Action} (execution : Runs s actions t) :
    CustodyAlong s actions t := by
  induction execution with
  | nil => exact .nil _
  | cons accepted _ ih => exact .cons accepted (step_named_custody accepted) ih

/-- The certificate is about the same action sequence actually run by the fixture codec.
It assumes no native refinement, source answer or already-correct receipt. -/
def certifiedRun (initial : State) (actions : List Action) :
    Except StepError { final : State // ∃ _execution : Runs initial actions final,
      CustodyAlong initial actions final } :=
  match success : run initial actions with
  | .error gap => .error gap
  | .ok final => .ok ⟨final, ⟨run_has_trace success, runs_named_custody (run_has_trace success)⟩⟩

/-- This is the remaining same-run policy target, not an assumed precondition of the
certificate above. Establishing custody along a run does not establish source-policy or
prepared-origin preservation, nor its simulation by the actual native call. -/
inductive ConstructionAlong : State → List Action → State → Prop where
  | nil {s : State} : ConstructionInvariant s → ConstructionAlong s [] s
  | cons {s t u : State} {action : Action} {actions : List Action} :
      ConstructionInvariant s → step s action = .ok t →
      ConstructionAlong t actions u → ConstructionAlong s (action :: actions) u

def ConstructionRun (initial : State) (actions : List Action) (final : State) : Prop :=
  Runs initial actions final ∧ ConstructionAlong initial actions final ∧
    CustodyAlong initial actions final

end Musubi.NativeLifecycle

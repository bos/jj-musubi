/-
The actual executable action list, not a separately chosen abstract run. These results
derive complete-record responsibility and historical construction policy along that trace.
Native observation authentication and simulation remain distinct obligations.
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
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases held : plan.computed.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    cases body : plan.canonicalWrites[index]? <;>
      simp only [stepCore, bound, body, held, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Bool.not_false] at accepted
    all_goals repeat (split at accepted <;> simp_all)
    all_goals cases accepted

theorem writeReceiptNative_records {s t : State} {index : Nat} {plan : ReceiptBuild}
    (success : step s (.writeReceiptNative index) = .ok t)
    (bound : s.receiptPlan = some plan) : responsible s plan.computed.records := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases held : plan.computed.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    cases body : plan.nativeWrites[index]? <;>
      simp only [stepCore, bound, body, held, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Bool.not_false] at accepted
    all_goals repeat (split at accepted <;> simp_all)
    all_goals cases accepted

def NamedWriteCustody (s : State) : Action → Prop
  | .writeReceiptCanonical _ | .writeReceiptNative _ =>
      ∀ plan, s.receiptPlan = some plan → responsible s plan.computed.records
  | .writeRender _ => ∀ plan receipt, s.renderPlan = some plan →
      plan.receipt = some receipt → responsible s receipt.records
  | .refreshCurrentGit => ∀ prepared plan git build receipt,
      s.prepared = some prepared → s.publication = some plan → s.git = some git →
      git.useCurrent = true →
      constructCurrentGit s.evidence s.nativeFacts s.heads prepared.inputs.target plan.incoming =
        .ok build → build.writes = true → prepared.inputs.receipt = some receipt →
      responsible s receipt.records
  | _ => True

theorem step_named_custody {s t : State} {action : Action}
    (success : step s action = .ok t) : NamedWriteCustody s action := by
  cases action <;> try exact True.intro
  · intro plan bound; exact writeReceiptCanonical_records success bound
  · intro plan bound; exact writeReceiptNative_records success bound
  · intro plan receipt bound captured; exact writeRender_captured_records success bound captured
  · intro prepared plan git build receipt bound publication choice uses computed writes captured
    exact refreshCurrentGit_records success bound publication choice uses computed writes captured

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

/-- Route observations follow the same executed actions, and are absent after every
unframed route-changing/unknown effect. This does not authenticate native frame laws. -/
inductive SourceRoutesAlong : State → List Action → State → Prop where
  | nil (s : State) : SourceRoutesAlong s [] s
  | cons {s t u : State} {action : Action} {actions : List Action} :
      step s action = .ok t → SourceRouteTransition s action t →
      SourceRoutesAlong t actions u → SourceRoutesAlong s (action :: actions) u

theorem runs_source_routes {s t : State} {actions : List Action} (execution : Runs s actions t) :
    SourceRoutesAlong s actions t := by
  induction execution with
  | nil => exact .nil _
  | cons accepted _ ih => exact .cons accepted (step_source_routes accepted) ih

/-- The certificate is about the same action sequence actually run by the fixture codec.
It assumes no native refinement, source answer or already-correct receipt. -/
def certifiedRun (initial : State) (actions : List Action) :
    Except StepError { final : State // ∃ _execution : Runs initial actions final,
      CustodyAlong initial actions final ∧ SourceRoutesAlong initial actions final } :=
  match success : run initial actions with
  | .error gap => .error gap
  | .ok final => .ok ⟨final, ⟨run_has_trace success,
      runs_named_custody (run_has_trace success), runs_source_routes (run_has_trace success)⟩⟩

/-- Planning-state construction policy along the exact executed action list. Native
authentication/simulation and policy recomputed after external mutations are separate. -/
inductive ConstructionAlong : State → List Action → State → Prop where
  | nil {s : State} : ConstructionInvariant s → ConstructionAlong s [] s
  | cons {s t u : State} {action : Action} {actions : List Action} :
      ConstructionInvariant s → step s action = .ok t →
      ConstructionAlong t actions u → ConstructionAlong s (action :: actions) u

def ConstructionRun (initial : State) (actions : List Action) (final : State) : Prop :=
  Runs initial actions final ∧ ConstructionAlong initial actions final ∧
    CustodyAlong initial actions final

theorem runs_construction {initial final : State} {actions : List Action}
    (execution : Runs initial actions final) (admitted : actions.all constructedAction = true)
    (initialConstruction : ConstructionInvariant initial) :
    ConstructionAlong initial actions final := by
  revert admitted initialConstruction
  induction execution with
  | nil =>
    intro _ initialConstruction
    exact .nil initialConstruction
  | cons accepted _ ih =>
    intro admitted initialConstruction
    simp only [List.all_cons, Bool.and_eq_true] at admitted
    have next := construction_step_preserves initialConstruction admitted.1 accepted
    exact .cons initialConstruction accepted (ih admitted.2 next)

/-- The public construction certificate starts from raw observations with every plan slot
empty. Its initial invariant is proved here, not supplied by the caller. The only program
restriction is the already declared four raw observation shortcuts. No source/receipt/
output correctness or native-refinement bundle is accepted as a premise. -/
def certifiedConstructionRun (me : Copy) (evidence : Evidence) (heads : List Physical)
    (saved : Persistent) (facts : NativeFacts) (physicalGit : Nat) (actions : List Action) :
    Except StepError { final : State //
      ConstructionRun (rawInitial me evidence heads saved facts physicalGit) actions final ∧
      SourceRoutesAlong (rawInitial me evidence heads saved facts physicalGit) actions final } :=
  if admitted : actions.all constructedAction = true then
    match success : run (rawInitial me evidence heads saved facts physicalGit) actions with
    | .error gap => .error gap
    | .ok final =>
      let execution := run_has_trace success
      .ok ⟨final, ⟨⟨execution,
        runs_construction execution admitted
          (rawInitial_construction me evidence heads saved facts physicalGit),
        runs_named_custody execution⟩, runs_source_routes execution⟩⟩
  else .error (.evidence (.nativeFact "raw shortcut outside constructed program"))

end Musubi.NativeLifecycle

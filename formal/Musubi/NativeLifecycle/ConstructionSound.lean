/-
Pure obligations discharged by the actual constructors. These do not authenticate the raw
native tables. The reachable policy invariant and Rust simulation must use these same
constructors, rather than the prototype receive/prepare observation actions.
-/
import Musubi.NativeLifecycle.Steps

namespace Musubi.NativeLifecycle

theorem encodeNative_observed {e : Evidence} {table : EncodingTable}
    {body result : NativeBody} (h : encodeNative e table body = .ok result) :
    result ∈ e.native ++ table.native ∧ sameNativeShape body result = true := by
  unfold encodeNative at h
  dsimp only at h
  cases hm : unique ((e.native ++ table.native).filter (sameNativeShape body)) with
  | nil =>
    rw [hm] at h
    cases h
  | cons first rest =>
    cases rest with
    | nil =>
      rw [hm] at h
      have hr : first = result := Except.ok.inj h
      subst result
      have member : first ∈ unique ((e.native ++ table.native).filter
          (sameNativeShape body)) := by rw [hm]; exact List.mem_cons_self
      have filtered : first ∈ (e.native ++ table.native).filter (sameNativeShape body) := by
        simpa [unique] using member
      exact List.mem_filter.mp filtered
    | cons other more =>
      rw [hm] at h
      cases h

theorem encodeCanonical_observed {e : Evidence} {table : EncodingTable}
    {body result : CanonicalBody} (h : encodeCanonical e table body = .ok result) :
    result ∈ e.canonical ++ table.canonical ∧ sameCanonicalShape body result = true := by
  unfold encodeCanonical at h
  dsimp only at h
  cases hm : unique ((e.canonical ++ table.canonical).filter (sameCanonicalShape body)) with
  | nil =>
    rw [hm] at h
    cases h
  | cons first rest =>
    cases rest with
    | nil =>
      rw [hm] at h
      have hr : first = result := Except.ok.inj h
      subst result
      have member : first ∈ unique ((e.canonical ++ table.canonical).filter
          (sameCanonicalShape body)) := by rw [hm]; exact List.mem_cons_self
      have filtered : first ∈ (e.canonical ++ table.canonical).filter
          (sameCanonicalShape body) := by simpa [unique] using member
      exact List.mem_filter.mp filtered
    | cons other more =>
      rw [hm] at h
      cases h

/-- Successful comparison retains every computed image, including changed mappings absent
from a sparse raw map. This depends on computed locals, never a supplied correct-map premise. -/
theorem receiptInputMatches_images {build : ReceiptBuild} {observed : Receipt}
    (h : receiptInputMatches build observed = true) {row : Physical × List Physical}
    (member : row ∈ build.computed.locals) :
    (lookup observed.locals row.1).getD [row.1] = row.2 := by
  simp only [receiptInputMatches, Bool.and_eq_true] at h
  have hall := h.2
  exact of_decide_eq_true (List.all_eq_true.mp hall row member)

theorem receiptInputMatches_no_extra {build : ReceiptBuild} {observed : Receipt}
    (h : receiptInputMatches build observed = true) {row : Physical × List Physical}
    (member : row ∈ observed.locals) : (lookup build.computed.locals row.1).isSome = true := by
  simp only [receiptInputMatches, Bool.and_eq_true] at h
  have hall := h.1.2
  exact List.all_eq_true.mp hall row member

/-- An adapter-owned native helper is an actual operation-creating action, but cannot
silently allocate canonical identities or classify itself as an external E1/E2 actor. -/
theorem ownHelper_frame {s t : State} {index : Nat}
    (success : step s (.ownHelper index) = .ok t) :
    t.outside = s.outside ∧ t.allocatedLabels = s.allocatedLabels ∧
      t.createdCanonicals = s.createdCanonicals := by
  cases outcome : helperOutcome s index with
  | error gap => simp [step, outcome, Functor.map, Except.map] at success
  | ok result =>
    simp [step, outcome, Functor.map, Except.map] at success
    subst t
    exact ⟨rfl, rfl, rfl⟩

/-- Successful execution requires responsibility for the plan's captured receipt, even
when another action could have changed the current receipt. No custody result is assumed. -/
theorem writeRender_captured_records {s t : State} {index : Nat} {plan : RenderBuild}
    {receipt : Receipt} (success : step s (.writeRender index) = .ok t)
    (bound : s.renderPlan = some plan) (captured : plan.receipt = some receipt) :
    ∀ record, record ∈ receipt.records → record ∈ s.saved.applied ++ s.saved.custody := by
  cases held : receipt.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    cases node : plan.nodes[index]? <;>
      simp only [step, bound, captured, node, held, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Bool.not_false] at success
    all_goals repeat (split at success <;> simp_all)

theorem writeRender_current {s t : State} {index : Nat} {plan : RenderBuild}
    (success : step s (.writeRender index) = .ok t) (bound : s.renderPlan = some plan) :
    renderPlanCurrent s plan = true := by
  cases current : renderPlanCurrent s plan with
  | true => rfl
  | false =>
    simp [step, bound, current, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at success

theorem renderPlanCurrent_receipt {s : State} {plan : RenderBuild}
    (current : renderPlanCurrent s plan = true) : s.receipt = plan.receipt := by
  simp only [renderPlanCurrent, Bool.and_eq_true] at current
  exact of_decide_eq_true current.2

theorem startRecovery_invalidates (s : State) :
    (step s .startRecovery).map (fun t =>
      (t.renderPlan, t.receiptPlan, t.prepared, t.receipt, t.saved)) =
        .ok (none, none, none, none, s.saved) := rfl

theorem interrupt_invalidates (s : State) :
    (step s .interrupt).map (fun t =>
      (t.renderPlan, t.receiptPlan, t.prepared, t.receipt, t.saved)) =
        .ok (none, none, none, none, s.saved) := rfl

theorem finish_invalidates {s t : State} (success : step s .finish = .ok t) :
    t.renderPlan = none ∧ t.receiptPlan = none ∧ t.prepared = none ∧
      t.receipt = none ∧ t.saved.custody = s.saved.custody := by
  simp only [step, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    pure, Except.pure] at success
  split at success
  · cases success
  · cases success
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The proof target for the constructed sublanguage is provenance plus policy facts about
the same actual run. Raw observation shortcuts cannot establish computed preparation. -/
def constructedAction : Action → Bool
  | .receive _ | .prepare _ _ | .write _ | .helperHeads _ => false
  | _ => true

def ReceiptOrigin (plan : ReceiptBuild) : Prop :=
  ∃ before facts saved me heads request,
    constructReceipt before facts saved me heads request = .ok plan

def RenderOrigin (plan : RenderBuild) : Prop :=
  ∃ before facts me heads receipt target,
    constructRender before facts me heads receipt target = .ok plan

theorem planReceipt_origin {s t : State} {request : ReceiptRequest}
    (success : step s (.planReceipt request) = .ok t) :
    ∃ plan, t.receiptPlan = some plan ∧ ReceiptOrigin plan := by
  cases computed : constructReceipt s.evidence s.nativeFacts s.saved s.me s.heads request with
  | error gap =>
    simp only [step, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at success
    all_goals repeat (split at success <;> simp_all)
    all_goals subst t
    all_goals simp_all
  | ok plan =>
    have origin : ReceiptOrigin plan :=
      ⟨s.evidence, s.nativeFacts, s.saved, s.me, s.heads, request, computed⟩
    simp only [step, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at success
    all_goals repeat (split at success <;> simp_all)
    all_goals subst t
    all_goals simp_all

theorem planRender_origin {s t : State} {target : Canonical}
    (success : step s (.planRender target) = .ok t) :
    ∀ plan, t.renderPlan = some plan → RenderOrigin plan := by
  cases computed : constructRender s.evidence s.nativeFacts s.me s.heads s.receipt target with
  | error gap =>
    simp only [step, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at success
    all_goals repeat (split at success <;> simp_all)
    all_goals subst t
    all_goals simp_all
  | ok result =>
    have origin : RenderOrigin result :=
      ⟨s.evidence, s.nativeFacts, s.me, s.heads, s.receipt, target, computed⟩
    simp only [step, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at success
    all_goals repeat (split at success <;> simp_all)
    all_goals subst t
    all_goals simp_all

/-- This records a genuine dependency path, but is not yet a proved invariant: preservation
must additionally connect committed plans, identity rows and native observation replay.
Neither this proposition nor arbitrary native laws are accepted as step preconditions. -/
def ConstructionInvariant (s : State) : Prop :=
  (∀ plan, s.receiptPlan = some plan → ReceiptOrigin plan) ∧
  (∀ plan, s.renderPlan = some plan → RenderOrigin plan) ∧
  (∀ plan, s.prepared = some plan →
    ∃ origin : RenderBuild, RenderOrigin origin ∧ origin.result = plan.rendered ∧
      origin.suffix = plan.suffix ∧ origin.reserved = plan.reserved)

end Musubi.NativeLifecycle

/-
Properties of the constructors, proved from their definitions. They do not authenticate the
raw native tables. An invariant over reachable states must use these same constructors, not
the four raw observation actions `receive`, `prepare`, `write` and `helperHeads`, which
`constructedAction` excludes.
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

theorem currentGitBody_fields (before : NativeBody) (canonical : Canonical) (fields : Nat) :
    (currentGitBody before canonical fields).gitFields = fields := by
  unfold currentGitBody
  split <;> simp_all

theorem currentGitBody_frame (before : NativeBody) (canonical : Canonical) (fields : Nat) :
    { currentGitBody before canonical fields with
      gitFields := before.gitFields, marker := before.marker } = before := by
  unfold currentGitBody
  split <;> rfl

theorem currentGitBody_marker {before : NativeBody} {canonical : Canonical} {fields : Nat}
    (changed : before.gitFields ≠ fields) :
    (currentGitBody before canonical fields).marker = some canonical := by
  simp [currentGitBody, changed]

theorem encodeCurrentGit_shape {e : Evidence} {table : EncodingTable} {before result : NativeBody}
    {canonical : Canonical} {fields : Nat}
    (success : encodeCurrentGit e table before canonical fields = .ok result) :
    sameNativeShape (currentGitBody before canonical fields) result = true := by
  unfold encodeCurrentGit at success
  split at success
  · rename_i equal
    cases success
    simp only [currentGitBody, ite_eq_left equal]
    simp [sameNativeShape]
  · exact (encodeNative_observed success).2

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

/-- An adapter-owned native helper creates native operations. It allocates no canonical
identities and is not counted as an external writer in the publication or
helper window (`Outside.publicationOverlap`, `Outside.helperOverlap`). -/
theorem ownHelper_frame {s t : State} {index : Nat}
    (success : step s (.ownHelper index) = .ok t) :
    t.outside = s.outside ∧ t.allocatedLabels = s.allocatedLabels ∧
      t.createdCanonicals = s.createdCanonicals := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases outcome : helperOutcome s index with
  | error gap => simp [stepCore, outcome, Functor.map, Except.map] at accepted
  | ok result =>
    simp [stepCore, outcome, Functor.map, Except.map] at accepted
    subst next
    exact ⟨rfl, rfl, rfl⟩

/-- Successful execution requires responsibility for the plan's captured receipt, even
when another action could have changed the current receipt. No custody result is assumed. -/
theorem writeRender_captured_records {s t : State} {index : Nat} {plan : RenderBuild}
    {receipt : Receipt} (success : step s (.writeRender index) = .ok t)
    (bound : s.renderPlan = some plan) (captured : plan.receipt = some receipt) :
    ∀ record, record ∈ receipt.records → record ∈ s.saved.applied ++ s.saved.custody := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases held : receipt.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    cases node : plan.nodes[index]? <;>
      simp only [stepCore, bound, captured, node, held, bind, Except.bind,
        throw, throwThe, MonadExceptOf.throw, Bool.not_false] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)

theorem writeRender_current {s t : State} {index : Nat} {plan : RenderBuild}
    (success : step s (.writeRender index) = .ok t) (bound : s.renderPlan = some plan) :
    renderPlanCurrent s plan = true := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases current : renderPlanCurrent s plan with
  | true => rfl
  | false =>
    simp [stepCore, bound, current, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted

/-- Only a changed refresh writes a body. It uses the receipt captured by preparation,
not an arbitrary current receipt supplied by a later action. -/
theorem refreshCurrentGit_records {s t : State} {prepared : Prepared} {plan : Publication}
    {git : GitChoice} {build : CurrentGitBuild} {receipt : Receipt}
    (success : step s .refreshCurrentGit = .ok t)
    (bound : s.prepared = some prepared) (publication : s.publication = some plan)
    (choice : s.git = some git) (uses : git.useCurrent = true)
    (computed : constructCurrentGit s.evidence s.nativeFacts s.heads
      prepared.inputs.target plan.incoming = .ok build)
    (writes : build.writes = true) (captured : prepared.inputs.receipt = some receipt) :
    ∀ record, record ∈ receipt.records → record ∈ s.saved.applied ++ s.saved.custody := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases held : receipt.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    simp only [stepCore, bound, publication, choice, uses, computed, writes, captured,
      held, liftQuery, Except.mapError, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw, Bool.not_false] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)

def CurrentGitOrigin (build : CurrentGitBuild) : Prop :=
  ∃ before facts heads canonical incoming,
    constructCurrentGit before facts heads canonical incoming = .ok build

theorem constructCurrentGit_pinned {e : Evidence} {facts : NativeFacts}
    {heads : List Physical} {canonical : Canonical} {incoming : Physical} {build : CurrentGitBuild}
    (computed : constructCurrentGit e facts heads canonical incoming = .ok build) :
    build.input = e ∧ build.heads = heads ∧ build.canonical = canonical := by
  simp only [constructCurrentGit, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw] at computed
  all_goals repeat' (split at computed <;> try simp_all)
  all_goals subst build
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- Installing the freshly computed body changes the incoming operand in the same action.
This does not assert that native merge/export has happened. -/
theorem refreshCurrentGit_origin {s t : State}
    (success : step s .refreshCurrentGit = .ok t) :
    ∀ plan build, t.publication = some plan → plan.refresh = some build →
      CurrentGitOrigin build ∧ plan.incoming = build.body.id := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  intro finalPlan finalBuild bound refreshed
  cases prepared : s.prepared with
  | none =>
    simp only [stepCore, prepared, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals try subst next
    all_goals simp_all
  | some before =>
    cases publication : s.publication with
    | none =>
      simp only [stepCore, publication, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at accepted
      all_goals repeat' (split at accepted <;> try simp_all)
      all_goals try subst next
      all_goals simp_all
    | some plan =>
      cases choice : s.git with
      | none =>
        simp only [stepCore, publication, choice, bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw] at accepted
        all_goals repeat' (split at accepted <;> try simp_all)
        all_goals try subst next
        all_goals simp_all
      | some git =>
        cases computed : constructCurrentGit s.evidence s.nativeFacts s.heads
            before.inputs.target plan.incoming with
        | error gap =>
          simp only [stepCore, prepared, publication, choice, computed, liftQuery,
            Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
            pure, Except.pure] at accepted
          all_goals repeat' (split at accepted <;> try simp_all)
          all_goals try subst next
          all_goals simp only [Option.some.injEq] at bound
          all_goals subst finalPlan
          all_goals cases refreshed
        | ok build =>
          have origin : CurrentGitOrigin build :=
            ⟨s.evidence, s.nativeFacts, s.heads, before.inputs.target, plan.incoming, computed⟩
          simp only [stepCore, prepared, publication, choice, computed, liftQuery,
            Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
            pure, Except.pure] at accepted
          all_goals repeat' (split at accepted <;> try simp_all)
          all_goals try subst next
          all_goals simp only [Option.some.injEq] at bound
          all_goals subst finalPlan
          all_goals cases refreshed
          all_goals exact ⟨origin, rfl⟩

theorem renderPlanCurrent_receipt {s : State} {plan : RenderBuild}
    (current : renderPlanCurrent s plan = true) : s.receipt = plan.receipt := by
  simp only [renderPlanCurrent, Bool.and_eq_true] at current
  exact of_decide_eq_true current.2

/-- A changed actual head set takes the retry branch without constructing a publication plan.
This is the modeled pre-final-reread interval, not a claim about after-reread writers. -/
theorem revalidate_changed_heads (s : State) (captured : List Physical)
    (phase : s.phase = .prepared) (bound : s.captured = some captured)
    (changed : sameSet captured s.heads = false) :
    (step s .revalidate).map (fun t => (t.phase, t.prepared, t.captured, t.publication)) =
      .ok (.preparing, none, none, s.publication) := by
  simp [step, stepCore, phase, bound, changed, Except.map, pure, Except.pure]

/-- Owned probe calls keep the captured plan and every historical origin slot. Their
unpublished body writes and native context change neither heads nor saved responsibility. -/
theorem preparationProbe_historical_frame {s t : State} {index : Nat}
    (success : step s (.preparationProbe index) = .ok t) :
    t.me = s.me ∧ t.receiptPlan = s.receiptPlan ∧ t.renderPlan = s.renderPlan ∧
      t.prepared = s.prepared ∧ t.publication = s.publication ∧ t.heads = s.heads ∧
      t.saved = s.saved := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  simp only [stepCore, bind, Except.bind, liftQuery, Except.mapError,
    throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
  all_goals repeat' (split at accepted <;> try simp_all)
  all_goals subst next
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem preparationProbe_captured_records {s t : State} {index : Nat}
    {prepared : Prepared} {receipt : Receipt}
    (success : step s (.preparationProbe index) = .ok t)
    (bound : s.prepared = some prepared) (captured : prepared.inputs.receipt = some receipt) :
    ∀ record, record ∈ receipt.records → record ∈ s.saved.applied ++ s.saved.custody := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases held : receipt.records.all ((s.saved.applied ++ s.saved.custody).contains ·) with
  | true =>
    intro record member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp held record member)
  | false =>
    simp only [stepCore, bound, captured, held, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, Bool.not_false] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals cases accepted

theorem preparationProbe_source_routes {s t : State} {index : Nat}
    (success : step s (.preparationProbe index) = .ok t) :
    t.evidence.sourceRoutes = none :=
  step_invalidates_source_routes success rfl

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
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  simp only [stepCore, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    pure, Except.pure] at accepted
  split at accepted
  · cases accepted
  · cases accepted
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The proof target for the constructed sublanguage is provenance plus policy facts about
the same actual run. Raw observation shortcuts cannot establish computed preparation. -/
def constructedAction : Action → Bool
  | .receive _ | .prepare _ _ | .write _ | .helperHeads _ => false
  | _ => true

def ReceiptOrigin (me : Copy) (plan : ReceiptBuild) : Prop :=
  ∃ before facts saved heads request,
    constructReceipt before facts saved me heads request = .ok plan

def RenderOrigin (me : Copy) (plan : RenderBuild) : Prop :=
  ∃ before facts heads receipt target,
    constructRender before facts me heads receipt target = .ok plan

/-- The committed preparation retains the exact constructor's owner, input snapshot,
captured head vector, target and receipt, as well as its result and suffix. These are
historical planning inputs, not a claim that policy stays current after external effects. -/
def preparedMatchesOrigin (me : Copy) (prepared : Prepared) (origin : RenderBuild) : Bool :=
  decide (prepared.inputs.me = me ∧
    prepared.rendered = origin.result ∧ prepared.suffix = origin.suffix ∧
    prepared.reserved = origin.reserved ∧ prepared.inputs.evidence = origin.input ∧
    prepared.inputs.heads = origin.heads ∧ prepared.inputs.target = origin.target ∧
    prepared.inputs.receipt = origin.receipt)

def PreparedOrigin (me : Copy) (prepared : Prepared) : Prop :=
  ∃ origin, RenderOrigin me origin ∧ preparedMatchesOrigin me prepared origin = true

theorem planReceipt_origin {s t : State} {request : ReceiptRequest}
    (success : step s (.planReceipt request) = .ok t) :
    ∃ plan, t.receiptPlan = some plan ∧ ReceiptOrigin s.me plan := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases computed : constructReceipt s.evidence s.nativeFacts s.saved s.me s.heads request with
  | error gap =>
    simp only [stepCore, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all
  | ok plan =>
    have origin : ReceiptOrigin s.me plan :=
      ⟨s.evidence, s.nativeFacts, s.saved, s.heads, request, computed⟩
    simp only [stepCore, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all

theorem planRender_origin {s t : State} {target : Canonical}
    (success : step s (.planRender target) = .ok t) :
    ∀ plan, t.renderPlan = some plan → RenderOrigin s.me plan := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases computed : constructRender s.evidence s.nativeFacts s.me s.heads s.receipt target with
  | error gap =>
    simp only [stepCore, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all
  | ok result =>
    have origin : RenderOrigin s.me result :=
      ⟨s.evidence, s.nativeFacts, s.heads, s.receipt, target, computed⟩
    simp only [stepCore, liftQuery, computed, Except.mapError, bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all

/-- Construction policy is computed at the recorded planning state. Committed preparation
must remain associated with that exact owner/input/target/receipt. Current-state policy and
native observation authentication are distinct obligations, not premises of preservation. -/
def ConstructionInvariant (s : State) : Prop :=
  (∀ plan, s.receiptPlan = some plan → ReceiptOrigin s.me plan) ∧
  (∀ plan, s.renderPlan = some plan → RenderOrigin s.me plan) ∧
  (∀ plan, s.prepared = some plan → PreparedOrigin s.me plan) ∧
  (∀ plan build, s.publication = some plan → plan.refresh = some build → CurrentGitOrigin build)

theorem commitRender_current {s t : State} {plan : RenderBuild}
    (success : step s .commitRender = .ok t) (bound : s.renderPlan = some plan) :
    renderPlanCurrent s plan = true := by
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  cases current : renderPlanCurrent s plan with
  | true => rfl
  | false =>
    simp [stepCore, bound, current, bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw] at accepted

theorem commitRender_association {s t : State} {origin : RenderBuild}
    (success : step s .commitRender = .ok t) (bound : s.renderPlan = some origin) :
    ∀ prepared, t.prepared = some prepared →
      preparedMatchesOrigin s.me prepared origin = true := by
  have current := commitRender_current success bound
  have receipt := renderPlanCurrent_receipt current
  obtain ⟨next, accepted, rfl⟩ := step_core_success success
  simp only [stepCore, bound, current, bind, Except.bind, liftQuery, Except.mapError,
    throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
  all_goals repeat' (split at accepted <;> try simp_all)
  all_goals subst next
  all_goals intro prepared associated
  all_goals simp only [Option.some.injEq] at associated
  all_goals subst prepared
  all_goals simp [preparedMatchesOrigin]

/-- The raw adapter supplies observations, never an existing plan or a correct-policy
certificate. Every construction slot starts empty by this executable constructor. -/
def rawInitial (me : Copy) (evidence : Evidence) (heads : List Physical) (saved : Persistent)
    (facts : NativeFacts) (physicalGit : Nat) : State :=
  { me, evidence, heads, saved, nativeFacts := facts, physicalGit }

theorem rawInitial_construction (me : Copy) (evidence : Evidence) (heads : List Physical)
    (saved : Persistent) (facts : NativeFacts) (physicalGit : Nat) :
    ConstructionInvariant (rawInitial me evidence heads saved facts physicalGit) := by
  simp [ConstructionInvariant, rawInitial]

set_option maxHeartbeats 2000000 in
/-- Step preservation for the constructed sublanguage: every action except the four raw
observation actions. Origin and policy facts refer to their actual constructor or planning
state, including across external effects; this does not assert native refinement or policy at
the later state. -/
theorem construction_step_preserves {s t : State} {action : Action}
    (before : ConstructionInvariant s) (admitted : constructedAction action = true)
    (success : step s action = .ok t) : ConstructionInvariant t := by
  rcases before with ⟨receiptOrigin, renderOrigin, preparedOrigin, refreshOrigin⟩
  cases action with
  | planReceipt request =>
    obtain ⟨plan, planned, origin⟩ := planReceipt_origin success
    obtain ⟨next, accepted, rfl⟩ := step_core_success success
    clear success
    simp only [stepCore, bind, Except.bind, liftQuery, Except.mapError,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all [ConstructionInvariant]
  | planRender target =>
    have planned := planRender_origin success
    obtain ⟨next, accepted, rfl⟩ := step_core_success success
    clear success
    simp only [stepCore, bind, Except.bind, liftQuery, Except.mapError,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all [ConstructionInvariant]
  | commitRender =>
    cases bound : s.renderPlan with
    | none => simp [step, stepCore, bound, throw, throwThe,
        MonadExceptOf.throw] at success
    | some origin =>
      have computed := renderOrigin origin bound
      have associated := commitRender_association success bound
      obtain ⟨next, accepted, rfl⟩ := step_core_success success
      clear success
      simp only [stepCore, bound, bind, Except.bind, liftQuery, Except.mapError,
        throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
      all_goals repeat' (split at accepted <;> try simp_all)
      all_goals subst next
      all_goals refine ⟨?_, ?_, ?_, ?_⟩
      all_goals try simp_all
      all_goals exact ⟨origin, computed, associated⟩
  | refreshCurrentGit =>
    have computed := refreshCurrentGit_origin success
    obtain ⟨next, accepted, rfl⟩ := step_core_success success
    clear success
    simp only [stepCore, bind, Except.bind, liftQuery, Except.mapError,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals subst next
    all_goals simp_all [ConstructionInvariant]
  | preparationProbe index =>
    obtain ⟨me, receipt, render, prepared, publication, _, _⟩ :=
      preparationProbe_historical_frame success
    simp only [ConstructionInvariant, me, receipt, render, prepared, publication]
    exact ⟨receiptOrigin, renderOrigin, preparedOrigin, refreshOrigin⟩
  | receive _ | prepare _ _ | write _ | helperHeads _ =>
    simp [constructedAction] at admitted
  | _ =>
    obtain ⟨next, accepted, rfl⟩ := step_core_success success
    clear success
    simp only [stepCore, noteExternal, bind, Except.bind, liftQuery, Except.mapError,
      throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at accepted
    all_goals repeat' (split at accepted <;> try simp_all)
    all_goals try simp only [Except.ok.injEq] at accepted
    all_goals try subst next
    all_goals simp_all [ConstructionInvariant]
    all_goals intro plan build bound refreshed
    all_goals subst plan
    all_goals simp_all
    all_goals exact refreshOrigin _ _ rfl refreshed

end Musubi.NativeLifecycle

/-
Executable observation phases for the first native lifecycle increment. This module records
successful native outcomes as data; it does not assert their native laws. E1/E2/recovery
violations and non-unique source boundaries stay visible and never become invented refusals.
The reachable-state theorem and Rust correspondence remain gated on native evidence.
-/
import Musubi.NativeLifecycle.Construction

namespace Musubi.NativeLifecycle

inductive Phase where
  | idle | preparing | prepared | validated | held | moving | cleanup | complete | interrupted
deriving DecidableEq, Repr, Inhabited

inductive Branch where
  | direct
  | lockedExport
deriving DecidableEq, Repr

inductive Outside where
  | publicationOverlap
  | helperOverlap
  | recoveryOverlap
  | sources (canonical : Canonical) (choice : SourceChoice)
  | failedCall
deriving DecidableEq, Repr

/-- Input equality I compares these observations, not computed output ids. Full relevant
Git fields and retained export/expected observations are kept separate from disposable memo. -/
structure Inputs where
  me : Copy
  evidence : Evidence
  heads : List Physical
  colocated : Bool
  physicalGit : Nat
  physicalScope : PhysicalScope := .selectedRef 0
  physicalKnown : Bool := true
  target : Canonical
  receipt : Option Receipt
  saved : Persistent
  expected : List (Physical × Nat)
  exports : List RetainedExport
deriving DecidableEq, Repr

structure Prepared where
  rendered : Physical
  suffix : Suffix
  selections : ParentSelection
  own : OwnSelection
  reserved : List Name
  inputs : Inputs
deriving DecidableEq, Repr

structure Memo where
  preferred : List (Canonical × Physical) := []
  published : List (Canonical × Physical) := []
  derivedExpected : List (Physical × Nat) := []
deriving DecidableEq, Repr, Inhabited

structure Publication where
  incoming : Physical
  beside : List Physical
  mergeBeforeExport : Bool
  merged : Option Physical := none
  firstExported : Bool := false
  mergeExported : Bool := false
deriving DecidableEq, Repr

structure State where
  me : Copy
  evidence : Evidence
  heads : List Physical
  colocated : Bool := true
  saved : Persistent := {}
  receipt : Option Receipt := none
  receiptPlan : Option ReceiptBuild := none
  renderPlan : Option RenderBuild := none
  nativeFacts : NativeFacts := {}
  memo : Memo := {}
  phase : Phase := .idle
  captured : Option (List Physical) := none
  prepared : Option Prepared := none
  ordinaryMove : Option Intent := none
  git : Option GitChoice := none
  publication : Option Publication := none
  /-- Exact content of the tagged projection. A selected ref is not a full refs/HEAD snapshot. -/
  physicalGit : Nat := 0
  physicalScope : PhysicalScope := .selectedRef 0
  physicalKnown : Bool := true
  helper : Option Branch := none
  closedPublication : Bool := false
  closedRecovery : Bool := false
  outside : List Outside := []
  allocatedLabels : Nat := 0
  /-- Native operation bodies and canonical bodies have separate allocation counters. -/
  createdBodies : Nat := 0
  createdCanonicals : Nat := 0
deriving DecidableEq, Repr

def queryFuel (e : Evidence) : Nat := e.native.length + e.canonical.length + 1

/-- An attempt may finish writing its captured plan before revalidating changed heads.
Its phase, capture and exact receipt must still be current. This is model call order, not
a claim that shipping Rust refuses an arbitrary operation sequence. -/
def renderPlanCurrent (s : State) (plan : RenderBuild) : Bool :=
  s.phase == .preparing && !s.closedPublication && !s.closedRecovery &&
    s.receiptPlan.isNone &&
    (s.captured.map (sameSet · plan.heads)).getD false && decide (s.receipt = plan.receipt)

def prepare (s : State) (canonical : Canonical) (rendered : Physical) : Query Prepared := do
  let fuel := queryFuel s.evidence
  let suffix ← suffix s.evidence s.heads s.receipt fuel canonical
  let selections ← selectParents s.evidence fuel s.heads s.receipt canonical
  let some parents := selections.parents | throw (.malformed "source query outside U")
  let own ← selectOwn s.evidence fuel s.me canonical parents s.heads s.receipt
  let reserved := (← ownAtHeads s.evidence fuel s.me s.heads).map (·.1)
  let inputs : Inputs := {
    me := s.me, evidence := s.evidence, heads := s.heads, colocated := s.colocated,
    physicalGit := s.physicalGit, target := canonical, receipt := s.receipt, saved := s.saved,
    physicalScope := s.physicalScope, physicalKnown := s.physicalKnown,
    expected := s.saved.expected, exports := s.saved.exports }
  return { rendered, suffix, selections, own, reserved, inputs }

/-- Canonical ancestry only removes strictly smaller canonical heads. Two physical aliases
of one canonical operation are both retained, as in moved_heads. -/
def maximalPhysical (e : Evidence) (fuel : Nat) (heads : List Physical) : Query (List Physical) := do
  let mut result := []
  for head in unique heads do
    let a ← e.counterpart head
    let mut keep := true
    for other in heads do
      let b ← e.counterpart other
      if let (some a, some b) := (a, b) then
        if a ≠ b && (← canonicalAncestor e fuel a b) then keep := false
    if keep then result := result ++ [head]
  return result

/-- Recovery applies only the saved mappings whose old heads still occur in the captured
frontier. Exact from/to frontiers have their own full-move/no-op cases. An unmapped native
head stays present even before its canonical identity has been learned. -/
def recoveryDestination (e : Evidence) (fuel : Nat) (captured : List Physical)
    (intent : Intent) : Query (List Physical) := do
  if sameSet captured intent.to then return captured
  if sameSet captured (intent.fromHeads.map (·.1)) then return intent.to
  if captured.any (fun head => (lookup intent.fromHeads head).isSome) then
    let expanded := captured.flatMap (fun head => (lookup intent.fromHeads head).getD [head])
    return ← maximalPhysical e fuel expanded
  return captured

def moveDestination (s : State) (incoming merged : Option Physical) : Query Intent := do
  let fuel := queryFuel s.evidence
  let locals := (s.receipt.map (·.locals)).getD []
  let expanded := s.heads.flatMap (fun head => (lookup locals head).getD [head])
  let mut to ← maximalPhysical s.evidence fuel (expanded ++ incoming.toList)
  if let some merge := merged then
    let body ← s.evidence.nativeBody merge
    to := to.filter (fun id => !body.parents.contains id) ++ [merge]
  return {
    fromHeads := s.heads.map (fun head => (head, (lookup locals head).getD [head])), to,
    identities := s.evidence.identities.filter (fun row =>
      (s.heads ++ to ++ locals.flatMap (·.2)).contains row.physical) }

def chainValid : Nat → List Record → Bool
  | _, [] => true
  | before, record :: rest => record.before == before && chainValid record.identity rest

def commonRecords (saved : Persistent) (receipt : Receipt) : Nat :=
  if saved.recordPrefix = receipt.recordPrefix ∧ saved.prunedCount = receipt.prunedCount then
    ((saved.applied.zip receipt.records).takeWhile (fun p => decide (p.1 = p.2))).length
  else 0

def recordDigests (saved : Persistent) : List Nat :=
  saved.recordPrefix :: saved.applied.map (·.identity)

/-- Keep the first readable body for each captured digest, with its own before link. -/
def uniqueRecords (records : List Record) : List Record :=
  records.foldl (fun kept record =>
    if kept.any (fun old => old.identity == record.identity) then kept else kept ++ [record]) []

def recordReaches (held : List Nat) (earlier : List Record) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, digest =>
    if digest == 0 || held.contains digest then true
    else match earlier.find? (fun record => record.identity == digest) with
      | none => false
      | some record => recordReaches held earlier fuel record.before

structure HeldRecords where
  recordPrefix : Nat
  prunedCount : Nat
  records : List Record
deriving DecidableEq, Repr

/-- Follow readable earlier receipts back to the current applied prefix or the root.
An opaque prefix can be an anchor only while it is still a current held digest. -/
def heldRecordChain (saved : Persistent) : Nat → Nat → Option HeldRecords
  | 0, _ => none
  | fuel + 1, digest =>
    match ((recordDigests saved).zipIdx).find? (fun row => row.1 == digest) with
    | some (_, index) => some ⟨saved.recordPrefix, saved.prunedCount, saved.applied.take index⟩
    | none =>
      if digest == 0 then some ⟨0, 0, []⟩
      else do
        let record ← saved.earlier.find? (fun record => record.identity == digest)
        let base ← heldRecordChain saved fuel record.before
        return { base with records := base.records ++ [record] }

def heldRecords (saved : Persistent) (count digest : Nat) : Option HeldRecords := do
  let held ← heldRecordChain saved (saved.earlier.length + 1) digest
  if held.prunedCount + held.records.length = count then return held
  else none

def retainEarlier (saved : Persistent) (receipt : Receipt) (lostCustody : List Record) :
    List Record :=
  let held := receipt.recordPrefix :: receipt.records.map (·.identity)
  let earlier := uniqueRecords ((saved.earlier ++ lostCustody ++ saved.applied).filter
    (fun record => !held.contains record.identity))
  earlier.filter (fun record => recordReaches held earlier (earlier.length + 1) record.identity)

def takeResponsibility (saved : Persistent) (receipt : Receipt) (intent : Intent) : Persistent :=
  let common := commonRecords saved receipt
  let incoming := receipt.recordPrefix :: receipt.records.map (·.identity)
  let lost := saved.custody.filter (fun record => !incoming.contains record.identity)
  let pending := unique (saved.pending ++ (saved.applied.drop common).flatMap (·.drops) ++
    lost.flatMap (·.drops))
  let acknowledged := receipt.records.flatMap (·.drops)
  { saved with
    recordPrefix := receipt.recordPrefix, prunedCount := receipt.prunedCount, applied := receipt.records,
    earlier := retainEarlier saved receipt lost, custody := [],
    pending := pending.filter (fun original => !acknowledged.contains original),
    intent := some intent }

inductive StepError where
  | evidence (gap : Gap)
  | phase
  | custody
  | intent
  | bodyConflict
deriving DecidableEq, Repr

instance [DecidableEq α] : DecidableEq (Except StepError α) := decidableExceptEq

def liftQuery (q : Query α) : Except StepError α := q.mapError .evidence

structure BodyWrite where
  body : NativeBody
  /-- Present for a record-named write; custody must already contain these readable records. -/
  records : List Record := []
deriving DecidableEq, Repr

/-- Independently captured native command outcome. Authentication of its author, identity,
complete payload and physical writers remains N01/N03/N07, not a premise proved here. -/
structure NativeObservation where
  canonical : List CanonicalBody := []
  native : List NativeBody := []
  identities : List IdentityRow := []
  heads : List Physical
  physicalGit : Nat
deriving DecidableEq, Repr

def installNative (e : Evidence) (observation : NativeObservation) :
    Except StepError (Evidence × Nat × Nat) := do
  let mut evidence := e
  let mut nativeCount := 0
  let mut canonicalCount := 0
  for body in observation.canonical do
    match evidence.canonical.find? (fun b => decide (b.id = body.id)) with
    | some old => if old ≠ body then throw .bodyConflict
    | none =>
      evidence := { evidence with canonical := evidence.canonical ++ [body] }
      canonicalCount := canonicalCount + 1
  for body in observation.native do
    match evidence.native.find? (fun b => decide (b.id = body.id)) with
    | some old => if old ≠ body then throw .bodyConflict
    | none =>
      evidence := { evidence with native := evidence.native ++ [body] }
      nativeCount := nativeCount + 1
  evidence := { evidence with identities := unique (evidence.identities ++ observation.identities) }
  let _ ← liftQuery (observation.identities.mapM (fun row => evidence.identity row.physical))
  let _ ← liftQuery (observation.heads.mapM evidence.nativeBody)
  return (evidence, nativeCount, canonicalCount)

/-- This is an observed native export, separately authenticated by N07. It records complete
input/output observations; an ordinary bookkeeping merge is a different action. -/
structure ExportObservation where
  input : Physical
  output : Physical
  before : Nat
  after : Nat
  recordedFields : Nat
  /-- Per-ref success/CAS-skip/failure details, retained by exact structural content. -/
  outcomes : Nat
deriving DecidableEq, Repr

inductive Action where
  | planReceipt (request : ReceiptRequest)
  | writeReceiptCanonical (index : Nat)
  | writeReceiptNative (index : Nat)
  | commitReceipt (observed : Receipt)
  | planRender (target : Canonical)
  | writeRender (index : Nat)
  | commitRender
  | ownHelper (index : Nat)
  /-- Prototype observation-only entry points below are outside constructed preparation. -/
  | receive (receipt : Receipt)
  | saveCustody
  | capture
  | prepare (canonical : Canonical) (rendered : Physical)
  | allocateLabel
  | write (data : BodyWrite)
  | revalidate
  | observeExport (observation : ExportObservation)
  /-- Actual arguments/result of the native merge, not an assumed merge-result law. -/
  | merge (inputs : List Physical) (output : Physical)
  | bookkeeping (physical : Physical) (fields : Nat)
  | saveIntent (incoming merged : Option Physical)
  | planOrdinary (incoming merged : Option Physical)
  | addHead (head : Physical)
  | finishMove
  | helperEnter (colocated : Bool)
  | helperExit
  | helperHeads (heads : List Physical)
  | finish
  | interrupt
  | restart
  | eraseMemo
  | startRecovery
  | finishRecovery
  /-- Independently observed external effects. They remain in the recorded trace even when
  they violate this first theorem's schedule domain. -/
  | external (heads : List Physical) (physicalGit : Nat)
  | native (observation : NativeObservation)
  | loseEvidence (physical : List Physical)
  | loseCanonicalEvidence (canonical : List Canonical)
  | failedCall
deriving DecidableEq, Repr

def noteExternal (s : State) : State :=
  { s with outside := s.outside ++
      (if s.closedPublication then [.publicationOverlap] else []) ++
      (if s.helper.isSome then [.helperOverlap] else []) ++
      (if s.closedRecovery then [.recoveryOverlap] else []) }

structure HelperResult where
  evidence : Evidence
  heads : List Physical
  physicalGit : Nat
  physicalKnown : Bool
  created : Nat

def helperOutcome (s : State) (index : Nat) : Except StepError HelperResult := do
  let some fact := s.nativeFacts.helpers[index]? | throw (.evidence (.nativeFact "helper"))
  if s.helper.isNone then throw .phase
  if !(← liftQuery (helperInputMatches s.evidence s.heads fact)) then
    throw (.evidence (.nativeFact "helper raw inputs"))
  if fact.kind = .load && s.heads.length ≤ 1 &&
      (!fact.written.isEmpty || !sameSet fact.afterHeads s.heads) then
    throw (.evidence (.nativeFact "single-head load"))
  let (evidence, count, _) ← installNative s.evidence
    { native := fact.written, heads := fact.afterHeads, physicalGit := s.physicalGit }
  if !fact.afterHeads.contains fact.result then
    throw (.evidence (.nativeFact "helper result frontier"))
  let reachable ← liftQuery (nativeFrontierClosure evidence (queryFuel evidence) fact.afterHeads)
  if !s.heads.all (reachable.contains ·) then
    throw (.evidence (.nativeFact "helper discards native ancestry"))
  let (physicalGit, physicalKnown) ← match fact.physical with
    | none => pure (s.physicalGit, false)
    | some observed => do
      if !s.physicalKnown || observed.scope ≠ s.physicalScope || observed.before ≠ s.physicalGit then
        throw (.evidence (.nativeFact "helper physical scope/input"))
      pure (observed.after, true)
  return { evidence, heads := fact.afterHeads, physicalGit, physicalKnown, created := count }

def step (s : State) : Action → Except StepError State
  | .planReceipt request => do
    if s.closedPublication || s.closedRecovery then throw .phase
    if !chainValid request.recordPrefix request.records then
      throw (.evidence (.malformed "record chain"))
    if ((request.records.getLast?).map (·.identity)).getD request.recordPrefix ≠ request.identity then
      throw (.evidence (.malformed "receipt identity"))
    let plan ← liftQuery (constructReceipt s.evidence s.nativeFacts s.saved s.me s.heads request)
    return { s with
      receiptPlan := some plan, receipt := none, prepared := none,
      captured := none, renderPlan := none, phase := .preparing }
  | .writeReceiptCanonical index => do
    let some plan := s.receiptPlan | throw .phase
    let some body := plan.canonicalWrites[index]? | throw .phase
    if !plan.computed.records.all ((s.saved.applied ++ s.saved.custody).contains ·) then
      throw .custody
    let _ ← liftQuery (body.parents.mapM s.evidence.canonicalBody)
    let (evidence, _, count) ← installNative s.evidence
      { canonical := [body], heads := s.heads, physicalGit := s.physicalGit }
    return { s with evidence, createdCanonicals := s.createdCanonicals + count }
  | .writeReceiptNative index => do
    let some plan := s.receiptPlan | throw .phase
    let some body := plan.nativeWrites[index]? | throw .phase
    if !plan.computed.records.all ((s.saved.applied ++ s.saved.custody).contains ·) then
      throw .custody
    let _ ← liftQuery (body.parents.mapM s.evidence.nativeBody)
    let (evidence, count, _) ← installNative s.evidence
      { native := [body], heads := s.heads, physicalGit := s.physicalGit }
    return { s with evidence, createdBodies := s.createdBodies + count }
  | .commitReceipt observed => do
    let some plan := s.receiptPlan | throw .phase
    if !sameSet plan.computed.capturedHeads s.heads || !receiptInputMatches plan observed then
      throw (.evidence (.malformed "observed receipt differs from construction"))
    if !plan.canonicalWrites.all (s.evidence.canonical.contains ·) ||
        !plan.nativeWrites.all (s.evidence.native.contains ·) then throw .phase
    let (evidence, _, _) ← installNative s.evidence
      { identities := plan.identities, heads := s.heads, physicalGit := s.physicalGit }
    return { s with
      evidence, receipt := some observed, receiptPlan := none,
      renderPlan := none, prepared := none, captured := none }
  | .planRender target => do
    if s.closedRecovery || s.closedPublication || s.receiptPlan.isSome ||
        s.phase ≠ .preparing || s.captured.isNone then throw .phase
    if let some receipt := s.receipt then
      if !receipt.switched && !receiptMatches receipt s.heads then
        return { s with prepared := none, captured := none, renderPlan := none }
    let plan ← liftQuery (constructRender s.evidence s.nativeFacts s.me s.heads s.receipt target)
    return { s with renderPlan := some plan }
  | .writeRender index => do
    let some plan := s.renderPlan | throw .phase
    if !renderPlanCurrent s plan then throw .phase
    let some node := plan.nodes[index]? | throw .phase
    if let some receipt := plan.receipt then
      if !receipt.records.all ((s.saved.applied ++ s.saved.custody).contains ·) then throw .custody
    let _ ← liftQuery (node.body.parents.mapM s.evidence.nativeBody)
    let (evidence, count, _) ← installNative s.evidence {
      native := [node.body], identities := [node.identity], heads := s.heads,
      physicalGit := s.physicalGit }
    return { s with evidence, createdBodies := s.createdBodies + count }
  | .commitRender => do
    let some plan := s.renderPlan | throw .phase
    if !renderPlanCurrent s plan then throw .phase
    if !sameSet plan.heads s.heads ||
        !plan.nodes.all (fun node => s.evidence.native.contains node.body &&
          s.evidence.identities.contains node.identity) then throw .phase
    let selections ← liftQuery (renderingSelection s.evidence (queryFuel s.evidence) s.heads
      s.receipt (plan.nodes.map (fun node => (node.canonical, node.body.id))) plan.target)
    let some parents := selections.parents | throw (.evidence (.malformed "parents outside U"))
    let own ← liftQuery (selectOwn s.evidence (queryFuel s.evidence) s.me plan.target parents
      s.heads s.receipt)
    let inputs : Inputs := {
      me := s.me, evidence := plan.input, heads := plan.heads, colocated := s.colocated,
      physicalGit := s.physicalGit, physicalScope := s.physicalScope,
      physicalKnown := s.physicalKnown, target := plan.target, receipt := s.receipt,
      saved := s.saved, expected := s.saved.expected, exports := s.saved.exports }
    let prepared : Prepared := {
      rendered := plan.result, suffix := plan.suffix, selections, own,
      reserved := plan.reserved, inputs }
    return { s with prepared := some prepared, renderPlan := none, phase := .prepared }
  | .ownHelper index => do
    let result ← helperOutcome s index
    return { s with
      evidence := result.evidence, heads := result.heads, physicalGit := result.physicalGit,
      physicalKnown := result.physicalKnown, createdBodies := s.createdBodies + result.created }
  | .receive r => do
    if s.closedPublication then throw .phase
    if !chainValid r.recordPrefix r.records then throw (.evidence (.malformed "record chain"))
    let identity := ((r.records.getLast?).map (·.identity)).getD r.recordPrefix
    if identity ≠ r.identity then throw (.evidence (.malformed "receipt identity"))
    return { s with
      receipt := some r, prepared := none, renderPlan := none, captured := none,
      phase := .preparing }
  | .saveCustody => do
    let some r := s.receipt.or (s.receiptPlan.map (·.computed)) | throw .phase
    let held := s.saved.applied.map (·.identity) ++ s.saved.custody.map (·.identity)
    let new := (r.records.drop (commonRecords s.saved r)).filter
      (fun record => !held.contains record.identity)
    return { s with saved := { s.saved with custody := s.saved.custody ++ new } }
  | .capture => do
    if s.closedPublication || s.closedRecovery then throw .phase
    return { s with
      captured := some s.heads, prepared := none, renderPlan := none, phase := .preparing }
  | .prepare canonical rendered => do
    if s.phase ≠ .preparing || s.captured.isNone then throw .phase
    if let some receipt := s.receipt then
      if !receipt.switched && !receiptMatches receipt s.heads then
        return { s with prepared := none, captured := none }
    let choices ← liftQuery (selectParents s.evidence (queryFuel s.evidence) s.heads s.receipt canonical)
    let walk ← liftQuery (suffix s.evidence s.heads s.receipt (queryFuel s.evidence) canonical)
    let cached ← liftQuery (candidates s.evidence (queryFuel s.evidence) s.heads s.receipt canonical)
    let queries := choices.choices ++ walk.anchors ++ walk.references ++ [(canonical, chooseSource cached)]
    let outside := queries.filterMap fun (parent, choice) => match choice with
      | .selected _ _ => none
      | other => some (Outside.sources parent other)
    if !outside.isEmpty then
      return { s with outside := s.outside ++ outside, phase := .preparing }
    let prepared ← liftQuery (prepare s canonical rendered)
    return { s with prepared := some prepared, phase := .prepared }
  | .allocateLabel => .ok { s with allocatedLabels := s.allocatedLabels + 1 }
  | .write data => do
    let responsible := s.saved.applied ++ s.saved.custody
    if !data.records.all (responsible.contains ·) then throw .custody
    match s.evidence.native.find? (fun b => decide (b.id = data.body.id)) with
    | some old =>
      if old ≠ data.body then throw .bodyConflict
      return s
    | none => return { s with
        evidence := { s.evidence with native := s.evidence.native ++ [data.body] },
        createdBodies := s.createdBodies + 1 }
  | .revalidate => do
    if s.phase ≠ .prepared then throw .phase
    let some captured := s.captured | throw .phase
    if !sameSet captured s.heads then
      return { s with phase := .preparing, prepared := none, captured := none }
    let some prepared := s.prepared | throw .phase
    let git ← liftQuery (gitChoice s.evidence (queryFuel s.evidence) s.me s.heads
      prepared.rendered s.saved s.receipt)
    let destination ← liftQuery (moveDestination s (some prepared.rendered) none)
    let beside := destination.to.filter (fun id => decide (id ≠ prepared.rendered))
    let publication : Publication := {
      incoming := prepared.rendered, beside,
      mergeBeforeExport := git.useCurrent && !beside.isEmpty }
    return { s with
      git := some git, publication := some publication,
      phase := .validated, closedPublication := true }
  | .observeExport observation => do
    if s.phase ≠ .validated && s.phase ≠ .cleanup && s.helper ≠ some .lockedExport then
      throw .phase
    if !s.physicalKnown || observation.before ≠ s.physicalGit then
      throw (.evidence (.malformed "export physical input"))
    let raw ← liftQuery (s.evidence.nativeBody observation.input)
    let output ← liftQuery (s.evidence.nativeBody observation.output)
    if { output with id := raw.id, gitFields := raw.gitFields } ≠ raw ||
        output.gitFields ≠ observation.recordedFields then
      throw (.evidence (.malformed "export replacement body"))
    let mut publication := s.publication
    if s.phase = .validated then
      let some plan := publication | throw .phase
      let expected := if plan.mergeBeforeExport || plan.firstExported then plan.merged
        else some plan.incoming
      if expected ≠ some observation.input then throw .phase
      publication := some (if plan.mergeBeforeExport || plan.firstExported then
        { plan with merged := some observation.output, firstExported := true, mergeExported := true }
        else { plan with incoming := observation.output, firstExported := true })
    return { s with
      physicalGit := observation.after,
      publication,
      saved := { s.saved with exports := s.saved.exports ++
        [{
           input := observation.input, output := observation.output, parents := raw.parents,
           recordedFields := observation.recordedFields, physicalBefore := observation.before,
           physicalAfter := observation.after, outcomes := observation.outcomes }] } }
  | .merge inputs output => do
    if s.phase ≠ .validated then throw .phase
    let some plan := s.publication | throw .phase
    if plan.beside.isEmpty || plan.merged.isSome ||
        (!plan.mergeBeforeExport && !plan.firstExported) then throw .phase
    let bodies ← liftQuery ((plan.beside ++ [plan.incoming]).mapM s.evidence.nativeBody)
    let ordered := (bodies.mergeSort fun a b =>
      if a.endTime = b.endTime then decide (a.id.value ≤ b.id.value)
      else decide (a.endTime ≤ b.endTime)).map (·.id)
    if inputs ≠ ordered then throw (.evidence (.malformed "native merge inputs"))
    let _ ← liftQuery (s.evidence.nativeBody output)
    return { s with publication := some { plan with merged := some output } }
  | .bookkeeping physical fields => do
    let _ ← liftQuery (s.evidence.nativeBody physical)
    return { s with saved := { s.saved with expected := put s.saved.expected physical fields } }
  | .saveIntent incoming merged => do
    let some receipt := s.receipt | throw .phase
    if s.phase ≠ .validated then throw .phase
    let some plan := s.publication | throw .phase
    if (s.colocated && (!plan.firstExported || (!plan.beside.isEmpty && !plan.mergeExported))) ||
        incoming ≠ some plan.incoming || merged ≠ plan.merged then throw .phase
    let intent ← liftQuery (moveDestination s incoming merged)
    let saved := takeResponsibility s.saved receipt intent
    return { s with saved, phase := .held }
  | .planOrdinary incoming merged => do
    if s.phase ≠ .validated || s.receipt.isSome then throw .phase
    let some plan := s.publication | throw .phase
    if (s.colocated && (!plan.firstExported || (!plan.beside.isEmpty && !plan.mergeExported))) ||
        incoming ≠ some plan.incoming || merged ≠ plan.merged then throw .phase
    let intent ← liftQuery (moveDestination s incoming merged)
    return { s with ordinaryMove := some intent, phase := .held }
  | .addHead head => do
    let some intent := s.saved.intent.or s.ordinaryMove | throw .intent
    let destination ← if s.closedRecovery then do
      let some captured := s.captured | throw .phase
      liftQuery (recoveryDestination s.evidence (queryFuel s.evidence) captured intent)
      else pure intent.to
    if !destination.contains head then throw .intent
    let _ ← liftQuery (s.evidence.nativeBody head)
    return { s with heads := unique (s.heads ++ [head]), phase := .moving }
  | .finishMove => do
    let some intent := s.saved.intent.or s.ordinaryMove | throw .intent
    let heads ← if s.closedRecovery then do
      let some captured := s.captured | throw .phase
      let destination ← liftQuery (recoveryDestination s.evidence (queryFuel s.evidence) captured intent)
      let removed := captured.filter (fun head => !destination.contains head)
      pure (unique (s.heads.filter (fun head => !removed.contains head) ++ destination))
      else
        let old := intent.fromHeads.map (·.1)
        pure (unique (s.heads.filter (fun head => !old.contains head) ++ intent.to))
    let _ ← liftQuery (heads.mapM s.evidence.nativeBody)
    return { s with
      heads, phase := .cleanup,
      renderPlan := none, receiptPlan := none, prepared := none, captured := none,
      receipt := s.receipt.map (fun r => { r with switched := true }) }
  | .helperEnter colocated => do
    if s.helper.isSome || colocated ≠ s.colocated then throw .phase
    return { s with helper := some (if colocated && s.heads.length > 1 then .lockedExport else .direct) }
  | .helperExit => .ok { s with helper := none }
  | .helperHeads heads => do
    -- This only records a frontier of pre-readable bodies. An admitted own action that
    -- creates helper operations is still required before any composed cleanup theorem.
    if s.helper.isNone then throw .phase
    let _ ← liftQuery (heads.mapM s.evidence.nativeBody)
    return { s with heads }
  | .finish => do
    if s.helper.isSome || s.phase ≠ .cleanup then throw .phase
    return { s with
      phase := .complete, closedPublication := false,
      closedRecovery := false, saved := { s.saved with intent := none }, receipt := none,
      receiptPlan := none, renderPlan := none, prepared := none, captured := none,
      ordinaryMove := none, git := none, publication := none }
  | .interrupt => .ok { s with
      phase := .interrupted, closedPublication := false,
      receipt := none, receiptPlan := none, renderPlan := none, prepared := none, captured := none,
      closedRecovery := false, helper := none }
  | .restart => .ok { s with
      phase := .interrupted, memo := {}, prepared := none, captured := none,
      receiptPlan := none, renderPlan := none,
      receipt := none, ordinaryMove := none, git := none, closedPublication := false,
      publication := none, closedRecovery := false, helper := none }
  | .eraseMemo => .ok { s with memo := {} }
  | .startRecovery => .ok { s with
      phase := .interrupted, captured := some s.heads, closedRecovery := true,
      receipt := none, receiptPlan := none, renderPlan := none, prepared := none }
  | .finishRecovery => .ok { s with
      closedRecovery := false, captured := none,
      receiptPlan := none, renderPlan := none, prepared := none }
  | .external heads physicalGit => .ok { noteExternal s with heads, physicalGit, physicalKnown := true }
  | .native observation => do
    let (evidence, nativeCount, canonicalCount) ← installNative s.evidence observation
    return { noteExternal s with
      evidence, heads := observation.heads,
      physicalKnown := true,
      physicalGit := observation.physicalGit, createdBodies := s.createdBodies + nativeCount,
      createdCanonicals := s.createdCanonicals + canonicalCount }
  | .loseEvidence ids => .ok { noteExternal s with
      evidence := { s.evidence with native := s.evidence.native.filter (fun b => !ids.contains b.id) } }
  | .loseCanonicalEvidence ids => .ok { noteExternal s with
      evidence :=
      { s.evidence with canonical := s.evidence.canonical.filter (fun b => !ids.contains b.id) } }
  | .failedCall => .ok { s with outside := s.outside ++ [.failedCall] }

def run (initial : State) (actions : List Action) : Except StepError State :=
  actions.foldlM step initial

/-- E1/E2 and recovery exclusions are computed from recorded external effects and intervals.
Source-domain failures and excluded mid-call outcomes are also retained in this list. -/
def inScope (s : State) : Bool := s.outside.isEmpty

/-- Pure frame facts only; these do not discharge an exporter, source or native-call law. -/
theorem eraseMemo_keeps_evidence (s : State) :
    step s .eraseMemo = .ok { s with memo := {} } := rfl

theorem restart_keeps_responsibility (s : State) :
    (step s .restart).map (·.saved) = .ok s.saved := rfl

end Musubi.NativeLifecycle

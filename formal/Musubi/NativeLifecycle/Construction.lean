/-
Executable receipt and render construction from raw observations. Encoding tables contain
independent hashes of complete computed shapes; native field tables contain exact native
merge inputs/results. Neither table supplies a correct source/ownership/render predicate.
Authentication and the actual Rust/codec correspondence remain explicit native gates.
-/
import Musubi.NativeLifecycle.NativeFacts

namespace Musubi.NativeLifecycle

def sortedBindings (bindings : Bindings) : Bindings :=
  bindings.mergeSort (fun a b => decide (String.ofList a.1 ≤ String.ofList b.1))

def stampOf (p : Presence) : Stamp :=
  let work := fun (rows : List (Copy × List Work)) =>
    (orderedCopies (rows.map (·.1))).map fun copy =>
      (copy, (unique (((lookup rows copy).getD []).map (·.original))).mergeSort
        (fun a b => decide (a.value ≤ b.value)))
  let durations := (orderedCopies (p.forgetAfter.map (·.1))).map fun copy =>
    (copy, (((lookup p.forgetAfter copy).getD []).map (fun entry =>
      (entry.1.original, entry.2))).mergeSort (fun a b => decide (a.1.value ≤ b.1.value)))
  { known := orderedCopies p.known, latest := work p.latest, worked := work p.worked,
    forgetAfter := durations }

structure CanonicalBuild where
  evidence : Evidence
  images : List (Canonical × List Canonical) := []
  writes : List CanonicalBody := []
deriving DecidableEq, Repr

/-- Complete input histories must not contain two raw versions of one original. Stored
historical bodies outside this closure remain allowed. -/
def originalClosure (e : Evidence) (fuel : Nat) (id : Canonical) : Query Unit := do
  let ids ← canonicalClosure e fuel id
  let bodies ← ids.mapM e.canonicalBody
  if !(decide (bodies.map (·.original)).Nodup) then
    throw (.malformed "two versions of an original in one input history")

def contractOne (before : Evidence) (table : EncodingTable) (drops : Drops) :
    Nat → Canonical → CanonicalBuild → Query (CanonicalBuild × List Canonical)
  | 0, _, _ => .error .exhausted
  | fuel + 1, id, build => do
    if let some images := lookup build.images id then return (build, images)
    let body ← before.canonicalBody id
    let mut build := build
    let mut parents := []
    for parent in body.parents do
      let (next, images) ← contractOne before table drops fuel parent build
      build := next
      parents := parents ++ images
    parents := unique parents
    let (nextBuild, images) ← if drops.contains body.original && id ≠ before.root then
        pure (build, parents)
      else if parents = body.parents then pure (build, [id])
      else do
        let was ← presence before (before.canonical.length + 1) id
        let parentPresence ← parents.mapM fun parent => do
          return (parent, ← presence build.evidence (build.evidence.canonical.length + 1) parent)
        let merged ← mergePresence build.evidence (build.evidence.canonical.length + 1) parentPresence
        let computed := applyKind { body with parents, stamp := none } merged
        let stamp := if stampOf computed = stampOf was then none else some (stampOf was)
        let result ← encodeCanonical build.evidence table { body with parents, stamp }
        let next := { build with
          evidence := { build.evidence with
            canonical := unique (build.evidence.canonical ++ [result]) },
          writes := unique (build.writes ++ [result]) }
        pure (next, [result.id])
    return ({ nextBuild with images := put nextBuild.images id images }, images)

structure ReceiptRequest where
  identity : Nat
  recordPrefix : Nat
  prunedCount : Nat := 0
  records : List Record
deriving DecidableEq, Repr

def requestReceipt (request : ReceiptRequest) (input : Evidence) (heads : List Physical) : Receipt :=
  { identity := request.identity, recordPrefix := request.recordPrefix,
    prunedCount := request.prunedCount, records := request.records, capturedHeads := heads,
    input, locals := [] }

def requestDrops (saved : Persistent) (receipt : Receipt) : Drops :=
  let common := if saved.recordPrefix = receipt.recordPrefix ∧ saved.prunedCount = receipt.prunedCount then
    ((saved.applied.zip receipt.records).takeWhile (fun pair => decide (pair.1 = pair.2))).length
    else 0
  let held := receipt.recordPrefix :: receipt.records.map (·.identity)
  unique (saved.pending ++ (receipt.records.drop common).flatMap (·.drops) ++
    (saved.applied.drop common).flatMap (·.drops) ++
    (saved.custody.filter (fun record => !held.contains record.identity)).flatMap (·.drops))

structure BaseBuild where
  evidence : Evidence
  writes : List CanonicalBody := []
  base : Option Canonical
deriving DecidableEq, Repr

/-- Receive advances the shared base through each new incoming record, not through the
union of local pending drops. A missing stored base stays unchanged; an expansion takes its
first image in parent order. Lost applied records reset the base to the root first. -/
def constructBase (before : Evidence) (table : EncodingTable) (saved : Persistent)
    (receipt : Receipt) : Query BaseBuild := do
  let common := if saved.recordPrefix = receipt.recordPrefix ∧
      saved.prunedCount = receipt.prunedCount then
    ((saved.applied.zip receipt.records).takeWhile (fun pair => decide (pair.1 = pair.2))).length
    else 0
  let mut result : BaseBuild := {
    evidence := before,
    base := if common < saved.applied.length then some before.root else saved.acceptedBase }
  for record in receipt.records.drop common do
    if let some old := result.base then
      if result.evidence.canonical.any (fun body => decide (body.id = old)) then
        let input := result.evidence
        let fuel := input.canonical.length + table.canonical.length + 1
        originalClosure input fuel old
        let (contracted, images) ← contractOne input table record.drops fuel old
          { evidence := input }
        result := { result with
          evidence := contracted.evidence, writes := unique (result.writes ++ contracted.writes),
          base := images.head? }
  return result

def canonicalGeneration (e : Evidence) : Nat → Canonical → Query Nat
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    if id = e.root then return 0
    let body ← e.canonicalBody id
    let parents ← body.parents.mapM (canonicalGeneration e fuel)
    return parents.foldl max 0 + 1

/-- Contraction's generation floor is derived from stored dropped originals. Matching
these original-named drops to the native receive path's exact canonical versions remains
part of the raw identity/template simulation obligation. -/
def rewriteFloor (e : Evidence) (fuel : Nat) (drops : Drops) : Query (Option Nat) := do
  let stored := e.canonical.filter fun body => body.id != e.root && drops.contains body.original
  let generations ← stored.mapM fun body => canonicalGeneration e fuel body.id
  return generations.foldl (fun floor generation =>
    some ((floor.map (min generation)).getD generation)) none

def mayRewrite (e : Evidence) (fuel : Nat) (drops : Drops) (floor : Option Nat)
    (id : Canonical) : Query Bool := do
  if id = e.root then return false
  let body ← e.canonicalBody id
  if drops.contains body.original then return true
  match floor with
  | none => return false
  | some floor =>
    let generation ← canonicalGeneration e fuel id
    return decide (floor < generation)

/-- Like rewrite_locals' standing walk, stop before unaffected canonical operations and
unmapped prejoin history. In particular, a join's physical parent is not canonical-normalized
merely because its canonical form has the root as parent. -/
def affectedStanding (e : Evidence) (drops : Drops) (floor : Option Nat) :
    Nat → Physical → Query (List Canonical)
  | 0, _ => .error .exhausted
  | fuel + 1, physical => do
    let raw ← e.nativeBody physical
    match ← sourceCounterpart e (fuel + 1) physical with
    | none => return []
    | some canonical =>
      if !(← mayRewrite e (fuel + 1) drops floor canonical) then return []
      return unique ((← raw.parents.mapM (affectedStanding e drops floor fuel)).flatten ++
        [canonical])

def affectedCanonical (e : Evidence) (drops : Drops) (floor : Option Nat)
    (standing : List Canonical) : Nat → Canonical → Query (List Canonical)
  | 0, _ => .error .exhausted
  | fuel + 1, id => do
    if id = e.root then return []
    if !standing.contains id && !(← mayRewrite e (fuel + 1) drops floor id) then return []
    let body ← e.canonicalBody id
    return unique ((← body.parents.mapM
      (affectedCanonical e drops floor standing fuel)).flatten ++ [id])

def receiptRewriteDomain (e : Evidence) (fuel : Nat) (drops : Drops)
    (heads : List Physical) : Query (List Canonical) := do
  let floor ← rewriteFloor e fuel drops
  let standing := unique (← heads.mapM (affectedStanding e drops floor fuel)).flatten
  let tops := unique (standing ++ (← heads.mapM e.counterpart).filterMap id)
  return unique (← tops.mapM (affectedCanonical e drops floor standing fuel)).flatten

def privateContext (e : Evidence) (fuel : Nat) (me : Copy) (canonical : Canonical)
    (own : Bindings) : Query (Option Namespace) := do
  let names ← ownNames e fuel me canonical
  if own.all (fun entry => names.contains entry.1) then return none
  return some {
    source := me, known := [me],
    names := (sortedBindings own).map (fun entry => (entry.1, ⟨me, entry.1⟩)) }

def selectedPhysical (e : Evidence) (fuel : Nat) (heads : List Physical)
    (receipt : Option Receipt) (generated : List (Canonical × Physical))
    (canonical : Canonical) : Query Physical := do
  if let some generated := lookup generated canonical then return generated
  match chooseSource (← candidates e fuel heads receipt canonical) with
  | .selected _ id => return id
  | .missing => throw (.source canonical)
  | .unavailable _ ((_, gap) :: _) => throw gap
  | _ => throw (.malformed "source query outside U")

structure ReceiptBuild where
  input : Evidence
  saved : Persistent
  computed : Receipt
  base : Option Canonical
  own : Bindings
  canonicalWrites : List CanonicalBody
  nativeWrites : List NativeBody
  identities : List IdentityRow
deriving DecidableEq, Repr

/-- The observed Taking.locals map is absent from this interface. The result is computed
from contraction, exact native templates and parents-first local rewrites. -/
def constructReceipt (before : Evidence) (facts : NativeFacts) (saved : Persistent)
    (me : Copy) (heads : List Physical) (request : ReceiptRequest) : Query ReceiptBuild := do
  let fuel := before.native.length + before.canonical.length + facts.encodings.canonical.length + 1
  let receipt := requestReceipt request before heads
  let own ← ownAtHeads before fuel me heads
  let drops := requestDrops saved receipt
  if drops.contains (← before.canonicalBody before.root).original then
    throw (.malformed "receipt drops the root")
  let sharedBase ← constructBase before facts.encodings saved receipt
  let affected ← receiptRewriteDomain before fuel drops heads
  let walk ← nativeFrontierClosure before fuel heads
  let mut contracted : CanonicalBuild := {
    evidence := sharedBase.evidence, writes := sharedBase.writes }
  for physical in walk do
    let counterpart ← before.counterpart physical
    if let some canonical := counterpart then
      if affected.contains canonical then
        originalClosure before fuel canonical
        let (next, _) ← contractOne before facts.encodings drops fuel canonical contracted
        contracted := next
  let mut evidence := contracted.evidence
  let mut generated := [(before.root, before.physicalRoot)]
  let mut locals := []
  let mut writes := []
  let mut identities := []
  for physical in walk do
    let raw ← before.nativeBody physical
    match ← sourceCounterpart before fuel physical with
    | none => locals := put locals physical [physical]
    | some canonical =>
      if !affected.contains canonical then
        locals := put locals physical [physical]
        continue
      let selected ← selectedPhysical before fuel heads none [] canonical
      if selected ≠ physical then throw (.malformed "receipt template outside U")
      let original ← before.canonicalBody canonical
      let images := (lookup contracted.images canonical).getD [canonical]
      if drops.contains original.original && canonical ≠ before.root then
        let images ← images.mapM (selectedPhysical evidence fuel heads none generated)
        locals := put locals physical (unique images)
      else do
        let some image := images.head? | throw (.malformed "surviving original has no image")
        let body ← evidence.canonicalBody image
        let parents ← body.parents.mapM (selectedPhysical evidence fuel heads none generated)
        let changed := image ≠ canonical || raw.parents ≠ parents ||
          (raw.marker.isSome && raw.marker ≠ some image)
        let result ← if changed then do
          let own ← ownOfNative before fuel me physical
          let context ← privateContext evidence fuel me image own
          encodeNative evidence facts.encodings { raw with parents, marker := some image, context }
          else pure raw
        evidence := { evidence with native := unique (evidence.native ++ [result]) }
        if changed then writes := unique (writes ++ [result])
        if result.id ≠ physical then
          let row : IdentityRow := ⟨result.id, image, body.original, .markedBody⟩
          identities := unique (identities ++ [row])
          evidence ← evidence.installIdentities [row]
        generated := put generated image result.id
        locals := put locals physical [result.id]
  return {
    input := before, saved, computed := { receipt with locals }, base := sharedBase.base, own,
    canonicalWrites := contracted.writes, nativeWrites := writes, identities }

/-- Sparse identity entries are an implementation detail. Every observed key must belong
to the computed native walk, and defaulting an omitted key to itself must give exactly the
computed image list. Changed mappings cannot disappear, and extra sources cannot appear. -/
def receiptInputMatches (build : ReceiptBuild) (observed : Receipt) : Bool :=
  let expected := build.computed
  observed.identity == expected.identity && observed.recordPrefix == expected.recordPrefix &&
    observed.prunedCount == expected.prunedCount && decide (observed.records = expected.records) &&
    sameSet observed.capturedHeads expected.capturedHeads && !observed.switched &&
    decide (observed.input = build.input) && uniqueKeys observed.locals &&
    observed.locals.all (fun row => (lookup expected.locals row.1).isSome) &&
    expected.locals.all (fun row => decide ((lookup observed.locals row.1).getD [row.1] = row.2))

/-- Reserved names are a union at the nearest mapped operations, not a workspace merge.
Only names containing slash can change another copy's displayed prefix. -/
def reservedNames (e : Evidence) (me : Copy) : Nat → List Physical → Query (List Name)
  | 0, _ => .error .exhausted
  | fuel + 1, heads => do
    let mut names := []
    for head in unique heads do
      let raw ← e.nativeBody head
      match ← sourceCounterpart e (fuel + 1) head with
      | some canonical =>
        names := names ++ (← ownNames e (fuel + 1) me canonical) ++
          (← privateNames e me (fuel + 1) head)
      | none => names := names ++ (← reservedNames e me fuel raw.parents)
    return unique (names.filter (·.contains '/'))

def orderedFrontierBases (e : Evidence) (fuel : Nat) (left right : List Physical) :
    Query (List Physical) := do
  let ours ← nativeFrontierClosure e fuel left
  let theirs ← nativeFrontierClosure e fuel right
  let common := ours.filter (theirs.contains ·)
  let mut maximal := []
  for a in common do
    let mut below := false
    for b in common do
      if a ≠ b && (← nativeAncestor e fuel a b) then below := true
    if !below then maximal := maximal ++ [a]
  match maximal with
  | [] => return []
  | [base] => return [base]
  | _ =>
    let some observed := e.frontierBases.find? (fun row =>
      decide (row.1 = left ∧ row.2.1 = right)) | throw (.frontierBases left right)
    if !sameSet observed.2.2 maximal || !(decide observed.2.2.Nodup) then
      throw (.malformed "frontier bases differ from complete graph")
    return observed.2.2

def keptNames (e : Evidence) (fuel : Nat) (me : Copy) (heads : List Physical)
    (receipt : Option Receipt) (walk : Suffix) (reserved : List Name) : Query Bindings := do
  let mut machines := []
  let mut starts := []
  for id in walk.order do
    let body ← e.canonicalBody id
    machines := machines ++ machinesOf body.workspaces (← presence e fuel id).known
    for parent in body.parents do
      if !walk.order.contains parent then
        starts := unique (starts ++ [← selectedPhysical e fuel heads receipt [] parent])
  let renamedNames := reserved.filter (namesOtherMachine me · (unique machines))
  if renamedNames.isEmpty || starts.isEmpty then return []
  let sortedHeads := heads.mergeSort (fun a b => decide (a.value ≤ b.value))
  let bases ← orderedFrontierBases e fuel starts sortedHeads
  let mut kept := []
  for base in bases do
    for (name, commit) in (← e.nativeBody base).workspaces do
      if renamedNames.contains name && (lookup kept name).isNone then
        kept := kept ++ [(name, commit)]
  return kept

def renderingSelection (e : Evidence) (fuel : Nat) (heads : List Physical)
    (receipt : Option Receipt) (generated : List (Canonical × Physical))
    (canonical : Canonical) : Query ParentSelection := do
  let body ← e.canonicalBody canonical
  let choices ← body.parents.mapM fun parent => do
    let choice ← match lookup generated parent with
      | some id => pure (SourceChoice.selected .rendered id)
      | none => do pure (chooseSource (← candidates e fuel heads receipt parent))
    return (parent, choice)
  return { choices }

def renderedSource (e : Evidence) (fuel : Nat) (heads : List Physical)
    (receipt : Option Receipt) (generated : List (Canonical × Physical))
    (body : CanonicalBody) : Query NativeSource := do
  match body.references with
  | [] => return .parents
  | [target] =>
    let mut ancestor := false
    for parent in body.parents do
      if ← canonicalAncestor e fuel target parent then ancestor := true
    if !ancestor then throw (.renderReference target)
    let physical ← selectedPhysical e fuel heads receipt generated target
    return if body.referenceRevert then .revert physical else .restore physical
  | _ => throw (.malformed "multiple restore/revert references")

structure RenderNode where
  canonical : Canonical
  selections : ParentSelection
  own : OwnSelection
  body : NativeBody
  identity : IdentityRow
deriving DecidableEq, Repr

structure RenderBuild where
  input : Evidence
  heads : List Physical
  receipt : Option Receipt
  target : Canonical
  suffix : Suffix
  reserved : List Name
  kept : Bindings
  nodes : List RenderNode
  result : Physical
deriving DecidableEq, Repr

structure CurrentGitBuild where
  input : Evidence
  heads : List Physical
  canonical : Canonical
  before : NativeBody
  fields : Nat
  body : NativeBody
  identity : IdentityRow
deriving DecidableEq, Repr

structure PreparationProbeBuild where
  input : Evidence
  capturedHeads : List Physical
  rendered : Physical
  orderedInputs : List Physical
  written : List NativeBody
  result : Physical
  contextAfter : Nat
deriving DecidableEq, Repr

/-- The single-rendered-operand branch of shipping check_mergeable/try_merge. Captured H
and the computed rendered operand determine the concurrent tuple. Timestamp sorting is
stable over that tuple; the second native call uses its reverse. No Rust-selected vector
or overlap Boolean supplies the result. -/
def preparationProbeInputs (e : Evidence) (heads : List Physical) (rendered : Physical)
    (index : Nat) : Query (List Physical) := do
  let body ← e.nativeBody rendered
  let mut concurrent := []
  for head in heads do
    if head ≠ rendered && !body.parents.contains head then
      if !(← nativeAncestor e (e.native.length + e.canonical.length + 1) head rendered) then
        concurrent := concurrent ++ [head]
  if concurrent.isEmpty then throw (.nativeFact "no preparation merge probe at this boundary")
  let ordered ← orderedPublicationInputs e (concurrent ++ [rendered])
  match index with
  | 0 => return ordered
  | 1 => return ordered.reverse
  | _ => throw (.nativeFact "preparation probe index")

def constructPreparationProbe (e : Evidence) (facts : NativeFacts)
    (heads : List Physical) (rendered : Physical) (index : Nat) :
    Query PreparationProbeBuild := do
  let ordered ← preparationProbeInputs e heads rendered index
  let matching := facts.preparationProbes.filter fun fact =>
    fact.contextBefore == e.repositoryContext && sameSet fact.nativeGraph e.native &&
      decide (fact.orderedInputs = ordered)
  let [fact] := unique matching | throw (.nativeFact "independent preparation probe observation")
  if fact.written.isEmpty || !fact.written.any (fun body => body.id == fact.result) then
    throw (.nativeFact "native probe has no recorded result write")
  if fact.written.any (fun body => body.marker.isSome) then
    throw (.nativeFact "marked probe needs a separate native identity law")
  let mut graph := e
  for body in fact.written do
    let _ ← body.parents.mapM graph.nativeBody
    match graph.native.find? (fun old => old.id == body.id) with
    | some old => if old ≠ body then throw (.malformed "native probe body conflict")
    | none => graph := { graph with native := graph.native ++ [body] }
  let result ← graph.nativeBody fact.result
  if result.parents ≠ ordered then throw (.nativeFact "native probe ordered result parents")
  return {
    input := e, capturedHeads := heads, rendered := rendered, orderedInputs := ordered,
    written := fact.written, result := fact.result, contextAfter := fact.contextAfter }

def CurrentGitBuild.writes (build : CurrentGitBuild) : Bool :=
  build.body.id != build.before.id

def currentGitBody (before : NativeBody) (canonical : Canonical) (fields : Nat) : NativeBody :=
  if before.gitFields = fields then before
  else { before with gitFields := fields, marker := some canonical }

def encodeCurrentGit (e : Evidence) (table : EncodingTable) (before : NativeBody)
    (canonical : Canonical) (fields : Nat) : Query NativeBody :=
  if before.gitFields = fields then .ok before
  else encodeNative e table (currentGitBody before canonical fields)

/-- `with_per_machine` reuses an equal field record verbatim. Otherwise it changes only
the full per-machine projection and makes canonical identity explicit. The exact observed
encoding is consulted only after this complete body has been computed. -/
def constructCurrentGit (e : Evidence) (facts : NativeFacts) (heads : List Physical)
    (canonical : Canonical) (incoming : Physical) : Query CurrentGitBuild := do
  let before ← e.nativeBody incoming
  let original := (← e.canonicalBody canonical).original
  if (← e.identity incoming) ≠ canonical then
    throw (.malformed "current Git input identity differs from prepared target")
  let fields ← inheritedFields e facts.fields heads
  let body ← encodeCurrentGit e facts.encodings before canonical fields
  let identity : IdentityRow :=
    ⟨body.id, canonical, original, if body.marker.isSome then .markedBody else .original⟩
  let checked := { e with native := unique (e.native ++ [body]) }
  checked.checkIdentity identity
  return { input := e, heads, canonical, before, fields, body, identity }

/-- Compute every hash-visible render field before looking up its independently observed
hash. Cached Git records are reused only for identical ordered physical parents. -/
def constructRender (input : Evidence) (facts : NativeFacts) (me : Copy)
    (heads : List Physical) (receipt : Option Receipt) (target : Canonical) :
    Query RenderBuild := do
  let fuel := input.native.length + input.canonical.length + facts.encodings.native.length + 1
  let walk ← suffix input heads receipt fuel target
  let reserved ← reservedNames input me fuel heads
  let kept ← keptNames input fuel me heads receipt walk reserved
  let mut evidence := input
  let mut generated := []
  let mut nodes := []
  for canonical in walk.order do
    let body ← evidence.canonicalBody canonical
    let selections ← renderingSelection evidence fuel heads receipt generated canonical
    let some parents := selections.parents | throw (.malformed "render parents outside U")
    let own ← selectOwn evidence fuel me canonical parents heads receipt
    let naming ← renderedNames evidence fuel me canonical
      (unique (reserved ++ own.bindings.map (·.1)))
    let mut workspaces := []
    for (key, commit) in body.workspaces do
      let some name := lookup naming key | throw (.malformed "missing rendered name")
      workspaces := put workspaces name commit
    for (name, commit) in own.bindings do
      if !(naming.map (·.2)).contains name then workspaces := put workspaces name commit
    -- Private metadata is computed before the merge-base slots are put back.
    let context ← privateContext evidence fuel me canonical own.bindings
    for (name, commit) in kept do
      if (lookup workspaces name).isNone then workspaces := put workspaces name commit
    let cached := chooseSource (← candidates input fuel heads receipt canonical)
    let fields ← match cached with
      | .selected _ id => do
        let raw ← input.nativeBody id
        if raw.marker.isNone then throw (.nativeFact "original native render authority")
        if raw.parents = parents then pure raw.gitFields
        else inheritedFields evidence facts.fields parents
      | .missing => inheritedFields evidence facts.fields parents
      | .unavailable _ ((_, gap) :: _) => throw gap
      | _ => throw (.malformed "render target outside U")
    let source ← renderedSource evidence fuel heads receipt generated body
    let p ← presence evidence fuel canonical
    let prefixes := Names.assign (orderedCopies (me :: machinesOf body.workspaces p.known))
      (unique ((← ownNames evidence fuel me canonical) ++ reserved ++ own.bindings.map (·.1)))
    let authorWorkspace := body.authorWorkspace.map fun key =>
      Names.localName me prefixes key.owner key.name
    let result ← encodeNative evidence facts.encodings {
      id := ⟨0⟩, parents, endTime := body.endTime, workspaces := sortedBindings workspaces,
      marker := some canonical, context, source,
      reserved := reserved.mergeSort (fun a b => decide (String.ofList a ≤ String.ofList b)),
      authorWorkspace, presenceStamp := body.stamp, gitFields := fields, content := body.content,
      description := body.description }
    let identity : IdentityRow := ⟨result.id, canonical, body.original, .markedBody⟩
    evidence := { evidence with native := unique (evidence.native ++ [result]) }
    evidence ← evidence.installIdentities [identity]
    generated := put generated canonical result.id
    nodes := nodes ++ [{ canonical, selections, own, body := result, identity }]
  let result ← selectedPhysical evidence fuel heads receipt generated target
  return { input, heads, receipt, target, suffix := walk, reserved, kept, nodes, result }

end Musubi.NativeLifecycle

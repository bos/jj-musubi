/-
Finite native fixture codec. Raw bodies and retained identity evidence are inputs; Rust's
selected locals, ownership and publication answers are comparison targets. Missing evidence
is an interpretation failure, never a claim that Rust refused the native call.
-/
import Lean
import Musubi.NativeLifecycle.RunSound

namespace Musubi.NativeLifecycle.Json
open Lean (Json ToJson toJson)

instance : ToJson Char where toJson c := Json.str (String.singleton c)
deriving instance ToJson for Musubi.Names.Key
deriving instance ToJson for Original, Canonical, Physical, WorkspaceKey, Namespace, Work
deriving instance ToJson for IdentityIssue, Gap
deriving instance ToJson for Stamp, CanonicalBody, NativeSource, NativeBody, IdentityKind, IdentityRow
deriving instance ToJson for BaseObservation, Evidence, Record, Receipt, Intent, RetainedExport
deriving instance ToJson for Persistent, ReceiptRequest, ReceiptBuild, Role, CandidateSet, Candidates
deriving instance ToJson for SourceChoice, Suffix, ParentSelection, OwnSource, OwnSelection, GitChoice
deriving instance ToJson for RenderNode, RenderBuild

def get (j : Json) (key : String) : Except String Json := j.getObjVal? key
def str (j : Json) (key : String) : Except String String := j.getObjValAs? String key
def rows (j : Json) (key : String) : Except String (List Json) := do
  return (← j.getObjValAs? (Array Json) key).toList
def strings (j : Json) (key : String) : Except String (List String) := do
  return (← j.getObjValAs? (Array String) key).toList
def optionalString (j : Json) (key : String) : Except String (Option String) :=
  j.getObjValAs? (Option String) key

def restoreReference (description : String) : Bool :=
  ["undo: restore to operation ", "redo: restore to operation ",
    "undo: revert operation ", "redo: revert operation ",
    "restore to operation ", "revert operation "].any (fun leading => description.startsWith leading)

def without (j : Json) (keys : List String) : Except String Json := do
  return Json.mkObj ((← j.getObj?).toList.filter fun row => !keys.contains row.1)

def content (raw : Json) : Except String String := do
  let metadata ← get raw "metadata"
  let attrs ← without (← get metadata "attributes")
    ["musubi.canonical", "musubi.local-workspaces", "musubi.reserved-workspaces", "musubi.presence"]
  let metadata ← without metadata ["workspaceName", "attributes"]
  let view ← get raw "view"
  let remotes ← without (← get view "remotes") ["git"]
  let view ← without view ["workspaces", "gitRefs", "gitHeads", "remotes"]
  return (Json.mkObj [
    ("metadata", Json.mkObj ((← metadata.getObj?).toList ++ [("attributes", attrs)])),
    ("view", Json.mkObj ((← view.getObj?).toList ++ [("remotes", remotes)])),
    ("predecessors", ← get raw "predecessors")]).compress

def gitFields (raw : Json) : Except String String := do
  let view ← get raw "view"
  let remote := ((← get view "remotes").getObjVal? "git").toOption.getD Json.null
  return (Json.mkObj [("refs", ← get view "gitRefs"), ("heads", ← get view "gitHeads"),
    ("remote", remote)]).compress

structure Context where
  physical : List String
  canonical : List String
  original : List String
  commits : List String
  digests : List String
  contents : List String
  fields : List String

def label (pool : List String) (value : String) : Except String Nat :=
  if pool.contains value then .ok (pool.idxOf value)
  else .error s!"incomplete native label pool: {value}"

def sortedPool (j : Json) (key : String) : Except String (List String) := do
  let values ← strings j key
  if values ≠ (unique values).mergeSort (fun a b => decide (a ≤ b)) then
    throw s!"{key}: labels must be distinct and in byte order"
  return values

def context (request : Json) : Except String Context := do
  let ids ← get request "ids"
  let before ← get request "before"
  let after ← get request "after"
  let all ← [before, after].mapM fun snapshot => do
    return (← rows snapshot "canonical") ++ (← rows snapshot "native")
  let all := all.flatten
  return {
    physical := ← sortedPool ids "physical", canonical := ← sortedPool ids "canonical",
    original := ← sortedPool ids "original", commits := ← sortedPool ids "commits",
    digests := ← sortedPool ids "digests",
    contents := unique ((← all.mapM content) ++
      (← rows before "expected").map (fun row => row.compress) ++
      [(← get before "physical").compress, (← get after "physical").compress]),
    fields := unique (← all.mapM gitFields) }

def copy (key : String) : Except String Copy :=
  match key.splitOn "#" with
  | [name, suffix] => if name.isEmpty || suffix.isEmpty || key.contains '/' then
      .error "invalid native copy key" else .ok ⟨name.toList, suffix.toList⟩
  | _ => .error "native copy key lacks its suffix"

def workspace (key : String) : Except String WorkspaceKey := do
  let parts := key.splitOn "/"
  let some owner := parts.head? | throw "empty qualified workspace"
  let name := String.intercalate "/" (parts.drop 1)
  if name.isEmpty then throw "unqualified canonical workspace"
  return ⟨← copy owner, name.toList⟩

def readAttr (metadata : Json) (name : String) : Except String (Option String) := do
  let attrs ← get metadata "attributes"
  match attrs.getObjVal? name with
  | .error _ => return none
  | .ok value => return some (← value.getStr?)

def namespaceAttribute (metadata : Json) : Except String (Option Namespace) := do
  let some text ← readAttr metadata "musubi.local-workspaces" | return none
  let raw ← Json.parse text
  let names ← (← get raw "names").getObj?
  let names ← names.toList.mapM fun (name, key) => do
    return (name.toList, ← workspace (← key.getStr?))
  let result : Namespace := {
    source := ← copy (← str raw "source"),
    known := ← (← strings raw "known").mapM copy, names }
  if !result.valid || !uniqueKeys (names.map fun row => (row.2, row.1)) then
    throw "invalid raw private namespace"
  return some result

def duration (text : String) : Except String (Option Nat) := do
  if text = "never" then return none
  match text.splitOn "." with
  | [seconds, nanos] =>
    let some seconds := seconds.toNat? | throw "invalid stamp seconds"
    let some value := nanos.toNat? | throw "invalid stamp nanoseconds"
    if nanos.length ≠ 9 || value ≥ 1000000000 then throw "noncanonical stamp duration"
    return some (seconds * 1000000000 + value)
  | _ => throw "unsupported raw duration in finite fixture"

def stampText (ctx : Context) (value : Stamp) : String := Id.run do
  let origin := fun id : Original => ctx.original[id.value]!
  let work := fun (kind : String) (entries : List (Copy × List Original)) =>
    (orderedCopies (entries.map (·.1))).flatMap fun owner =>
      ((unique ((lookup entries owner).getD [])).mergeSort
        (fun a b => decide (a.value ≤ b.value))).map fun id =>
          s!"{kind} {copyText owner} {origin id}"
  let mut lines := (orderedCopies value.known).map (fun owner => s!"known {copyText owner}")
  lines := lines ++ work "latest" value.latest ++ work "worked" value.worked
  for owner in orderedCopies (value.forgetAfter.map (·.1)) do
    let entries := ((lookup value.forgetAfter owner).getD []).foldl
      (fun entries row => put entries row.1 row.2) []
    for (id, after) in entries.mergeSort (fun a b => decide (a.1.value ≤ b.1.value)) do
      let after := match after with
        | none => "never"
        | some value =>
          let digits := toString (value % 1000000000)
          s!"{value / 1000000000}." ++ String.ofList (List.replicate (9 - digits.length) '0') ++ digits
      lines := lines ++ [s!"forget-after {copyText owner} {origin id} {after}"]
  return String.intercalate "\n" lines

def stamp (ctx : Context) (metadata : Json) : Except String (Option Stamp) := do
  let some text ← readAttr metadata "musubi.presence" | return none
  let mut known := []
  let mut latest := []
  let mut worked := []
  let mut forgetAfter := []
  for line in text.splitOn "\n" do
    match line.splitOn " " with
    | ["known", owner] => known := unique (known ++ [← copy owner])
    | ["latest", owner, original] =>
      let owner ← copy owner
      latest := put latest owner ((lookup latest owner).getD [] ++ [⟨← label ctx.original original⟩])
    | ["worked", owner, original] =>
      let owner ← copy owner
      worked := put worked owner ((lookup worked owner).getD [] ++ [⟨← label ctx.original original⟩])
    | ["forget-after", owner, original, after] =>
      let owner ← copy owner
      forgetAfter := put forgetAfter owner ((lookup forgetAfter owner).getD [] ++
        [(⟨← label ctx.original original⟩, ← duration after)])
    | _ => throw "invalid raw presence stamp"
  let value : Stamp := { known, latest, worked, forgetAfter }
  if stampText ctx value ≠ text ||
      !(latest ++ worked).all (fun row => known.contains row.1) ||
      !forgetAfter.all (fun row => known.contains row.1) then
    throw "noncanonical raw presence stamp"
  return some value

def bindings (ctx : Context) (view : Json) : Except String Bindings := do
  let bindings ← rows view "workspaces"
  let result ← bindings.mapM fun row => do
    let values ← row.getArr?
    if values.size ≠ 2 then throw "workspace binding arity"
    return ((← values[0]!.getStr?).toList, ← label ctx.commits (← values[1]!.getStr?))
  if !uniqueKeys result then throw "duplicate raw workspace binding"
  return result

def decodeCanonical (ctx : Context) (raw : Json) : Except String CanonicalBody := do
  let metadata ← get raw "metadata"
  let author ← optionalString metadata "workspaceName"
  let owner ← match author with
    | some key => do pure (some (← workspace key).owner)
    | none => (← readAttr metadata "musubi.work").mapM copy
  let forgets := ((← readAttr metadata "musubi.forget").getD "").splitOn " " |>.filter (!·.isEmpty)
  let originalParents := ((← readAttr metadata "musubi.original-parents").getD "").splitOn " "
    |>.filter (!·.isEmpty)
  let rawRewrites ← get raw "predecessors"
  let rewrites ← match rawRewrites with
    | .null => pure []
    | other => do pure (← other.getArr?).toList
  let rewrites ← rewrites.mapM fun row => do
    let row ← row.getArr?
    if row.size ≠ 2 then throw "predecessor binding arity"
    return (← label ctx.commits (← row[0]!.getStr?),
      ← (← row[1]!.getArr?).toList.mapM (fun value => do label ctx.commits (← value.getStr?)))
  let own ← bindings ctx (← get raw "view")
  let workspaces ← own.mapM fun (name, commit) => do return (← workspace (String.ofList name), commit)
  let description ← str metadata "description"
  if restoreReference description then
    throw "restore/revert is outside the two finite native fixtures"
  let after ← readAttr metadata "musubi.forget-after"
  let forgetAfter ← after.mapM duration
  return {
    id := ⟨← label ctx.canonical (← str raw "id")⟩,
    original := ⟨← label ctx.original (← str raw "original")⟩,
    originalParents := ← originalParents.mapM (fun id => do return ⟨← label ctx.original id⟩),
    parents := ← (← strings raw "parents").mapM (fun id => do return ⟨← label ctx.canonical id⟩),
    authorWorkspace := ← author.mapM workspace,
    endTime := ← (← get metadata "end").getObjValAs? Int "millis",
    work := owner, forgets := ← forgets.mapM copy, forgetAfter,
    fixup := (← readAttr metadata "musubi.fixup").isSome,
    rewrites, stamp := ← stamp ctx metadata, workspaces,
    content := ← label ctx.contents (← content raw) }

def decodeNative (ctx : Context) (raw : Json) : Except String NativeBody := do
  let metadata ← get raw "metadata"
  if restoreReference (← str metadata "description") then
    throw "native restore/revert is outside the two finite fixtures"
  let marker ← (← readAttr metadata "musubi.canonical").mapM fun id => do
    return Canonical.mk (← label ctx.canonical id)
  let reserved ← match ← readAttr metadata "musubi.reserved-workspaces" with
    | none => pure []
    | some text => do
      let raw ← Json.parse text
      pure ((← Lean.fromJson? (α := List String) raw).map String.toList)
  return {
    id := ⟨← label ctx.physical (← str raw "id")⟩,
    parents := ← (← strings raw "parents").mapM (fun id => do return ⟨← label ctx.physical id⟩),
    endTime := ← (← get metadata "end").getObjValAs? Int "millis",
    workspaces := ← bindings ctx (← get raw "view"), marker,
    context := ← namespaceAttribute metadata, reserved,
    authorWorkspace := (← optionalString metadata "workspaceName").map String.toList,
    presenceStamp := ← stamp ctx metadata,
    gitFields := ← label ctx.fields (← gitFields raw),
    content := ← label ctx.contents (← content raw) }

def query (value : Query α) : Except String α := value.mapError (fun gap => reprStr gap)

def decodeEvidence (ctx : Context) (raw : Json) : Except String Evidence := do
  let canonicalRows ← rows raw "canonical"
  let nativeRows ← rows raw "native"
  if (← canonicalRows.mapM (str · "id")) ≠ (← strings raw "canonicalManifest") ||
      (← nativeRows.mapM (str · "id")) ≠ (← strings raw "nativeManifest") then
    throw "raw body manifest is incomplete or inconsistent"
  let canonical ← (← rows raw "canonical").mapM (decodeCanonical ctx)
  let native ← (← rows raw "native").mapM (decodeNative ctx)
  if !uniqueKeys (canonical.map fun body => (body.id, body)) ||
      !uniqueKeys (native.map fun body => (body.id, body)) then throw "duplicate raw bodies"
  let joins ← rows raw "joins"
  let originals ← rows raw "originals"
  let joinInputs ← joins.mapM fun row => do
    return Physical.mk (← label ctx.physical (← str row "physical"))
  let nativeFingerprints ← nativeRows.mapM fun row => do
    return (Physical.mk (← label ctx.physical (← str row "id")),
      ← label ctx.original (← str row "fingerprint"))
  let originalFingerprints ← originals.mapM fun row => do
    return (Original.mk (← label ctx.original (← str row "original")),
      ← label ctx.original (← str row "fingerprint"))
  let joinFingerprints ← joins.mapM fun row => do
    let canonical := Canonical.mk (← label ctx.canonical (← str row "canonical"))
    if !canonicalRows.any (fun row =>
        (str row "id").toOption == some ctx.canonical[canonical.value]!) then
      throw "retained join lacks its canonical body"
    return (canonical, ← label ctx.original (← str row "fingerprint"))
  let evidence : Evidence := {
    root := ⟨← label ctx.canonical (← str raw "canonicalRoot")⟩,
    physicalRoot := ⟨← label ctx.physical (← str raw "physicalRoot")⟩,
    canonical, native, joinInputs, nativeFingerprints, originalFingerprints, joinFingerprints }
  let fuel := native.length + canonical.length + 1
  let _ ← native.mapM fun body => query (nativeClosure evidence fuel body.id)
  let _ ← canonical.mapM fun body => query (canonicalClosure evidence fuel body.id)
  -- Fatal structural errors still reject the snapshot. Unresolved identities are typed
  -- classifications over the retained corpus, not missing or discarded native bodies.
  let _ ← native.mapM fun body => query (classifyIdentity evidence fuel body.id)
  return evidence

def decodeRecord (ctx : Context) (e : Evidence) (raw : Json) : Except String Record := do
  let names ← (← strings raw "names").mapM fun id => do return Canonical.mk (← label ctx.canonical id)
  let drops ← names.mapM fun id => do return (← query (e.canonicalBody id)).original
  return {
    before := ← label ctx.digests (← str raw "before"),
    identity := ← label ctx.digests (← str raw "identity"), drops, names }

def decodeSaved (ctx : Context) (e : Evidence) (raw : Json) : Except String Persistent := do
  let saved ← get raw "saved"
  if (← saved.getObjValAs? Nat "prefixCount") ≠ 0 then
    throw "pruned prefixes are outside the two finite fixtures"
  return {
    acceptedBase := ← (← optionalString saved "base").mapM fun id => do
      return Canonical.mk (← label ctx.canonical id),
    recordPrefix := ← label ctx.digests (← str saved "prefixDigest"),
    applied := ← (← rows saved "applied").mapM (decodeRecord ctx e),
    custody := ← (← rows saved "custody").mapM (decodeRecord ctx e),
    earlier := ← (← rows saved "earlier").mapM (decodeRecord ctx e),
    pending := ← (← strings saved "pending").mapM fun id => do
      return (← query (e.canonicalBody ⟨← label ctx.canonical id⟩)).original,
    expected := ← (← rows raw "expected").mapM fun row => do
      return (Physical.mk (← label ctx.physical (← str row "operation")),
        ← label ctx.contents row.compress) }

def decodeReceipt (ctx : Context) (input : Evidence) (raw : Json) : Except String Receipt := do
  let records ← (← rows raw "records").mapM (decodeRecord ctx input)
  let locals ← (← rows raw "locals").mapM fun row => do
    let row ← row.getArr?
    if row.size ≠ 2 then throw "receipt mapping arity"
    return (Physical.mk (← label ctx.physical (← row[0]!.getStr?)),
      ← (← row[1]!.getArr?).toList.mapM fun value => do
        return Physical.mk (← label ctx.physical (← value.getStr?)))
  return {
    identity := ← label ctx.digests (← str raw "identity"),
    recordPrefix := ← label ctx.digests (← str raw "prefixDigest"),
    prunedCount := ← raw.getObjValAs? Nat "prefixCount", records,
    capturedHeads := ← (← strings raw "heads").mapM fun id => do return ⟨← label ctx.physical id⟩,
    input, locals, switched := ← raw.getObjValAs? Bool "switched" }

def reply (request : Json) : Except String Json := do
  if (← request.getObjValAs? Nat "schema") ≠ 1 then throw "native lifecycle schema version"
  let ctx ← context request
  let raw ← get request "before"
  let e ← decodeEvidence ctx raw
  let heads ← (← strings raw "heads").mapM fun id => do return Physical.mk (← label ctx.physical id)
  let me ← copy (← str request "me")
  let saved ← decodeSaved ctx e raw
  let physical ← get raw "physical"
  if (← str physical "scope") ≠ "refs/heads/x" then throw "finite physical projection scope"
  let physicalGit ← label ctx.contents physical.compress
  let after ← get request "after"
  let observedBodies ← decodeEvidence ctx after
  let facts : NativeFacts := { encodings := {
    canonical := observedBodies.canonical, native := observedBodies.native } }
  match ← str request "kind" with
  | "receipt" =>
    let incoming ← get request "incoming"
    let records ← (← rows incoming "records").mapM (decodeRecord ctx e)
    let receiptRequest : ReceiptRequest := {
      identity := ← label ctx.digests (← str incoming "identity"),
      recordPrefix := ← label ctx.digests (← str incoming "prefixDigest"), records }
    let build ← (constructReceipt e facts saved me heads receiptRequest).mapError fun gap =>
      match gap with
      | .encoding message =>
        match Lean.Json.parse message with
        | .ok diagnostic => (Lean.Json.mkObj [
          ("encodingDiagnostic", diagnostic),
          ("ids", (get request "ids").toOption.getD .null),
          ("normalizedContent", toJson ctx.contents),
          ("rawCanonicalBefore", (get raw "canonical").toOption.getD .null),
          ("rawCanonicalAfter", (get after "canonical").toOption.getD .null)]).compress
        | .error _ => reprStr gap
      | _ => reprStr gap
    let observed ← decodeReceipt ctx e (← get after "receipt")
    if !receiptInputMatches build observed then throw "native receipt differs from computed construction"
    let actualWrites ← (← strings (← get request "observed") "writes").mapM fun id => do
      return Physical.mk (← label ctx.physical id)
    if !sameSet actualWrites (build.nativeWrites.map (·.id)) then
      throw "native write set differs from independently computed receipt bodies"
    let writeIndices ← actualWrites.mapM fun id => do
      let some index := (List.range build.nativeWrites.length).find? (fun index =>
        (build.nativeWrites[index]?.map (·.id)) == some id) | throw "unpredicted native write"
      return index
    let actions := [Action.planReceipt receiptRequest, .saveCustody] ++
      (List.range build.canonicalWrites.length).map Action.writeReceiptCanonical ++
      writeIndices.map Action.writeReceiptNative ++ [.commitReceipt observed]
    let initial : State := { me, evidence := e, heads, saved, nativeFacts := facts, physicalGit }
    let checked ← (certifiedRun initial actions).mapError reprStr
    let final := checked.val
    return Json.mkObj [("ok", toJson true), ("computed", toJson build),
      ("custody", toJson final.saved.custody), ("created", toJson final.createdBodies),
      ("constructedActions", toJson (actions.all constructedAction)),
      ("sameRunCustody", toJson true)]
  | "publication" =>
    let target : Canonical := ⟨← label ctx.canonical (← str request "target")⟩
    let build ← query (constructRender e facts me heads none target)
    let actions := [Action.capture, .planRender target] ++
      (List.range build.nodes.length).map Action.writeRender ++ [.commitRender, .revalidate]
    let initial : State := { me, evidence := e, heads, saved, nativeFacts := facts, physicalGit }
    let checked ← (certifiedRun initial actions).mapError reprStr
    let final := checked.val
    let some git := final.git | throw "publication lacks computed Git policy"
    let some plan := final.publication | throw "publication lacks computed order"
    -- This finite comparison also checks the real pre-export with_per_machine copy.
    -- Installing that publication effect is not yet part of the certified prefix.
    let incoming ← query (final.evidence.nativeBody plan.incoming)
    let adjusted ← if git.useCurrent then do
      let fields ← query (inheritedFields final.evidence facts.fields final.heads)
      query (encodeNative final.evidence facts.encodings { incoming with gitFields := fields })
      else pure incoming
    let mergeEvidence := { final.evidence with
      native := unique (final.evidence.native ++ [adjusted]) }
    let ordered ← query (orderedPublicationInputs mergeEvidence (plan.beside ++ [adjusted.id]))
    return Json.mkObj [("ok", toJson true), ("computed", toJson build), ("git", toJson git),
      ("mergeBeforeExport", toJson plan.mergeBeforeExport), ("incoming", toJson plan.incoming),
      ("gitAdjustedIncoming", toJson adjusted), ("orderedMergeInputs", toJson ordered),
      ("beside", toJson plan.beside), ("constructedActions", toJson (actions.all constructedAction)),
      ("sameRunCustody", toJson true)]
  | _ => throw "unknown finite native lifecycle fixture"

end Musubi.NativeLifecycle.Json

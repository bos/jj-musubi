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
deriving instance ToJson for SourceRealign, SourceRename, SourceFrame, SourceHubFrame,
  SourceCheckpoint, SourceMemory
deriving instance ToJson for SourceRoutes, DescriptionExclusion
deriving instance ToJson for BaseObservation, Evidence, Record, Receipt, Intent, RetainedExport
deriving instance ToJson for Persistent, ReceiptRequest, ReceiptBuild, Role, CandidateSet, Candidates
deriving instance ToJson for SourceChoice, Suffix, ParentSelection, OwnSource, OwnSelection, GitChoice
deriving instance ToJson for RenderNode, RenderBuild, CurrentGitBuild

def get (j : Json) (key : String) : Except String Json := j.getObjVal? key
def str (j : Json) (key : String) : Except String String := j.getObjValAs? String key
def rows (j : Json) (key : String) : Except String (List Json) := do
  return (← j.getObjValAs? (Array Json) key).toList
def strings (j : Json) (key : String) : Except String (List String) := do
  return (← j.getObjValAs? (Array String) key).toList
def optionalString (j : Json) (key : String) : Except String (Option String) :=
  j.getObjValAs? (Option String) key

def restoreReference (description : String) : Bool :=
  restoreDescription description

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
  let interleaved := (← str request "kind") == "retry"
  let snapshots ← if interleaved then do
      pure [before, ← get request "prepared", ← get request "postNative", after]
    else pure [before, after]
  let all ← snapshots.mapM fun snapshot => do
    return (← rows snapshot "canonical") ++ (← rows snapshot "native")
  let all := all.flatten
  let expected ← if interleaved then do
      return (← snapshots.mapM (fun snapshot => rows snapshot "expected")).flatten
    else rows before "expected"
  let physical ← snapshots.mapM (fun snapshot => get snapshot "physical")
  return {
    physical := ← sortedPool ids "physical", canonical := ← sortedPool ids "canonical",
    original := ← sortedPool ids "original", commits := ← sortedPool ids "commits",
    digests := ← sortedPool ids "digests",
    contents := unique ((← all.mapM content) ++ expected.map (fun row => row.compress) ++
      physical.map (fun row => row.compress)),
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

/-- Stamp maps use the construction's key order internally. Keep each complete value
unchanged; raw byte canonicality is checked before applying this representation choice. -/
def orderStampRows (values : List (Copy × α)) : List (Copy × α) :=
  values.mergeSort (fun a b => decide (copyText a.1 ≤ copyText b.1))

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
  return some { value with
    latest := orderStampRows value.latest, worked := orderStampRows value.worked,
    forgetAfter := orderStampRows value.forgetAfter }

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
    content := ← label ctx.contents (← content raw), description }

def decodeNative (ctx : Context) (raw : Json) : Except String NativeBody := do
  let metadata ← get raw "metadata"
  let description ← str metadata "description"
  if restoreReference description then
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
    content := ← label ctx.contents (← content raw), description }

def query (value : Query α) : Except String α := value.mapError (fun gap => reprStr gap)

def sourceHash (text : String) : Except String String := do
  if text.length ≠ 128 || !text.toList.all (fun c =>
      ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
    throw "source state contains a noncanonical operation/digest hash"
  return text

def sourcePhysical (ctx : Context) (e : Evidence) (text : String) : Except String Physical := do
  let id : Physical := ⟨← label ctx.physical (← sourceHash text)⟩
  let _ ← query (e.nativeBody id)
  return id

def sourceCanonical (ctx : Context) (e : Evidence) (text : String) : Except String Canonical := do
  let id : Canonical := ⟨← label ctx.canonical (← sourceHash text)⟩
  let _ ← query (e.canonicalBody id)
  return id

def sourcePair (row : Json) : Except String (Json × Json) := do
  let values ← row.getArr?
  if values.size ≠ 2 then throw "source state pair has wrong arity"
  return (values[0]!, values[1]!)

def sourceDefault [Lean.FromJson α] (raw : Json) (key : String) (fallback : α) :
    Except String α :=
  match raw.getObjVal? key with
  | .error _ => .ok fallback
  | .ok value => Lean.fromJson? value

def sourceAliases (ctx : Context) (e : Evidence) (values : List Json) :
    Except String (List (Physical × Canonical)) := do
  let result ← values.mapM fun row => do
    let (physical, canonical) ← sourcePair row
    return (← sourcePhysical ctx e (← physical.getStr?),
      ← sourceCanonical ctx e (← canonical.getStr?))
  if !uniqueKeys result then throw "duplicate supplied source relation key"
  return result

def sourceRealign (ctx : Context) (e : Evidence) (raw : Json) : Except String SourceRealign := do
  let fromHeads ← (← rows raw "from").mapM fun row => do
    let (old, values) ← sourcePair row
    return (← sourcePhysical ctx e (← old.getStr?),
      ← (← values.getArr?).toList.mapM fun id => do sourcePhysical ctx e (← id.getStr?))
  if !uniqueKeys fromHeads then throw "duplicate source realign frontier key"
  return {
    fromHeads,
    to := ← (← strings raw "to").mapM (sourcePhysical ctx e),
    canonical := ← sourceAliases ctx e (← rows raw "canonical") }

def sourceOptionalRealign (ctx : Context) (e : Evidence) (raw : Json) :
    Except String (Option SourceRealign) :=
  if raw == .null then .ok none else do return some (← sourceRealign ctx e raw)

def sourceNumber (text : String) : Except String Nat := do
  if text.length ≠ 20 || !text.toList.all (fun c => '0' ≤ c && c ≤ '9') then
    throw "source step header has a noncanonical number"
  let some value := text.toNat? | throw "source step number is unreadable"
  return value

def sourceFrameComplete (frame : SourceFrame) : Except String Unit := do
  if frame.declaredLines ≠ frame.renames.length + frame.sources.length then
    throw "source step block is incomplete or has extra lines"

/-- A strict finite subset of the native framed-log parser. Torn/unrecognized input is
an interpretation gap, not a new native refusal. All complete frames are retained. -/
def sourceFrames (ctx : Context) (e : Evidence) (text : String) :
    Except String (List SourceFrame) := do
  let mut result := []
  let mut current : Option SourceFrame := none
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " " with
    | ["step", number, count] =>
      if let some frame := current then
        sourceFrameComplete frame
        result := result ++ [frame]
      current := some { number := ← sourceNumber number, declaredLines := ← sourceNumber count }
    | ["source", physical, canonical] =>
      let some frame := current | throw "source row has no framed step"
      current := some { frame with sources := frame.sources ++
        [(← sourcePhysical ctx e physical, ← sourceCanonical ctx e canonical)] }
    | [old, next] =>
      let some frame := current | throw "renaming row has no framed step"
      let dropped := old.startsWith "-"
      let old := if dropped then String.ofList (old.toList.drop 1) else old
      let next : Option Canonical ← if next = "-" then pure none else
        some <$> sourceCanonical ctx e next
      current := some { frame with renames := frame.renames ++
        [{ old := ← sourceCanonical ctx e old, new := next, dropped }] }
    | _ => throw "unsupported or torn source step line"
  if let some frame := current then
    sourceFrameComplete frame
    result := result ++ [frame]
  return result

def sourceCounted (count : Nat) (frames : List SourceFrame) :
    Except String (List (Physical × Canonical)) := do
  let indexed := frames.foldl (fun acc frame => put acc frame.number frame) []
  if count > indexed.length then throw "checkpoint counts missing source steps"
  let mut result := []
  for i in List.range count do
    let some frame := lookup indexed (i + 1) | throw "checkpoint source step sequence has a hole"
    result := frame.sources.foldl (fun acc row => put acc row.1 row.2) result
  return result

def sourceHubFrames (ctx : Context) (e : Evidence) (text : String) :
    Except String (List SourceHubFrame) := do
  let mut result := []
  let mut current : Option SourceHubFrame := none
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match line.splitOn " " with
    | ["record", digest, count] =>
      if let some frame := current then
        if frame.declaredLines ≠ frame.renames.length then throw "incomplete hub renaming frame"
        result := result ++ [frame]
      current := some { digest := ← sourceHash digest, declaredLines := ← sourceNumber count }
    | [new, old] =>
      let some frame := current | throw "hub renaming has no record frame"
      current := some { frame with renames := frame.renames ++
        [(← sourceCanonical ctx e new, ← sourceCanonical ctx e old)] }
    | _ => throw "unsupported or torn hub renaming line"
  if let some frame := current then
    if frame.declaredLines ≠ frame.renames.length then throw "incomplete hub renaming frame"
    result := result ++ [frame]
  return result

def sourceNames (ctx : Context) (e : Evidence) (values : List Json) :
    Except String (List Canonical) :=
  values.mapM fun value => do sourceCanonical ctx e (← value.getStr?)

def sourceHistory (ctx : Context) (e : Evidence) (raw : Json) (checkpoint : Bool) :
    Except String (Nat × List Canonical) := do
  let applied ← rows raw "applied"
  let appliedNames ← applied.mapM fun row => do sourceNames ctx e (← row.getArr?).toList
  let pending ← sourceNames ctx e (← rows raw "pending")
  let mut names := appliedNames.flatten ++ pending
  let mut count := applied.length + pending.length
  for field in ["earlier", "custody"] do
    let values ← sourceDefault raw field (#[] : Array Json)
    count := count + values.size
    for row in values.toList do
      let values ← if checkpoint then do
          let (digest, values) ← sourcePair row
          let _ ← sourceHash (← digest.getStr?)
          pure values
        else pure row
      names := names ++ (← sourceNames ctx e (← values.getArr?).toList)
  return (count, names)

def sourceCheckpoint (ctx : Context) (e : Evidence) (text : Option String) :
    Except String SourceCheckpoint := do
  let some text := text | return {}
  -- Relevant checkpoint strings are ASCII hashes. This finite parser rejects escapes
  -- instead of allowing a duplicated/escaped object key to hide behind JSON map parsing.
  if text.contains '\\' then throw "escaped checkpoint JSON is outside the finite source parser"
  let raw ← Lean.Json.parse text
  let fields := (← raw.getObj?).toList
  let allowed := ["prefix", "applied", "pending", "fixup", "fixup_written", "fixup_from",
    "moving", "realign", "steps", "fresh", "earlier", "custody"]
  for (name, _) in fields do
    if !allowed.contains name || (text.splitOn s!"\"{name}\"").length ≠ 2 then
      throw "unknown or duplicate source checkpoint field"
  let fixup ← get raw "fixup"
  if fixup != .null then
    throw "nonempty checkpoint fixup needs further source-route interpretation"
  let (records, names) ← sourceHistory ctx e raw true
  let storedPrefix := (get raw "prefix").toOption.getD .null
  let prefixCount ← if storedPrefix == .null then pure 0 else do
    let (count, digest) ← sourcePair storedPrefix
    let _ ← sourceHash (← digest.getStr?)
    count.getNat?
  let fixupFrom ← sourceDefault raw "fixup_from" (none : Option String)
  let fixupFrom ← fixupFrom.mapM (sourceCanonical ctx e)
  let realign := (get raw "realign").toOption.getD .null
  if realign != .null then
    for key in ["from", "to", "canonical"] do
      if (text.splitOn s!"\"{key}\"").length ≠ 2 then throw "duplicate realign object key"
  return {
    steps := ← sourceDefault raw "steps" 0,
    realign := ← sourceOptionalRealign ctx e realign,
    moving := ← sourceDefault raw "moving" false,
    fixup := (← raw.getObjValAs? Bool "fixup_written") || fixupFrom.isSome,
    recordCount := records + prefixCount, recordNames := names ++ fixupFrom.toList }

def sourceMemory (ctx : Context) (e : Evidence) (raw : Json) : Except String SourceMemory := do
  if (← str raw "provenance") ≠ "NodeRepo.records and join fields, exact supplied snapshot" then
    throw "unrecognized supplied source-state provenance"
  let superseded ← (← rows raw "superseded").mapM fun row => do
    let (old, values) ← sourcePair row
    return (← sourceCanonical ctx e (← old.getStr?),
      ← sourceNames ctx e (← values.getArr?).toList)
  if !uniqueKeys superseded then throw "duplicate supplied superseded key"
  let joins ← (← rows raw "joins").mapM fun row => do
    let (fingerprint, canonical) ← sourcePair row
    return (← label ctx.original (← sourceHash (← fingerprint.getStr?)),
      ← sourceCanonical ctx e (← canonical.getStr?))
  if !uniqueKeys joins then throw "duplicate supplied join fingerprint"
  let (records, names) ← sourceHistory ctx e raw false
  let fixupFrom ← (← raw.getObjValAs? (Option String) "fixupFrom").mapM (sourceCanonical ctx e)
  return {
    steps := ← raw.getObjValAs? Nat "steps",
    sources := ← sourceAliases ctx e (← rows raw "sources"), superseded,
    dropped := ← sourceNames ctx e (← rows raw "dropped"),
    realign := ← sourceOptionalRealign ctx e (← get raw "realign"),
    moving := ← raw.getObjValAs? Bool "moving", taking := ← raw.getObjValAs? Bool "taking",
    fixup := (← get raw "fixup") != .null ||
      (← raw.getObjValAs? Bool "fixupWritten") || fixupFrom.isSome,
    recordCount := records + (← raw.getObjValAs? Nat "prefixCount"),
    recordNames := names ++ fixupFrom.toList,
    joins, joinPoints := ← (← strings raw "joinPoints").mapM (sourcePhysical ctx e),
    prejoin := ← (← strings raw "prejoin").mapM (sourcePhysical ctx e) }

def sourceRoutes (ctx : Context) (e : Evidence) (raw : Json) : Except String SourceRoutes := do
  let state ← get raw "identitySourceState"
  if (← state.getObjValAs? Nat "schema") ≠ 1 then throw "source-state schema version"
  let files ← get state "files"
  let checkpoint ← sourceCheckpoint ctx e (← optionalString files "checkpoint")
  let frames ← sourceFrames ctx e ((← optionalString files "steps").getD "")
  let countedSources ← sourceCounted checkpoint.steps frames
  let accepted ← ["acceptedBase", "acceptedPush"].filterMapM fun key => do
    let some text ← optionalString files key | return none
    return some (← sourceCanonical ctx e text.trimAscii.toString)
  return {
    checkpoint, frames, countedSources, memory := ← sourceMemory ctx e (← get state "memory"),
    accepted, hubRenamings := ← sourceHubFrames ctx e
      ((← optionalString files "hubRenamings").getD "") }

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
  for body in canonical do
    if canonical.any (fun other => other.original == body.original &&
        (other.description != body.description || other.authorWorkspace != body.authorWorkspace)) then
      throw "inconsistent immutable-original description/author lineage"
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
  let routes ← sourceRoutes ctx evidence raw
  let evidence := { evidence with sourceRoutes := some routes }
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

/-- One scoped native reparent observation: retain the complete old corpus and compare
the exact new body with its old body, changing only its id and ordered parents. No positive
identity is supplied for the new alias, and no subsequent canonicalization law is asserted. -/
def observedHeadReparent (before after : Evidence) (oldHeads newHeads : List Physical)
    (abandoned : Physical) (physicalGit : Nat) : Except String NativeObservation := do
  let ([old], [next]) := (oldHeads, newHeads) | throw "C needs one old and one new physical head"
  if old = next then throw "native reparent did not change the physical head"
  let prior ← query (before.nativeBody old)
  let dropped ← query (before.nativeBody abandoned)
  let replacement ← query (after.nativeBody next)
  if before.root ≠ after.root || before.physicalRoot ≠ after.physicalRoot then
    throw "native command changed a repository root observation"
  if prior.parents ≠ [abandoned] || dropped.parents.length ≠ 1 then
    throw "C abandon operand must be the current head's one-parent ancestor"
  if replacement ≠ { prior with id := next, parents := dropped.parents } then
    throw "native replacement differs beyond the exact ordered parent rewrite"
  if !sameSet before.canonical after.canonical ||
      !before.native.all (after.native.contains ·) then
    throw "native command removed or changed an old immutable body"
  let added := after.native.filter (fun body => !before.native.any (fun old => old.id == body.id))
  if added ≠ [replacement] then throw "C must retain exactly one independently observed new body"
  return { native := [replacement], heads := newHeads, physicalGit }

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
  -- C certifies only its first changed-head retry. Later retry canonicalization and
  -- publication remain raw observations, never an extra identity/encoding premise here.
  let encodingRaw ← if (← str request "kind") = "retry" then get request "prepared" else pure after
  let observedBodies ← decodeEvidence ctx encodingRaw
  let facts : NativeFacts := { encodings := {
    canonical := observedBodies.canonical, native := observedBodies.native } }
  match ← str request "kind" with
  | "receipt" =>
    let incoming ← get request "incoming"
    let records ← (← rows incoming "records").mapM (decodeRecord ctx e)
    let receiptRequest : ReceiptRequest := {
      identity := ← label ctx.digests (← str incoming "identity"),
      recordPrefix := ← label ctx.digests (← str incoming "prefixDigest"), records }
    let build ← query (constructReceipt e facts saved me heads receiptRequest)
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
    let checked ← (certifiedConstructionRun me e heads saved facts physicalGit actions).mapError reprStr
    let final := checked.val
    return Json.mkObj [("ok", toJson true), ("computed", toJson build),
      ("custody", toJson final.saved.custody), ("created", toJson final.createdBodies),
      ("constructedActions", toJson (actions.all constructedAction)),
      ("sameRunCustody", toJson true), ("sameRunSourceRoutes", toJson true),
      ("sameRunConstruction", toJson true), ("constructionPrepared", toJson final.prepared.isSome)]
  | "publication" =>
    let target : Canonical := ⟨← label ctx.canonical (← str request "target")⟩
    let build ← query (constructRender e facts me heads none target)
    let actions := [Action.capture, .planRender target] ++
      (List.range build.nodes.length).map Action.writeRender ++
      [.commitRender, .revalidate, .refreshCurrentGit]
    let checked ← (certifiedConstructionRun me e heads saved facts physicalGit actions).mapError reprStr
    let final := checked.val
    let some prepared := final.prepared | throw "construction certificate lost committed preparation"
    let association := preparedMatchesOrigin me prepared build
    if !association then throw "committed preparation differs from computed planning inputs"
    let some git := final.git | throw "publication lacks computed Git policy"
    let some plan := final.publication | throw "publication lacks computed order"
    if !plan.refreshDone then throw "current Git refresh not installed by certified actions"
    let adjusted ← query (final.evidence.nativeBody plan.incoming)
    let ordered ← query (orderedPublicationInputs final.evidence (plan.beside ++ [plan.incoming]))
    return Json.mkObj [("ok", toJson true), ("computed", toJson build), ("git", toJson git),
      ("mergeBeforeExport", toJson plan.mergeBeforeExport), ("incoming", toJson plan.incoming),
      ("preparedIncoming", toJson build.result), ("currentGit", toJson plan.refresh),
      ("refreshWrote", toJson ((plan.refresh.map (·.writes)).getD false)),
      ("preferredIncoming", toJson (lookup final.memo.preferred target)),
      ("gitAdjustedIncoming", toJson adjusted), ("orderedMergeInputs", toJson ordered),
      ("beside", toJson plan.beside), ("constructedActions", toJson (actions.all constructedAction)),
      ("sameRunCustody", toJson true), ("sameRunSourceRoutes", toJson true),
      ("sameRunConstruction", toJson true), ("constructionPrepared", toJson true),
      ("preparedAssociation", toJson association)]
  | "retry" =>
    let target : Canonical := ⟨← label ctx.canonical (← str request "target")⟩
    let build ← query (constructRender e facts me heads none target)
    let setup := [Action.capture, .planRender target] ++
      (List.range build.nodes.length).map Action.writeRender ++ [.commitRender]
    let attempted ← (run (rawInitial me e heads saved facts physicalGit) setup).mapError reprStr
    let preparedRaw ← get request "prepared"
    let nativeRaw ← get request "postNative"
    let preparedEvidence ← decodeEvidence ctx preparedRaw
    let nativeEvidence ← decodeEvidence ctx nativeRaw
    let preparedHeads ← (← strings preparedRaw "heads").mapM fun id => do
      return Physical.mk (← label ctx.physical id)
    let nativeHeads ← (← strings nativeRaw "heads").mapM fun id => do
      return Physical.mk (← label ctx.physical id)
    if !sameSet attempted.heads preparedHeads ||
        !sameSet attempted.evidence.native preparedEvidence.native ||
        !sameSet attempted.evidence.canonical preparedEvidence.canonical then
      throw "actual prepared corpus differs from independently constructed prefix"
    if (← get preparedRaw "physical") ≠ (← get nativeRaw "physical") ||
        (← get preparedRaw "identitySourceState") ≠ (← get nativeRaw "identitySourceState") then
      throw "C head-only command changed observed physical/source state"
    for name in ["originals", "joins", "receipt", "expected", "saved"] do
      if (← get preparedRaw name) ≠ (← get nativeRaw name) then
        throw s!"C head-only command changed retained {name}"
    let abandoned : Physical := ⟨← label ctx.physical (← str request "abandoned")⟩
    let observation ← observedHeadReparent preparedEvidence nativeEvidence
      preparedHeads nativeHeads abandoned
      (← label ctx.contents (← get nativeRaw "physical").compress)
    let observed ← (step attempted (.native observation)).mapError reprStr
    let some historical := observed.prepared |
      throw "native observation lost historical preparation"
    let association := preparedMatchesOrigin me historical build
    if !association then throw "native observation detached the historical render origin"
    let classifications ← nativeHeads.mapM fun id =>
      query (classifyIdentity observed.evidence (queryFuel observed.evidence) id)
    let unresolved := classifications.all fun value => match value with
      | .unresolved _ => true
      | _ => false
    let actions := setup ++ [.native observation, .revalidate]
    let checked ←
      (certifiedConstructionRun me e heads saved facts physicalGit actions).mapError reprStr
    let final := checked.val
    if final.phase ≠ .preparing || final.prepared.isSome || final.captured.isSome ||
        final.publication.isSome then throw "changed heads did not yield the modeled retry prefix"
    return Json.mkObj [("ok", toJson true), ("preparedIncoming", toJson build.result),
      ("retry", toJson true), ("retryHeads", toJson final.heads),
      ("constructionPrepared", toJson final.prepared.isSome),
      ("historicalPreparedAssociation", toJson association),
      ("sourceRoutesInvalidated", toJson final.evidence.sourceRoutes.isNone),
      ("nativeIdentityRowsSupplied", toJson observation.identities.length),
      ("nativeAliasUnresolved", toJson unresolved),
      ("constructedActions", toJson (actions.all constructedAction)),
      ("sameRunConstruction", toJson true), ("sameRunCustody", toJson true),
      ("sameRunSourceRoutes", toJson true)]
  | _ => throw "unknown finite native lifecycle fixture"

end Musubi.NativeLifecycle.Json

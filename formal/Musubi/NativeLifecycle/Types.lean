/-
Finite inputs of the native preparation and publication steps: native and canonical operation
bodies, identity rows, records, receipts, namespaces and Git fields, decoded from observations.
They are data only: nothing here certifies that an observation is authentic or that musubi
selected the right source, and no declaration is a native law or a refinement of `NodeSys`.
-/
import Musubi.Names

namespace Musubi.NativeLifecycle

structure Original where
  value : Nat
deriving DecidableEq, Repr, Inhabited

structure Canonical where
  value : Nat
deriving DecidableEq, Repr, Inhabited

structure Physical where
  value : Nat
deriving DecidableEq, Repr, Inhabited

abbrev Copy := Names.Key
abbrev Name := Names.Str
abbrev Commit := Nat
abbrev Bindings := List (Name × Commit)

structure WorkspaceKey where
  owner : Copy
  name : Name
deriving DecidableEq, Repr

abbrev SharedBindings := List (WorkspaceKey × Commit)

def lookup [DecidableEq α] (xs : List (α × β)) (key : α) : Option β :=
  (xs.find? fun e => decide (e.1 = key)).map (·.2)

def put [DecidableEq α] (xs : List (α × β)) (key : α) (value : β) : List (α × β) :=
  (key, value) :: xs.filter (fun e => decide (e.1 ≠ key))

def unique [DecidableEq α] (xs : List α) : List α := xs.eraseDups

def sameSet [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (ys.contains ·) && ys.all (xs.contains ·)

def uniqueKeys [DecidableEq α] (xs : List (α × β)) : Bool :=
  decide (xs.map (·.1)).Nodup

inductive IdentityIssue where
  | missingFingerprint
  | noMatch
  | ambiguous
  | dependency (parent : Physical)
  | exhausted
deriving DecidableEq, Repr

inductive Gap where
  | canonical (id : Canonical)
  | physical (id : Physical)
  | identity (id : Physical)
  | unresolvedIdentity (id : Physical) (issue : IdentityIssue)
  | source (id : Canonical)
  | original (id : Original)
  | nativeBases (left : List Physical) (right : Physical)
  | frontierBases (left right : List Physical)
  | encoding (what : String)
  | nativeFact (what : String)
  | renderReference (target : Canonical)
  | exhausted
  | malformed (what : String)
deriving DecidableEq, Repr

abbrev Query := Except Gap

def decidableExceptEq [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => decidable_of_iff (a = b) (by simp)
  | .error a, .error b => decidable_of_iff (a = b) (by simp)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

instance [DecidableEq α] : DecidableEq (Query α) := decidableExceptEq

/-- Full decoded namespace attribute. An absent attribute is an observation, not a missing
operation body. Ownership is derived later from these names, source and native edges. -/
structure Namespace where
  source : Copy
  known : List Copy
  names : List (Name × WorkspaceKey)
deriving DecidableEq, Repr

/-- What `Namespace::read_attribute` accepts, besides what the decoder checks itself (the key
characters, and that no two names share a qualified key): the source is known, no name appears
twice, every key's machine is known, and an entry keyed to the source machine names the
workspace it is named for. -/
def Namespace.valid (n : Namespace) : Bool :=
  n.known.contains n.source && uniqueKeys n.names &&
    n.names.all (fun e => n.known.contains e.2.owner && (e.2.owner != n.source || e.2.name = e.1))

structure Work where
  original : Original
  standing : Option Canonical
deriving DecidableEq, Repr

/-- Equality of work sets is by immutable original, including erased work. -/
def workEq (a b : Work) : Bool := decide (a.original = b.original)

structure Presence where
  known : List Copy := []
  latest : List (Copy × List Work) := []
  worked : List (Copy × List Work) := []
  forgetAfter : List (Copy × List (Work × Option Nat)) := []
deriving DecidableEq, Repr, Inhabited

/-- Stamp entries name originals, as the stored presence attribute does. Concrete standing
operations are reconstructed from the operation and its parents, not passed as a selector. -/
structure Stamp where
  known : List Copy
  latest : List (Copy × List Original)
  worked : List (Copy × List Original)
  forgetAfter : List (Copy × List (Original × Option Nat)) := []
deriving DecidableEq, Repr

structure CanonicalBody where
  id : Canonical
  original : Original
  originalParents : List Original
  parents : List Canonical
  /-- Raw restore/revert references consulted in addition to ordered parents. -/
  references : List Canonical := []
  referenceRevert : Bool := false
  authorWorkspace : Option WorkspaceKey := none
  endTime : Int := 0
  work : Option Copy := none
  forgets : List Copy := []
  forgetAfter : Option (Option Nat) := none
  fixup : Bool := false
  rewrites : List (Commit × List Commit) := []
  stamp : Option Stamp := none
  /-- The namespace context (`musubi.workspace-context`) the canonical operation carries. -/
  context : Option Namespace := none
  workspaces : SharedBindings := []
  /-- All remaining hash-visible bytes, interned by exact content by the eventual codec. -/
  content : Nat := 0
  description : String := ""
deriving DecidableEq, Repr

inductive NativeSource where
  | parents
  | restore (target : Physical)
  | revert (target : Physical)
deriving DecidableEq, Repr, Inhabited

structure NativeBody where
  id : Physical
  parents : List Physical
  endTime : Int := 0
  workspaces : Bindings := []
  marker : Option Canonical := none
  context : Option Namespace := none
  source : NativeSource := .parents
  reserved : List Name := []
  authorWorkspace : Option Name := none
  presenceStamp : Option Stamp := none
  /-- Complete per-machine fields, compared by exact content rather than a scalar HEAD. -/
  gitFields : Nat := 0
  content : Nat := 0
  description : String := ""
deriving DecidableEq, Repr

inductive IdentityKind where
  | original
  | countedSource
  | markedBody
deriving DecidableEq, Repr

/-- Raw persisted evidence rows, as recorded. Whether they are authentic is checked
separately. -/
structure IdentityRow where
  physical : Physical
  canonical : Canonical
  original : Original
  kind : IdentityKind
deriving DecidableEq, Repr

/-- A total classification keeps unknown identity distinct from proved prejoin history.
The join input in `prejoin` is checked against the raw ancestry by the classifier. -/
inductive IdentityClass where
  | known (row : IdentityRow)
  | prejoin (input : Physical)
  | unresolved (issue : IdentityIssue)
deriving DecidableEq, Repr

structure BaseObservation where
  left : List Physical
  right : Physical
  bases : List Physical
deriving DecidableEq, Repr

structure SourceRealign where
  fromHeads : List (Physical × List Physical)
  to : List Physical
  canonical : List (Physical × Canonical)
deriving DecidableEq, Repr

structure SourceRename where
  old : Canonical
  new : Option Canonical
  dropped : Bool
deriving DecidableEq, Repr

structure SourceFrame where
  number : Nat
  declaredLines : Nat
  renames : List SourceRename := []
  sources : List (Physical × Canonical) := []
deriving DecidableEq, Repr

structure SourceHubFrame where
  digest : String
  declaredLines : Nat
  renames : List (Canonical × Canonical) := []
deriving DecidableEq, Repr

structure SourceCheckpoint where
  steps : Nat := 0
  realign : Option SourceRealign := none
  fixup : Bool := false
  recordCount : Nat := 0
  recordNames : List Canonical := []
deriving DecidableEq, Repr

structure SourceMemory where
  steps : Nat
  sources : List (Physical × Canonical)
  superseded : List (Canonical × List Canonical)
  dropped : List Canonical
  realign : Option SourceRealign
  taking : Bool
  fixup : Bool
  recordCount : Nat
  recordNames : List Canonical
  joins : List (Nat × Canonical)
  joinPoints : List Physical
  prejoin : List Physical
deriving DecidableEq, Repr

/-- Parsed durable state and, separately, a snapshot of the actual memory. The two may differ,
and a missing file yields no memory relation. -/
structure SourceRoutes where
  checkpoint : SourceCheckpoint
  frames : List SourceFrame
  countedSources : List (Physical × Canonical)
  memory : SourceMemory
  accepted : List Canonical
  hubRenamings : List SourceHubFrame
deriving DecidableEq, Repr

/-- Holds when the observations show only the ordinary route by which a native operation gets
its canonical source: no checkpoint steps or log frames, no realign (a saved move of the heads),
take or fix-up in progress, and no records, joins or renamings. The model handles only this case; any other
state is an interpretation gap. -/
def SourceRoutes.closed (s : SourceRoutes) : Bool :=
  s.checkpoint.steps == 0 && s.frames.isEmpty && s.countedSources.isEmpty &&
  s.checkpoint.realign.isNone && !s.checkpoint.fixup &&
  s.checkpoint.recordCount == 0 && s.checkpoint.recordNames.isEmpty &&
  s.memory.steps == 0 && s.memory.sources.isEmpty && s.memory.superseded.isEmpty &&
  s.memory.dropped.isEmpty && s.memory.realign.isNone &&
  !s.memory.taking && !s.memory.fixup && s.memory.recordCount == 0 &&
  s.memory.recordNames.isEmpty && s.memory.joins.isEmpty && s.memory.joinPoints.isEmpty &&
  s.memory.prejoin.isEmpty &&
  s.accepted.isEmpty && s.hubRenamings.isEmpty

structure DescriptionExclusion where
  physical : Physical
  target : Canonical
  targetOriginal : Original
  nativeDescription : String
  originalDescription : String
deriving DecidableEq, Repr

/-- Canonicalizing an ordinary native operation copies its description unchanged. Join,
restore/revert and renaming routes are other constructors, checked separately. -/
def ordinaryOriginalDescription (native : String) : String := native

/-- An overapproximation of the ordinary constructor: every other field is arbitrary,
but its description is copied from the native input. -/
def ordinaryOriginalBody (nativeDescription : String) (other : CanonicalBody) : CanonicalBody :=
  { other with description := ordinaryOriginalDescription nativeDescription }

def DescriptionExclusion.necessary (w : DescriptionExclusion) : Prop :=
  ordinaryOriginalDescription w.nativeDescription ≠ w.originalDescription

theorem DescriptionExclusion.no_ordinary_body (w : DescriptionExclusion) (checked : w.necessary)
    (other : CanonicalBody) :
    (ordinaryOriginalBody w.nativeDescription other).description ≠ w.originalDescription := checked

def restoreDescription (description : String) : Bool :=
  ["undo: restore to operation ", "redo: restore to operation ",
    "undo: revert operation ", "redo: revert operation ",
    "restore to operation ", "revert operation "].any (fun start => description.startsWith start)

structure Evidence where
  root : Canonical
  physicalRoot : Physical
  canonical : List CanonicalBody := []
  native : List NativeBody := []
  identities : List IdentityRow := []
  /-- Complete raw retained identity material. Fingerprints are interned exact hash bytes,
  not preferred translations. Classification is recomputed when evidence grows. -/
  nativeFingerprints : List (Physical × Nat) := []
  originalFingerprints : List (Original × Nat) := []
  joinFingerprints : List (Canonical × Nat) := []
  sourceRoutes : Option SourceRoutes := none
  /-- Independently captured native inputs of joins, not arbitrary unknown operations. -/
  joinInputs : List Physical := []
  /-- Native order is retained, and checked against graph-derived closest-base membership. -/
  bases : List BaseObservation := []
  frontierBases : List (List Physical × List Physical × List Physical) := []
  /-- Exact independently captured source repository/index context for native replay. -/
  repositoryContext : Nat := 0
deriving DecidableEq, Repr

def Evidence.canonicalBody (e : Evidence) (id : Canonical) : Query CanonicalBody :=
  match e.canonical.filter (fun b => decide (b.id = id)) with
  | [] => .error (.canonical id)
  | b :: rest => if rest.all (fun other => decide (other = b)) then .ok b
      else .error (.malformed "conflicting canonical bodies")

def Evidence.nativeBody (e : Evidence) (id : Physical) : Query NativeBody :=
  match e.native.filter (fun b => decide (b.id = id)) with
  | [] => .error (.physical id)
  | b :: rest => if rest.all (fun other => decide (other = b)) then .ok b
      else .error (.malformed "conflicting physical bodies")

def Evidence.checkIdentity (e : Evidence) (row : IdentityRow) : Query Unit := do
  let native ← e.nativeBody row.physical
  let canonical ← e.canonicalBody row.canonical
  if canonical.original ≠ row.original then throw (.malformed "identity original differs")
  if let some marker := native.marker then
    if marker ≠ row.canonical then throw (.malformed "identity differs from native marker")
  if row.kind = .markedBody && native.marker ≠ some row.canonical then
    throw (.malformed "marked identity lacks its native marker")
  if row.physical = e.physicalRoot && row.canonical ≠ e.root then
    throw (.malformed "physical root identity differs")
  for prior in e.identities.filter (fun prior => decide (prior.physical = row.physical)) do
    if prior.canonical ≠ row.canonical || prior.original ≠ row.original then
      throw (.malformed "conflicting identity rows")

abbrev Drops := List Original

/-- Readable record and its captured chain identities. A count/digest without this body
does not create a record or a dropped-original witness. -/
structure Record where
  before : Nat
  identity : Nat
  drops : Drops
  /-- Exact native record names, separately from their immutable-original projection. -/
  names : List Canonical := []
deriving DecidableEq, Repr

structure Receipt where
  /-- Exact prefix/list identity; opaque-prefix count alone supplies no readable records. -/
  identity : Nat
  recordPrefix : Nat
  prunedCount : Nat := 0
  records : List Record
  capturedHeads : List Physical
  /-- Observer's full pre-contraction input, from which the model derives captured ownership.
  This is observed data, not all of which Rust persists. -/
  input : Evidence
  locals : List (Physical × List Physical)
  switched : Bool := false
deriving DecidableEq, Repr

structure Intent where
  fromHeads : List (Physical × List Physical)
  to : List Physical
  identities : List IdentityRow
deriving DecidableEq, Repr

structure RetainedExport where
  input : Physical
  output : Physical
  parents : List Physical
  recordedFields : Nat
  physicalBefore : Nat
  physicalAfter : Nat
  outcomes : Nat
deriving DecidableEq, Repr

structure Persistent where
  acceptedBase : Option Canonical := none
  recordPrefix : Nat := 0
  prunedCount : Nat := 0
  applied : List Record := []
  earlier : List Record := []
  custody : List Record := []
  pending : Drops := []
  /-- Readable renamings by canonical id. Expansion never supplies dropped original names. -/
  renamings : List (Canonical × List Canonical) := []
  intent : Option Intent := none
  /-- Authoritative saved expectations and independently retained export observations. -/
  expected : List (Physical × Nat) := []
  exports : List RetainedExport := []
deriving DecidableEq, Repr, Inhabited

end Musubi.NativeLifecycle

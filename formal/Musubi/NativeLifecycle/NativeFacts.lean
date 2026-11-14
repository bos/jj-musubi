/-
Exact raw observation lookups, not source-selection or rendered-output predicates. Tables
must come from independent native replay/encoding observations before Rust correspondence
consumes them. Reference labels do not authenticate a table. No native law is asserted here.
-/
import Musubi.NativeLifecycle.Selectors
import Lean

namespace Musubi.NativeLifecycle

structure EncodingTable where
  canonical : List CanonicalBody := []
  native : List NativeBody := []
deriving DecidableEq, Repr, Inhabited

def sameCanonicalShape (a b : CanonicalBody) : Bool := decide ({ a with id := b.id } = b)
def sameNativeShape (a b : NativeBody) : Bool := decide ({ a with id := b.id } = b)

/- Diagnostic-only serialization. Numeric labels and content tokens are expanded against
the immutable raw request by the codec; this does not add an encoding candidate. -/
namespace EncodingDiagnostic
open Lean (Json toJson)

def list (f : α → Json) (values : List α) : Json := .arr (values.map f).toArray
def optional (f : α → Json) : Option α → Json
  | none => .null
  | some value => Json.mkObj [("some", f value)]
def pair (f : α → Json) (g : β → Json) (value : α × β) : Json :=
  .arr #[f value.1, g value.2]
def copy (value : Copy) : Json := Json.mkObj [
  ("name", toJson (String.ofList value.name)), ("suffix", toJson (String.ofList value.suffix))]
def workspace (value : WorkspaceKey) : Json := Json.mkObj [
  ("owner", copy value.owner), ("name", toJson (String.ofList value.name))]
def stamp (value : Stamp) : Json := Json.mkObj [
  ("known", list copy value.known),
  ("latest", list (pair copy (list (fun id => toJson id.value))) value.latest),
  ("worked", list (pair copy (list (fun id => toJson id.value))) value.worked),
  ("forgetAfter", list (pair copy (list (pair (fun id => toJson id.value)
    (optional toJson)))) value.forgetAfter)]
def canonical (value : CanonicalBody) : Json := Json.mkObj [
  ("id", toJson value.id.value), ("original", toJson value.original.value),
  ("originalParents", list (fun id => toJson id.value) value.originalParents),
  ("parents", list (fun id => toJson id.value) value.parents),
  ("references", list (fun id => toJson id.value) value.references),
  ("referenceRevert", toJson value.referenceRevert),
  ("authorWorkspace", optional workspace value.authorWorkspace),
  ("endTime", toJson value.endTime), ("work", optional copy value.work),
  ("forgets", list copy value.forgets),
  ("forgetAfter", optional (optional toJson) value.forgetAfter),
  ("fixup", toJson value.fixup),
  ("rewrites", list (pair toJson (list toJson)) value.rewrites),
  ("stamp", optional stamp value.stamp),
  ("workspaces", list (pair workspace toJson) value.workspaces),
  ("content", toJson value.content)]
def differences (a b : CanonicalBody) : List String :=
  ([ ("original", decide (a.original = b.original)),
     ("originalParents", decide (a.originalParents = b.originalParents)),
     ("parents", decide (a.parents = b.parents)),
     ("references", decide (a.references = b.references)),
     ("referenceRevert", decide (a.referenceRevert = b.referenceRevert)),
     ("authorWorkspace", decide (a.authorWorkspace = b.authorWorkspace)),
     ("endTime", decide (a.endTime = b.endTime)), ("work", decide (a.work = b.work)),
     ("forgets", decide (a.forgets = b.forgets)),
     ("forgetAfter", decide (a.forgetAfter = b.forgetAfter)),
     ("fixup", decide (a.fixup = b.fixup)), ("rewrites", decide (a.rewrites = b.rewrites)),
     ("stamp", decide (a.stamp = b.stamp)),
     ("workspaces", decide (a.workspaces = b.workspaces)),
     ("content", decide (a.content = b.content)) ].filter (fun row => !row.2)).map (·.1)
def failed (computed : CanonicalBody) (candidates : List CanonicalBody) : Json := Json.mkObj [
  ("kind", toJson "canonical encoding failure"), ("computed", canonical computed),
  ("candidates", list (fun observed => Json.mkObj [
    ("body", canonical observed), ("differentFields", toJson (differences computed observed))])
    candidates)]

end EncodingDiagnostic

/-- The independent encoding table is searched by the complete computed body, excluding
only the hash result. An absent entry never allocates an invented identity. -/
def encodeCanonical (e : Evidence) (table : EncodingTable) (body : CanonicalBody) :
    Query CanonicalBody := do
  let matching := (e.canonical ++ table.canonical).filter (sameCanonicalShape body)
  match unique matching with
  | [result] => return result
  | [] => throw (.encoding ((EncodingDiagnostic.failed body (e.canonical ++ table.canonical)).compress))
  | _ => throw (.encoding "conflicting canonical hashes")

def encodeNative (e : Evidence) (table : EncodingTable) (body : NativeBody) : Query NativeBody := do
  let matching := (e.native ++ table.native).filter (sameNativeShape body)
  match unique matching with
  | [result] => return result
  | [] => throw (.encoding "native body")
  | _ => throw (.encoding "conflicting native hashes")

structure FieldFact where
  /-- Portable fixture/source reference plus an exact input instance, not a validity bit. -/
  reference : String
  repositoryContext : Nat
  nativeGraph : List NativeBody
  parents : List Physical
  fields : Nat
deriving DecidableEq, Repr

def inheritedFields (e : Evidence) (facts : List FieldFact) (parents : List Physical) : Query Nat := do
  match parents with
  | [] => throw (.nativeFact "parentless field inheritance")
  | [parent] => return (← e.nativeBody parent).gitFields
  | _ =>
    let matching := facts.filter fun fact => decide
      (fact.repositoryContext = e.repositoryContext ∧ fact.nativeGraph = e.native ∧
        fact.parents = parents)
    match unique (matching.map (·.fields)) with
    | [fields] => return fields
    | [] => throw (.nativeFact "complete native field merge observation")
    | _ => throw (.nativeFact "conflicting native field merge observations")

inductive PhysicalScope where
  | selectedRef (name : Nat)
  | completeSnapshot
deriving DecidableEq, Repr, Inhabited

structure PhysicalFact where
  scope : PhysicalScope
  before : Nat
  after : Nat
deriving DecidableEq, Repr

inductive HelperKind where
  | load
  | repair
deriving DecidableEq, Repr

structure HelperFact where
  reference : String
  kind : HelperKind
  repositoryContext : Nat
  nativeGraph : List NativeBody
  heads : List Physical
  orderedInputs : List Physical
  written : List NativeBody
  result : Physical
  afterHeads : List Physical
  /-- None leaves physical state unknown. A bookmark-x observation is scoped to that ref. -/
  physical : Option PhysicalFact := none
deriving DecidableEq, Repr

def orderedNativeInputs (e : Evidence) (heads : List Physical) : Query (List Physical) := do
  let bodies ← heads.mapM e.nativeBody
  return (bodies.mergeSort fun a b =>
    if a.endTime = b.endTime then decide (a.id.value ≤ b.id.value)
    else decide (a.endTime ≤ b.endTime)).map (·.id)

/-- Publication receives an operand vector, not a head-set enumeration. The native stable
timestamp sort preserves that vector on ties; explicit indices avoid relying on sort stability. -/
def orderedPublicationInputs (e : Evidence) (operands : List Physical) :
    Query (List Physical) := do
  let bodies ← operands.mapM e.nativeBody
  let indexed := (List.range bodies.length).zip bodies
  return (indexed.mergeSort fun a b =>
    if a.2.endTime = b.2.endTime then decide (a.1 ≤ b.1)
    else decide (a.2.endTime ≤ b.2.endTime)).map (·.2.id)

/-- This checks an observation's exact raw operands. Native semantic authentication is a
separate gate, including the codec's embedding of physical-id tie order. -/
def helperInputMatches (e : Evidence) (heads : List Physical) (fact : HelperFact) : Query Bool := do
  return fact.repositoryContext == e.repositoryContext &&
    decide (fact.nativeGraph = e.native) && sameSet fact.heads heads &&
    decide (fact.orderedInputs = (← orderedNativeInputs e heads))

structure NativeFacts where
  encodings : EncodingTable := {}
  fields : List FieldFact := []
  helpers : List HelperFact := []
deriving DecidableEq, Repr, Inhabited

end Musubi.NativeLifecycle

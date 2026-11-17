/-
Lookups in tables of exact raw observations: encodings of complete bodies, native merge calls,
helper outcomes and the physical Git state. A table must come from independent native replay or
encoding observations, and a reference label does not authenticate it. The lookups answer no
source-selection or rendering question, and no native law is asserted.
-/
import Musubi.NativeLifecycle.Selectors

namespace Musubi.NativeLifecycle

structure EncodingTable where
  canonical : List CanonicalBody := []
  native : List NativeBody := []
deriving DecidableEq, Repr, Inhabited

def sameCanonicalShape (a b : CanonicalBody) : Bool := decide ({ a with id := b.id } = b)
def sameNativeShape (a b : NativeBody) : Bool := decide ({ a with id := b.id } = b)

/-- The independent encoding table is searched by the complete computed body, excluding
only the hash result. An absent entry never allocates an invented identity. -/
def encodeCanonical (e : Evidence) (table : EncodingTable) (body : CanonicalBody) :
    Query CanonicalBody := do
  let matching := (e.canonical ++ table.canonical).filter (sameCanonicalShape body)
  match unique matching with
  | [result] => return result
  | [] => throw (.encoding "canonical body")
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

/-- One independently replayed unpublished native merge call. The context label retains
the full caller configuration and backend/index snapshot; the native graph and ordered
operands are separate exact inputs. Written bodies are the replay's complete write sequence,
not selected Rust outputs or a description-based subset of the physical corpus. -/
structure PreparationProbeFact where
  reference : String
  contextBefore : Nat
  nativeGraph : List NativeBody
  orderedInputs : List Physical
  written : List NativeBody
  result : Physical
  contextAfter : Nat
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
  preparationProbes : List PreparationProbeFact := []
deriving DecidableEq, Repr, Inhabited

end Musubi.NativeLifecycle

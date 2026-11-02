/- The finite operation DAG and commit observations used by expected-value conformance. -/
import Musubi.Expected

namespace Musubi.Refs.Expected.Exec

/-- The commit's time and a target number ordered as its commit id. -/
abbrev Side := Int × Nat

/-- Prefer later committer time, then greater commit id; removals are not candidates. -/
def latest (sides : List Side) : Option Nat :=
  (sides.foldl (fun best candidate => match best with
    | none => some candidate
    | some old =>
      if old.1 < candidate.1 || (old.1 == candidate.1 && old.2 < candidate.2)
      then some candidate else some old) none).map Prod.snd

structure Node where
  target : Nat
  known : Option (Option Nat) := none
  recorded : Option (Option Nat) := none
  boundary : Bool := false
  parents : List Nat := []
  deriving Inhabited

structure Table where
  resolved : List Nat
  /-- Target and its positive, present terms' commit times and commit-id-ordered numbers. -/
  sides : List (Nat × List Side)

def Table.side (tb : Table) (target : Nat) : Option Nat :=
  latest ((tb.sides.find? (·.1 == target)).map Prod.snd |>.getD [])

def observe (nodes : List Node) (i : Nat) : Observation Nat Nat :=
  let node := nodes[i]?.getD default
  { target := node.target, known := node.known, recorded := node.recorded,
    boundary := node.boundary,
    parents := node.parents.map fun p => (p, (nodes[p]?.getD default).target) }

/-- Parents precede children. Reject malformed tables rather than hiding fuel exhaustion. -/
def valid (nodes : List Node) (head : Nat) : Bool :=
  head < nodes.length && (nodes.zipIdx.all fun (node, i) => node.parents.all (· < i))

def run (tb : Table) (nodes : List Node) (head : Nat) : Option (Option Nat) :=
  if valid nodes head then eval tb.resolved.contains tb.side (observe nodes) (nodes.length + 1) head
  else none

end Musubi.Refs.Expected.Exec

/-
What musubi decides when it moves jj operation heads that it read earlier
(`docs/internals/design.md`, "Moving op heads"; `crates/musubi-jj/src/node/heads.rs`), as pure
functions for the oracle (`docs/internals/conformance.md`, "Moving op heads"), and what it reads of
operations.

An operation is a `Nat`, and `Graph` has what musubi reads of one: its parents.

* `same` is `plan::same` in `heads/plan.rs`, the check that the op heads are those musubi read,
  before it moves them. `OpHeadsRace.lean` puts it among jj's commands.
-/

namespace Musubi.OpHeads

/-- What musubi reads of operations. -/
structure Graph where
  parents : Nat → List Nat

/-- `g` with operation `n`. -/
def Graph.add (g : Graph) (n : Nat) (ps : List Nat) : Graph where
  parents i := if i = n then ps else g.parents i

/-- Every operation's parents come before it, as ids go in the oracle and in the model. -/
def Graph.Dag (g : Graph) : Prop := ∀ x p, p ∈ g.parents x → p < x

/-- Whether `a` and `b` are the same op heads, in any order: the check before a move. -/
def same (a b : List Nat) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

theorem same_iff {a b : List Nat} : same a b = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [same, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩
  · intro h
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

/-- The op heads musubi read, that it puts `new` in place of: those not in `new`. -/
def oldOf (read new : List Nat) : List Nat := read.filter fun h => !new.contains h

end Musubi.OpHeads

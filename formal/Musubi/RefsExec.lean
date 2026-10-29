/-
`Refs.lean`'s functions over ref targets a test names by number, for the oracle
(`docs/internals/conformance.md`, "Per-machine refs").

The model is over any `RefAlg`. The tests' targets are jj's, merged by jj-lib, which the
oracle can't run, so a test numbers the targets it uses, `0` for none, and sends with each
request what the model needs of them: which are resolved and which writable, the terms of
each conflict, and jj's merge of each triple the request can merge that the laws don't
settle. `tableAlg` is the `RefAlg` on those numbers: the laws first, so they hold by
construction, then the table. Every merge `Refs.lean`'s slot functions make is of their
arguments' targets, so a test that sends the merges of every triple of them sends all a
request needs; one it didn't send gives `unknown`, which the test refuses.
-/
import Musubi.Refs

namespace Musubi.Refs.Exec

open Musubi.Refs

/-- What a test says of its targets. -/
structure Table where
  resolved : List Nat
  writable : List Nat
  /-- Each conflict, and its terms, absent included. -/
  terms : List (Nat × List Nat)
  /-- `(a, b, c, m)`: jj merges `a` with the change from `b` to `c` to `m`. -/
  merges : List (Nat × Nat × Nat × Nat)

/-- The merge a request needed and its test didn't send. -/
def unknown : Nat := 4294967295

def Table.merge (tb : Table) (a b c : Nat) : Nat :=
  match tb.merges.find? fun (x, y, z, _) => x == a && y == b && z == c with
  | some (_, _, _, m) => m
  | none => unknown

/-- The `RefAlg` of a test's targets: the laws, then jj's merges as the test sent them. -/
@[instance_reducible] def tableAlg (tb : Table) : RefAlg Nat where
  merge a b c := if b = c then a else if a = b then c else if a = c then a else tb.merge a b c
  absent := 0
  resolved t := tb.resolved.contains t
  writable t := tb.writable.contains t && tb.resolved.contains t
  writable_resolved _ h := by simp only [Bool.and_eq_true] at h; exact h.2
  merge_unchanged_other _ _ := by simp
  merge_unchanged_self b c := by by_cases h : b = c <;> simp [h]
  merge_same_change a b := by by_cases h : b = a <;> simp [h]

/-- The terms of a test's conflicts. `side` is musubi's choice among them, which the test
makes, so none here: no function the oracle answers reads it. -/
@[instance_reducible] def tableSides (tb : Table) : @Sides Nat (tableAlg tb) :=
  @Sides.mk Nat (tableAlg tb) (fun _ => none)
    (fun t g => ((tb.terms.find? (·.1 == t)).map (·.2.contains g)).getD false)
    (fun _ _ h => nomatch h)

instance decLInv [DecidableEq T] [RefAlg T] (s : Machine T) : Decidable (LInv s) := by
  unfold LInv; infer_instance

instance decCInv [DecidableEq T] [RefAlg T] [Sides T] (s : CMachine T) : Decidable (CInv s) := by
  unfold CInv; infer_instance

instance decRestorable [DecidableEq T] [RefAlg T] (o : Slot T) (s : Machine T) :
    Decidable (Restorable o s) := by
  unfold Restorable; infer_instance

instance decRestorableRemote [DecidableEq T] [RefAlg T] (o : Slot T) (s : Machine T) :
    Decidable (RestorableRemote o s) := by
  unfold RestorableRemote; infer_instance

/-- A request: one of the slot functions, with its arguments. -/
inductive Call where
  | set (s : TSlot Nat) (l : Nat)
  | track (s : TSlot Nat)
  /-- jj's import, a new remote ref tracked by default, as the test configures `origin`. -/
  | import (s : TSlot Nat) (g : Nat)
  | merge (b v w : TSlot Nat)
  | exportLocal (s : TSlot Nat) (g : Nat)
  | exportRemote (s : TSlot Nat) (g : Nat)
  | exportConflicted (s : TSlot Nat) (g e : Nat)
  /-- `LInv`, and `CInv` with expected value `e`. -/
  | linv (s : TSlot Nat) (g : Nat) (moved : Bool)
  | cinv (s : TSlot Nat) (g : Nat) (moved : Bool) (e : Nat)
  /-- `Restorable o`, and `CStep.restore`'s condition for a remote bookmark. -/
  | restorable (o s : TSlot Nat)
  | restorableRemote (o s : TSlot Nat)

/-- An answer: a slot and `.git`'s value, a slot after an import and whether the import set
the bookmark (`TSlot.importSets`), or whether a proposition holds. -/
inductive Answer where
  | slot (s : TSlot Nat) (g : Option Nat)
  | imported (s : TSlot Nat) (sets : Bool)
  | holds (b : Bool)

/-- The machine with slot `s` and `.git` at `g`, its tracking state aside. -/
def machine (s : TSlot Nat) (g : Nat) (moved : Bool) : Machine Nat := ⟨s.toSlot, g, moved⟩

/-- `s` with the targets of `v`. -/
def withSlot (s : TSlot Nat) (v : Slot Nat) : TSlot Nat := { s with toSlot := v }

def run (tb : Table) : Call → Answer
  | .set s l => letI := tableAlg tb; .slot (TSlot.set l s) none
  | .track s => letI := tableAlg tb; .slot (TSlot.track s) none
  | .import s g =>
    letI := tableAlg tb; .imported (TSlot.import true s g) (TSlot.importSets true s g)
  | .merge b v w => letI := tableAlg tb; .slot (TSlot.merge b v w) none
  | .exportLocal s g =>
    letI := tableAlg tb
    let (s', g') := TSlot.exportLocal s g
    .slot s' (some g')
  | .exportRemote s g =>
    letI := tableAlg tb
    let m := exportRemote (machine s g false)
    .slot (withSlot s m.v) (some m.G)
  | .exportConflicted s g e =>
    letI := tableAlg tb
    letI := tableSides tb
    let m := exportConflicted (⟨machine s g false, e⟩ : CMachine Nat)
    .slot (withSlot s m.v) (some m.G)
  | .linv s g moved => letI := tableAlg tb; .holds (decide (LInv (machine s g moved)))
  | .cinv s g moved e =>
    letI := tableAlg tb
    letI := tableSides tb
    .holds (decide (CInv (⟨machine s g moved, e⟩ : CMachine Nat)))
  | .restorable o s => letI := tableAlg tb; .holds (decide (Restorable o.toSlot (machine s 0 false)))
  | .restorableRemote o s =>
    letI := tableAlg tb
    .holds (decide (RefAlg.resolved o.R = true → RestorableRemote o.toSlot (machine s 0 false)))

end Musubi.Refs.Exec

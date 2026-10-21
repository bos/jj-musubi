/-
Per-machine and shared state in a replicated view, for one git ref (docs/design.md,
"Per-machine state in a replicated view").

In a colocated repository each view records what jj last saw in this machine's `.git`, and
every `jj` command imports any difference between that record and `.git` as a change made
with git. musubi replicates the rest of the view and keeps the record per-machine. This file
models one ref. jj's ref merge is an abstract three-way merge that obeys the trivial
resolution laws of `merge_ref_targets`, and git is an adversary that can move the ref at any
time. Commit graphs, rebases and jj's conflict algebra are not modeled.

For a local bookmark `x`, whose record (`x@git` and `git_refs`) is per-machine:

- an import changes the bookmark only if git moved `refs/heads/x` since jj last imported
  (`noSpuriousRevert`). This holds whatever musubi realizes, and whether or not its export
  succeeds. It also holds if the realization is published and a `jj` command imports before
  the export; musubi exports first, and the other unlocked order, an import against the old
  op head after `.git` changed, makes a concurrent operation, which this linear model does
  not cover;
- replicating the record verbatim instead reverts another machine's move of the bookmark
  with no git move at all (`verbatim_reverts`), because the record lets one machine's `.git`
  reach another (`verbatim_interferes`, against `realize_noninterference`).

For a remote bookmark `x@origin`, which is shared, the record of `refs/remotes/origin/x`
(`git_refs`) is per-machine but the remote bookmark itself is replicated:

- an import changes nothing while every realization is exported before any `jj` command can
  import (`remoteNoSpuriousRevert`);
- otherwise, the import resets the remote bookmark to this machine's `.git` value and merges
  that into the bookmark tracking it (`remote_reset_without_export`), with no `git` command
  having run. jj skips the export of a conflicted remote bookmark, so musubi writes one of
  its sides to `.git` itself, the same on every machine (`export_conflicted_remote_bookmarks`
  in `node.rs`); the import then resolves the conflict to that side. A ref update that fails
  for another reason still ends this way.

Only one ref and a linear op history are modeled. Concurrent op heads appear only in
`merge_in_sync`, a fact about `merge` not connected to the step relations.
-/

namespace Musubi.Refs

/-- jj's `RefTarget`, abstractly: absent, one commit, or a conflict. `merge a b c` is
`merge_ref_targets(a, b, c)`, `a` with the change from base `b` to `c` applied. The laws are
the trivial resolutions jj's `Merge::resolve_trivial` applies before looking at commits. -/
class RefAlg (T : Type) where
  merge : T → T → T → T
  /-- Not a conflict: absent or one commit. `.git` holds only resolved values. -/
  resolved : T → Bool
  /-- A value export writes to git: resolved and not the root commit. -/
  writable : T → Bool
  writable_resolved : ∀ a, writable a = true → resolved a = true
  merge_unchanged_other : ∀ a b, merge a b b = a
  merge_unchanged_self : ∀ b c, merge b b c = c
  merge_same_change : ∀ a b, merge a b a = a

open RefAlg

variable {T : Type} [DecidableEq T] [RefAlg T]

/-- One ref as an op head's view records it.

For a local bookmark `x`, `L` is the bookmark, `R` is `x@git`, and `K` is
`git_refs["refs/heads/x"]`. `L` is shared; `R` and `K` are per-machine.

For a remote bookmark `x@origin` tracked by `x`, `L` is `x`, `R` is `x@origin`, and `K` is
`git_refs["refs/remotes/origin/x"]`. `L` and `R` are shared; `K` is per-machine. -/
structure Slot (T : Type) where
  L : T
  R : T
  K : T

/-- jj's import of the ref when `.git` holds `g` (`import_refs`): the record takes `g`, and if
`g` differs from `R`, the change from `R` to `g` is merged into the bookmark. That assumes
`R` is tracked, as `x@git` always is; jj merges nothing into the bookmark from an untracked
remote bookmark, or from a new one unless auto-tracking is configured. -/
def Slot.import (v : Slot T) (g : T) : Slot T :=
  { L := if g = v.R then v.L else merge v.L v.R g, R := g, K := g }

theorem Slot.import_self {v : Slot T} {g : T} (hR : v.R = g) (hK : v.K = g) :
    v.import g = v := by
  cases v with
  | mk L R K =>
    simp only at hR hK
    subst hR hK
    simp [Slot.import]

/-- One machine: its op head's view of the ref, and `.git`. -/
structure Machine (T : Type) where
  v : Slot T
  /-- The ref in this machine's `.git`. -/
  G : T
  /-- Ghost: something other than jj or musubi moved the ref in `.git` since jj last
  imported. -/
  moved : Bool

/-! ## Local bookmarks -/

/-- jj's export of a local bookmark (`export_refs`). If the bookmark matches `git_refs` there
is nothing to write, but `x@git` catches up with a resolved bookmark. Otherwise the update of
`refs/heads/x` is a compare-and-swap against `git_refs`, refused for a conflicted bookmark,
the root commit, or a conflicted record. A failed update changes nothing, so it is the same
as not exporting. -/
def exportLocal (s : Machine T) : Machine T :=
  if s.v.L = s.v.K then
    if resolved s.v.L then { s with v := { s.v with R := s.v.L } } else s
  else if writable s.v.L = true ∧ resolved s.v.K = true ∧ s.G = s.v.K then
    { s with v := { s.v with R := s.v.L, K := s.v.L }, G := s.v.L }
  else s

/-- musubi's realization of a canonical operation whose view has the bookmark at `c`: the
shared field from the canonical view, the per-machine fields inherited from the parent. -/
def realizeLocal (c : T) (v : Slot T) : Slot T := { v with L := c }

/-- A machine's steps. A `jj` command is an import, a `set`, and an export; musubi's sync is
an `advance` and an export. Steps interleave freely, so a `jj` command may import between
musubi's `advance` and its export, which jj's import/export lock prevents. -/
inductive LStep : Machine T → Machine T → Prop
  /-- A `git` command moves the ref. -/
  | gitMove (s : Machine T) (g : T) : LStep s { s with G := g, moved := true }
  | jjImport (s : Machine T) : LStep s { s with v := s.v.import s.G, moved := false }
  | jjExport (s : Machine T) : LStep s (exportLocal s)
  /-- A `jj` command changes the bookmark. -/
  | set (s : Machine T) (l : T) : LStep s { s with v := { s.v with L := l } }
  /-- musubi realizes a canonical operation and publishes it. -/
  | advance (s : Machine T) (c : T) : LStep s { s with v := realizeLocal c s.v }

/-- Unless git moved the ref, the record matches `.git`. -/
def LInv (s : Machine T) : Prop := s.moved = false → s.v.R = s.G ∧ s.v.K = s.G

theorem exportLocal_inv {s : Machine T} (hs : LInv s) : LInv (exportLocal s) := by
  unfold exportLocal
  by_cases h1 : s.v.L = s.v.K
  · rw [ite_eq_left h1]
    by_cases h2 : resolved s.v.L = true
    · rw [ite_eq_left h2]
      intro hm
      obtain ⟨_, hK⟩ := hs hm
      exact ⟨h1.trans hK, hK⟩
    · rw [ite_eq_right h2]
      exact hs
  · rw [ite_eq_right h1]
    by_cases h2 : writable s.v.L = true ∧ resolved s.v.K = true ∧ s.G = s.v.K
    · rw [ite_eq_left h2]
      exact fun _ => ⟨rfl, rfl⟩
    · rw [ite_eq_right h2]
      exact hs

theorem LStep.inv {s t : Machine T} (h : LStep s t) (hs : LInv s) : LInv t := by
  cases h with
  | gitMove => intro hm; simp at hm
  | jjImport => intro _; simp [Slot.import]
  | jjExport => exact exportLocal_inv hs
  | set => exact hs
  | advance => exact hs

/-- Runs from any state satisfying the invariant, such as one just after an import. -/
inductive LReach : Machine T → Prop
  | init {s : Machine T} : LInv s → LReach s
  | step {s t : Machine T} : LReach s → LStep s t → LReach t

theorem LReach.inv {s : Machine T} (h : LReach s) : LInv s := by
  induction h with
  | init h => exact h
  | step _ hst ih => exact hst.inv ih

/-- **No spurious revert.** Unless git moved the ref, an import changes nothing. -/
theorem noSpuriousRevert {s : Machine T} (h : LReach s) (hm : s.moved = false) :
    s.v.import s.G = s.v :=
  have ⟨hR, hK⟩ := h.inv hm
  Slot.import_self hR hK

/-- An import moves the bookmark only if git moved the ref. -/
theorem import_moves_only_after_git {s : Machine T} (h : LReach s)
    (hL : (s.v.import s.G).L ≠ s.v.L) : s.moved = true := by
  cases hm : s.moved
  · exact absurd (by rw [noSpuriousRevert h hm]) hL
  · rfl

/-- **Verbatim replication reverts.** Machine B is in sync with its `.git` at `x`; machine A
moved the bookmark to `y` and exported it, so A's view records `y` throughout. If B adopts
A's view whole, B's next import sees git "move" the branch from `y` back to `x`, and puts the
bookmark back at `x`, although no `git` command ran. Realized instead, the bookmark stays at
`y`. (The test `verbatim_replication_reverts_bookmarks` is the same scenario.) -/
theorem verbatim_reverts {x y : T} (hxy : x ≠ y) :
    let b : Machine T := ⟨⟨x, x, x⟩, x, false⟩
    let a : Slot T := ⟨y, y, y⟩
    LReach b ∧ (a.import b.G).L = x ∧ ((realizeLocal a.L b.v).import b.G).L = y := by
  refine ⟨LReach.init (fun _ => ⟨rfl, rfl⟩), ?_, ?_⟩
  · simp [Slot.import, hxy, merge_unchanged_self]
  · simp [Slot.import, realizeLocal]

omit [DecidableEq T] [RefAlg T] in
/-- **Noninterference.** What a machine realizes from another machine's view depends only on
that view's shared field. -/
theorem realize_noninterference {a a' : Slot T} (h : a.L = a'.L) (v : Slot T) :
    realizeLocal a.L v = realizeLocal a'.L v := by
  rw [h]

/-- Verbatim, two views that agree on the shared field can leave a machine with different
bookmarks after its next import: the other machine's record reaches it. -/
theorem verbatim_interferes {x y : T} (hxy : x ≠ y) :
    ∃ a a' : Slot T, a.L = a'.L ∧ (a.import x).L ≠ (a'.import x).L := by
  refine ⟨⟨y, y, y⟩, ⟨y, x, x⟩, rfl, ?_⟩
  simp [Slot.import, hxy, merge_unchanged_self]

omit [DecidableEq T] in
/-- Concurrent op heads with base `b` merge each per-machine field three-way, in jj and in
musubi's realization of a merge operation (`inherited_per_machine`). If one head left the
field as the base had it, or both agree, the merge is the other's value. -/
theorem merge_in_sync {b f₁ f₂ g : T}
    (h : (f₁ = b ∧ f₂ = g) ∨ (f₁ = g ∧ f₂ = b) ∨ (f₁ = g ∧ f₂ = g)) : merge f₁ b f₂ = g := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact merge_unchanged_self _ _
  · exact merge_unchanged_other _ _
  · exact merge_same_change _ _

/-! ## Remote bookmarks -/

/-- jj's export of a remote bookmark: a compare-and-swap of `refs/remotes/origin/x` from
`git_refs` to `x@origin`, refused for a conflicted remote bookmark, the root commit, or a
conflicted record. jj records no `@git` copy of a remote bookmark. -/
def exportRemote (s : Machine T) : Machine T :=
  if s.v.R ≠ s.v.K ∧ writable s.v.R = true ∧ resolved s.v.K = true ∧ s.G = s.v.K then
    { s with v := { s.v with K := s.v.R }, G := s.v.R }
  else s

/-- musubi's realization: both shared fields from the canonical view. -/
def realizeRemote (l c : T) (v : Slot T) : Slot T := { v with L := l, R := c }

/-- A machine's steps for a remote bookmark. -/
inductive RStep : Machine T → Machine T → Prop
  | gitMove (s : Machine T) (g : T) :
      resolved g = true → RStep s { s with G := g, moved := true }
  | jjImport (s : Machine T) : RStep s { s with v := s.v.import s.G, moved := false }
  | jjExport (s : Machine T) : RStep s (exportRemote s)
  | set (s : Machine T) (l : T) : RStep s { s with v := { s.v with L := l } }
  /-- `jj git fetch`: git updates the ref, and jj imports at once. -/
  | fetch (s : Machine T) (r : T) :
      resolved r = true → RStep s { s with v := s.v.import r, G := r, moved := false }
  /-- musubi realizes a canonical operation and, holding jj's import/export lock, exports it
  before publishing it. Only exports that succeed: `c` is already `.git`'s value, or
  writable. -/
  | advance (s : Machine T) (l c : T) :
      (c = s.G ∨ writable c = true) →
      RStep s (exportRemote { s with v := realizeRemote l c s.v })

/-- `.git` holds a resolved value, and unless git moved the ref, the remote bookmark and the
record match it. -/
def RInv (s : Machine T) : Prop :=
  resolved s.G = true ∧ (s.moved = false → s.v.R = s.G ∧ s.v.K = s.G)

theorem exportRemote_inv {s : Machine T} (hs : RInv s) : RInv (exportRemote s) := by
  unfold exportRemote
  by_cases h : s.v.R ≠ s.v.K ∧ writable s.v.R = true ∧ resolved s.v.K = true ∧ s.G = s.v.K
  · rw [ite_eq_left h]
    exact ⟨writable_resolved _ h.2.1, fun _ => ⟨rfl, rfl⟩⟩
  · rw [ite_eq_right h]
    exact hs

theorem advance_inv {s : Machine T} {l c : T} (hs : RInv s) (hc : c = s.G ∨ writable c = true) :
    RInv (exportRemote { s with v := realizeRemote l c s.v }) := by
  obtain ⟨hg, hsync⟩ := hs
  unfold exportRemote realizeRemote
  simp only
  by_cases h : c ≠ s.v.K ∧ writable c = true ∧ resolved s.v.K = true ∧ s.G = s.v.K
  · rw [ite_eq_left h]
    exact ⟨writable_resolved _ h.2.1, fun _ => ⟨rfl, rfl⟩⟩
  · rw [ite_eq_right h]
    refine ⟨hg, fun hm => ?_⟩
    obtain ⟨_, hK⟩ := hsync hm
    refine ⟨?_, hK⟩
    -- The export was not needed or not possible; either way `c` is `.git`'s value.
    by_cases hcK : c = s.v.K
    · exact hcK.trans hK
    · rcases hc with hc | hw
      · exact hc
      · exact absurd ⟨hcK, hw, hK ▸ hg, hK.symm⟩ h

theorem RStep.inv {s t : Machine T} (h : RStep s t) (hs : RInv s) : RInv t := by
  cases h with
  | gitMove g hg => exact ⟨hg, fun hm => by simp at hm⟩
  | jjImport => exact ⟨hs.1, fun _ => by simp [Slot.import]⟩
  | jjExport => exact exportRemote_inv hs
  | set => exact hs
  | fetch r hr => exact ⟨hr, fun _ => by simp [Slot.import]⟩
  | advance l c hc => exact advance_inv hs hc

inductive RReach : Machine T → Prop
  | init {s : Machine T} : RInv s → RReach s
  | step {s t : Machine T} : RReach s → RStep s t → RReach t

theorem RReach.inv {s : Machine T} (h : RReach s) : RInv s := by
  induction h with
  | init h => exact h
  | step _ hst ih => exact hst.inv ih

/-- **No spurious revert**, for remote bookmarks: while every realization is exported before
it is published, an import changes nothing unless git moved the ref. -/
theorem remoteNoSpuriousRevert {s : Machine T} (h : RReach s) (hm : s.moved = false) :
    s.v.import s.G = s.v :=
  have ⟨hR, hK⟩ := h.inv.2 hm
  Slot.import_self hR hK

/-- **A remote bookmark published without its export is reset.** Machine B is in sync with
its `.git`, and realizes a canonical operation that moves `x@origin` to `c`, a value export
can't write (a conflict, say). jj skips the export and the realization is published
anyway, as musubi did for conflicts before it wrote one of their sides itself. Then B's next import sets `x@origin` to B's `.git` value and merges that change into
`x`, although no `git` command ran. (A ref update that fails for another reason leaves the
state the same, so ends the same way.) The import's operation is an ordinary local
operation, which musubi replicates; that is not modeled here. -/
theorem remote_reset_without_export {s : Machine T} {l c : T} (hs : RInv s)
    (hm : s.moved = false) (hc : c ≠ s.G) (hw : writable c = false) :
    let t : Machine T := exportRemote { s with v := realizeRemote l c s.v }
    t.moved = false ∧ t.v.R = c ∧ (t.v.import t.G).R = s.G ∧
      (t.v.import t.G).L = merge l c s.G := by
  have hG := hs.2 hm
  have ht : exportRemote { s with v := realizeRemote l c s.v } =
      { s with v := realizeRemote l c s.v } := by
    unfold exportRemote
    rw [ite_eq_right]
    intro h
    simp [realizeRemote, hw] at h
  simp only [ht]
  refine ⟨hm, rfl, rfl, ?_⟩
  simp [Slot.import, realizeRemote, Ne.symm hc]

/-! ## Non-vacuity

The laws are satisfiable, and the counterexamples have instances. -/

/-- A minimal ref target: absent, a commit (`0` is the root), or a conflict. -/
inductive Tgt
  | absent
  | commit (n : Nat)
  | conflict
  deriving DecidableEq

instance : RefAlg Tgt where
  merge a b c := if b = c then a else if a = b then c else if a = c then a else .conflict
  resolved t := t != .conflict
  writable t := t != .conflict && t != .commit 0
  writable_resolved t h := by cases t <;> simp_all
  merge_unchanged_other a b := by simp
  merge_unchanged_self b c := by by_cases h : b = c <;> simp [h]
  merge_same_change a b := by by_cases h : b = a <;> simp [h]

example : (⟨Tgt.commit 2, .commit 2, .commit 2⟩ : Slot Tgt).import (.commit 1) =
    ⟨.commit 1, .commit 1, .commit 1⟩ := by
  simp [Slot.import, RefAlg.merge]

end Musubi.Refs

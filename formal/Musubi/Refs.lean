/-
Per-machine and shared state in a replicated view, for one git ref (docs/internals/design.md,
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
  op head after `.git` changed, makes a concurrent operation (below);
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
  its sides to `.git` itself, the same on every machine
  (`export_conflicted_remote_bookmarks` in `node/git.rs`); the import then resolves the
  conflict to that side. A ref update that fails for another reason still ends this way.

Concurrent op heads, which a `jj` command at an older operation makes, or one that loaded the
head before musubi published, are merged as jj merges views (`Slot.merge3`, `TSlot.merge`):

- a forked machine whose heads step as `LStep` against the one `.git` merges, unless both
  heads changed the record, to a machine `LReach` reaches, so every theorem above about
  local bookmarks holds after the merge (`fork_merge_inv`, `fork_noSpuriousRevert`). If
  both did, the merged record needn't match `.git`, and the next import moves the bookmark
  with no `git` command having run (`concurrent_records_revert`). jj does the same without
  musubi: it is jj's merge;
- jj merges a remote ref's target and tracking state separately, and drops a tracked remote
  ref with no target when its bookmark goes (`TSlot`). The targets are each merged three-way
  whatever the tracking states (`TSlot.merge_toSlot`), and the import agrees with
  `Slot.import` wherever the remote ref is tracked (`TSlot.import_toSlot`);
- musubi's realization of a canonical merge is jj's merge (`realizeMerge_eq`): its shortcut
  for the per-machine fields agrees with jj's merge wherever it applies (`shortcut_agrees`),
  as it didn't before #56 was fixed (`shortcutUnguarded_keeps_absent`,
  `shortcutUnguarded_untracks`); and where the heads have several closest common ancestors
  it merges against those merged, as jj does, since against the first of them a record can
  be left that the export can't correct (`firstBase_reverts`).

What the model still leaves out, as testing it against jj showed
(`crates/musubi-sync/tests/races/refs.rs`, docs/internals/conformance.md, "Per-machine refs"):

- Tracking in the steps above: `Slot.import` merges into the bookmark as from a tracked remote
  bookmark. jj keeps a tracked remote bookmark with no target only while its local bookmark
  exists, so once git or a fetch deletes `refs/remotes/origin/x` and the import deletes `x`
  with it, jj forgets that `x` tracked it. When the ref comes back, jj imports it untracked
  and leaves `x` absent, unless `remotes.origin.auto-track-bookmarks` covers `x`; the model
  sets `x`. `TSlot.import` has it right, as `TSlot.track` has `jj bookmark set` tracking
  the remote refs of a bookmark it creates; and a merge can leave `x@git` untracked too
  (`shortcutUnguarded_untracks`), after which git's moves of `refs/heads/x` don't move `x`
  until an export tracks it again.
- musubi's realization inherits the record whole, so it keeps a tracked absent `x@git` where
  the canonical operation deletes `x`, which jj would drop (`realize_not_WF`). Only the
  tracking state of a remote ref with no target differs.
- Merges of more than two heads, which jj and musubi merge one at a time, and criss-cross
  merges, whose base is itself a merge, are not modeled as runs; nor are concurrent heads of
  remote bookmarks, though `merge3_synced` is about any slot.
-/

namespace Musubi.Refs

/-- jj's `RefTarget`, abstractly: absent, one commit, or a conflict. `merge a b c` is
`merge_ref_targets(a, b, c)`, `a` with the change from base `b` to `c` applied. The laws are
the trivial resolutions jj's `Merge::resolve_trivial` applies before looking at commits. -/
class RefAlg (T : Type) where
  merge : T → T → T → T
  /-- No target: the ref doesn't exist. -/
  absent : T
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
the root commit, or a conflicted record. jj counts it a success, too, if `.git` already has
the bookmark's value (`move_git_ref`, `create_git_ref` and `delete_git_ref` in jj-lib), which
it can if git moved the ref there since the last import, and records it as exported. A
failed update changes nothing, so it is the same as not exporting. -/
def exportLocal (s : Machine T) : Machine T :=
  if s.v.L = s.v.K then
    if resolved s.v.L then { s with v := { s.v with R := s.v.L } } else s
  else if writable s.v.L = true ∧ resolved s.v.K = true ∧ (s.G = s.v.K ∨ s.G = s.v.L) then
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
    by_cases h2 : writable s.v.L = true ∧ resolved s.v.K = true ∧ (s.G = s.v.K ∨ s.G = s.v.L)
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
conflicted record, and a success if `.git` already has `x@origin`'s value, as for a local
bookmark. jj records no `@git` copy of a remote bookmark. -/
def exportRemote (s : Machine T) : Machine T :=
  if s.v.R ≠ s.v.K ∧ writable s.v.R = true ∧ resolved s.v.K = true ∧
      (s.G = s.v.K ∨ s.G = s.v.R) then
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
  by_cases h : s.v.R ≠ s.v.K ∧ writable s.v.R = true ∧ resolved s.v.K = true ∧
      (s.G = s.v.K ∨ s.G = s.v.R)
  · rw [ite_eq_left h]
    exact ⟨writable_resolved _ h.2.1, fun _ => ⟨rfl, rfl⟩⟩
  · rw [ite_eq_right h]
    exact hs

theorem advance_inv {s : Machine T} {l c : T} (hs : RInv s) (hc : c = s.G ∨ writable c = true) :
    RInv (exportRemote { s with v := realizeRemote l c s.v }) := by
  obtain ⟨hg, hsync⟩ := hs
  unfold exportRemote realizeRemote
  simp only
  by_cases h : c ≠ s.v.K ∧ writable c = true ∧ resolved s.v.K = true ∧ (s.G = s.v.K ∨ s.G = c)
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
      · exact absurd ⟨hcK, hw, hK ▸ hg, Or.inl hK.symm⟩ h

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

/-! ## Merges of concurrent op heads

jj merges concurrent op heads' views three-way against their closest common ancestor, field by
field (`merge_view` in jj-lib's `repo.rs`), and where they have several closest common
ancestors, against those merged first (`merge_operations`). Every `jj` command does so when it
finds several op heads, and so does musubi's `merge_heads`, each followed by its export.
musubi's realization of a canonical merge operation takes the shared fields from the
canonical view, which jj merged so on the machine that made it, and merges the per-machine
fields of its parents' local operations as jj would (`inherited_per_machine` in
`node/realize.rs`). Merges of more than two heads merge them one at a time. -/

/-- The targets of jj's merge of two op heads' views of one ref, `v` merged with `w` against
their base `b`: each field three-way, as `merge_ref_targets`. With tracking states, see
`TSlot.merge`, whose targets these are (`TSlot.merge_toSlot`). -/
def Slot.merge3 (b v w : Slot T) : Slot T :=
  { L := merge v.L b.L w.L, R := merge v.R b.R w.R, K := merge v.K b.K w.K }

/-- A head's record is the base's. -/
def Untouched (b v : Slot T) : Prop := v.R = b.R ∧ v.K = b.K

/-- A head's record matches `.git`'s value `g`. -/
def Synced (v : Slot T) (g : T) : Prop := v.R = g ∧ v.K = g

omit [DecidableEq T] in
/-- If each head's record is the base's or `.git`'s, and one of the three matches `.git`, so
does the merged record: `merge_in_sync` for both fields. -/
theorem merge3_synced {b v w : Slot T} {g : T}
    (hv : Untouched b v ∨ Synced v g) (hw : Untouched b w ∨ Synced w g)
    (h : Synced v g ∨ Synced w g ∨ Synced b g) : Synced (Slot.merge3 b v w) g := by
  unfold Slot.merge3 Synced
  simp only
  rcases hv with ⟨hvR, hvK⟩ | ⟨hvR, hvK⟩ <;> rcases hw with ⟨hwR, hwK⟩ | ⟨hwR, hwK⟩
  · rw [hvR, hvK, hwR, hwK, merge_unchanged_other, merge_unchanged_other]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact ⟨hvR ▸ h1, hvK ▸ h2⟩
    · exact ⟨hwR ▸ h1, hwK ▸ h2⟩
    · exact h
  · rw [hvR, hvK, hwR, hwK, merge_unchanged_self, merge_unchanged_self]
    exact ⟨rfl, rfl⟩
  · rw [hvR, hvK, hwR, hwK, merge_unchanged_other, merge_unchanged_other]
    exact ⟨rfl, rfl⟩
  · rw [hvR, hvK, hwR, hwK, merge_same_change, merge_same_change]
    exact ⟨rfl, rfl⟩

/-! ### Two op heads on one machine

A `jj` command that loaded an op head before musubi published a realization, or one run at an
older operation (`--at-op`), publishes an operation concurrent with the head, and the next
command merges them. Both heads' records describe the one `.git`. A `Fork` is a machine with
two heads `v` and `w` forked from the head `b`, each stepping as `LStep` against the shared
`.git`, until a merge makes them one again. -/

/-- A machine with two op heads, `v` and `w`, both descending from `b`. -/
structure Fork (T : Type) where
  b : Slot T
  v : Slot T
  w : Slot T
  /-- The ref in this machine's `.git`. -/
  G : T
  /-- Ghost: git moved the ref since `v`'s last import. -/
  mv : Bool
  /-- Ghost: git moved the ref since `w`'s last import. -/
  mw : Bool
  /-- Ghost: a step of `v` has changed its record since the fork. -/
  tv : Bool
  /-- Ghost: a step of `w` has changed its record since the fork. -/
  tw : Bool

/-- The same fork with its heads exchanged. -/
def Fork.swap (f : Fork T) : Fork T :=
  { f with v := f.w, w := f.v, mv := f.mw, mw := f.mv, tv := f.tw, tw := f.tv }

omit [DecidableEq T] [RefAlg T] in
@[simp] theorem Fork.swap_swap (f : Fork T) : f.swap.swap = f := by
  cases f; rfl

/-- The ghost `tv` after `v` became `t`. -/
def touch (tv : Bool) (v t : Slot T) : Bool := if t.R = v.R ∧ t.K = v.K then tv else true

/-- `v`'s export. -/
def Fork.exp (f : Fork T) : Machine T := exportLocal ⟨f.v, f.G, f.mv⟩

/-- A step of the head `v`: an `LStep` other than `gitMove`, against the shared `.git`. -/
inductive HStep : Fork T → Fork T → Prop
  | jjImport (f : Fork T) :
      HStep f { f with v := f.v.import f.G, mv := false, tv := touch f.tv f.v (f.v.import f.G) }
  | jjExport (f : Fork T) :
      HStep f { f with v := f.exp.v, G := f.exp.G, tv := touch f.tv f.v f.exp.v }
  | set (f : Fork T) (l : T) : HStep f { f with v := { f.v with L := l } }
  | advance (f : Fork T) (c : T) : HStep f { f with v := realizeLocal c f.v }

/-- A step of a forked machine: git moves the ref, or either head steps. -/
inductive FStep : Fork T → Fork T → Prop
  | gitMove (f : Fork T) (g : T) : FStep f { f with G := g, mv := true, mw := true }
  | left {f f' : Fork T} : HStep f f' → FStep f f'
  | right {f f' : Fork T} : HStep f.swap f' → FStep f f'.swap

/-- A machine's head forked in two. -/
def Fork.of (s : Machine T) : Fork T := ⟨s.v, s.v, s.v, s.G, s.moved, s.moved, false, false⟩

/-- Runs of a fork of any reachable machine. -/
inductive FReach : Fork T → Prop
  | fork {s : Machine T} : LReach s → FReach (Fork.of s)
  | step {f f' : Fork T} : FReach f → FStep f f' → FReach f'

/-- The machine once the heads are merged. Its ghost `moved` says git moved the ref since one
of the heads last imported. -/
def Fork.merged (f : Fork T) : Machine T := ⟨Slot.merge3 f.b f.v f.w, f.G, f.mv || f.mw⟩

/-- An untouched head's record is the base's. A head that alone touched its record matches
`.git` unless git moved the ref since it imported; and if neither did, the base does. -/
def FInv (f : Fork T) : Prop :=
  (f.tv = false → Untouched f.b f.v) ∧ (f.tw = false → Untouched f.b f.w) ∧
  (f.tv = true → f.tw = false → f.mv = false → Synced f.v f.G) ∧
  (f.tw = true → f.tv = false → f.mw = false → Synced f.w f.G) ∧
  (f.tv = false → f.tw = false → (f.mv = false ∨ f.mw = false) → Synced f.b f.G)

omit [DecidableEq T] [RefAlg T] in
theorem FInv.swap {f : Fork T} (h : FInv f) : FInv f.swap := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h2, h1, h4, h3, fun a b m => h5 b a (Or.comm.mp m)⟩

omit [DecidableEq T] [RefAlg T] in
/-- What a step of `v` must keep for the invariant to hold after it. -/
theorem FInv.of_v {f : Fork T} (hf : FInv f) (v' : Slot T) (G' : T) (mv' tv' : Bool)
    (h1 : tv' = false → Untouched f.b v')
    (h3 : tv' = true → f.tw = false → mv' = false → Synced v' G')
    (h4 : f.tw = true → tv' = false → f.mw = false → Synced f.w G')
    (h5 : tv' = false → f.tw = false → (mv' = false ∨ f.mw = false) → Synced f.b G') :
    FInv { f with v := v', G := G', mv := mv', tv := tv' } :=
  ⟨h1, hf.2.1, h3, h4, h5⟩

omit [RefAlg T] in
theorem touch_same {tv : Bool} {v t : Slot T} (h : t.R = v.R ∧ t.K = v.K) : touch tv v t = tv :=
  ite_eq_left h

omit [RefAlg T] in
theorem touch_changed {tv : Bool} {v t : Slot T} (h : ¬(t.R = v.R ∧ t.K = v.K)) :
    touch tv v t = true :=
  ite_eq_right h

omit [DecidableEq T] [RefAlg T] in
theorem Slot.ext' {s t : Slot T} (hL : s.L = t.L) (hR : s.R = t.R) (hK : s.K = t.K) : s = t := by
  cases s; cases t; simp_all

/-- `exportLocal` leaves the ghost alone, and either changes nothing, or copies the bookmark
to `R` (`L = K`), or writes it to `.git` and the record, which then match. -/
theorem exportLocal_cases (s : Machine T) :
    exportLocal s = s ∨
      ((exportLocal s).v = { s.v with R := s.v.L } ∧ s.v.L = s.v.K ∧ (exportLocal s).G = s.G ∧
        (exportLocal s).moved = s.moved) ∨
      (Synced (exportLocal s).v (exportLocal s).G ∧ (exportLocal s).v.K ≠ s.v.K ∧
        (exportLocal s).moved = s.moved) := by
  unfold exportLocal
  by_cases h1 : s.v.L = s.v.K
  · rw [ite_eq_left h1]
    by_cases h2 : resolved s.v.L = true
    · rw [ite_eq_left h2]
      exact Or.inr (Or.inl ⟨rfl, h1, rfl, rfl⟩)
    · rw [ite_eq_right h2]
      exact Or.inl rfl
  · rw [ite_eq_right h1]
    by_cases h2 : writable s.v.L = true ∧ resolved s.v.K = true ∧ (s.G = s.v.K ∨ s.G = s.v.L)
    · rw [ite_eq_left h2]
      exact Or.inr (Or.inr ⟨⟨rfl, rfl⟩, fun h => h1 h, rfl⟩)
    · rw [ite_eq_right h2]
      exact Or.inl rfl

theorem HStep.inv {f f' : Fork T} (h : HStep f f') (hf : FInv f) : FInv f' := by
  have hf' := hf
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf'
  cases h with
  | jjImport =>
    have hs : Synced (f.v.import f.G) f.G := ⟨rfl, rfl⟩
    by_cases hc : (f.v.import f.G).R = f.v.R ∧ (f.v.import f.G).K = f.v.K
    · rw [touch_same hc]
      refine hf.of_v _ _ _ _ (fun ht => ?_) (fun _ _ _ => hs) h4 (fun ht hw _ => ?_)
      · exact ⟨hc.1.trans (h1 ht).1, hc.2.trans (h1 ht).2⟩
      · exact ⟨(h1 ht).1 ▸ hc.1 ▸ hs.1, (h1 ht).2 ▸ hc.2 ▸ hs.2⟩
    · rw [touch_changed hc]
      exact hf.of_v _ _ _ _ (fun h => nomatch h) (fun _ _ _ => hs) (fun _ h => nomatch h)
        (fun h => nomatch h)
  | jjExport =>
    rcases exportLocal_cases ⟨f.v, f.G, f.mv⟩ with he | ⟨hv, hLK, hG, _⟩ | ⟨hs, hK, _⟩
    · have he' : f.exp = ⟨f.v, f.G, f.mv⟩ := he
      rw [he', touch_same ⟨rfl, rfl⟩]
      exact hf
    · have hv' : f.exp.v = { f.v with R := f.v.L } := hv
      have hG' : f.exp.G = f.G := hG
      rw [hv', hG']
      by_cases hc : f.v.L = f.v.R
      · have : ({ f.v with R := f.v.L } : Slot T) = f.v := Slot.ext' rfl hc rfl
        rw [this, touch_same ⟨rfl, rfl⟩]
        exact hf
      · rw [touch_changed (fun h => hc h.1)]
        refine hf.of_v _ _ _ _ (fun h => nomatch h) (fun _ hw hm => ?_) (fun _ h => nomatch h)
          (fun h => nomatch h)
        have hK : f.v.K = f.G := by
          cases htv : f.tv
          · exact (h1 htv).2.trans (h5 htv hw (Or.inl hm)).2
          · exact (h3 htv hw hm).2
        exact ⟨hLK.trans hK, hK⟩
    · have hs' : Synced f.exp.v f.exp.G := hs
      have hK' : ¬(f.exp.v.R = f.v.R ∧ f.exp.v.K = f.v.K) := fun h => hK h.2
      rw [touch_changed hK']
      exact hf.of_v _ _ _ _ (fun h => nomatch h) (fun _ _ _ => hs') (fun _ h => nomatch h)
        (fun h => nomatch h)
  | set => exact hf
  | advance => exact hf

theorem FStep.inv {f f' : Fork T} (h : FStep f f') (hf : FInv f) : FInv f' := by
  cases h with
  | gitMove =>
    obtain ⟨h1, h2, _, _, _⟩ := hf
    refine ⟨h1, h2, fun _ _ h => ?_, fun _ _ h => ?_, fun _ _ h => ?_⟩ <;> simp at h
  | left h => exact h.inv hf
  | right h =>
    have := (h.inv hf.swap).swap
    exact this

theorem FReach.inv {f : Fork T} (h : FReach f) : FInv f := by
  induction h with
  | fork hs =>
    refine ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩, fun h => ?_, fun h => ?_, fun _ _ hm => ?_⟩
    · simp [Fork.of] at h
    · simp [Fork.of] at h
    · rcases hm with hm | hm <;> exact hs.inv hm
  | step _ hst ih => exact hst.inv ih

/-- **A merge keeps the invariant**, unless both heads changed the record. Then the merged
machine is one `LReach` reaches (`fork_merged_reach`), and every theorem above about local
bookmarks holds of its runs. -/
theorem fork_merge_inv {f : Fork T} (h : FReach f) (ht : ¬(f.tv = true ∧ f.tw = true)) :
    LInv f.merged := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.inv
  intro hm
  simp only [Fork.merged, Bool.or_eq_false_iff] at hm
  obtain ⟨hmv, hmw⟩ := hm
  show Synced (Slot.merge3 f.b f.v f.w) f.G
  cases htv : f.tv <;> cases htw : f.tw
  · exact merge3_synced (Or.inl (h1 htv)) (Or.inl (h2 htw)) (Or.inr (Or.inr (h5 htv htw (Or.inl hmv))))
  · exact merge3_synced (Or.inl (h1 htv)) (Or.inr (h4 htw htv hmw)) (Or.inr (Or.inl (h4 htw htv hmw)))
  · exact merge3_synced (Or.inr (h3 htv htw hmv)) (Or.inl (h2 htw)) (Or.inl (h3 htv htw hmv))
  · exact absurd ⟨htv, htw⟩ ht

theorem fork_merged_reach {f : Fork T} (h : FReach f) (ht : ¬(f.tv = true ∧ f.tw = true)) :
    LReach f.merged :=
  LReach.init (fork_merge_inv h ht)

/-- **No spurious revert across a merge.** Unless both heads changed the record, an import
after the merge changes nothing unless git moved the ref since one of them imported. -/
theorem fork_noSpuriousRevert {f : Fork T} (h : FReach f) (ht : ¬(f.tv = true ∧ f.tw = true))
    (hm : f.merged.moved = false) : f.merged.v.import f.G = f.merged.v :=
  noSpuriousRevert (fork_merged_reach h ht) hm

/-! ### Tracking

jj records with each remote ref whether its bookmark tracks it, and keeps a tracked remote ref
with no target only while its bookmark exists (`View::set_local_bookmark_target` and
`set_remote_bookmark` in jj-lib's `view.rs`). It merges a remote ref's target and tracking
state separately (`merge_remote_refs` in `refs.rs`). Until here the model took every remote
ref to be tracked; a merge can untrack one. -/

/-- A ref with the tracking state `tr` of its remote ref `R`. `R = absent` with `tr = false`
is no remote ref at all, jj's `RemoteRef::absent()`. -/
structure TSlot (T : Type) extends Slot T where
  tr : Bool

/-- jj's view drops a remote ref with no target unless it is tracked and its bookmark exists. -/
def TSlot.norm (s : TSlot T) : TSlot T :=
  if s.R = absent ∧ (s.tr = false ∨ s.L = absent) then { s with tr := false } else s

/-- Every view jj makes. -/
def TSlot.WF (s : TSlot T) : Prop := s.R = absent → s.tr = true → s.L ≠ absent

omit [RefAlg T] [DecidableEq T] in
theorem TSlot.ext' {s t : TSlot T} (hL : s.L = t.L) (hR : s.R = t.R) (hK : s.K = t.K)
    (htr : s.tr = t.tr) : s = t := by
  obtain ⟨⟨_, _, _⟩, _⟩ := s
  obtain ⟨⟨_, _, _⟩, _⟩ := t
  simp_all

@[simp] theorem TSlot.norm_toSlot (s : TSlot T) : s.norm.toSlot = s.toSlot := by
  unfold TSlot.norm; split <;> rfl

@[simp] theorem TSlot.norm_L (s : TSlot T) : s.norm.L = s.L := congrArg Slot.L s.norm_toSlot
@[simp] theorem TSlot.norm_R (s : TSlot T) : s.norm.R = s.R := congrArg Slot.R s.norm_toSlot
@[simp] theorem TSlot.norm_K (s : TSlot T) : s.norm.K = s.K := congrArg Slot.K s.norm_toSlot

theorem TSlot.norm_WF (s : TSlot T) : s.norm.WF := by
  unfold TSlot.norm TSlot.WF
  split
  · intro _ h; exact nomatch h
  · next h =>
    intro hR _ hL
    exact h ⟨hR, Or.inr hL⟩

/-- `norm` changes only the tracking state of a tracked absent remote ref. -/
theorem TSlot.norm_tr {s : TSlot T} (h : ¬(s.R = absent ∧ s.tr = true)) : s.norm.tr = s.tr := by
  unfold TSlot.norm
  split
  · next h' =>
    cases htr : s.tr
    · rfl
    · exact absurd ⟨h'.1, htr⟩ h
  · rfl

/-- jj's `set_local_bookmark_target`: a `jj` command moving or deleting the bookmark. -/
def TSlot.set (l : T) (s : TSlot T) : TSlot T := TSlot.norm { s with L := l }

/-- jj's `track_remote_bookmark`: the remote ref's change since it was last tracked merged
into the bookmark, and the remote ref tracked. `jj bookmark set` runs it for a bookmark it
creates, on each remote whose `auto-track-bookmarks` covers it, the remote ref there or not. -/
def TSlot.track (s : TSlot T) : TSlot T :=
  TSlot.norm ⟨⟨merge s.L (if s.tr then s.R else absent) s.R, s.R, s.K⟩, true⟩

/-- Tracking a tracked remote ref changes no target. -/
theorem TSlot.track_toSlot {s : TSlot T} (h : s.tr = true) : s.track.toSlot = s.toSlot := by
  unfold TSlot.track
  rw [TSlot.norm_toSlot]
  simp only [h, ite_true, merge_unchanged_other]

/-- jj's import with tracking (`import_refs`): a remote ref that is new, absent before,
takes the default state `auto` (tracked for `git`, and for `origin` if
`remotes.origin.auto-track-bookmarks` covers it), and only a tracked one is merged into the
bookmark. -/
def TSlot.import (auto : Bool) (s : TSlot T) (g : T) : TSlot T :=
  if g = s.R then { s with K := g }
  else
    let tr := if s.R = absent ∧ s.tr = false then auto else s.tr
    TSlot.norm ⟨⟨if tr then merge s.L s.R g else s.L, g, g⟩, tr⟩

/-- Where the remote ref is tracked, or new and tracked by default, the targets are
`Slot.import`'s. -/
theorem TSlot.import_toSlot {s : TSlot T} {auto : Bool} (g : T)
    (h : s.tr = true ∨ (s.R = absent ∧ auto = true)) :
    (s.import auto g).toSlot = s.toSlot.import g := by
  unfold TSlot.import Slot.import
  by_cases hg : g = s.R
  · simp [hg]
  · have htr : (if s.R = absent ∧ s.tr = false then auto else s.tr) = true := by
      rcases h with h | ⟨_, h⟩ <;> split <;> simp_all
    simp only [hg, ite_false, TSlot.norm_toSlot, htr, ite_true]

theorem TSlot.import_self {s : TSlot T} {auto : Bool} {g : T} (hR : s.R = g) (hK : s.K = g) :
    s.import auto g = s := by
  unfold TSlot.import
  rw [ite_eq_left hR.symm]
  exact TSlot.ext' rfl rfl hK.symm rfl

/-- jj's export of a local bookmark with tracking: copying the bookmark to `x@git`
(`copy_exportable_local_bookmarks_to_remote_view`) tracks it. -/
def TSlot.exportLocal (s : TSlot T) (g : T) : TSlot T × T :=
  let e := Refs.exportLocal ⟨s.toSlot, g, false⟩
  (if e.v.R = s.R then { s with K := e.v.K } else TSlot.norm ⟨e.v, true⟩, e.G)

theorem TSlot.exportLocal_toSlot (s : TSlot T) (g : T) (m : Bool) :
    (s.exportLocal g).1.toSlot = (Refs.exportLocal ⟨s.toSlot, g, m⟩).v ∧
      (s.exportLocal g).2 = (Refs.exportLocal ⟨s.toSlot, g, m⟩).G := by
  have hv : (Refs.exportLocal ⟨s.toSlot, g, m⟩).v = (Refs.exportLocal ⟨s.toSlot, g, false⟩).v ∧
      (Refs.exportLocal ⟨s.toSlot, g, m⟩).G = (Refs.exportLocal ⟨s.toSlot, g, false⟩).G := by
    unfold Refs.exportLocal; split <;> (try split) <;> exact ⟨rfl, rfl⟩
  have hL : (Refs.exportLocal ⟨s.toSlot, g, false⟩).v.L = s.L := by
    unfold Refs.exportLocal; split <;> (try split) <;> rfl
  rw [hv.1, hv.2]
  refine ⟨?_, rfl⟩
  simp only [TSlot.exportLocal]
  split
  · next h => exact Slot.ext' hL.symm h.symm rfl
  · exact TSlot.norm_toSlot _

/-- musubi's realization of a local bookmark: the canonical bookmark, the record inherited
whole, tracking state and all. Unlike jj, it doesn't drop a tracked absent `x@git` when the
bookmark goes (`realize_not_WF`). -/
def TSlot.realizeLocal (c : T) (s : TSlot T) : TSlot T := { s with L := c }

/-- Two-valued `trivial_merge`, as `merge_remote_refs` merges tracking states. -/
def bmerge (a b c : Bool) : Bool := if a = b then c else a

/-- `v` once jj's merge has merged the bookmark: if `w` changed it, the merged bookmark, with
`v`'s remote ref dropped if absent and the bookmark is too. -/
def TSlot.mergeL (b v w : TSlot T) : TSlot T :=
  if b.L = w.L then v else TSlot.norm { v with L := RefAlg.merge v.L b.L w.L }

theorem TSlot.mergeL_fields (b v w : TSlot T) :
    (TSlot.mergeL b v w).L = RefAlg.merge v.L b.L w.L ∧ (TSlot.mergeL b v w).R = v.R ∧
      (TSlot.mergeL b v w).K = v.K := by
  unfold TSlot.mergeL
  split
  · next h => rw [← h, merge_unchanged_other]; exact ⟨rfl, rfl, rfl⟩
  · simp

theorem TSlot.mergeL_tr {b v w : TSlot T} (h : ¬(v.R = absent ∧ v.tr = true)) :
    (TSlot.mergeL b v w).tr = v.tr := by
  unfold TSlot.mergeL
  split
  · rfl
  · exact TSlot.norm_tr h

/-- jj's merge of one ref's views (`merge_view`): `v` merged with `w` against `b`. It merges
the bookmark first (`mergeL`), then `git_refs`, then, if `w` changed the remote ref, its
target and tracking state, each three-way, dropping the result if absent and not tracked by a
bookmark. A field `w` left alone stays as `v` has it. -/
def TSlot.merge (b v w : TSlot T) : TSlot T :=
  if b.R = w.R ∧ b.tr = w.tr then { TSlot.mergeL b v w with K := RefAlg.merge v.K b.K w.K }
  else
    TSlot.norm ⟨⟨RefAlg.merge v.L b.L w.L, RefAlg.merge (TSlot.mergeL b v w).R b.R w.R,
      RefAlg.merge v.K b.K w.K⟩, bmerge (TSlot.mergeL b v w).tr b.tr w.tr⟩

/-- The targets of jj's merge are each merged three-way, whatever the tracking states. -/
theorem TSlot.merge_toSlot (b v w : TSlot T) :
    (TSlot.merge b v w).toSlot = Slot.merge3 b.toSlot v.toSlot w.toSlot := by
  obtain ⟨hL, hR, _⟩ := TSlot.mergeL_fields b v w
  unfold TSlot.merge Slot.merge3
  split
  · next h =>
    refine Slot.ext' hL ?_ rfl
    show (TSlot.mergeL b v w).R = _
    rw [hR, ← h.1, merge_unchanged_other]
  · rw [TSlot.norm_toSlot]
    exact Slot.ext' rfl (by show RefAlg.merge _ _ _ = _; rw [hR]) rfl

omit [DecidableEq T] in
theorem TSlot.WF_K {s : TSlot T} (k : T) : ({ s with K := k } : TSlot T).WF ↔ s.WF := Iff.rfl

/-- jj's merge keeps its views' invariant. -/
theorem TSlot.merge_WF {b v w : TSlot T} (hv : v.WF) : (TSlot.merge b v w).WF := by
  unfold TSlot.merge
  split
  · rw [TSlot.WF_K]
    unfold TSlot.mergeL
    split
    · exact hv
    · exact TSlot.norm_WF _
  · exact TSlot.norm_WF _

/-- The per-machine fields of a local bookmark's view: `x@git`, its tracking state, and
`git_refs["refs/heads/x"]`. -/
def TSlot.pm (s : TSlot T) : T × Bool × T := (s.R, s.tr, s.K)

/-- A tracked remote ref with no target (`PerMachine::has_absent_remote_ref`). -/
def absentRef (p : T × Bool × T) : Bool := decide (p.1 = absent) && p.2.1

/-- musubi's shortcut for the per-machine fields of a merge (`merged_trivially`): the side
that changed them from the base, if only one did. As fixed for #56, it leaves a merge with a
tracked absent remote ref to jj. -/
def shortcut (b a c : T × Bool × T) : Option (T × Bool × T) :=
  if absentRef b || absentRef a || absentRef c then none
  else if c = b then some a else if a = b then some c else none

/-- The shortcut before #56's fix. -/
def shortcutUnguarded (b a c : T × Bool × T) : Option (T × Bool × T) :=
  if c = b then some a else if a = b then some c else none

/-- Where `w` kept the base's per-machine fields, jj's merge keeps `v`'s, unless `v` has a
tracked absent remote ref. -/
theorem TSlot.merge_pm_left {b v w : TSlot T} (hw : w.pm = b.pm)
    (hv : ¬(v.R = absent ∧ v.tr = true)) : (TSlot.merge b v w).pm = v.pm := by
  simp only [TSlot.pm, Prod.mk.injEq] at hw
  obtain ⟨hwR, hwtr, hwK⟩ := hw
  obtain ⟨_, hR, _⟩ := TSlot.mergeL_fields b v w
  unfold TSlot.merge
  rw [ite_eq_left ⟨hwR.symm, hwtr.symm⟩]
  show ((TSlot.mergeL b v w).R, (TSlot.mergeL b v w).tr, RefAlg.merge v.K b.K w.K) = _
  rw [hR, TSlot.mergeL_tr hv, hwK, merge_unchanged_other]
  rfl

/-- Where `v` kept the base's per-machine fields, jj's merge takes `w`'s, unless either has a
tracked absent remote ref. -/
theorem TSlot.merge_pm_right {b v w : TSlot T} (hv' : v.pm = b.pm)
    (hv : ¬(v.R = absent ∧ v.tr = true)) (hw : ¬(w.R = absent ∧ w.tr = true)) :
    (TSlot.merge b v w).pm = w.pm := by
  simp only [TSlot.pm, Prod.mk.injEq] at hv'
  obtain ⟨hvR, hvtr, hvK⟩ := hv'
  obtain ⟨_, hR, _⟩ := TSlot.mergeL_fields b v w
  have htr := TSlot.mergeL_tr (w := w) (b := b) hv
  unfold TSlot.merge
  split
  · next h =>
    show ((TSlot.mergeL b v w).R, (TSlot.mergeL b v w).tr, RefAlg.merge v.K b.K w.K) = _
    rw [hR, htr, hvR, hvtr, hvK, merge_unchanged_self, h.1, h.2]
    rfl
  · simp only [TSlot.pm, TSlot.norm_R, TSlot.norm_K]
    rw [hR, htr, hvR, hvtr, hvK, merge_unchanged_self, merge_unchanged_self]
    have : bmerge b.tr b.tr w.tr = w.tr := by simp [bmerge]
    have hn := TSlot.norm_tr (s := ⟨⟨RefAlg.merge v.L b.L w.L, w.R, w.K⟩, w.tr⟩) hw
    rw [this, hn]

/-- **The shortcut, as fixed, is jj's merge** wherever it applies. -/
theorem shortcut_agrees {b v w : TSlot T} {p : T × Bool × T}
    (h : shortcut b.pm v.pm w.pm = some p) : p = (TSlot.merge b v w).pm := by
  unfold shortcut at h
  split at h
  · exact nomatch h
  next hg =>
  simp only [absentRef, TSlot.pm, Bool.or_eq_true, Bool.and_eq_true,
    not_or] at hg
  obtain ⟨⟨_, hv⟩, hw⟩ := hg
  have hv : ¬(v.R = absent ∧ v.tr = true) := fun h => hv ⟨by simp [h.1], h.2⟩
  have hw : ¬(w.R = absent ∧ w.tr = true) := fun h => hw ⟨by simp [h.1], h.2⟩
  split at h
  · next hc =>
    cases h
    exact (TSlot.merge_pm_left hc hv).symm
  · split at h
    · next ha =>
      cases h
      exact (TSlot.merge_pm_right ha hv hw).symm
    · exact nomatch h

/-- musubi's realization of a canonical merge operation whose view has the bookmark at `c`:
the per-machine fields as `inherited_per_machine` merges them, the shortcut's where it
applies and otherwise jj's merge's. -/
def realizeMerge (c : T) (b v w : TSlot T) : TSlot T :=
  let p := (shortcut b.pm v.pm w.pm).getD (TSlot.merge b v w).pm
  ⟨⟨c, p.1, p.2.2⟩, p.2.1⟩

/-- **musubi realizes a merge as jj merges it**: the canonical bookmark is jj's merge of the
parents' (all their views share it), and the per-machine fields are jj's merge's. -/
theorem realizeMerge_eq {c : T} {b v w : TSlot T} (hc : c = RefAlg.merge v.L b.L w.L) :
    realizeMerge c b v w = TSlot.merge b v w := by
  have hp : (shortcut b.pm v.pm w.pm).getD (TSlot.merge b v w).pm = (TSlot.merge b v w).pm := by
    cases h : shortcut b.pm v.pm w.pm with
    | none => rfl
    | some p => exact shortcut_agrees h
  have hL := congrArg Slot.L (TSlot.merge_toSlot b v w)
  unfold realizeMerge
  simp only [hp]
  exact TSlot.ext' (hc.trans hL.symm) rfl rfl rfl

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
  absent := .absent
  resolved t := t != .conflict
  writable t := t != .conflict && t != .commit 0
  writable_resolved t h := by cases t <;> simp_all
  merge_unchanged_other a b := by simp
  merge_unchanged_self b c := by by_cases h : b = c <;> simp [h]
  merge_same_change a b := by by_cases h : b = a <;> simp [h]

example : (⟨Tgt.commit 2, .commit 2, .commit 2⟩ : Slot Tgt).import (.commit 1) =
    ⟨.commit 1, .commit 1, .commit 1⟩ := by
  simp [Slot.import, RefAlg.merge]

/-! ## What merges do that the theorems exclude -/

/-- **Two heads that both changed the record.** A `jj` command loads the op head `b`, with the
bookmark at `a` and `.git` in sync. Before it imports, musubi realizes another machine's move
of the bookmark to `c`, exports it, and publishes `w`. The command then imports `c` against
`b`, as a move made with git, sets the bookmark back to `a`, and exports that, publishing `v`.
jj's merge of the two heads puts the bookmark at `c`, as `w` moved it and `v` seems not to
have, and the record at `c`, though `.git` has `a`; so the next import moves the bookmark back
to `a`, with no `git` command having run. jj does the same with any two concurrent operations
that each import or export: musubi's realization of the merge is jj's (`realizeMerge_eq`). -/
theorem concurrent_records_revert :
    ∃ f : Fork Tgt, FReach f ∧ f.mv = false ∧ f.mw = false ∧
      (f.merged.v.import f.G).L ≠ f.merged.v.L := by
  let s : Machine Tgt := ⟨⟨.commit 1, .commit 1, .commit 1⟩, .commit 1, false⟩
  have h0 : FReach (Fork.of s) := FReach.fork (LReach.init (fun _ => ⟨rfl, rfl⟩))
  have h1 := FReach.step h0 (FStep.right (HStep.set _ (.commit 2)))
  have h2 := FReach.step h1 (FStep.right (HStep.jjExport _))
  have h3 := FReach.step h2 (FStep.left (HStep.jjImport _))
  have h4 := FReach.step h3 (FStep.left (HStep.set _ (.commit 1)))
  have h5 := FReach.step h4 (FStep.left (HStep.jjExport _))
  exact ⟨_, h5, by decide, by decide, by decide⟩

/-- **#56, first shape.** One head has a tracked `x@git` with no target, kept while `x`
exists; the other deleted `x` and left the record as the base had it. jj's merge deletes `x`
and so drops `x@git`; the shortcut before the fix kept it, tracked. -/
theorem shortcutUnguarded_keeps_absent :
    let b : TSlot Tgt := ⟨⟨.commit 1, .absent, .absent⟩, false⟩
    let v : TSlot Tgt := ⟨⟨.commit 1, .absent, .absent⟩, true⟩
    let w : TSlot Tgt := ⟨⟨.absent, .absent, .absent⟩, false⟩
    v.WF ∧ shortcutUnguarded b.pm v.pm w.pm = some v.pm ∧ (TSlot.merge b v w).pm ≠ v.pm ∧
      shortcut b.pm v.pm w.pm = none := by
  intro b v w
  exact ⟨fun _ _ h => Tgt.noConfusion h, by decide⟩

/-- **#56, second shape.** The base and one head have a tracked `x@git` with no target; the
other has no `x` and `x@git` at `2`, tracked, as after importing git's creation of
`refs/heads/x` there and then deleting `x`, the export of that failing. jj's merge
drops the absent `x@git` with the bookmark, then merges the other head's as from nothing,
leaving it untracked; the shortcut before the fix took it tracked. Untracked, a later move
of `refs/heads/x` by git no longer moves `x`, until an export tracks `x@git` again. -/
theorem shortcutUnguarded_untracks :
    let b : TSlot Tgt := ⟨⟨.commit 1, .absent, .absent⟩, true⟩
    let w : TSlot Tgt := ⟨⟨.absent, .commit 2, .commit 2⟩, true⟩
    shortcutUnguarded b.pm b.pm w.pm = some w.pm ∧ (TSlot.merge b b w).pm ≠ w.pm ∧
      (TSlot.merge b b w).tr = false ∧ ((TSlot.merge b b w).import true (.commit 3)).L = .absent ∧
      shortcut b.pm b.pm w.pm = none := by
  decide

/-- **musubi's realization isn't always a view jj would make.** It inherits the record whole,
so where the canonical operation deletes a bookmark whose `x@git` is tracked and absent, it
keeps that `x@git`, which jj drops (`TSlot.set`). Only the tracking state of a remote ref with
no target differs; the targets are the same. -/
theorem realize_not_WF :
    let s : TSlot Tgt := ⟨⟨.commit 1, .absent, .absent⟩, true⟩
    s.WF ∧ ¬(s.realizeLocal .absent).WF ∧ (s.set .absent).WF ∧
      (s.realizeLocal .absent).toSlot = (s.set .absent).toSlot := by
  intro s
  exact ⟨fun _ _ h => Tgt.noConfusion h, fun h => h rfl rfl rfl, TSlot.norm_WF _, rfl⟩

/-- **The first of several bases.** Where the heads have several closest common ancestors,
jj merges against those ancestors merged (`merge_operations`). musubi merged the per-machine
fields against the first of them, saying the export would correct them, and could get a
record that matches neither `.git` nor jj's merge. Here this machine's own operation `b2`
moved the bookmark to `2` beside another machine's `b1`; two machines each merged them; this
machine then moved it to `3` (`v`) while another moved it to `4` (`w`, whose export failed).
jj's merge leaves a conflict of `3` and `4` and the record at `3`, as `.git` has it. Against
`b1`, the record is a conflict too, so the export can't correct it, and the next import
merges that conflict into the bookmark, with no `git` command having run: here, where all
conflicts are one, it resolves the bookmark to `3`, losing `4`; in jj's algebra it makes a
larger conflict. -/
theorem firstBase_reverts :
    let b0 : Slot Tgt := ⟨.commit 1, .commit 1, .commit 1⟩
    let b1 : Slot Tgt := ⟨.commit 1, .commit 1, .commit 1⟩
    let b2 : Slot Tgt := ⟨.commit 2, .commit 2, .commit 2⟩
    let v : Slot Tgt := ⟨.commit 3, .commit 3, .commit 3⟩
    let w : Slot Tgt := ⟨.commit 4, .commit 2, .commit 2⟩
    let jj := Slot.merge3 (Slot.merge3 b0 b1 b2) v w
    let first : Slot Tgt := { Slot.merge3 b1 v w with L := jj.L }
    let ejj := exportLocal ⟨jj, .commit 3, false⟩
    let efirst := exportLocal ⟨first, .commit 3, false⟩
    (ejj.v.import ejj.G).L = ejj.v.L ∧ (efirst.v.import efirst.G).L ≠ efirst.v.L := by
  decide

end Musubi.Refs

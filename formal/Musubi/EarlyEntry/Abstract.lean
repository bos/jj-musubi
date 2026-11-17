/-
The invariant that bursts of node steps need of a state, wherever the hub's head is, and the
NodeSettle context a burst runs in. The convergence proof uses this file. Ids are raw hub-space
ones throughout, as in NodeSettle.
-/
import Musubi.NodeSettle

namespace Musubi.EarlyEntry

open Musubi Musubi.NodeSettle

/-! ## Bursts with the known pair frozen -/

/-- What NodeSettle's steps need of a state, wherever the hub's head is. -/
structure LInv (σ : NS) : Prop where
  /-- Parents come before their children. -/
  parLt : ParLt σ.par
  /-- The known head is below the next fresh id. -/
  knownLt : σ.known.head < σ.next
  /-- There is at least one op head. -/
  headsNe : σ.heads ≠ []
  /-- Every op head is below the next fresh id. -/
  headsLt : ∀ y ∈ σ.heads, y < σ.next
  /-- The known head has at least one node-space image. -/
  imgNe : σ.img ≠ []
  /-- Every image is below the next fresh id. -/
  imgLt : ∀ i ∈ σ.img, i < σ.next

/-- NodeSettle's context for a burst with known pair `K`: the hub's records `R`, and a pair that
is not `K`, so that none of NodeSettle's replies, which teach the context's pair, is part of a
burst. -/
def bctx (R : Nat) (drops : Nat → Nat → Prop) (K : Known) : Ctx :=
  ⟨K.1 + 1, K.2, R, drops⟩

theorem LInv.sinv {σ : NS} (I : LInv σ) (R : Nat) (drops : Nat → Nat → Prop) :
    NodeSettle.SInv (bctx R drops σ.known) σ where
  parLt := I.parLt
  knownLt := I.knownLt
  hLt := I.knownLt
  headsNe := I.headsNe
  headsLt := I.headsLt
  imgNe := I.imgNe
  imgLt := I.imgLt
  recs := by
    intro h
    have h1 := congrArg Known.seq h
    simp only [bctx] at h1
    omega

theorem linv_of_sinv {c : Ctx} {σ : NS} (I : NodeSettle.SInv c σ) : LInv σ :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

/-! ## Steps that keep the invariant -/

theorem LInv.act {σ : NS} (I : LInv σ) (b : Bool) : LInv { σ with act := b } :=
  ⟨I.parLt, I.knownLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt⟩

theorem LInv.ext {σ σ' : NS} (I : LInv σ) (E : Ext σ σ') : LInv σ' := by
  refine ⟨E.parLt, ?_, E.headsNe, E.headsLt, ?_, ?_⟩
  · rw [E.known]; exact Nat.lt_of_lt_of_le I.knownLt E.grows
  · rw [E.img]; exact I.imgNe
  · rw [E.img]; exact fun i hi => Nat.lt_of_lt_of_le (I.imgLt i hi) E.grows

end Musubi.EarlyEntry

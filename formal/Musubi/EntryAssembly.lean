/-
Ordered-record identity and custody of pending names give an eligible node an empty pending
list (`eligible_pending_empty`). The packet algebra keeps a noneligible node's answer from moving
the hub once the records are fixed (`raw_noneligible_answer_frame`).

The convergence proof uses `PendingOriginals` and `eligible_pending_empty` from this file. It does
not use `raw_pending_empty_of_fixed_records` or `raw_noneligible_answer_frame`, which derive the
native packet and record laws the assembly takes as premises.
-/
import Musubi.EarlyEntry
import Musubi.PacketAcceptance

namespace Musubi.Recovery

open Musubi NodeSettle EarlyEntry

/-- Raw pending names can differ while describing the same original. Custody provides their
immutable identities, and record matching removes an original already applied. -/
structure PendingOriginals (s : Exec.SEState) (n : Nat) (σ : NS) (origin : Nat → Nat) : Prop where
  /-- Custody: each pending name's original is among the node's drops. -/
  owned : ∀ p ∈ σ.pending, origin p ∈ s.nodeDF n
  /-- Record matching: no pending name's original is in the applied records. -/
  unpublished : ∀ p ∈ σ.pending, origin p ∉ Exec.flat (s.appliedF n)

/-- Native packet/record algebra, independent of an original-history executable step.
Acceptance appends a record exactly when contraction has effective raw drops (`heffect`). Under
current naming, each pending raw name is effective or its original is already recorded
(`hcover`). Unchanged ordered records (`hfixed`) force the effective list empty; matching applied
records and custody (`hmatch`, `hunpublished`) exclude the second alternative too. The naming
coverage is an adapter law, not a consequence of raw `is_superseded` alone: a superseded raw name
can also name a rewritten surviving original. -/
theorem raw_pending_empty_of_fixed_records (before after applied : List Exec.Rec)
    (pending effective : List Nat) (origin : Nat → Nat)
    (heffect : after = if effective = [] then before else before ++ [effective.map origin])
    (hfixed : after = before) (hmatch : applied = before)
    (hcover : ∀ p ∈ pending, p ∈ effective ∨ origin p ∈ Exec.flat before)
    (hunpublished : ∀ p ∈ pending, origin p ∉ Exec.flat applied) : pending = [] := by
  have hempty : effective = [] := by
    apply Classical.byContradiction
    intro hne
    rw [ite_eq_right hne, hfixed] at heffect
    have hl := congrArg List.length heffect
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    omega
  apply List.eq_nil_iff_forall_not_mem.2
  intro p hp
  rcases hcover p hp with he | hr
  · simp [hempty] at he
  · exact hunpublished p hp (hmatch ▸ hr)

/-- A fresh noneligible packet cannot move the hub after the record cut. Wrong offered records
are refused first; only an actual acceptance needs current applied records. For that decision,
the native append effect and current naming coverage force the packet's raw pending list empty.
Complete custody then makes its original drop set the hub's, contradicting noneligibility. The
record effect and coverage are about this packet at this actual decision, not another executable
state with equal head fields. -/
theorem raw_noneligible_answer_frame (h : RawPublish.Hub) (p : RawPublish.Push)
    (c : RawPublish.Checks) (before after applied : List Exec.Rec)
    (knownDrops effective : List Nat) (origin : Nat → Nat)
    (hfixed : after = before)
    (heffect : RawPublish.answer h p c = .accepted →
      after = if effective = [] then before else before ++ [effective.map origin])
    (hmatch : c.recordsMatch = true → applied = before)
    (hcover : RawPublish.answer h p c = .accepted →
      ∀ x ∈ p.dropped, x ∈ effective ∨ origin x ∈ Exec.flat before)
    (hunpublished : ∀ x ∈ p.dropped, origin x ∉ Exec.flat applied)
    (hcomplete : ∀ x, x ∈ knownDrops ↔ x ∈ Exec.flat applied ∨
      ∃ q ∈ p.dropped, origin q = x)
    (hnoneligible : ¬ ∀ x, x ∈ knownDrops ↔ x ∈ Exec.flat before) :
    RawPublish.after h p c = h := by
  have hno : RawPublish.answer h p c ≠ .accepted := by
    intro ha
    have hr : c.recordsMatch = true := by
      cases hm : c.recordsMatch
      · simp [RawPublish.answer, hm] at ha
      · rfl
    have hap := hmatch hr
    have hempty := raw_pending_empty_of_fixed_records before after applied p.dropped effective
      origin (heffect ha) hfixed hap (hcover ha) hunpublished
    apply hnoneligible
    intro x
    rw [hcomplete x, hempty, hap]
    simp
  simp [RawPublish.after, hno]

/-- Wire-record identities are decoded into original drop sets (`decode`), since different raw
records may describe the same originals. Current applied records and custody leave no pending
raw names. -/
theorem eligible_pending_empty {s : Exec.SEState} {n : Nat} {σ : NS}
    (decode : Nat → List Exec.Rec) (R : Nat) (origin : Nat → Nat)
    (hsource : s.appliedF n = decode σ.ap) (hcurrent : σ.ap = R)
    (hhub : s.recs = decode R) (hp : PendingOriginals s n σ origin)
    (hd : ∀ x, x ∈ s.nodeDF n ↔ x ∈ s.hubDL) : σ.pending = [] := by
  have heq : s.appliedF n = s.recs :=
    hsource.trans ((congrArg decode hcurrent).trans hhub.symm)
  apply List.eq_nil_iff_forall_not_mem.2
  intro p hmem
  apply hp.unpublished p hmem
  rw [heq]
  exact (hd (origin p)).1 (hp.owned p hmem)

end Musubi.Recovery

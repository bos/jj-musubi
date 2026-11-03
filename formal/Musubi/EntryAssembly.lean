/-
Common eligible-node entry before hub stabilization. EarlyEntry proves local completion
under individual-call fairness; this module joins the finitely many cuts. Ordered-record
identity and the fixed drop-set projection then disable both core publication writes.
Neither maintenance finiteness nor hub stabilization is assumed to prove that exclusion.
-/
import Musubi.EarlyEntry
import Musubi.RecoveryBridge
import Musubi.HistoryWindow

namespace Musubi.Recovery

open Musubi NodeSettle EarlyEntry

structure EarlyTrace (R w : Nat) (drops : Nat → Nat → Prop)
    (run : Nat → NS) (lab : Nat → ELab) (k0 : Nat) : Prop where
  events : ∀ i, k0 ≤ i → EEv R w drops (lab i) (run i) (run (i + 1))
  wellFormed : LInv (run k0)
  maintenance : ∃ kb, ∀ i, kb ≤ i → lab i ≠ .maint
  eligible : ∀ i, k0 ≤ i → ¬ ∃ y ∈ (run i).heads, drops R y
  start : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start
  core : ∀ i, k0 ≤ i → (run i).act = true → ∃ j, i ≤ j ∧
    (lab j = .step ∨ lab j = .idle ∨ lab j = .poll ∨ lab j = .push ∨ lab j = .maint)

theorem eligible_nodes_enter (N R w k0 : Nat) (E : Nat → Prop)
    (nodes : Nat → Nat → NS) (labels : Nat → Nat → ELab)
    (drops : Nat → Nat → Nat → Prop) (hN : ∀ n, E n → n < N)
    (ht : ∀ n, E n → EarlyTrace R w (drops n) (nodes n) (labels n) k0) :
    ∃ k, k0 ≤ k ∧ ∀ i, k ≤ i → ∀ n, E n → Entry R w (nodes n i) := by
  have each : ∀ n, n < N → ∃ k, ∀ i, k ≤ i → (E n → Entry R w (nodes n i)) := by
    intro n _
    by_cases he : E n
    · have t := ht n he
      obtain ⟨k, _, hk⟩ := early_entry R w (drops n) (nodes n) (labels n) k0
        t.events t.wellFormed t.maintenance t.eligible t.start t.core
      exact ⟨k, fun i hi _ => hk i hi⟩
    · exact ⟨0, fun _ _ hn => False.elim (he hn)⟩
  obtain ⟨k, hk⟩ := finite_common_cut N _ each
  exact ⟨max k0 k, by omega, fun i hi n hn => hk i (by omega) n (hN n hn) hn⟩

/-- Every eligible node enters, raw, and stays entered, from one finite cut on: each enters
(`EarlyEntry.Control.raw_entry_reached` on its run from the common cut `k0`), and entry lasts
(`EarlyEntry.Control.raw_entry_persists`): after ordinary failures and their reopens cease, an
`Incomplete` answer is excluded by the conditional closure law for an entered node's push.
Nothing is read as NodeSettle's state before the cut this gives; there each eligible node's
is formed. -/
theorem eligible_nodes_raw_enter {ρ : Type} (N : Nat) (E : Nat → Prop) (R : ρ) (w k0 : Nat)
    (hN : ∀ n, E n → n < N) (state : Nat → Nat → EarlyEntry.Control.RawNode ρ)
    (reopen incomplete : Nat → Nat → Prop) (expectedIsHead closed : Nat → Nat → Bool)
    (henter : ∀ n, E n → ∃ j, k0 ≤ j ∧ EarlyEntry.Control.RawEntry R w (state n j))
    (hreopen : ∀ n i, E n → k0 ≤ i → reopen n i → incomplete n i)
    (hinc : ∀ n i, E n → k0 ≤ i → incomplete n i →
      expectedIsHead n i = true ∧ closed n i = false)
    (hclosure : ∀ n i, E n → k0 ≤ i → EarlyEntry.Control.RawEntry R w (state n i) →
      expectedIsHead n i = true → closed n i = true)
    (hkeep : ∀ n i, E n → k0 ≤ i → EarlyEntry.Control.RawEntry R w (state n i) →
      ¬ reopen n i → EarlyEntry.Control.RawEntry R w (state n (i + 1))) :
    ∃ k, k0 ≤ k ∧ ∀ i, k ≤ i → ∀ n, E n →
      EarlyEntry.Control.RawEntry R w (state n i) := by
  have each : ∀ n, n < N → ∃ k, ∀ i, k ≤ i →
      (E n → EarlyEntry.Control.RawEntry R w (state n i)) := by
    intro n _
    by_cases he : E n
    · obtain ⟨j, hj, hej⟩ := henter n he
      exact ⟨j, fun i hi _ => EarlyEntry.Control.raw_entry_persists R w (state n) (reopen n)
        (incomplete n) (expectedIsHead n) (closed n) j hej
        (fun i hi' => hreopen n i he (by omega)) (fun i hi' => hinc n i he (by omega))
        (fun i hi' => hclosure n i he (by omega)) (fun i hi' => hkeep n i he (by omega)) i hi⟩
    · exact ⟨0, fun _ _ hn => absurd hn he⟩
  obtain ⟨k, hk⟩ := finite_common_cut N _ each
  exact ⟨max k0 k, by omega, fun i hi n hn => hk i (by omega) n (hN n hn) hn⟩

/-- Raw pending names can differ while describing the same original. Custody provides their
immutable identities, and record matching removes an original already applied. -/
structure PendingOriginals (s : Exec.SEState) (n : Nat) (σ : NS) (origin : Nat → Nat) : Prop where
  owned : ∀ p ∈ σ.pending, origin p ∈ s.nodeDF n
  unpublished : ∀ p ∈ σ.pending, origin p ∉ Exec.flat (s.appliedF n)

/-- Native packet/record algebra, independent of an original-history executable step.
Acceptance appends a record exactly when contraction has effective raw drops. Under current
naming, each pending raw name is effective or its original is already recorded. Unchanged
ordered records force the effective list empty; matching applied records and custody exclude
the second alternative too. The naming coverage is an adapter law, not a consequence of raw
`is_superseded` alone: a superseded raw name can also name a rewritten surviving original. -/
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

/-- A fresh noneligible packet cannot move the hub after the record cut. Wrong offered
records refuse first; only an actual acceptance needs current applied records. For that same
decision, the native append effect and current naming coverage force its raw pending list
empty. Complete custody would then make its original drop set the hub's, contrary to its
noneligibility. This uses neither an original-history execution nor a noneligible embedding.
The record effect and coverage concern this packet at this actual decision, not a different
executable state with coincidentally equal head fields. -/
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

/-- Decode opaque wire-record identities into original drop sets, rather than trying to
encode those sets injectively as raw record identities: different raw records may describe
the same originals. Current applied records and custody leave no pending RAW names. -/
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

/-- A packet the hub accepts without changing its records came from a sender with no pending
raw drops: coupled to the state it was sent from, its sender dropped what the hub's records
drop (`Exec.packet_sender_aligned`), the records being the same from its sending to its
acceptance; and with its applied records the current ones and custody of its pending names,
that leaves it none pending (`eligible_pending_empty`). -/
theorem accepted_sender_pending_empty {N : Nat} {source s t : Exec.SEState}
    {p : Exec.PushPacket} {σ : NS} (decode : Nat → List Exec.Rec) (R : Nat)
    (origin : Nat → Nat) (hsource : p.sourceMatchesB N source = true)
    (haccept : Exec.cexecAction N s p.accept = .ok t) (hfix : t.recs = s.recs)
    (hsame : source.recs = s.recs) (happlied : source.appliedF p.node = decode σ.ap)
    (hcurrent : σ.ap = R) (hhub : source.recs = decode R)
    (hcustody : PendingOriginals source p.node σ origin) : σ.pending = [] := by
  apply eligible_pending_empty decode R origin happlied hcurrent hhub hcustody
  intro x
  have h := Exec.packet_sender_aligned hsource haccept hfix x
  simpa only [Exec.SEState.hubDL, hsame] using h

/-- So once the records stay as they are, the hub accepts no packet a node with pending raw
drops sends: every answer to one leaves the hub as it was, and a system of the eligible
nodes can leave it out. No hub stability is needed. -/
theorem pending_push_not_accepted_fixed {N : Nat} {source s t : Exec.SEState}
    {p : Exec.PushPacket} {σ : NS} (decode : Nat → List Exec.Rec) (R : Nat)
    (origin : Nat → Nat) (hsource : p.sourceMatchesB N source = true)
    (hsame : source.recs = s.recs) (happlied : source.appliedF p.node = decode σ.ap)
    (hcurrent : σ.ap = R) (hhub : source.recs = decode R)
    (hcustody : PendingOriginals source p.node σ origin) (hpend : σ.pending ≠ []) :
    ¬ (Exec.cexecAction N s p.accept = .ok t ∧ t.recs = s.recs) := fun ⟨haccept, hfix⟩ =>
  hpend (accepted_sender_pending_empty decode R origin hsource haccept hfix hsame happlied
    hcurrent hhub hcustody)

theorem eligible_publication_silent {σ : NS} (hp : σ.pending = []) :
    (pubOf σ).write.2 = (false, false) := by
  have he := Retry.publication_empty_pending (pubOf σ) hp
  rw [he]

/-- The converse uses custody's full decomposition: a node owns exactly its applied drops
and the originals still pending publication. It needs no injective encoding of raw names. -/
theorem pending_empty_aligned {s : Exec.SEState} {n : Nat} {σ : NS}
    (decode : Nat → List Exec.Rec) (R : Nat) (origin : Nat → Nat)
    (hsource : s.appliedF n = decode σ.ap) (hcurrent : σ.ap = R)
    (hhub : s.recs = decode R)
    (hdecomp : ∀ x, x ∈ s.nodeDF n ↔
      x ∈ Exec.flat (s.appliedF n) ∨ ∃ p ∈ σ.pending, origin p = x)
    (hp : σ.pending = []) : ∀ x, x ∈ s.nodeDF n ↔ x ∈ s.hubDL := by
  have heq : s.appliedF n = s.recs :=
    hsource.trans ((congrArg decode hcurrent).trans hhub.symm)
  intro x
  simpa only [hp, List.not_mem_nil, false_and, exists_false, or_false, heq,
    Exec.SEState.hubDL] using hdecomp x

theorem aligned_iff_pending_empty {s : Exec.SEState} {n : Nat} {σ : NS}
    (decode : Nat → List Exec.Rec) (R : Nat) (origin : Nat → Nat)
    (hsource : s.appliedF n = decode σ.ap) (hcurrent : σ.ap = R)
    (hhub : s.recs = decode R) (hp : PendingOriginals s n σ origin)
    (hdecomp : ∀ x, x ∈ s.nodeDF n ↔
      x ∈ Exec.flat (s.appliedF n) ∨ ∃ p ∈ σ.pending, origin p = x) :
    (∀ x, x ∈ s.nodeDF n ↔ x ∈ s.hubDL) ↔ σ.pending = [] :=
  ⟨eligible_pending_empty decode R origin hsource hcurrent hhub hp,
    pending_empty_aligned decode R origin hsource hcurrent hhub hdecomp⟩

theorem eligible_write_unchanged {σ σ1 : NS} {new : Nat}
    (hp : σ.pending = []) (hw : WriteRes σ σ1 new) :
    σ1 = σ ∧ σ.heads = [new] := by
  have silent := eligible_publication_silent hp
  obtain ⟨y, hy, hw⟩ := hw
  rcases hw with ⟨hem, _⟩ | ⟨_, he, hn⟩
  · rw [show (pubOf σ).write.2.1 = false from congrArg Prod.fst silent,
      show (pubOf σ).write.2.2 = false from congrArg Prod.snd silent] at hem
    contradiction
  · exact ⟨he, hn ▸ hy⟩

end Musubi.Recovery

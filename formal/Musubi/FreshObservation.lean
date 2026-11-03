/-
Entry's record equality and sequence lower bound do not by themselves prove truthful
knowledge: an old pre-rollback pair can accidentally satisfy both. Independently force one
actual fresh own-response observation. Before it, notifications cannot interrupt a running round,
the known pair is frozen and the local-burst rank rules out endless work. No whole round's
completion and no head stabilization are assumed.
-/
import Musubi.EarlyEntry
import Musubi.SerialReply

namespace Musubi.Recovery

open Musubi NodeSettle EarlyEntry

def ObservesHead (l : ELab) : Prop :=
  l = .start ∨ l = .poll ∨ l = .push

theorem fresh_observation_from (R w : Nat) (drops : Nat → Nat → Prop)
    (run : Nat → NS) (lab : Nat → ELab) (k0 : Nat)
    (hev : ∀ i, k0 ≤ i → EEv R w drops (lab i) (run i) (run (i + 1)))
    (h0 : LInv (run k0))
    (nomaint : ∀ i, k0 ≤ i → lab i ≠ .maint)
    (hstart : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k0 ≤ i → (run i).act = true → ∃ j, i ≤ j ∧
      (lab j = .step ∨ lab j = .idle ∨ lab j = .poll ∨ lab j = .push ∨ lab j = .maint)) :
    ∃ i, k0 ≤ i ∧ ObservesHead (lab i) := by
  apply Classical.byContradiction
  intro hno
  have noobs : ∀ i, k0 ≤ i → ¬ ObservesHead (lab i) := fun i hi h => hno ⟨i, hi, h⟩
  have actTrue : ∀ i, k0 ≤ i → (run i).act = true := by
    intro i hi
    cases ha : (run i).act with
    | true => rfl
    | false =>
      obtain ⟨j, hj, hl⟩ := hstart i hi ha
      exact (noobs j (by omega) (.inl hl)).elim
  have only : ∀ i, k0 ≤ i → lab i = .step ∨ lab i = .frame := by
    intro i hi
    have h := hev i hi
    cases hl : lab i with
    | step => exact .inl rfl
    | frame => exact .inr rfl
    | start => exact (noobs i hi (.inl hl)).elim
    | poll => exact (noobs i hi (.inr (.inl hl))).elim
    | push => exact (noobs i hi (.inr (.inr hl))).elim
    | notify =>
      rw [hl] at h
      have ha := notify_act h
      rw [actTrue i hi] at ha
      contradiction
    | maint => exact absurd hl (nomaint i hi)
    | idle =>
      rw [hl] at h
      have ha := idle_act' h
      rw [actTrue (i + 1) (by omega)] at ha
      contradiction
  have known : ∀ d, (run (k0 + d)).known = (run k0).known := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      have h := hev (k0 + d) (by omega)
      show (run (k0 + d + 1)).known = (run k0).known
      rcases only (k0 + d) (by omega) with hl | hl <;> rw [hl] at h
      · rw [(step_facts h).2, ih]
      · rw [frame_eq h, ih]
  have hinv : ∀ d, LInv (run (k0 + d)) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih => exact linv_ev ih (hev _ (by omega))
  have hSI : ∀ d, NodeSettle.SInv (bctx R drops (run k0).known) (run (k0 + d)) := by
    intro d
    have hi := (hinv d).sinv R drops
    rwa [known d] at hi
  have mono : ∀ d,
      LexLe (rank (bctx R drops (run k0).known) (run (k0 + d + 1)))
        (rank (bctx R drops (run k0).known) (run (k0 + d))) ∧
      (lab (k0 + d) = .step →
        LexLt (rank (bctx R drops (run k0).known) (run (k0 + d + 1)))
          (rank (bctx R drops (run k0).known) (run (k0 + d)))) := by
    intro d
    have h := hev (k0 + d) (by omega)
    rcases only (k0 + d) (by omega) with hl | hl <;> rw [hl] at h
    · have hb := (step_facts h).1
      rw [known d] at hb
      have hlt := rank_busy (hSI d) hb
      exact ⟨hlt.le, fun _ => hlt⟩
    · rw [frame_eq h]
      exact ⟨.inr rfl, fun e => by rw [hl] at e; contradiction⟩
  obtain ⟨cut, hc⟩ := lex_stabilizes 11
    (fun d => rank (bctx R drops (run k0).known) (run (k0 + d)))
    (fun _ => rank_length _ _) (fun d => (mono d).1)
  obtain ⟨j, hj, hl⟩ := hcore (k0 + cut) (by omega) (actTrue _ (by omega))
  have hstep : lab j = .step := by
    rcases only j (by omega) with h | h
    · exact h
    · rw [h] at hl
      rcases hl with e | e | e | e | e <;> contradiction
  have lt := (mono (j - k0)).2 (by rw [show k0 + (j - k0) = j by omega]; exact hstep)
  have e1 := hc (j - k0) (by omega)
  have e2 := hc (j - k0 + 1) (by omega)
  rw [show k0 + (j - k0) = j by omega] at e1
  rw [show k0 + (j - k0 + 1) = j + 1 by omega] at e2
  rw [show k0 + (j - k0) = j by omega] at lt
  rw [e1, e2] at lt
  exact lexLt_irrefl _ lt

theorem fresh_observation_eventually (R w : Nat) (drops : Nat → Nat → Prop)
    (run : Nat → NS) (lab : Nat → ELab) (k0 : Nat)
    (hev : ∀ i, k0 ≤ i → EEv R w drops (lab i) (run i) (run (i + 1)))
    (h0 : LInv (run k0)) (hmaint : ∃ kb, ∀ i, kb ≤ i → lab i ≠ .maint)
    (hstart : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k0 ≤ i → (run i).act = true → ∃ j, i ≤ j ∧
      (lab j = .step ∨ lab j = .idle ∨ lab j = .poll ∨ lab j = .push ∨ lab j = .maint)) :
    ∃ i, k0 ≤ i ∧ ObservesHead (lab i) := by
  obtain ⟨kb, hkb⟩ := hmaint
  have hi : ∀ d, LInv (run (k0 + d)) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih => exact linv_ev ih (hev _ (by omega))
  obtain ⟨i, hit, ho⟩ := fresh_observation_from R w drops run lab (k0 + kb)
    (fun i hi => hev i (by omega)) (hi kb) (fun i hi => hkb i (by omega))
    (fun i hi ha => hstart i (by omega) ha) (fun i hi ha => hcore i (by omega) ha)
  exact ⟨i, by omega, ho⟩

/-- The first honest own head repairs arbitrary initial knowledge. A notification alone
would not: filtered learning can ignore a current notification below an obsolete sequence. -/
theorem own_observation_truthful (root : Nat) (before reply : Retry.Serial.Head)
    (hist : Nat → Nat) (seq w : Nat)
    (hroot : reply.1 = 0 → reply.2 = root)
    (hw : w ≤ reply.1) (hs : reply.1 ≤ seq) (hh : hist reply.1 = reply.2) :
    let known := Retry.Serial.handleHead root true false before reply
    w ≤ known.1 ∧ known.1 ≤ seq ∧ hist known.1 = known.2 := by
  rw [Retry.Serial.own_reply_learns root before reply hroot]
  exact ⟨hw, hs, hh⟩

/-- After entry, a truthful notification either learns another truthful window pair or
leaves the existing truthful pair alone. Infinitely many fresh notices do not reset it. -/
theorem notification_preserves_truth (root : Nat) (before reply : Retry.Serial.Head)
    (hist : Nat → Nat) (seq w : Nat)
    (hb : w ≤ before.1 ∧ before.1 ≤ seq ∧ hist before.1 = before.2)
    (hr : w ≤ reply.1 ∧ reply.1 ≤ seq ∧ hist reply.1 = reply.2) :
    let known := Retry.Serial.handleHead root false true before reply
    w ≤ known.1 ∧ known.1 ≤ seq ∧ hist known.1 = known.2 := by
  simp only [Retry.Serial.handleHead, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Retry.Serial.filteredLearn]
  split
  · exact hr
  · exact hb

end Musubi.Recovery

/-
Pruned-prefix custody for the extended recovery model, and reconstruction of a fresh reply's
ordered records. A dropped-set cut alone does not imply that a node can read a pruned prefix;
that fact must survive the added prepared-adoption and survivor-acceptance transitions too.
-/
import Musubi.NodeReconcile
import Musubi.SerialReply

namespace Musubi.Exec

theorem seheld_adoptR {N : Nat} {s : SEState} (h : SEHeld N s) (n : Nat) (R : List Rec) :
    SEHeld N (s.adoptR n R) := by
  refine seheld_mono h rfl rfl rfl rfl
    (fun m L hL => heldF_adoptR_mono s n R m hL) (fun m => ?_)
  rw [appliedF_adoptR, heldF_adoptR]
  by_cases hm : m = n
  · subst m; simp only [ite_true]; exact List.mem_cons_self
  · simp only [hm, ite_false]; exact h.applied m

theorem seheld_imageAccept {N : Nat} {s : SEState} (hok : SEOK s)
    (h : SEHeld N s) (n : Nat) (S O : List Nat) (d : Nat) (D : List Nat) :
    SEHeld N (s.imageAccept n S O d D) := by
  have hprefix := takeRecs_take s D hok.pruned
  have now : ∀ m, m < N → s.heldPrefix m (s.takeRecs D) s.pruned = true := by
    intro m hm
    unfold SEState.heldPrefix
    rw [hprefix]
    exact h.now m hm
  refine ⟨h.applied, now, fun entry he m hm => ?_, h.msgs⟩
  rcases List.mem_cons.1 he with rfl | he
  · exact now m hm
  · exact h.hist entry he m hm

theorem cexec_held {N : Nat} {s t : SEState} {a : SAction}
    (hok : SEOK s) (hH : SEHeld N s) (h : cexecStep N s a = .ok t) : SEHeld N t := by
  unfold cexecStep at h
  cases hs : sexecStep N s a with
  | ok result =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h; exact sexec_held hok hH hs
    · contradiction
  | error error =>
    rw [hs] at h
    cases a with
    | base action =>
      cases action <;> simp only at h
      all_goals first | contradiction | skip
      split at h
      · cases h; exact ⟨hH.applied, hH.now, hH.hist, hH.msgs⟩
      · contradiction
    | hubSupAccept n S O e d A D =>
      simp only at h
      split at h
      · cases h; exact seheld_imageAccept hok hH n S O d D
      · contradiction
    | _ => contradiction

theorem cexecAction_held {N : Nat} {s t : SEState} {a : CAction}
    (hok : SEOK s) (hH : SEHeld N s) (h : cexecAction N s a = .ok t) : SEHeld N t := by
  cases a with
  | old action => exact cexec_held hok hH h
  | advancePrepared n R =>
    simp only [cexecAction] at h
    split at h
    · cases h
      exact seheld_adoptR
        (show SEHeld N (s.preparedFrontier n R) from ⟨hH.applied, hH.now, hH.hist, hH.msgs⟩) n R
    · contradiction
  | reject n S O e d A D =>
    simp only [cexecAction] at h
    split at h
    · exact sexec_held hok hH h
    · contradiction

theorem cexec_reachable_held {N : Nat} {s : SEState} (h : CExecReachable N s) : SEHeld N s := by
  induction h with
  | init => exact seheld_init N
  | step reach _ hs ih => exact cexecAction_held (cexec_reachable_ok reach) ih hs

theorem record_seteq_self (xs : List Nat) : seteq xs xs = true := by
  simp [seteq, List.all_eq_true]

theorem recEq_append_same {A B : List Rec} (h : recEq A B = true) (C : List Rec) :
    recEq (A ++ C) (B ++ C) = true := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => simpa using recEq_self C
    | cons => simp [recEq] at h
  | cons a A ih =>
    cases B with
    | nil => simp [recEq] at h
    | cons b B =>
      simp only [recEq, Bool.and_eq_true] at h
      simpa only [List.cons_append, recEq, Bool.and_eq_true] using ⟨h.1, ih h.2⟩

/-- The exact held prefix, followed by the hub's remaining records, reconstructs the hub's
ordered list. Records stay ordered; equality of flattened dropped sets is not substituted. -/
theorem held_prefix_reconstructs {s : SEState} {n p : Nat} {R : List Rec}
    (h : s.heldPrefix n R p = true) :
    ∃ L ∈ s.heldF n, recEq (L.take p ++ R.drop p) R = true := by
  obtain ⟨L, hL, hprefix⟩ := List.any_eq_true.1 h
  refine ⟨L, hL, ?_⟩
  simpa only [List.take_append_drop] using recEq_append_same hprefix (R.drop p)

/-- In every extended reachable state, a current full reply starting at the pruned boundary
has a reconstructible prefix for every participant, even if it took an obsolete list since.
This rules out missing-pruned-prefix refusal of that fresh reply in the model. -/
theorem current_pruned_reply_reconstructs {N : Nat} {s : SEState}
    (h : CExecReachable N s) {n : Nat} (hn : n < N) :
    ∃ L ∈ s.heldF n,
      recEq (L.take s.pruned ++ s.recs.drop s.pruned) s.recs = true :=
  held_prefix_reconstructs ((cexec_reachable_held h).now n hn)

/-- The two reconstruction branches in `note_announced`. Equality here stands for the
count and digest check, under the same collision-free record identity assumption as `recEq`.
 The response body supplies `R.drop offset`; it need not resend an already matching prefix. -/
def completeRecordReply (A : List Rec) (held : List (List Rec))
    (R : List Rec) (pruned offset : Nat) : Option (List Rec) :=
  let direct := A.take offset ++ R.drop offset
  if offset ≤ A.length ∧ recEq direct R = true then some direct
  else if offset = pruned then
    match held.find? (fun L => recEq (L.take pruned) (R.take pruned)) with
    | some L => some (L.take pruned ++ R.drop offset)
    | none => none
  else none

/-- A fresh request's applied records match the chosen hub prefix, or `records_since`
falls back to the pruning boundary. Either branch completes: the old-response branch that
silently ignores a candidate cannot recur for fresh serialized requests. -/
theorem fresh_record_reply_completes {N : Nat} {s : SEState} {n offset : Nat}
    (h : CExecReachable N s) (hn : n < N)
    (hoffset : (offset = (s.appliedF n).length ∧
      recEq (s.appliedF n) (s.recs.take offset) = true) ∨ offset = s.pruned) :
    ∃ R, completeRecordReply (s.appliedF n) (s.heldF n) s.recs s.pruned offset = some R ∧
      recEq R s.recs = true := by
  have held := (cexec_reachable_held h).now n hn
  have fallback : offset = s.pruned → ∃ R,
      completeRecordReply (s.appliedF n) (s.heldF n) s.recs s.pruned offset = some R ∧
        recEq R s.recs = true := by
    intro hf
    subst offset
    by_cases hg : s.pruned ≤ (s.appliedF n).length ∧
        recEq ((s.appliedF n).take s.pruned ++ s.recs.drop s.pruned) s.recs = true
    · exact ⟨_, by simp [completeRecordReply, hg], hg.2⟩
    ·
      cases hfind : (s.heldF n).find? (fun L => recEq (L.take s.pruned)
          (s.recs.take s.pruned)) with
      | none =>
        obtain ⟨L, hL, hp⟩ := List.any_eq_true.1 held
        exact False.elim ((List.find?_eq_none.1 hfind L hL) hp)
      | some L =>
        have hp := List.find?_some hfind
        refine ⟨L.take s.pruned ++ s.recs.drop s.pruned,
          by simp [completeRecordReply, hg, hfind], ?_⟩
        simpa only [List.take_append_drop] using recEq_append_same hp (s.recs.drop s.pruned)
  rcases hoffset with ⟨hlen, hp⟩ | hf
  · subst offset
    have he : recEq ((s.appliedF n) ++ s.recs.drop (s.appliedF n).length) s.recs = true := by
      simpa only [List.take_append_drop] using
        recEq_append_same hp (s.recs.drop (s.appliedF n).length)
    exact ⟨_, by simp [completeRecordReply, he], he⟩
  · exact fallback hf

/-- `records_since` chooses its offset from the request snapshot. Serialization supplies
the missing identity with the receiver's current records; taking records between calls
cannot invalidate the live call's prefix while it is outstanding. -/
theorem serialized_record_reply_completes {N : Nat} {s : SEState} {n offset : Nat}
    {control : Retry.Serial.State} {call : Retry.Serial.Call}
    (h : CExecReachable N s) (hn : n < N)
    (hi : Retry.Serial.Inv control) (hc : control.active = some call)
    (hrepo : control.applied = s.appliedF n)
    (hoffset : (offset = call.beforeRecords.length ∧
      recEq call.beforeRecords (s.recs.take offset) = true) ∨ offset = s.pruned) :
    ∃ R, completeRecordReply (s.appliedF n) (s.heldF n) s.recs s.pruned offset = some R ∧
      recEq R s.recs = true := by
  have he := (Retry.Serial.active_records_unchanged hi hc).trans hrepo
  rw [he] at hoffset
  exact fresh_record_reply_completes h hn hoffset

end Musubi.Exec

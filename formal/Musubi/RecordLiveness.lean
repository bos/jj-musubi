/-
Ordered-record reconciliation after the set-based supersede policy. The abstraction forgets
record boundaries and order, so `SConverged` alone does not open the executable push guard.
Taking current hub records repairs one node in one adoption, without requiring a missing
drop. Set-based progress can increase this debt, so it is the last measure component.
-/
import Musubi.SupersedeExecSound

namespace Musubi.Exec

open Musubi

theorem recEq_self (R : List Rec) : recEq R R = true := by
  induction R with
  | nil => rfl
  | cons r R ih => simp [recEq, seteq, ih]

def RecordConverged (N : Nat) (ses : SEState) : Prop :=
  SConverged N (sabs ses) ∧ ∀ n, n < N → recEq (ses.appliedF n) ses.recs = true

theorem recordConvergedE_iff {N : Nat} {ses : SEState} :
    ses.recordConvergedE N = true ↔ RecordConverged N ses := by
  simp [SEState.recordConvergedE, RecordConverged, sconvergedE_iff,
    List.all_eq_true, List.mem_range]

/-- The old measure with finite record debt appended. -/
noncomputable def recordMeasure (N : Nat) (ses : SEState) :=
  (smeasure N (sabs ses), ses.recordLagE N)

def RecordLex := Prod.Lex Lex8 (fun a b : Nat => a < b)

theorem recordLex_wf : WellFounded RecordLex :=
  (Prod.lex ⟨Lex8, lex8_wf⟩ Nat.lt_wfRel).wf

theorem recordMeasureE_eq {N : Nat} {ses : SEState} (hok : ses.es.parOK = true) :
    ses.recordMeasureE N = recordMeasure N ses := by
  simp [SEState.recordMeasureE, recordMeasure, smeasureE_eq hok]

/-- Taking current records removes one mismatch; all other nodes keep theirs. -/
theorem recordLag_adopt_lt {N n : Nat} {ses : SEState} (hn : n < N)
    (hm : recEq (ses.appliedF n) ses.recs = false) :
    (ses.adoptR n ses.recs).recordLagE N < ses.recordLagE N := by
  apply sumN_lt hn
  · change (if recEq ((ses.adoptR n ses.recs).appliedF n) ses.recs then 0 else 1) < _
    rw [appliedF_adoptR]
    simp [recEq_self, hm]
  · intro i _ hi
    change (if recEq ((ses.adoptR n ses.recs).appliedF i) ses.recs then 0 else 1) = _
    rw [appliedF_adoptR]
    simp [hi]

/-- With no missing hub drop, taking its records is invisible to the set abstraction. -/
theorem sabs_adoptR_same {ses : SEState} {n : Nat}
    (hsub : ∀ x, x ∈ ses.hubDL → x ∈ ses.nodeDF n) :
    sabs (ses.adoptR n ses.recs) = sabs ses := by
  have hd : (fun i => setP ((ses.adoptR n ses.recs).nodeDF i)) =
      fun i => setP (ses.nodeDF i) := by
    change (fun i => setP ((ses.setD n (union (ses.nodeDF n) ses.hubDL)).nodeDF i)) = _
    rw [setP_nodeD_setD, setP_union]
    funext i x
    by_cases hi : i = n
    · subst i
      simp only [upd, ↓reduceIte]
      exact propext ⟨fun h => h.elim id (hsub x), Or.inl⟩
    · simp [upd, hi]
  show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
  congr 1

/-- Effective exchanges: a projected set-based policy step, or adoption of current records
that adds no drop. Unchanged fetches/announcements are not effective steps. The reply/retry
scheduling bridge is separate from this relation. -/
inductive RecordPolicy (N : Nat) : SEState → SEState → Prop
  | projected {ses ses' : SEState} (h : SPStepR N (sabs ses) (sabs ses')) :
      RecordPolicy N ses ses'
  | reconcile (ses : SEState) (n : Nat) (hn : n < N)
      (hm : recEq (ses.appliedF n) ses.recs = false)
      (hsub : ∀ x, x ∈ ses.hubDL → x ∈ ses.nodeDF n)
      (hheads : ∀ h, h ∈ (ses.es.nodeOf n).heads → h ∉ ses.hubDL) :
      RecordPolicy N ses (ses.adoptR n ses.recs)

/-- Both kinds of effective progress decrease the refined well-founded measure. -/
theorem recordMeasure_decreases {N : Nat} {ses ses' : SEState}
    (hr : SRReachable N (sabs ses)) (hA : AllPruned N (sabs ses))
    (hp : RecordPolicy N ses ses') :
    RecordLex (recordMeasure N ses') (recordMeasure N ses) := by
  cases hp with
  | projected h => exact Prod.Lex.left _ _ (smeasure_decreases hr hA h)
  | reconcile n hn hm hsub _ =>
    have he := sabs_adoptR_same hsub
    unfold recordMeasure
    rw [he]
    exact Prod.Lex.right _ (recordLag_adopt_lt hn hm)

theorem recordPolicy_wf : WellFounded
    (fun ses' ses => (SRReachable N (sabs ses) ∧ AllPruned N (sabs ses)) ∧
      RecordPolicy N ses ses') :=
  Subrelation.wf (fun ⟨⟨hr, hA⟩, hp⟩ => recordMeasure_decreases hr hA hp)
    (InvImage.wf (recordMeasure N) recordLex_wf)

/-- An actual executable adoption after announcing current records, with exactly the head
check used by NodeCore's prepare/adopt path, and the check that the node has held the records
the hub pruned, as every node has (`sexec_announced_held`). -/
theorem reconcile_executable {N n : Nat} {ses : SEState} (hn : n < N)
    (hok : ses.es.parOK = true)
    (hheld : ses.heldPrefix n ses.recs ses.pruned = true)
    (hh : ∀ h, h ∈ (ses.es.nodeOf n).heads → h ∉ ses.hubDL) :
    sexecStep N { ses with dmsgs := ses.dmsgs ++ [(n, ses.recs, ses.pruned)] }
      (.adopt n ses.recs) =
      .ok { ses.adoptR n ses.recs with dmsgs := ses.dmsgs ++ [(n, ses.recs, ses.pruned)] } := by
  simp only [SEState.heldPrefix, SEState.heldF] at hheld
  simp [sexecStep, sexecCore, sreq, hok, hn, List.any_append, recEq_self,
    SEState.hubDL, SEState.adoptR, SEState.setD, SEState.nodeDF, SEState.heldPrefix,
    SEState.heldF, hheld] at *
  exact hh

/-- At abstract convergence every mismatch is enabled: all drops are local and the sole
head survives the hub's records. -/
theorem record_progress_at_convergence {N : Nat} {ses : SEState}
    (hr : SRReachable N (sabs ses)) (hc : SConverged N (sabs ses))
    (hnc : ¬ RecordConverged N ses) : ∃ ses', RecordPolicy N ses ses' := by
  have hm : ∃ n, n < N ∧ recEq (ses.appliedF n) ses.recs = false := by
    apply Classical.byContradiction
    intro h
    apply hnc
    refine ⟨hc, fun n hn => ?_⟩
    cases he : recEq (ses.appliedF n) ses.recs
    · exact False.elim (h ⟨n, hn, he⟩)
    · rfl
  obtain ⟨n, hn, hm⟩ := hm
  refine ⟨_, RecordPolicy.reconcile ses n hn hm (fun x hx => (hc.2 n hn x).2 hx) ?_⟩
  intro h hh hd
  have he := ((hc.1 n hn).1 h).1 hh
  exact (sinv_reachable hr).headOK (by simpa [he, sabs, setP] using hd)

/-- There is at most one unit of reconciliation debt per machine. -/
theorem recordLag_le (N : Nat) (ses : SEState) : ses.recordLagE N ≤ N := by
  unfold SEState.recordLagE
  induction N with
  | zero => simp [sumN]
  | succ N ih =>
    simp only [sumN]
    split <;> omega

/-- Finite runs of effective exchanges. -/
inductive RecordSteps (N : Nat) : SEState → SEState → Prop
  | refl (ses : SEState) : RecordSteps N ses ses
  | head {ses next last : SEState} : RecordPolicy N ses next →
      RecordSteps N next last → RecordSteps N ses last

/-- Abstract convergence suffices for a finite completion with exactly the hub's ordered
records. All these remaining steps preserve the abstract state, including the hub. -/
theorem record_finish {N : Nat} {ses : SEState} (hr : SRReachable N (sabs ses))
    (hA : AllPruned N (sabs ses)) (hc : SConverged N (sabs ses)) :
    ∃ ses', RecordSteps N ses ses' ∧
      sabs ses' = sabs ses ∧ RecordConverged N ses' := by
  induction ses using (recordPolicy_wf (N := N)).induction with
  | h ses ih =>
    by_cases hd : RecordConverged N ses
    · exact ⟨ses, .refl ses, rfl, hd⟩
    obtain ⟨next, hp⟩ := record_progress_at_convergence hr hc hd
    have he : sabs next = sabs ses := by
      cases hp with
      | projected hp => exact False.elim (converged_quiescentS hr hc hp)
      | reconcile n _ _ hsub _ => exact sabs_adoptR_same hsub
    have hr' : SRReachable N (sabs next) := by rw [he]; exact hr
    have hA' : AllPruned N (sabs next) := by rw [he]; exact hA
    have hc' : SConverged N (sabs next) := by rw [he]; exact hc
    obtain ⟨last, steps, same, done⟩ := ih next ⟨⟨hr, hA⟩, hp⟩ hr' hA' hc'
    exact ⟨last, .head hp steps, same.trans he, done⟩

end Musubi.Exec

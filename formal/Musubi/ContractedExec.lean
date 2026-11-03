/-
An explicit extension of the executable original-operation submodel. Survivor advancement,
atomic prepared adoption and contracted acceptance extend the old transitions; rejection
also checks the contracted packet. This is not a claim that every raw canonical store
projects to this original-operation submodel.
-/
import Musubi.SupersedeExecSound
import Musubi.ContractedSafety

namespace Musubi.Exec

open Musubi Contract

def SEState.imageAdvance (ses : SEState) (n : Nat) : SEState :=
  { ses with es := ses.es.setNode n { ses.es.nodeOf n with
      heads := advanceImages ses.es.parF (ses.nodeDF n).contains
        (ses.es.nodeOf n).heads (ses.es.nodeOf n).known.2 } }

def imageAdvanceB (N : Nat) (ses : SEState) (n : Nat) : Bool :=
  let nd := ses.es.nodeOf n
  let images := exp ses.es.parF (ses.nodeDF n).contains nd.known.2
  ses.es.parOK && decide (n < N) && decide (nd.known.2 < ses.es.next) &&
    (ses.nodeDF n).contains nd.known.2 && !images.isEmpty &&
    images.all nd.lops.contains &&
    !(nd.heads.any (belowB ses.es.parF (ses.nodeDF n).contains nd.known.2))

def SEState.cabs (ses : SEState) : Contracted.View :=
  ⟨abs ses.es, ses.hubDL.contains, fun n => (ses.nodeDF n).contains⟩

theorem cabs_imageAdvance {ses : SEState} {n : Nat} (hlt : ParLt ses.es.parF) :
    (ses.imageAdvance n).cabs =
      ses.cabs.advanceImages n (ses.es.nodeOf n).known.2 := by
  unfold SEState.cabs SEState.imageAdvance Contracted.View.advanceImages
  simp only [abs_setNode]
  congr 1
  congr 1
  change Node.mk _ _ _ _ _ _ = Node.mk _ _ _ _ _ _
  congr 1
  exact advanceImages_set hlt

/-- The added finite advance is exactly the proved frontier transition, not an unchecked
escape from the original executable model. -/
theorem imageAdvance_safe (h : Contracted.Safe ses.cabs)
    (hg : imageAdvanceB N ses n = true) : Contracted.Safe (ses.imageAdvance n).cabs := by
  simp only [imageAdvanceB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, hk⟩, _⟩, _⟩, hl⟩, _⟩ := hg
  rw [cabs_imageAdvance h.parLt]
  apply Contracted.safe_advanceImages h (of_decide_eq_true hk)
  simpa only [SEState.cabs, abs, ENode.abs, setP, List.all_eq_true,
    List.contains_iff_mem] using hl

/-- The effective set for this acceptance includes every pending drop in the packet. It
uses the whole retained record prefix, not only the ids the hub has yet to prune. -/
def acceptDrops (ses : SEState) (_A : List Rec) (D : List Nat) : List Nat :=
  union ses.hubDL D

def SEState.imageAccept (ses : SEState) (n : Nat) (S O : List Nat)
    (d : Nat) (D : List Nat) : SEState :=
  ses.supAccept
    ((((ses.es.hubStore S O).hubAccept d).send
      (.head n .accepted (ses.es.hub.seq + 1) d)).send
      (.notifyAll (ses.es.hub.seq + 1) d)) D

/-- Finite well-formedness premises of the added acceptance. Created operation labels and
drop labels must refer to the existing universe, and the root and new head must survive. -/
def imageAcceptSafeB (ses : SEState) (S : List Nat) (d : Nat)
    (A : List Rec) (D : List Nat) : Bool :=
  decide (d < ses.es.next) && S.all (· < ses.es.next) &&
    (acceptDrops ses A D).all (· < ses.es.next) &&
    !(acceptDrops ses A D).contains root && !(acceptDrops ses A D).contains d

def imageAcceptB (ses : SEState) (n : Nat) (S O : List Nat) (e d : Nat)
    (A : List Rec) (D : List Nat) : Bool :=
  ses.es.parOK &&
    (ses.sups.any fun s => s.1 == n && recEq s.2.1 A && seteq s.2.2.1 D && s.2.2.2 == d) &&
    recEq A ses.recs &&
    !ses.remDL.contains d && !(pendingOf A D).contains d &&
    ses.es.inNet (.push n S O e d) && decide (ses.es.hub.head ≠ d) &&
    decide (ses.es.hub.head = e) &&
    belowB ses.es.parF (acceptDrops ses A D).contains e d &&
    (ses.es.hubStore S O).closedB d && imageAcceptSafeB ses S d A D

theorem imageAccept_drops {ses : SEState} :
    (ses.imageAccept n S O d D).cabs.hubD = (acceptDrops ses A D).contains := by
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [SEState.imageAccept, SEState.cabs, SEState.supAccept, SEState.hubDL,
    List.contains_iff_mem, mem_takeRecs, acceptDrops, mem_union]

/-- Acceptance preserves the same common store/head safety facts as survivor advancement.
This proves the added primitive's invariant case; it is not a full union invariant theorem. -/
theorem imageAccept_safe (h : Contracted.Safe ses.cabs)
    (hg : imageAcceptB ses n S O e d A D = true) :
    Contracted.Safe (ses.imageAccept n S O d D).cabs := by
  have hg' := hg
  simp only [imageAcceptB, Bool.and_eq_true] at hg'
  have hc := hg'.1.2
  have hb := hg'.2
  simp only [imageAcceptSafeB, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨⟨hd, hS⟩, hD⟩, hr⟩, hs⟩ := hb
  have hc' : ClosedAt (abs (ses.es.hubStore S O)) d :=
    (closedB_iff (es := ses.es.hubStore S O) h.parLt).1 hc
  unfold SEState.cabs SEState.imageAccept SEState.supAccept
  rw [abs_send_notify, abs_send _ (by intros _ _ he; cases he), abs_hubAccept,
    abs_hubStore]
  refine { h with
    hubRoot := ?_
    hubDropLt := ?_
    headLt := hd
    hubOpsLt := ?_
    headSurvives := ?_
    hubClosed := ?_ }
  · change (ses.imageAccept n S O d D).cabs.hubD root = false
    rw [imageAccept_drops]; exact hr
  · change ∀ x, (ses.imageAccept n S O d D).cabs.hubD x = true → x < ses.es.next
    rw [imageAccept_drops]
    intro x hx
    exact hD x (List.contains_iff_mem.1 hx)
  · intro x hx
    change x ∈ ses.es.hub.ops ∨ x ∈ S at hx
    rcases hx with hx | hx
    · exact h.hubOpsLt x hx
    · exact hS x hx
  · change (ses.imageAccept n S O d D).cabs.hubD d = false
    rw [imageAccept_drops]; exact hs
  · intro a ha _
    rw [abs_hubStore] at hc'
    exact hc' a ha

/-- While announced records are prepared, the old physical heads still use the previous
drop set. Switching them expands every old head under the prepared set, as well as known. -/
def preparedHeads (ses : SEState) (n : Nat) (R : List Rec) : List Nat :=
  let D := (union (ses.nodeDF n) (flat R)).contains
  maxL ses.es.parF (dd (((ses.es.nodeOf n).heads ++ [(ses.es.nodeOf n).known.2]).flatMap
    (exp ses.es.parF D)))

def SEState.preparedFrontier (ses : SEState) (n : Nat) (R : List Rec) : SEState :=
  { ses with es := ses.es.setNode n { ses.es.nodeOf n with heads := preparedHeads ses n R } }

/-- Preparation holds the records before publishing the replacement frontier. The finite
backend boundary is atomic too: it exposes no head-before-custody state to the scheduler. -/
def SEState.preparedAdvance (ses : SEState) (n : Nat) (R : List Rec) : SEState :=
  (ses.preparedFrontier n R).adoptR n R

def preparedAdvanceB (N : Nat) (ses : SEState) (n : Nat) (R : List Rec) : Bool :=
  ses.es.parOK && decide (n < N) &&
    (ses.dmsgs.any fun e => e.1 == n && recEq e.2.1 R && ses.heldPrefix n e.2.1 e.2.2) &&
    ((ses.es.nodeOf n).heads.any (flat R).contains) &&
    !(preparedHeads ses n R).isEmpty &&
    (preparedHeads ses n R).all (ses.es.nodeOf n).lops.contains &&
    (preparedHeads ses n R).all (fun x => !(union (ses.nodeDF n) (flat R)).contains x) &&
    !(union (ses.nodeDF n) (flat R)).contains root &&
    (union (ses.nodeDF n) (flat R)).all (· < ses.es.next)

theorem cabs_preparedFrontier {ses : SEState} {n : Nat} {R : List Rec} :
    (ses.preparedFrontier n R).cabs =
      ses.cabs.frontier n (setP (preparedHeads ses n R)) := by
  unfold SEState.cabs SEState.preparedFrontier Contracted.View.frontier
  rw [abs_setNode]
  rfl

theorem preparedFrontier_safe (h : Contracted.Safe ses.cabs)
    (hg : preparedAdvanceB N ses n R = true) :
    Contracted.Safe (ses.preparedFrontier n R).cabs := by
  simp only [preparedAdvanceB, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpar, _⟩, _⟩, _⟩, hne⟩, hl⟩, hs⟩, _⟩, _⟩ := hg
  rw [cabs_preparedFrontier]
  apply Contracted.safe_frontier h
  · simpa only [SEState.cabs, abs, ENode.abs, setP, List.all_eq_true,
      List.contains_iff_mem] using hl
  · intro x hx
    have hf := (List.all_eq_true.1 hs) x hx
    have hn : x ∉ union (ses.nodeDF n) (flat R) := not_mem_of_not_contains hf
    have hnot : x ∉ ses.nodeDF n := fun hm => hn (mem_union.2 (Or.inl hm))
    exact Bool.eq_false_iff.2 (fun hm => hnot (List.contains_iff_mem.1 hm))
  · intro x y hx hy hxy
    rw [preparedHeads, setP_maxL (parOK_parLt hpar)] at hx hy
    exact hx.2 y hy.1 hxy
  · cases he : preparedHeads ses n R with
    | nil => simp [he] at hne
    | cons x xs => exact ⟨x, by simp [setP]⟩

theorem cabs_adoptR {ses : SEState} {n : Nat} {R : List Rec} :
    (ses.adoptR n R).cabs = { ses.cabs with nodeD := fun m =>
      if m = n then (union (ses.nodeDF n) (flat R)).contains else ses.cabs.nodeD m } := by
  unfold SEState.cabs SEState.adoptR SEState.setD
  congr 1
  funext m
  change ((ses.setD n (union (ses.nodeDF n) (flat R))).nodeDF m).contains = _
  rw [nodeDF_setD]
  by_cases hm : m = n <;> simp [hm]

theorem preparedAdvance_safe (h : Contracted.Safe ses.cabs)
    (hg : preparedAdvanceB N ses n R = true) :
    Contracted.Safe (ses.preparedAdvance n R).cabs := by
  have hf := preparedFrontier_safe h hg
  have hg' := hg
  simp only [preparedAdvanceB, Bool.and_eq_true] at hg'
  have hbound := hg'.2
  have hroot := hg'.1.2
  have hsurvive := hg'.1.1.2
  unfold SEState.preparedAdvance
  rw [cabs_adoptR]
  refine { hf with nodeRoot := ?_, nodeDropLt := ?_, localClosed := ?_, headsSurvive := ?_ }
  · intro m
    by_cases hm : m = n
    · subst m
      simpa [SEState.preparedFrontier, SEState.nodeDF] using hroot
    · simp only [hm, ↓reduceIte]; exact hf.nodeRoot m
  · intro m x hx
    by_cases hm : m = n
    · subst m
      simp only [↓reduceIte] at hx
      exact of_decide_eq_true ((List.all_eq_true.1 hbound) x (List.contains_iff_mem.1 hx))
    · simp only [hm, ↓reduceIte] at hx; exact hf.nodeDropLt m x hx
  · intro m x a hx ha hd
    apply hf.localClosed m x a hx ha
    by_cases hm : m = n
    · subst m
      simp only [↓reduceIte] at hd
      apply Bool.eq_false_iff.2
      intro hm
      have hu : (union ((ses.preparedFrontier n R).nodeDF n) (flat R)).contains a = true :=
        List.contains_iff_mem.2 (mem_union.2 (Or.inl (List.contains_iff_mem.1 hm)))
      rw [hd] at hu; contradiction
    · simpa only [hm, ↓reduceIte] using hd
  · intro m x hx
    by_cases hm : m = n
    · subst m
      simp only [↓reduceIte]
      have hx' : x ∈ preparedHeads ses n R := by
        simpa [SEState.preparedFrontier, SEState.cabs, abs, ENode.abs, EState.nodeOf,
          EState.setNode, nodeAt_setN, setP] using hx
      simpa only [SEState.preparedFrontier, SEState.nodeDF, Bool.not_eq_true'] using
        ((List.all_eq_true.1 hsurvive) x hx')
    · simp only [hm, ↓reduceIte]; exact hf.headsSurvive m x hx

/-- A relation on the finite model itself, extending rather than silently changing SRStep.
The legacy constructor carries its original soundness theorem. The new constructors name
the complete checked guards and exact state changes of the added backend boundaries. -/
inductive ContractedRStep (N : Nat) : SEState → SEState → Prop
  | legacy (s t : SEState)
      (h : SRStep N (sabs s) (sabs t) ∨ sabs t = sabs s) : ContractedRStep N s t
  | advance (s : SEState) (n : Nat) (h : imageAdvanceB N s n = true) :
      ContractedRStep N s (s.imageAdvance n)
  | accept (s : SEState) (n : Nat) (S O : List Nat) (e d : Nat)
      (A : List Rec) (D : List Nat) (h : imageAcceptB s n S O e d A D = true) :
      ContractedRStep N s (s.imageAccept n S O d D)
  | prepared (s : SEState) (n : Nat) (R : List Rec)
      (h : preparedAdvanceB N s n R = true) :
      ContractedRStep N s (s.preparedAdvance n R)

/-- A legacy rejection must not contradict an acceptable contracted packet. Normal body
loss leaves every retained history entry replayable. Historical objects may be lost, but
rollback must recover to a closed target; an explicit remake models environment-chosen
recovery otherwise. This does not model every observable damaged-store prefix. -/
def legacyOutcomeB (ses : SEState) : SAction → Bool
  | .base (.hubPushReject n S O e d) =>
    !(ses.sups.any fun packet => packet.1 == n && packet.2.2.2 == d &&
      imageAcceptB ses n S O e d packet.2.1 packet.2.2.1)
  | .base (.hubForget S O) =>
    (List.range (ses.es.hub.seq + 1)).all fun i =>
      (ancL ses.es.parF (ses.es.hub.histF i)).all (ses.es.forget S O).hub.ops.contains
  | .base (.hubRegress i) => ses.es.closedB (ses.es.hub.histF i)
  | _ => true

def legacyOutcomeError : SAction → String
  | .base (.hubForget ..) => "hubForget: an operation needed by retained history is missing"
  | .base (.hubRegress ..) => "hubRegress: target incomplete; explicit recovery is required"
  | _ => "hubPushReject: a contracted supersede is acceptable"

/-- Keep the old executable results after checking rejection consistency. An old rejection
has exactly two additional cases; all other failed guards remain failures. -/
def cexecStep (N : Nat) (ses : SEState) (a : SAction) : Except String SEState :=
  match sexecStep N ses a with
  | .ok t => if legacyOutcomeB ses a then .ok t else .error (legacyOutcomeError a)
  | .error error =>
    match a with
    | .base (.advance n) =>
      if imageAdvanceB N ses n then .ok (ses.imageAdvance n) else .error error
    | .hubSupAccept n S O e d A D =>
      if imageAcceptB ses n S O e d A D then .ok (ses.imageAccept n S O d D)
      else .error error
    | _ => .error error

/-- Every accepted action is an old checked step or one of the two explicit new steps.
In particular the theorem does not incorrectly identify the new accepts with SRStep. -/
theorem cexec_sound (hok : SEOK ses) (h : cexecStep N ses a = .ok t) :
    ContractedRStep N ses t := by
  unfold cexecStep at h
  cases hs : sexecStep N ses a with
  | ok s =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h; exact .legacy _ _ (sexec_sound hok hs)
    · contradiction
  | error error =>
    rw [hs] at h
    cases a with
    | base a =>
      cases a <;> simp only at h
      all_goals first | contradiction | skip
      split at h
      · cases h; exact .advance _ _ (by assumption)
      · contradiction
    | hubSupAccept n S O e d A D =>
      simp only at h
      split at h
      · cases h; exact .accept _ _ _ _ _ _ _ _ (by assumption)
      · contradiction
    | _ => contradiction

/-- The record-custody premise needed by the legacy soundness theorem is kept across the
new boundaries too. Advancing changes no records; accepting appends at most one record. -/
theorem cexec_ok (hok : SEOK ses) (h : cexecStep N ses a = .ok t) : SEOK t := by
  unfold cexecStep at h
  cases hs : sexecStep N ses a with
  | ok s =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h; exact sexec_ok hok hs
    · contradiction
  | error error =>
    rw [hs] at h
    cases a with
    | base a =>
      cases a <;> simp only at h
      all_goals first | contradiction | skip
      split at h
      · cases h; exact ⟨hok.applied, hok.pruned, hok.hist, hok.held⟩
      · contradiction
    | hubSupAccept n S O e d A D =>
      simp only at h
      split at h
      · cases h
        refine { hok with pruned := ?_, hist := ?_ }
        · exact Nat.le_trans hok.pruned (length_takeRecs _ _)
        · intro entry he
          rcases List.mem_cons.1 he with rfl | he
          · exact Nat.le_trans hok.pruned (length_takeRecs _ _)
          · exact hok.hist entry he
      · contradiction
    | _ => contradiction

inductive CAction
  | old (action : SAction)
  | advancePrepared (node : Nat) (records : List Rec)
  | reject (node : Nat) (ops objs : List Nat) (expected new : Nat)
      (applied : List Rec) (dropped : List Nat)

/-- Rejection is packet-specific. Using original ancestry here would allow both acceptance
and rejection of the very push that repairs a dropped expected head. -/
def imageRejectB (ses : SEState) (n : Nat) (S O : List Nat) (e d : Nat)
    (A : List Rec) (D : List Nat) : Bool :=
  (ses.sups.any fun s => s.1 == n && recEq s.2.1 A && seteq s.2.2.1 D && s.2.2.2 == d) &&
    recEq A ses.recs && !ses.remDL.contains d && !(pendingOf A D).contains d &&
    (!decide (ses.es.hub.head = e) ||
      ((ses.es.hubStore S O).closedB d &&
        !belowB ses.es.parF (acceptDrops ses A D).contains e d))

theorem seok_adoptR (hok : SEOK ses) (n : Nat) (R : List Rec) : SEOK (ses.adoptR n R) := by
  have e1 : ∀ m, (ses.adoptR n R).nodeDF m =
      (ses.setD n (union (ses.nodeDF n) (flat R))).nodeDF m := fun _ => rfl
  refine { hok with applied := ?_, held := ?_ }
  · intro m x hx
    rw [e1, nodeDF_setD]
    rw [appliedF_adoptR] at hx
    by_cases hm : m = n
    · subst m; simp only [↓reduceIte] at hx ⊢; exact mem_union.2 (Or.inr hx)
    · simp only [hm, ↓reduceIte] at hx ⊢; exact hok.applied m x hx
  · intro m L x hL hx
    rw [e1, nodeDF_setD]
    rw [heldF_adoptR] at hL
    by_cases hm : m = n
    · subst m; simp only [↓reduceIte] at hL ⊢
      rcases List.mem_cons.1 hL with rfl | hL
      · exact mem_union.2 (Or.inr hx)
      · exact mem_union.2 (Or.inl (hok.held n L x hL hx))
    · simp only [hm, ↓reduceIte] at hL ⊢; exact hok.held m L x hL hx

def cexecAction (N : Nat) (ses : SEState) : CAction → Except String SEState
  | .old action => cexecStep N ses action
  | .advancePrepared n R =>
    if preparedAdvanceB N ses n R then .ok (ses.preparedAdvance n R)
    else .error "advancePrepared: records, locality or frontier guard failed"
  | .reject n S O e d A D =>
    if imageRejectB ses n S O e d A D then
      sexecStep N ses (.base (.hubPushReject n S O e d))
    else .error "hubPushReject: packet is acceptable, incomplete, or should be refused"

theorem cexecAction_sound (hok : SEOK ses) (h : cexecAction N ses a = .ok t) :
    ContractedRStep N ses t := by
  cases a with
  | old action => exact cexec_sound hok h
  | advancePrepared n R =>
    simp only [cexecAction] at h
    split at h
    · cases h; exact .prepared _ _ _ (by assumption)
    · contradiction
  | reject n S O e d A D =>
    simp only [cexecAction] at h
    split at h
    · exact .legacy _ _ (sexec_sound hok h)
    · contradiction

theorem cexecAction_ok (hok : SEOK ses) (h : cexecAction N ses a = .ok t) : SEOK t := by
  cases a with
  | old action => exact cexec_ok hok h
  | advancePrepared n R =>
    simp only [cexecAction] at h
    split at h
    · cases h
      apply seok_adoptR
      exact ⟨hok.applied, hok.pruned, hok.hist, hok.held⟩
    · contradiction
  | reject n S O e d A D =>
    simp only [cexecAction] at h
    split at h
    · exact sexec_ok hok h
    · contradiction

inductive CExecReachable (N : Nat) : SEState → Prop
  | init : CExecReachable N initSE
  | step {s t : SEState} (reach : CExecReachable N s) (a : CAction)
      (h : cexecAction N s a = .ok t) : CExecReachable N t

/-- The soundness premise is invariant from reset, including across added transitions. -/
theorem cexec_reachable_ok (h : CExecReachable N ses) : SEOK ses := by
  induction h with
  | init => exact seok_init
  | step _ _ hs ih => exact cexecAction_ok ih hs

theorem cexec_reachable_step (hr : CExecReachable N ses)
    (hs : cexecAction N ses a = .ok t) : ContractedRStep N ses t :=
  cexecAction_sound (cexec_reachable_ok hr) hs

end Musubi.Exec

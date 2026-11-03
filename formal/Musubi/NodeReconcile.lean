/-
The node-side entry to the stable-record suffix. A node that has already dropped every
current hub drop can take the current record list immediately: none of its surviving heads
can block adoption. This does not require the hub's head to have stabilized.
-/
import Musubi.PacketCoupling

namespace Musubi.Exec

open Musubi Contract

def HeadsSurvive (s : SState) : Prop :=
  ∀ n x, (s.s.node n).heads x → ¬ s.nodeD n x

theorem srstep_heads_survive {N : Nat} {s t : SState}
    (h : HeadsSurvive s) (hs : SRStep N s t) : HeadsSurvive t := by
  rcases hs with step | ⟨i, _, rfl⟩
  · cases step with
    | base t _ _ hn | sup t _ _ _ _ _ _ _ _ _ hn =>
      intro n x hx
      exact (hn n x hx).elim (h n x) id
    | abandon m D _ _ hD _ | adopt m D _ _ hD =>
      intro n x hx hd
      by_cases hn : n = m
      · subst n
        change upd s.nodeD m (fun y => s.nodeD m y ∨ D y) m x at hd
        rw [upd_same] at hd
        exact hd.elim (h m x hx) (hD x hx)
      · change upd s.nodeD m (fun y => s.nodeD m y ∨ D y) n x at hd
        rw [upd_ne _ _ hn] at hd
        exact h n x hx hd
    | sendSup => exact h
    | sendD => exact h
    | prune => exact h
  · simpa only [HeadsSurvive, SState.regress, State.regress] using h

def NodeHeadsSurvive (s : SEState) : Prop :=
  ∀ n x, x ∈ (s.es.nodeOf n).heads → x ∉ s.nodeDF n

theorem node_heads_survive_init : NodeHeadsSurvive initSE := by
  intro n x _
  simp [initSE, SEState.nodeDF, assocF]

theorem contracted_heads_survive {N : Nat} {s t : SEState}
    (h : NodeHeadsSurvive s) (hs : ContractedRStep N s t) : NodeHeadsSurvive t := by
  cases hs with
  | legacy t step =>
    have h' : HeadsSurvive (sabs s) := h
    change HeadsSurvive (sabs t)
    rcases step with step | same
    · exact srstep_heads_survive h' step
    · rw [same]; exact h'
  | advance m hg =>
    have hpar : ParLt s.es.parF := by
      simp only [imageAdvanceB, Bool.and_eq_true] at hg
      exact parOK_parLt hg.1.1.1.1.1.1
    intro n x hx
    by_cases hn : n = m
    · subst n
      have hx' : x ∈ advanceImages s.es.parF (s.nodeDF m).contains
          (s.es.nodeOf m).heads (s.es.nodeOf m).known.2 := by
        simpa [SEState.imageAdvance, EState.setNode, EState.nodeOf, nodeAt_setN] using hx
      have hd := advanceImages_survives hpar (fun y hy => by
        have hn := h m y hy
        apply Bool.eq_false_iff.2
        intro hm
        exact hn (List.contains_iff_mem.1 hm)) hx'
      change x ∉ s.nodeDF m
      intro hm
      rw [List.contains_iff_mem.2 hm] at hd
      contradiction
    · apply h n x
      simpa [SEState.imageAdvance, EState.setNode, EState.nodeOf, nodeAt_setN, hn] using hx
  | accept =>
    have send_nodes (es : EState) (msg : EMsg) : (es.send msg).nodes = es.nodes := by
      unfold EState.send
      split <;> rfl
    simpa [NodeHeadsSurvive, SEState.imageAccept, SEState.supAccept, EState.nodeOf,
      send_nodes, EState.hubAccept, EState.hubStore, EState.hubStoreOps,
      EState.hubStoreObjs, SEState.nodeDF] using h
  | prepared m R hg =>
    have hsurvive : (preparedHeads s m R).all
        (fun x => !(union (s.nodeDF m) (flat R)).contains x) = true := by
      simp only [preparedAdvanceB, Bool.and_eq_true] at hg
      exact hg.1.1.2
    intro n x hx
    have hD : (s.preparedAdvance m R).nodeDF n =
        if n = m then union (s.nodeDF m) (flat R) else s.nodeDF n :=
      nodeDF_setD (s.preparedFrontier m R) m _ n
    rw [hD]
    by_cases hn : n = m
    · subst n
      simp only [ite_true]
      have hx' : x ∈ preparedHeads s m R := by
        simpa [SEState.preparedAdvance, SEState.adoptR, SEState.setD,
          SEState.preparedFrontier, EState.setNode, EState.nodeOf, nodeAt_setN,
          ] using hx
      exact not_mem_of_not_contains ((List.all_eq_true.1 hsurvive) x hx')
    · simp only [hn, ite_false]
      apply h n x
      simpa [SEState.preparedAdvance, SEState.adoptR, SEState.setD,
        SEState.preparedFrontier, EState.setNode, EState.nodeOf, nodeAt_setN,
        hn] using hx

theorem cexec_reachable_heads_survive {N : Nat} {s : SEState}
    (h : CExecReachable N s) : NodeHeadsSurvive s := by
  induction h with
  | init => exact node_heads_survive_init
  | step reach _ hs ih =>
    exact contracted_heads_survive ih (cexec_reachable_step reach hs)

/-- A current announcement cannot block on an operation head of a node that already
holds all its drops. The native policy checks this adoption before merge, transfer or push. -/
theorem current_adoption_enabled {N : Nat} {s : SEState} {n : Nat} {R : List Rec}
    (hpar : s.es.parOK = true) (hn : n < N) (hheads : NodeHeadsSurvive s)
    (hheld : ∀ x, x ∈ flat R → x ∈ s.nodeDF n)
    (hmsg : (s.dmsgs.any fun e => e.1 == n && recEq e.2.1 R &&
      s.heldPrefix n e.2.1 e.2.2) = true) :
    cexecAction N s (.old (.adopt n R)) = .ok (s.adoptR n R) := by
  have hnone : ∀ x ∈ (s.es.nodeOf n).heads, x ∉ flat R :=
    fun x hx hr => hheads n x hx (hheld x hr)
  have hadopt : sexecStep N s (.adopt n R) = .ok (s.adoptR n R) := by
    simpa [sexecStep, sexecCore, sreq, hpar, hn, hmsg] using hnone
  simp only [cexecAction, cexecStep, hadopt, legacyOutcomeB, ite_true]

/-- Eligibility plus current ordered records leaves no unpublished drops. The core's
fix-up and neutral-tip guards are both false in this state, before the hub head settles. -/
theorem aligned_records_no_pending {s : SEState} {n : Nat}
    (hrec : recEq (s.appliedF n) s.recs = true)
    (hdrop : ∀ x, x ∈ s.nodeDF n ↔ x ∈ s.hubDL) :
    pendingOf (s.appliedF n) (s.nodeDF n) = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  obtain ⟨hd, ha⟩ := (mem_pendingOf _ _ _).1 hx
  exact ha ((mem_flat_of_recEq hrec x).2 ((hdrop x).1 hd))

end Musubi.Exec

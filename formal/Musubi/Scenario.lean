/-
A concrete run, as a non-vacuity check: two nodes write concurrently, both push, one loses
the race, fetches, realizes, advances, merges, and pushes the merge. Every step is a step of
the asynchronous model (via `pstep_reachable`).
-/
import Musubi.Liveness

namespace Musubi.Scenario

open Musubi

/-- Node 0 writes op 1 on the root. -/
def s1 : State := init.userOp 0 root []
/-- Node 1 writes op 2 on the root. -/
def s2 : State := s1.userOp 1 root []
/-- Node 0 uploads and pushes op 1; the hub accepts it. -/
def s3 : State := s2.pPushAccept 0 1
/-- Node 1 uploads and pushes op 2; the hub rejects it and node 1 learns `(1, 1)`. -/
def s4 : State := s3.pPushReject 1 2
/-- Node 1 fetches and realizes op 1. -/
def s5 : State := s4.pRealize 1 1
/-- Node 1 advances: its heads become `{2, 1}`. -/
def s6 : State := s5.advance 1
/-- Node 1 merges: op 3 with parents `[2, 1]`. -/
def s7 : State := s6.mergeOp 1 [2, 1] []
/-- Node 1 uploads and pushes the merge; the hub accepts it. -/
def s8 : State := s7.pPushAccept 1 3

theorem userOp_node_ne {s : State} {n p i : Nat} {O : List Nat} (h : i ≠ n) :
    (s.userOp n p O).node i = s.node i := createOp_node_ne h

theorem node1_s1 : s1.node 1 = initNode := by rw [s1, userOp_node_ne (by decide)]; rfl
theorem node0_s2 : s2.node 0 = s1.node 0 := by rw [s2, userOp_node_ne (by decide)]
theorem known0_s2 : (s2.node 0).known = (0, root) := by
  rw [node0_s2]; simp only [s1, State.userOp, createOp_known]; rfl

theorem r1 : Reachable 2 s1 :=
  Reachable.init.step (Or.inl (EnvStep.userOp init 0 root [] (by decide) rfl))

theorem heads_s1_0 (y : Nat) : (s1.node 0).heads y ↔ y = 1 := by
  have := userOp_heads_iff (N := 2) (y := y) (inv_init 2) (n := 0) (p := root) rfl
  simp only [s1, State.userOp, createOp_heads]
  rw [this]
  simp [init, initNode]
  omega

theorem r2 : Reachable 2 s2 :=
  r1.step (Or.inl (EnvStep.userOp s1 1 root [] (by decide) (by rw [node1_s1]; rfl)))

theorem heads_s2_1 (y : Nat) : (s2.node 1).heads y ↔ y = 2 := by
  have hI := inv_reachable r1
  have := userOp_heads_iff (y := y) hI (n := 1) (p := root) (by rw [node1_s1]; rfl)
  simp only [s2, State.userOp, createOp_heads]
  rw [this, node1_s1]
  have h2 : s1.U.next = 2 := rfl
  rw [h2]
  simp [initNode]
  omega

theorem heads_s2_0 (y : Nat) : (s2.node 0).heads y ↔ y = 1 := by
  rw [node0_s2]; exact heads_s1_0 y

theorem par_s2_1 : s2.U.par 1 = [root] := rfl
theorem par_s2_2 : s2.U.par 2 = [root] := rfl

theorem r3 : Reachable 2 s3 := by
  refine pstep_reachable r2 (PStep.pushAccept s2 0 1 (by decide) heads_s2_0 ?_ ?_ ?_)
  · rw [known0_s2]; decide
  · rw [known0_s2]; exact Anc.parent (by rw [par_s2_1]; simp)
  · rw [known0_s2]; rfl

theorem node1_s3 : s3.node 1 = s2.node 1 := by
  simp [s3, State.pPushAccept, State.learn, setNode_ne]

theorem r4 : Reachable 2 s4 := by
  have hk : (s3.node 1).known = (0, root) := by
    rw [node1_s3, s2]; simp only [State.userOp, createOp_known]; rw [node1_s1]; rfl
  refine pstep_reachable r3 (PStep.pushReject s3 1 2 (by decide)
    (by rw [node1_s3]; exact heads_s2_1) ?_ ?_ ?_ ?_)
  · rw [hk]; decide
  · rw [hk]; exact Anc.parent (by show root ∈ s2.U.par 2; rw [par_s2_2]; simp)
  · rw [hk]; decide
  · decide

theorem node1_s4 : (s4.node 1).known = (1, 1) ∧ (s4.node 1).lops = (s2.node 1).lops ∧
    (s4.node 1).heads = (s2.node 1).heads := by
  simp [s4, State.pPushReject, State.learn, node1_s3]
  exact ⟨rfl, rfl⟩

theorem lops_s2_1 (y : Nat) : (s2.node 1).lops y ↔ y = root ∨ y = 2 := by
  simp only [s2, State.userOp, createOp_lops]
  rw [node1_s1]
  rfl

theorem r5 : Reachable 2 s5 := by
  refine pstep_reachable r4 (PStep.realize s4 1 1 (by decide) ?_ ?_ ?_)
  · rw [node1_s4.1]; exact Anc.refl
  · rw [node1_s4.2.1, lops_s2_1]; decide
  · intro p hp
    have hp' : p ∈ s2.U.par 1 := hp
    rw [par_s2_1] at hp'
    simp at hp'
    rw [node1_s4.2.1, lops_s2_1]
    exact Or.inl hp'

theorem node1_s5 : (s5.node 1).known = (1, 1) ∧ (s5.node 1).lops 1 ∧
    (s5.node 1).heads = (s2.node 1).heads := by
  have h := node1_s4
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [s5, State.pRealize, State.realize, State.recvObjs, State.recvOps, h.1, h.2.2]

theorem U_s5 : s5.U = s2.U := rfl

theorem not_anc_1_2 : ¬ Anc s2.U.par 1 2 := by
  intro hA
  cases hA with
  | step hp hA' =>
    have hp' : _ ∈ s2.U.par 2 := hp
    rw [par_s2_2] at hp'
    simp at hp'
    subst hp'
    exact absurd (hA'.le (inv_reachable r2).parLt) (by decide)

theorem hna_s5 : ¬ ∃ h, (s5.node 1).heads h ∧ Anc s5.U.par (s5.node 1).known.2 h := by
  rw [node1_s5.1, node1_s5.2.2, U_s5]
  rintro ⟨h, hh, hA⟩
  rw [heads_s2_1] at hh
  subst hh
  exact not_anc_1_2 hA

theorem r6 : Reachable 2 s6 := by
  refine pstep_reachable r5 (PStep.advance s5 1 (by decide) ?_ hna_s5)
  rw [node1_s5.1]; exact node1_s5.2.1

theorem heads_s6_1 (y : Nat) : (s6.node 1).heads y ↔ y = 2 ∨ y = 1 := by
  have hI := inv_reachable r5
  have := advance_heads_iff (y := y) hI hna_s5
  simp only [s6, State.advance, setNode_self]
  rw [this, node1_s5.1, node1_s5.2.2, heads_s2_1]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · subst h
      exact Or.inr ⟨rfl, Anc.not_of_lt hI.parLt (by decide)⟩
    · exact Or.inl h

theorem r7 : Reachable 2 s7 := by
  refine pstep_reachable r6 (PStep.merge s6 1 [2, 1] [] (by decide) ?_ ⟨2, 1, by simp, by simp,
    by decide⟩)
  intro x
  rw [heads_s6_1]
  simp

theorem r8 : Reachable 2 s8 := by
  have hk : (s7.node 1).known = (1, 1) := by
    simp only [s7, State.mergeOp, createOp_known]
    simp [s6, State.advance, node1_s5.1]
  refine pstep_reachable r7 (PStep.pushAccept s7 1 3 (by decide) ?_ ?_ ?_ ?_)
  · intro y; simp only [s7, State.mergeOp, createOp_heads]; rfl
  · rw [hk]; decide
  · rw [hk]
    exact Anc.parent (by show 1 ∈ upd s6.U.par 3 [2, 1] 3; simp)
  · rw [hk]; rfl

/-- **Non-vacuity**: a run with a lost Cas race, a fetch, an advance, and a merge that is then
accepted is reachable, and the merge is owned as `MergeOwnership` requires. -/
theorem scenario :
    ∃ s, Reachable 2 s ∧ s.U.isMerge 3 = true ∧ s.U.creator 3 = some 1 ∧ s.U.par 3 = [2, 1] ∧
      s.U.creator 2 = some 1 ∧ s.U.creator 1 = some 0 ∧ s.hub.head = 3 ∧ s.hub.seq = 2 :=
  ⟨s8, r8, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Musubi.Scenario

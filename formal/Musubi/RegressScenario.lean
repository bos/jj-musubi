/-
A concrete run of the extended system in which two nodes merge the same heads, so
`noDuplicateMerge` fails once the hub can go back, and `RReachable` is strictly larger than
`Reachable`. It is a trace of the executable model, checked by evaluating `execStep`, and
lifted by `exec_rreachable`.
-/
import Musubi.ExecSound

namespace Musubi.RegressScenario

open Musubi Musubi.Exec

/-- Three nodes: A (0), B (1) and C (2). A's operation 1 is accepted at seq 1, and B fetches
it. The hub goes back to the root, and C's operation 2 is accepted at seq 1. A and B each
restart on the reply that tells them so, learn `(1, 2)`, fetch and realize 2, advance to
heads `{1, 2}`, and merge them: operations 3 and 4. -/
def trace : List Action :=
  [.userOp 0 root [], .userOp 2 root [],
   -- A pushes 1; B fetches it
   .pushAll 0 [1] [] root 1, .hubPushAccept 0 [1] [] root 1, .learn 0 .accepted 1 1,
   .fetchAll 1 root [], .hubFetch 1 root [], .learn 1 .head 1 1, .recvOps 1 [1],
   .recvObjs 1 [], .realize 1 1, .advance 1,
   -- the hub goes back; C pushes 2
   .hubRegress 0,
   .pushAll 2 [2] [] root 2, .hubPushAccept 2 [2] [] root 2,
   -- A catches up and merges
   .loseKnown 0, .fetchAll 0 root [], .hubFetch 0 root [], .learn 0 .head 1 2,
   .recvOps 0 [2], .recvObjs 0 [], .realize 0 2, .advance 0, .merge 0 [1, 2] [],
   -- so does B
   .loseKnown 1, .hubFetch 1 root [], .learn 1 .head 1 2, .recvOps 1 [2], .recvObjs 1 [],
   .realize 1 2, .advance 1, .merge 1 [1, 2] []]

/-- The state the trace ends in. -/
def final : EState :=
  match run 3 initE trace with
  | .ok es => es
  | .error _ => initE

theorem trace_ok : run 3 initE trace = .ok final := by
  have h : (run 3 initE trace).isOk = true := by decide
  unfold final
  revert h
  cases run 3 initE trace with
  | ok es => intro; rfl
  | error e => intro h; cases h

theorem facts : (final.next == 5 && final.isMergeF 3 && final.isMergeF 4 &&
    final.creatorF 3 == some 0 && final.creatorF 4 == some 1 &&
    final.parF 3 == [1, 2] && final.parF 4 == [1, 2]) = true := by
  decide

/-- **Duplicate merges after the hub goes back**: in a state of the extended system, two
different nodes have created merges with the same parents. -/
theorem duplicateMerge :
    ∃ s, RReachable 3 s ∧ ∃ m1 m2, m1 < s.U.next ∧ m2 < s.U.next ∧
      s.U.isMerge m1 = true ∧ s.U.isMerge m2 = true ∧ s.U.creator m1 ≠ s.U.creator m2 ∧
      ∀ x, x ∈ s.U.par m1 ↔ x ∈ s.U.par m2 := by
  have h := facts
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hn, hm3⟩, hm4⟩, hc3⟩, hc4⟩, hp3⟩, hp4⟩ := h
  refine ⟨abs final, exec_rreachable (run_rreachable ExecRReachable.init trace_ok), 3, 4,
    ?_, ?_, hm3, hm4, ?_, ?_⟩
  · show 3 < final.next; omega
  · show 4 < final.next; omega
  · show final.creatorF 3 ≠ final.creatorF 4; rw [hc3, hc4]; decide
  · intro x; show x ∈ final.parF 3 ↔ x ∈ final.parF 4; rw [hp3, hp4]

/-- Hence the extended system reaches states the durable one does not. -/
theorem rreachable_not_reachable : ∃ s, RReachable 3 s ∧ ¬ Reachable 3 s := by
  obtain ⟨s, hs, m1, m2, h1, h2, g1, g2, hc, hp⟩ := duplicateMerge
  exact ⟨s, hs, fun hr => noDuplicateMerge hr h1 h2 g1 g2 hc hp⟩

end Musubi.RegressScenario

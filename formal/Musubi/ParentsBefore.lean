/-
The check the oracle makes of every operation history it is sent: each operation's parents are
operations that come before it. Several executable models and their requests share it
(`PresenceExec.lean`, `ExpectedExec.lean`, `RefsExec.lean`, `ExecJson.lean`), each with its own
message when it fails.
-/

namespace Musubi

/-- Whether each entry of `ps`, the parents of the operations in order, names only parents
that come before it: entry `i` holds numbers below `i`. -/
def parentsBefore (ps : List (List Nat)) : Bool :=
  ps.zipIdx.all fun (q, i) => q.all (· < i)

/-- A parent of operation `i` in a history that passes the check is below `i`. -/
theorem parentsBefore_lt {ps : List (List Nat)} (h : parentsBefore ps = true) {i p : Nat}
    {q : List Nat} (hq : ps[i]? = some q) (hp : p ∈ q) : p < i := by
  simp only [parentsBefore, List.all_eq_true, decide_eq_true_eq] at h
  exact h (q, i) (List.mem_zipIdx_iff_getElem?.2 hq) p hp

end Musubi

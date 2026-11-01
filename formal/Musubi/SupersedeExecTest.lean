/-
Smoke test of the executable model with supersedes, checked at build time: node 0 pushes two
operations, abandons the first, and publishes the abandon with a fix-up operation; node 1
fetches the hub's head with its records, catches up and takes them. Then the guards: no head
abandoned, no push accepted whose records aren't the hub's, and no head the hub dropped.
`test/smoke.jsonl` replays the run through the oracle.
-/
import Musubi.SupersedeExecSound
import Musubi.ExecTest

namespace Musubi.Exec.SupersedeTest

open Musubi

/-- Runs actions in turn, stopping at the first one rejected. -/
def srun (N : Nat) (ses : SEState) : List SAction → Except String SEState
  | [] => .ok ses
  | a :: as => do srun N (← sexecStep N ses a) as

def errorOf : Except String SEState → String
  | .error e => e
  | .ok _ => "(accepted)"

/-- Node 0 pushes operations 1 and 2 with their records (none), each accepted. -/
def pushes : List SAction :=
  [.base (.userOp 0 root []), .base (.pushAll 0 [1] [] root 1), .sendSup 0,
   .hubSupAccept 0 [1] [] root 1 [] [], .base (.learn 0 .accepted 1 1),
   .base (.userOp 0 1 []), .base (.pushAll 0 [2] [] 1 2), .sendSup 0,
   .hubSupAccept 0 [2] [] 1 2 [] [], .base (.learn 0 .accepted 2 2)]

/-- Node 0 abandons operation 1 and pushes the fix-up, 3, with its dropped set. -/
def supersede : List SAction :=
  [.abandon 0 [1], .base (.userOp 0 2 []), .base (.pushAll 0 [3] [] 2 3), .sendSup 0,
   .hubSupAccept 0 [3] [] 2 3 [] [1], .base (.learn 0 .accepted 3 3)]

/-- Node 1 fetches the head and the hub's records, catches up, and takes them. -/
def catchUp : List SAction :=
  [.base (.fetchAll 1 root []), .base (.hubFetch 1 root []), .sendD 1,
   .base (.learn 1 .head 3 3), .base (.recvOps 1 [1, 2, 3]), .base (.recvObjs 1 []),
   .base (.realize 1 1), .base (.realize 1 2), .base (.realize 1 3), .base (.advance 1),
   .adopt 1 [[1]]]

-- The run is accepted and converges: both nodes at the hub's head, with its dropped set.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp) with
  | .ok ses => ses.recs == [[1]] && ses.es.hub.head == 3 && ses.sconvergedE 2 &&
      ses.smeasureE 2 == (0, 0, (0, 0, 0, 0, 0, 0))
  | .error _ => false

-- Until node 1 takes the hub's records, it has dropped less than the hub: `mLag` counts it.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp.dropLast) with
  | .ok ses => (ses.smeasureE 2).2.1 == 1 && !ses.sconvergedE 2
  | .error _ => false

-- jj never abandons a head.
#guard errorOf (srun 2 initSE (pushes ++ [.abandon 0 [2]])) ==
  "abandon: [2] drops a head of node 0"

-- A push whose node hasn't the hub's records is refused, not accepted.
#guard errorOf (srun 2 initSE (pushes ++ supersede ++
    [.base (.userOp 1 root []), .base (.pushAll 1 [4] [] 3 4), .sendSup 1,
     .hubSupAccept 1 [4] [] 3 4 [] []])) ==
  "hubSupAccept: node 1's records are not the hub's"
#guard errorOf (srun 2 initSE (pushes ++ supersede ++
    [.base (.userOp 1 root []), .base (.pushAll 1 [4] [] 3 4), .sendSup 1,
     .hubPushRefuse 1 [4] [] 3 4 [] []])) == "(accepted)"

-- The hub never takes a head it dropped.
#guard errorOf (srun 2 initSE (pushes ++ [.abandon 0 [1], .base (.pushAll 0 [1] [] 2 1),
    .sendSup 0, .hubSupAccept 0 [1] [] 2 1 [] [1]])) ==
  "hubSupAccept: new head 1 is dropped"

end Musubi.Exec.SupersedeTest

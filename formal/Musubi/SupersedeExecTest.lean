/-
Smoke test of the executable model with supersedes, checked at build time: node 0 pushes two
operations, abandons the first, and publishes the abandon with a fix-up operation; node 1
fetches the hub's head with its records, catches up and takes them; then node 0 takes them, the
hub prunes them, and takes a push and another record after. A node that takes fewer records
from an announcement older than the prune takes the hub's again. Then the guards: no head
abandoned, no push accepted whose records aren't the hub's, or to a head it or the push drops,
nothing pruned that a node has never taken, no op named that a record its node took drops,
and no stale push accepted to a head the hub has pruned. `test/smoke.jsonl` replays the run
through the oracle.
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
  [.base (.userOp 0 root []), .base (.pushAll 0 [1] [] root 1), .sendSup 0 1,
   .hubSupAccept 0 [1] [] root 1 [] [], .base (.learn 0 .accepted 1 1),
   .base (.userOp 0 1 []), .base (.pushAll 0 [2] [] 1 2), .sendSup 0 2,
   .hubSupAccept 0 [2] [] 1 2 [] [], .base (.learn 0 .accepted 2 2)]

/-- Node 0 abandons operation 1 and pushes the fix-up, 3, with its dropped set. -/
def supersede : List SAction :=
  [.abandon 0 [1], .base (.userOp 0 2 []), .base (.pushAll 0 [3] [] 2 3), .sendSup 0 3,
   .hubSupAccept 0 [3] [] 2 3 [] [1], .base (.learn 0 .accepted 3 3)]

/-- Node 1 fetches the head and the hub's records, catches up, and takes them. -/
def catchUp : List SAction :=
  [.base (.fetchAll 1 root []), .base (.hubFetch 1 root []), .sendD 1,
   .base (.learn 1 .head 3 3), .base (.recvOps 1 [1, 2, 3]), .base (.recvObjs 1 []),
   .base (.realize 1 1), .base (.realize 1 2), .base (.realize 1 3), .base (.advance 1),
   .adopt 1 [[1]]]

/-- Node 0 takes the hub's records too, and the hub prunes them. -/
def pruning : List SAction := [.sendD 0, .adopt 0 [[1]], .prune 1]

/-- Then node 0 pushes 4, with the hub's records, which the hub accepts; makes 5, abandons 4,
and pushes the fix-up, 6, which the hub takes with a record of 4. -/
def afterPruning : List SAction :=
  [.base (.userOp 0 3 []), .base (.pushAll 0 [4] [] 3 4), .sendSup 0 4,
   .hubSupAccept 0 [4] [] 3 4 [[1]] [1], .base (.learn 0 .accepted 4 4),
   .base (.userOp 0 4 []), .abandon 0 [4], .base (.userOp 0 5 []),
   .base (.pushAll 0 [5, 6] [] 4 6), .sendSup 0 6,
   .hubSupAccept 0 [5, 6] [] 4 6 [[1]] [1, 4], .base (.learn 0 .accepted 5 6)]

-- The run is accepted and converges: both nodes at the hub's head, with its dropped set.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp) with
  | .ok ses => ses.recs == [[1]] && ses.es.hub.head == 3 && ses.sconvergedE 2 &&
      ses.smeasureE 2 == (0, 0, (0, 0, 0, 0, 0, 0))
  | .error _ => false

-- So it stays once the hub prunes the record, which it remembers none of.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp ++ pruning) with
  | .ok ses => ses.pruned == 1 && ses.remDL == [] && ses.sconvergedE 2 &&
      ses.smeasureE 2 == (0, 0, (0, 0, 0, 0, 0, 0))
  | .error _ => false

-- After pruning, the hub accepts a push with its records, and takes another record.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp ++ pruning ++ afterPruning) with
  | .ok ses => ses.recs == [[1], [4]] && ses.pruned == 1 && ses.remDL == [4] &&
      ses.es.hub.head == 6
  | .error _ => false

-- Going back to a head from before the prune, the hub remembers the record again; to the head
-- it pruned at, it doesn't.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp ++ pruning ++ afterPruning ++
    [.base (.hubRegress 2)]) with
  | .ok ses => ses.recs == [] && ses.pruned == 0
  | .error _ => false
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp ++ pruning ++ afterPruning ++
    [.base (.hubRegress 3)]) with
  | .ok ses => ses.recs == [[1]] && ses.pruned == 1
  | .error _ => false

-- Node 1, told of the hub's records before there were any, takes that announcement after the
-- prune, and holds none of the records; then it takes the hub's, having held the pruned one.
#guard match srun 2 initSE (pushes ++ [.sendD 1] ++ supersede ++ catchUp ++ pruning ++
    [.adopt 1 [], .sendD 1, .adopt 1 [[1]]]) with
  | .ok ses => ses.appliedF 1 == [[1]] && ses.pruned == 1 && ses.sconvergedE 2
  | .error _ => false

-- A node has held no records but none, to begin with.
#guard !(initSE.heldPrefix 0 [[1]] 1) && initSE.heldPrefix 0 [[1]] 0

-- The hub prunes nothing a node has never taken: node 0 published the record, but hasn't taken
-- it; and node 1 hasn't taken the second.
#guard errorOf (srun 2 initSE (pushes ++ supersede ++ catchUp ++ [.prune 1])) ==
  "prune: a node has never taken the first 1 records"
#guard errorOf (srun 2 initSE (pushes ++ supersede ++ catchUp ++ pruning ++ afterPruning ++
    [.sendD 0, .adopt 0 [[1], [4]], .prune 2])) ==
  "prune: a node has never taken the first 2 records"

-- No node pushes an operation that a record it took drops.
#guard errorOf (srun 2 initSE (pushes ++ supersede ++ catchUp ++ [.sendSup 1 1])) ==
  "sendSup: node 1 pushes 1, which a record it took drops"

-- The hub refuses a push to a head the push drops, though the node may name it.
#guard errorOf (srun 2 initSE (pushes ++ [.abandon 0 [1], .sendSup 0 1,
    .hubSupAccept 0 [] [] 2 1 [] [1]])) ==
  "hubSupAccept: new head 1 is dropped"

/-- One node makes 1, 2 and 3, and pushes 2 from 1; then it abandons 2, publishes that with a
push to 1, takes the record, and the hub prunes it. The hub's head is 1 again, as the push to 2
expects. -/
def stale : List SAction :=
  [.base (.userOp 0 root []), .base (.userOp 0 1 []), .base (.userOp 0 2 []),
   .base (.pushAll 0 [1, 2] [] 1 2), .sendSup 0 2,
   .abandon 0 [2], .base (.pushAll 0 [1] [] root 1), .sendSup 0 1,
   .hubSupAccept 0 [1] [] root 1 [] [2], .sendD 0, .adopt 0 [[2]], .prune 1]

#guard match srun 1 initSE stale with
  | .ok ses => ses.es.hub.head == 1 && ses.pruned == 1 && ses.remDL == []
  | .error _ => false

-- The push to 2 from before the abandon, which the hub no longer knows the id of, carries
-- records that aren't the hub's: refused, as a supersede and as a plain push.
#guard errorOf (srun 1 initSE (stale ++ [.hubSupAccept 0 [1, 2] [] 1 2 [] []])) ==
  "hubSupAccept: node 0's records are not the hub's"
#guard errorOf (srun 1 initSE (stale ++ [.base (.hubPushAccept 0 [1, 2] [] 1 2)])) ==
  "supersede: the hub's new head 2 comes without its records, or is one it dropped"
#guard errorOf (srun 1 initSE (stale ++ [.hubPushRefuse 0 [1, 2] [] 1 2 [] []])) ==
  "(accepted)"

-- Until node 1 takes the hub's records, it has dropped less than the hub: `mLag` counts it.
#guard match srun 2 initSE (pushes ++ supersede ++ catchUp.dropLast) with
  | .ok ses => (ses.smeasureE 2).2.1 == 1 && !ses.sconvergedE 2
  | .error _ => false

-- jj never abandons a head.
#guard errorOf (srun 2 initSE (pushes ++ [.abandon 0 [2]])) ==
  "abandon: [2] drops a head of node 0"

-- A push whose node hasn't the hub's records is refused, not accepted.
#guard errorOf (srun 2 initSE (pushes ++ supersede ++
    [.base (.userOp 1 root []), .base (.pushAll 1 [4] [] 3 4), .sendSup 1 4,
     .hubSupAccept 1 [4] [] 3 4 [] []])) ==
  "hubSupAccept: node 1's records are not the hub's"
#guard errorOf (srun 2 initSE (pushes ++ supersede ++
    [.base (.userOp 1 root []), .base (.pushAll 1 [4] [] 3 4), .sendSup 1 4,
     .hubPushRefuse 1 [4] [] 3 4 [] []])) == "(accepted)"

-- The hub never takes a head it dropped: a push to 1 from before the abandon carries records
-- that aren't the hub's.
#guard errorOf (srun 2 initSE (pushes ++ supersede ++ [.base (.pushAll 0 [1] [] 3 1),
    .hubSupAccept 0 [1] [] 3 1 [] []])) ==
  "hubSupAccept: node 0's records are not the hub's"

end Musubi.Exec.SupersedeTest

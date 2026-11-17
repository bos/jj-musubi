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

namespace Musubi.Exec.ContractedTest

/-! ## Pushes that contract their expected head, and frontiers through surviving images

The receiver has independent work 3 and has dropped the hub's head 2, whose survivor is 1. The
node that sent the push need not run again: advance adds 1, a merge retains 1 and 3, and the hub
takes the push with its drop. Original ancestry of 2 is false at acceptance. -/

def receiver : SEState :=
  { initSE with
    es := { initE with
      next := 4
      ops := [⟨1, [0], [], some 0, false, 0⟩,
              ⟨2, [1], [], some 0, false, 0⟩,
              ⟨3, [0], [], some 1, false, 0⟩]
      hub := { initE.hub with ops := [0, 1, 2], head := 2, seq := 1, hist := [(1, 2)] }
      nodes := [(1, { ENode.init with lops := [0, 1, 3], heads := [3], known := ⟨1, 2⟩ })] }
    nodeD := [(1, [2])] }

def run (s : SEState) : List SAction → Except String SEState
  | [] => .ok s
  | a :: as => do run (← sexecStep 2 s a) as

def repair : List SAction :=
  [.base (.advance 1), .base (.merge 1 [1, 3] []),
   .base (.pushAll 1 [3, 4] [] 2 4), .sendSup 1 4,
   .hubSupAccept 1 [3, 4] [] 2 4 [] [2]]

#guard match sexecStep 2 receiver (.base (.advance 1)) with
  | .ok s => seteq (s.es.nodeOf 1).heads [1, 3] && !(s.es.nodeOf 1).heads.contains 2
  | .error _ => false

#guard match run receiver repair with
  | .ok s => s.es.hub.head == 4 && s.recs == [[2]] &&
      !(ancB s.es.parF 2 4) && Contract.belowB s.es.parF [2].contains 2 4
  | .error _ => false

-- Knowing the dropped body's name is insufficient: every surviving image must be local.
def missingImage : SEState :=
  { receiver with es := receiver.es.setNode 1 { receiver.es.nodeOf 1 with lops := [0, 2, 3] } }
#guard !advanceB 2 missingImage 1

-- Neither a dropped target nor a push without its expected survivor is accepted.
#guard match run receiver
    [.base (.userOp 1 3 []), .base (.pushAll 1 [3, 4] [] 2 4), .sendSup 1 4] with
  | .ok s => !acceptB s 1 [3, 4] [] 2 4 [] [2]
  | .error _ => false
def withDroppedBody : SEState :=
  { receiver with es := receiver.es.setNode 1 { receiver.es.nodeOf 1 with lops := [0, 1, 2, 3] } }

-- The original progress component rises from one head to two while mAdv stays one.
-- The extended check counts uncovered images, which falls before the merge count rises.
#guard match sexecStep 2 withDroppedBody (.base (.advance 1)) with
  | .error _ => false
  | .ok s => s.es.advE 1 == 1 && withDroppedBody.es.advE 1 == 1 &&
      s.es.multiE 1 == 1 && withDroppedBody.es.multiE 1 == 0 &&
      s.advCE 1 == 0 && withDroppedBody.advCE 1 == 1 &&
      rankLess (s.recordRankCE 2) (withDroppedBody.recordRankCE 2)

-- A dropped merge can leave a receiver at one image or at their common ancestor. Such a
-- receiver is already unsettled: adding the other images must not increase earlier credit.
def mergeReceiver (atParent : Bool) : SEState :=
  { initSE with
    es := { initE with
      next := 5
      ops := [⟨1, [0], [], some 0, false, 0⟩, ⟨2, [1], [], some 0, false, 0⟩,
              ⟨3, [1], [], some 0, false, 0⟩, ⟨4, [2, 3], [], some 0, true, 0⟩]
      hub := { initE.hub with ops := [0, 1, 2, 3, 4], head := 4, seq := 1, hist := [(1, 4)] }
      nodes := [(1, { ENode.init with
        lops := [0, 1, 2, 3, 4],
        heads := [if atParent then 2 else 1], known := ⟨1, 4⟩ })] }
    nodeD := [(1, [4])] }

#guard ([true, false] : List Bool).all fun atParent =>
  let before := mergeReceiver atParent
  match sexecStep 2 before (.base (.advance 1)) with
  | .error _ => false
  | .ok after => !before.settledCE 1 && !after.settledCE 1 &&
      seteq (after.es.nodeOf 1).heads [2, 3] &&
      rankLess (after.recordRankCE 2) (before.recordRankCE 2)
#guard match run withDroppedBody
    [.base (.pushAll 1 [] [] 2 2), .sendSup 1 2] with
  | .ok s => !acceptB s 1 [] [] 2 2 [] [2]
  | .error _ => false

-- A follower still at the raw dropped head switches its frontier and record custody in the
-- same backend boundary. A restart never observes a head-before-custody state.
#guard match run receiver repair with
  | .error _ => false
  | .ok accepted =>
    let nd := { accepted.es.nodeOf 1 with
      lops := [0, 1, 2, 3, 4], heads := [2], known := ⟨2, 4⟩ }
    let follower := { accepted with
      nodeD := [], es := accepted.es.setNode 1 nd,
      dmsgs := [⟨1, ⟨[[2]], 0⟩⟩] }
    match sexecStep 2 follower (.advancePrepared 1 [[2]]) with
    | .error _ => false
    | .ok switched =>
      (switched.es.nodeOf 1).heads == [4] && switched.nodeDF 1 == [2] &&
        switched.appliedF 1 == [[2]]

-- A matching, closed contracted push cannot also be rejected on original ancestry.
#guard match run receiver (repair.take 4) with
  | .error _ => false
  | .ok s =>
    acceptB s 1 [3, 4] [] 2 4 [] [2] &&
      match sexecStep 2 s (.hubSupReject 1 [3, 4] [] 2 4 [] [2]),
          sexecStep 2 s (.base (.hubPushReject 1 [3, 4] [] 2 4)) with
      | .error _, .error _ => true
      | _, _ => false

-- A contracted acceptance can leave an older retained head outside the current closure.
-- Normal store loss preserves all replayed heads; corruption takes the remake path instead.
#guard match run receiver repair with
  | .error _ => false
  | .ok s =>
    match sexecStep 2 s (.base (.hubForget [0, 1, 3, 4] [])),
        run s [.base (.hubRegress 0), .base (.hubForget [0] [])] with
    | .error _, .ok remade => remade.es.hub.head == 0 && remade.es.hub.ops == [0]
    | _, _ => false

def objectReceiver : SEState :=
  let ops := receiver.es.ops.map fun op => if op.id == 2 then { op with objs := [10] } else op
  { receiver with es := { receiver.es with ops := ops, hub := { receiver.es.hub with objs := [10] } } }

-- Historical-only objects can be lost while the current head remains healthy. The damaged
-- target is not a normal rollback result in this abstraction; explicit recovery is modeled
-- separately, without claiming that native startup detects every such damaged prefix.
#guard match run objectReceiver repair with
  | .error _ => false
  | .ok s =>
    match sexecStep 2 s (.base (.hubForget [0, 1, 2, 3, 4] [])) with
    | .error _ => false
    | .ok lost =>
      lost.es.hub.ops.contains 2 && !lost.es.hub.objs.contains 10 && !lost.es.closedB 2 &&
        match sexecStep 2 lost (.base (.hubRegress 1)),
            run lost [.base (.hubRegress 0), .base (.hubForget [0] [])] with
        | .error _, .ok remade => remade.es.hub.head == 0
        | _, _ => false

end Musubi.Exec.ContractedTest

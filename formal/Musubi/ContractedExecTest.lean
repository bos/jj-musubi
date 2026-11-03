/-
The receiver has independent work 3 and has dropped the hub's head 2, whose survivor is 1.
The old sender need not run again: advance adds 1, a merge retains 1 and 3, and the hub takes
the push with its drop. Original ancestry of 2 is deliberately false at acceptance.
-/
import Musubi.ContractedExec
import Musubi.ContractedMeasure

namespace Musubi.Exec.ContractedTest

def receiver : SEState :=
  { initSE with
    es := { initE with
      next := 4
      ops := [⟨1, [0], [], some 0, false, 0⟩,
              ⟨2, [1], [], some 0, false, 0⟩,
              ⟨3, [0], [], some 1, false, 0⟩]
      hub := { initE.hub with ops := [0, 1, 2], head := 2, seq := 1, hist := [(1, 2)] }
      nodes := [(1, { ENode.init with lops := [0, 1, 3], heads := [3], known := (1, 2) })] }
    nodeD := [(1, [2])] }

def run (s : SEState) : List SAction → Except String SEState
  | [] => .ok s
  | a :: as => do run (← cexecStep 2 s a) as

def repair : List SAction :=
  [.base (.advance 1), .base (.merge 1 [1, 3] []),
   .base (.pushAll 1 [3, 4] [] 2 4), .sendSup 1 4,
   .hubSupAccept 1 [3, 4] [] 2 4 [] [2]]

#guard match sexecStep 2 receiver (.base (.advance 1)) with
  | .error _ => true
  | .ok _ => false

#guard match cexecStep 2 receiver (.base (.advance 1)) with
  | .ok s => seteq (s.es.nodeOf 1).heads [1, 3] && !(s.es.nodeOf 1).heads.contains 2
  | .error _ => false

#guard match run receiver repair with
  | .ok s => s.es.hub.head == 4 && s.recs == [[2]] &&
      !(ancB s.es.parF 2 4) && Contract.belowB s.es.parF [2].contains 2 4
  | .error _ => false

-- Knowing the dropped body's name is insufficient: every surviving image must be local.
def missingImage : SEState :=
  { receiver with es := receiver.es.setNode 1 { receiver.es.nodeOf 1 with lops := [0, 2, 3] } }
#guard !imageAdvanceB 2 missingImage 1

-- Neither a dropped target nor a push without its expected survivor is accepted.
#guard match run receiver
    [.base (.userOp 1 3 []), .base (.pushAll 1 [3, 4] [] 2 4), .sendSup 1 4] with
  | .ok s => !imageAcceptB s 1 [3, 4] [] 2 4 [] [2]
  | .error _ => false
def withDroppedBody : SEState :=
  { receiver with es := receiver.es.setNode 1 { receiver.es.nodeOf 1 with lops := [0, 1, 2, 3] } }

-- The original progress component rises from one head to two while mAdv stays one.
-- The extended check counts uncovered images, which falls before the merge count rises.
#guard match cexecStep 2 withDroppedBody (.base (.advance 1)) with
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
        heads := [if atParent then 2 else 1], known := (1, 4) })] }
    nodeD := [(1, [4])] }

#guard ([true, false] : List Bool).all fun atParent =>
  let before := mergeReceiver atParent
  match cexecStep 2 before (.base (.advance 1)) with
  | .error _ => false
  | .ok after => !before.settledCE 1 && !after.settledCE 1 &&
      seteq (after.es.nodeOf 1).heads [2, 3] &&
      rankLess (after.recordRankCE 2) (before.recordRankCE 2)
#guard match run withDroppedBody
    [.base (.pushAll 1 [] [] 2 2), .sendSup 1 2] with
  | .ok s => !imageAcceptB s 1 [] [] 2 2 [] [2]
  | .error _ => false

-- A follower still at the raw dropped head switches its frontier and record custody in the
-- same backend boundary. A restart never observes a head-before-custody state.
#guard match run receiver repair with
  | .error _ => false
  | .ok accepted =>
    let nd := { accepted.es.nodeOf 1 with
      lops := [0, 1, 2, 3, 4], heads := [2], known := (2, 4) }
    let follower := { accepted with
      nodeD := [], es := accepted.es.setNode 1 nd,
      dmsgs := [(1, [[2]], 0)] }
    match cexecAction 2 follower (.advancePrepared 1 [[2]]) with
    | .error _ => false
    | .ok switched =>
      (switched.es.nodeOf 1).heads == [4] && switched.nodeDF 1 == [2] &&
        switched.appliedF 1 == [[2]]

-- A matching, closed contracted push cannot also be rejected on original ancestry.
#guard match run receiver (repair.take 4) with
  | .error _ => false
  | .ok s =>
    imageAcceptB s 1 [3, 4] [] 2 4 [] [2] &&
      match cexecAction 2 s (.reject 1 [3, 4] [] 2 4 [] [2]),
          cexecStep 2 s (.base (.hubPushReject 1 [3, 4] [] 2 4)) with
      | .error _, .error _ => true
      | _, _ => false

-- A contracted acceptance can leave an older retained head outside the current closure.
-- Normal store loss preserves all replayed heads; corruption takes the remake path instead.
#guard match run receiver repair with
  | .error _ => false
  | .ok s =>
    match sexecStep 2 s (.base (.hubForget [0, 1, 3, 4] [])),
        cexecStep 2 s (.base (.hubForget [0, 1, 3, 4] [])),
        run s [.base (.hubRegress 0), .base (.hubForget [0] [])] with
    | .ok _, .error _, .ok remade => remade.es.hub.head == 0 && remade.es.hub.ops == [0]
    | _, _, _ => false

def objectReceiver : SEState :=
  let ops := receiver.es.ops.map fun op => if op.id == 2 then { op with objs := [10] } else op
  { receiver with es := { receiver.es with ops := ops, hub := { receiver.es.hub with objs := [10] } } }

-- Historical-only objects can be lost while the current head remains healthy. The damaged
-- target is not a normal rollback result in this abstraction; explicit recovery is modeled
-- separately, without claiming that native startup detects every such damaged prefix.
#guard match run objectReceiver repair with
  | .error _ => false
  | .ok s =>
    match cexecStep 2 s (.base (.hubForget [0, 1, 2, 3, 4] [])) with
    | .error _ => false
    | .ok lost =>
      lost.es.hub.ops.contains 2 && !lost.es.hub.objs.contains 10 && !lost.es.closedB 2 &&
        match cexecStep 2 lost (.base (.hubRegress 1)),
            run lost [.base (.hubRegress 0), .base (.hubForget [0] [])] with
        | .error _, .ok remade => remade.es.hub.head == 0
        | _, _ => false

end Musubi.Exec.ContractedTest

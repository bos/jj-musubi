/-
Smoke test of the executable model, checked at build time: a two-node run (user op, upload,
push, casAccept, a notification learned by the other node, fetch, realize, advance) and one
rejected action. `test/smoke.jsonl` replays the same run through the oracle.
-/
import Musubi.ExecSound

namespace Musubi.Exec.Test

open Musubi

def run (N : Nat) (es : EState) : List Action → Except String EState
  | [] => .ok es
  | a :: as => do run N (← execStep N es a) as

/-- Node 0 writes op 1 (requiring object 10) and pushes it before uploading. -/
def pre : List Action := [.userOp 0 root [10], .push 0 root 1]

/-- Upload, store, accept; node 0 learns `Accepted`, node 1 learns the notification, then
fetches, realizes, and advances. -/
def rest : List Action :=
  [.uploadOps 0 [1], .uploadObjs 0 [10], .hubPutOps 0 [1], .hubPutObjs 0 [10],
   .casAccept 0 root 1, .learn 0 .accepted 1 1, .learn 1 .notify 1 1,
   .fetchOps 1 [1], .hubGetOps 1 [1], .recvOps 1 [1],
   .fetchObjs 1 [10], .hubGetObjs 1 [10], .recvObjs 1 [10],
   .realize 1 1, .advance 1]

def errorOf : Except String EState → String
  | .error e => e
  | .ok _ => "(accepted)"

-- Accepting the Cas before the upload is rejected, naming the failed guard.
#guard errorOf (run 2 initE pre >>= fun es => execStep 2 es (.casAccept 0 root 1)) ==
  "casAccept: closure of 1 not stored at hub (missing op 1)"

-- The full run is accepted and ends with both nodes at the hub head.
#guard match run 2 initE (pre ++ rest) with
  | .ok es => es.hub.head == 1 && es.hub.seq == 1 && (es.nodeOf 0).heads == [1] &&
      (es.nodeOf 1).heads == [1] && (es.nodeOf 1).known == (1, 1)
  | .error _ => false

-- A stale notification is not learned twice.
#guard errorOf (run 2 initE (pre ++ rest ++ [.learn 1 .notify 1 1])) ==
  "learn: seq 1 not greater than known.seq 1"

-- Node 1 cannot fetch an operation outside anc*(known.head) (here before learning).
#guard errorOf (run 2 initE (pre ++ [.fetchOps 1 [1]])) ==
  "fetchOps: [1] not all in anc*(known.head = 0)"

/-- The same run with the merged requests: node 0's `push` uploads and is accepted at once,
and node 1's `fetch` brings the head with the operation and its object. -/
def merged : List Action :=
  [.userOp 0 root [10], .pushAll 0 [1] [10] root 1, .hubPushAccept 0 [1] [10] root 1,
   .learn 0 .accepted 1 1, .fetchAll 1 root [], .hubFetch 1 root [], .learn 1 .head 1 1,
   .recvOps 1 [1], .recvObjs 1 [10], .realize 1 1, .advance 1]

#guard match run 2 initE merged with
  | .ok es => es.hub.head == 1 && es.hub.seq == 1 && (es.nodeOf 1).heads == [1] &&
      (es.nodeOf 1).known == (1, 1)
  | .error _ => false

-- A push whose upload leaves the closure incomplete is rejected, and stores what it carried.
#guard errorOf (run 2 initE [.userOp 0 root [10], .pushAll 0 [1] [] root 1,
    .hubPushAccept 0 [1] [] root 1]) ==
  "hubPushAccept: closure of 1 not stored at hub (missing object 10 of op 1)"
#guard match run 2 initE [.userOp 0 root [10], .pushAll 0 [1] [] root 1,
    .hubPushReject 0 [1] [] root 1] with
  | .ok es => es.hub.ops.contains 1 && es.hub.head == root
  | .error _ => false

-- A fetch returns nothing below its base, and leaves out the haves.
#guard match run 2 initE (merged ++ [.userOp 1 1 [11], .pushAll 1 [2] [11] 1 2,
    .hubPushAccept 1 [2] [11] 1 2, .fetchAll 0 1 [11], .hubFetch 0 1 [11]]) with
  | .ok es => es.inNet (.ops 0 [2]) && es.inNet (.objs 0 [])
  | .error _ => false

end Musubi.Exec.Test

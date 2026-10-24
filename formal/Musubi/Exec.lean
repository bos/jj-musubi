/-
The executable model: finite, computable states, an `Action` vocabulary matching
`docs/internals/conformance.md`, and `execStep`, which evaluates every guard of the relational
model and names the guard that failed. `exec_sound` proves that every accepted action other than
`hubRegress` is a `Step` of the relational model between the abstracted states, and `exec_rsound`
that every accepted action is an `RStep`. A hive made again (`remakeActions`: the hub goes back to
the root, then forgets all else) is `State.remake` (`exec_remake`).
-/
import Musubi.Regress

namespace Musubi.Exec

open Musubi

/-! ## Finite state -/

/-- A created operation (the root, id 0, is implicit). -/
structure EOp where
  id : Nat
  parents : List Nat
  objs : List Nat
  creator : Option Nat
  isMerge : Bool
  birth : Nat
  deriving Repr

structure ENode where
  lops : List Nat
  lobj : List Nat
  heads : List Nat
  known : Nat × Nat
  sops : List Nat
  sobj : List Nat
  deriving Repr

def ENode.init : ENode := ⟨[root], [], [root], (0, root), [], []⟩

structure EHub where
  ops : List Nat
  objs : List Nat
  head : Nat
  seq : Nat
  /-- Ghost history, as an association list `seq ↦ head` (default `root`). -/
  hist : List (Nat × Nat)
  deriving Repr

/-- Finite messages. `notifyAll` is the hub's publication of a new head: it stands for
`head n notify sq h` for every node `n`. -/
inductive EMsg
  | getHead (n : Nat)
  | putOps (n : Nat) (S : List Nat)
  | putObjs (n : Nat) (S : List Nat)
  | getOps (n : Nat) (S : List Nat)
  | getObjs (n : Nat) (S : List Nat)
  | cas (n e d : Nat)
  | head (n : Nat) (k : HeadKind) (sq h : Nat)
  | ops (n : Nat) (S : List Nat)
  | objs (n : Nat) (S : List Nat)
  | stored (n : Nat)
  | push (n : Nat) (S O : List Nat) (e d : Nat)
  | fetch (n b : Nat) (H : List Nat)
  | notifyAll (sq h : Nat)
  deriving Repr

/-- The executable state. Operations, nodes and the ghost history are association lists;
sets are lists; `net` is a list read as a set. -/
structure EState where
  next : Nat
  ops : List EOp
  hub : EHub
  nodes : List (Nat × ENode)
  net : List EMsg
  deriving Repr

def initE : EState where
  next := 1
  ops := []
  hub := { ops := [root], objs := [], head := root, seq := 0, hist := [] }
  nodes := []
  net := []

/-! ## Lookups -/

namespace EState

def findOp (es : EState) (x : Nat) : Option EOp := es.ops.find? (fun o => o.id == x)
def parF (es : EState) (x : Nat) : List Nat := ((es.findOp x).map EOp.parents).getD []
def objsF (es : EState) (x : Nat) : List Nat := ((es.findOp x).map EOp.objs).getD []
def creatorF (es : EState) (x : Nat) : Option Nat := ((es.findOp x).map EOp.creator).getD none
def isMergeF (es : EState) (x : Nat) : Bool := ((es.findOp x).map EOp.isMerge).getD false
def birthF (es : EState) (x : Nat) : Nat := ((es.findOp x).map EOp.birth).getD 0

end EState

def EHub.histF (h : EHub) (i : Nat) : Nat :=
  ((h.hist.find? (fun p => p.1 == i)).map Prod.snd).getD root

def nodeAt (l : List (Nat × ENode)) (i : Nat) : ENode :=
  ((l.find? (fun p => p.1 == i)).map Prod.snd).getD ENode.init

def EState.nodeOf (es : EState) (i : Nat) : ENode := nodeAt es.nodes i

/-- Replace node `n`'s entry. -/
def setN (l : List (Nat × ENode)) (n : Nat) (nd : ENode) : List (Nat × ENode) :=
  (n, nd) :: l.filter (fun p => p.1 != n)

/-- Set union on lists. -/
def union (l S : List Nat) : List Nat := l ++ S.filter (fun x => !l.contains x)

/-- Set equality on lists. -/
def seteq (a b : List Nat) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

/-! ## Abstraction -/

def setP (l : List Nat) : OSet := (· ∈ l)

def ENode.abs (nd : ENode) : Node where
  lops := setP nd.lops
  lobj := setP nd.lobj
  heads := setP nd.heads
  known := nd.known
  sops := setP nd.sops
  sobj := setP nd.sobj

/-- The relational message a (non-broadcast) finite message denotes. -/
def EMsg.toMsg : EMsg → Msg
  | .getHead n => .getHead n
  | .putOps n S => .putOps n (setP S)
  | .putObjs n S => .putObjs n (setP S)
  | .getOps n S => .getOps n (setP S)
  | .getObjs n S => .getObjs n (setP S)
  | .cas n e d => .cas n e d
  | .head n k sq h => .head n k sq h
  | .ops n S => .ops n (setP S)
  | .objs n S => .objs n (setP S)
  | .stored n => .stored n
  | .push n S O e d => .push n (setP S) (setP O) e d
  | .fetch n b H => .fetch n b (setP H)
  | .notifyAll sq h => .head 0 .notify sq h

/-- The relational messages a finite message stands for. -/
def EMsg.covers : EMsg → Msg → Prop
  | .notifyAll sq h, m => ∃ n, m = .head n .notify sq h
  | .getHead n, m => m = .getHead n
  | .putOps n S, m => m = .putOps n (setP S)
  | .putObjs n S, m => m = .putObjs n (setP S)
  | .getOps n S, m => m = .getOps n (setP S)
  | .getObjs n S, m => m = .getObjs n (setP S)
  | .cas n e d, m => m = .cas n e d
  | .head n k sq h, m => m = .head n k sq h
  | .ops n S, m => m = .ops n (setP S)
  | .objs n S, m => m = .objs n (setP S)
  | .stored n, m => m = .stored n
  | .push n S O e d, m => m = .push n (setP S) (setP O) e d
  | .fetch n b H, m => m = .fetch n b (setP H)

def abs (es : EState) : State where
  U := { next := es.next, par := es.parF, objs := es.objsF, creator := es.creatorF,
         isMerge := es.isMergeF, birth := es.birthF }
  hub := { ops := setP es.hub.ops, objs := setP es.hub.objs, head := es.hub.head,
           seq := es.hub.seq, hist := es.hub.histF }
  node := fun i => (es.nodeOf i).abs
  net := fun m => ∃ em ∈ es.net, em.covers m

/-! ## Deciding `anc*`

Since parents have smaller ids, `anc*(x)` is computed by one downward sweep from `x`. -/

/-- `marks par x k` is the set of `y` with `x - k ≤ y ≤ x` and `y ∈ anc*(x)`. -/
def marks (par : Nat → List Nat) (x : Nat) : Nat → List Nat
  | 0 => [x]
  | k + 1 =>
    let M := marks par x k
    if M.any (fun z => (par z).contains (x - (k + 1))) then (x - (k + 1)) :: M else M

/-- `anc*(x)` as a list. -/
def ancL (par : Nat → List Nat) (x : Nat) : List Nat := marks par x x

def ancB (par : Nat → List Nat) (a x : Nat) : Bool := (ancL par x).contains a

/-- `max(T)`. -/
def maxL (par : Nat → List Nat) (T : List Nat) : List Nat :=
  T.filter (fun x => T.all (fun y => !(ancB par x y) || x == y))

/-! ## Message matching -/

def matchB : EMsg → EMsg → Bool
  | .getHead a, .getHead b => a == b
  | .putOps a S, .putOps b T => a == b && seteq S T
  | .putObjs a S, .putObjs b T => a == b && seteq S T
  | .getOps a S, .getOps b T => a == b && seteq S T
  | .getObjs a S, .getObjs b T => a == b && seteq S T
  | .cas a e d, .cas b e' d' => a == b && e == e' && d == d'
  | .head a k s h, .head b k' s' h' => a == b && k == k' && s == s' && h == h'
  | .ops a S, .ops b T => a == b && seteq S T
  | .objs a S, .objs b T => a == b && seteq S T
  | .stored a, .stored b => a == b
  | .push a S O e d, .push b T P e' d' =>
    a == b && seteq S T && seteq O P && e == e' && d == d'
  | .fetch a c H, .fetch b c' H' => a == b && c == c' && seteq H H'
  | .notifyAll s h, .head _ k s' h' => k == .notify && s == s' && h == h'
  | .notifyAll s h, .notifyAll s' h' => s == s' && h == h'
  | _, _ => false

/-- The message is (covered by something) in the network. -/
def EState.inNet (es : EState) (m : EMsg) : Bool := es.net.any (fun em => matchB em m)

/-! ## Transitions -/

namespace EState

def send (es : EState) (m : EMsg) : EState :=
  if es.inNet m then es else { es with net := es.net ++ [m] }

def setNode (es : EState) (n : Nat) (nd : ENode) : EState :=
  { es with nodes := setN es.nodes n nd }

def createOp (es : EState) (n : Nat) (L O : List Nat) (mg : Bool) (H' : List Nat) : EState :=
  { es with
    next := es.next + 1
    ops := ⟨es.next, L, O, some n, mg, es.hub.seq⟩ :: es.ops
    nodes := setN es.nodes n
      { es.nodeOf n with
        lops := union (es.nodeOf n).lops [es.next]
        lobj := union (es.nodeOf n).lobj O
        heads := H' } }

def userOp (es : EState) (n p : Nat) (O : List Nat) : EState :=
  es.createOp n [p] O false
    (maxL (upd es.parF es.next [p]) ((es.nodeOf n).heads.filter (· != p) ++ [es.next]))

def mergeOp (es : EState) (n : Nat) (L O : List Nat) : EState :=
  es.createOp n L O true [es.next]

def hubStoreOps (es : EState) (S : List Nat) : EState :=
  { es with hub := { es.hub with ops := union es.hub.ops S } }

def hubStoreObjs (es : EState) (S : List Nat) : EState :=
  { es with hub := { es.hub with objs := union es.hub.objs S } }

def hubStore (es : EState) (S O : List Nat) : EState := (es.hubStoreOps S).hubStoreObjs O

/-- The stored operations in `anc*(head) \ anc*(b)`, which a `fetch` returns. -/
def sinceOpsL (es : EState) (b : Nat) : List Nat :=
  (ancL es.parF es.hub.head).filter (fun x => !ancB es.parF x b && es.hub.ops.contains x)

/-- The stored objects they require, less the haves `H`. -/
def sinceObjsL (es : EState) (b : Nat) (H : List Nat) : List Nat :=
  ((es.sinceOpsL b).flatMap es.objsF).filter (fun o => !H.contains o && es.hub.objs.contains o)

/-- The hub goes back to the head it accepted at `i`. The ghost history is kept whole:
`histF` finds the newest entry for a sequence number, so the next accept overwrites
entry `i + 1` as the relational `hubAccept` does. -/
def regress (es : EState) (i : Nat) : EState :=
  { es with hub := { es.hub with head := es.hub.histF i, seq := i } }

/-- The hub keeps only `S` and `O` of what it stores (`hubForget`). -/
def forget (es : EState) (S O : List Nat) : EState :=
  { es with hub := { es.hub with ops := S, objs := O } }

def hubAccept (es : EState) (d : Nat) : EState :=
  { es with hub := { es.hub with head := d, seq := es.hub.seq + 1,
                                 hist := (es.hub.seq + 1, d) :: es.hub.hist } }

/-- Every recorded operation's parents are below it. -/
def parOK (es : EState) : Bool := es.ops.all (fun o => o.parents.all (· < o.id))

/-- `closure(d) ⊆ ops ∪ objects` at the hub. -/
def closedB (es : EState) (d : Nat) : Bool :=
  (ancL es.parF d).all (fun y => es.hub.ops.contains y && (es.objsF y).all (es.hub.objs.contains ·))

/-- Explanation of why `closure(d)` is not stored. -/
def missingMsg (es : EState) (d : Nat) : String :=
  match (ancL es.parF d).find? (fun y => !es.hub.ops.contains y) with
  | some y => s!"missing op {y}"
  | none =>
    match (ancL es.parF d).findSome? (fun y =>
        ((es.objsF y).find? (fun o => !es.hub.objs.contains o)).map (fun o => (y, o))) with
    | some (y, o) => s!"missing object {o} of op {y}"
    | none => "nothing missing"

end EState

/-! ## Actions -/

/-- The action vocabulary of `docs/internals/conformance.md`: one constructor per relational step
that the conformance tests exercise. -/
inductive Action
  | userOp (node parent : Nat) (objs : List Nat)
  | merge (node : Nat) (parents objs : List Nat)
  | getHead (node : Nat)
  | learn (node : Nat) (headKind : HeadKind) (seq head : Nat)
  | fetchOps (node : Nat) (ops : List Nat)
  | fetchObjs (node : Nat) (objs : List Nat)
  | recvOps (node : Nat) (ops : List Nat)
  | recvObjs (node : Nat) (objs : List Nat)
  | realize (node opId : Nat)
  | advance (node : Nat)
  | uploadOps (node : Nat) (ops : List Nat)
  | uploadObjs (node : Nat) (objs : List Nat)
  | push (node expected new : Nat)
  | pushAll (node : Nat) (ops objs : List Nat) (expected new : Nat)
  | fetchAll (node base : Nat) (haves : List Nat)
  | crashNode (node : Nat)
  | loseKnown (node : Nat)
  | loseVolatile (node : Nat)
  | hubGetHead (node : Nat)
  | hubPutOps (node : Nat) (ops : List Nat)
  | hubPutObjs (node : Nat) (objs : List Nat)
  | hubGetOps (node : Nat) (ops : List Nat)
  | hubGetObjs (node : Nat) (objs : List Nat)
  | casIdem (node expected new : Nat)
  | casAccept (node expected new : Nat)
  | casReject (node expected new : Nat)
  | hubPushIdem (node : Nat) (ops objs : List Nat) (expected new : Nat)
  | hubPushAccept (node : Nat) (ops objs : List Nat) (expected new : Nat)
  | hubPushReject (node : Nat) (ops objs : List Nat) (expected new : Nat)
  | hubPushIncomplete (node : Nat) (ops objs : List Nat) (expected new : Nat)
  | hubFetch (node base : Nat) (haves : List Nat)
  | crashHub
  /-- The hub keeps only `ops` and `objs` of what it stores, which must hold
  `closure(head)`. -/
  | hubForget (ops objs : List Nat)
  /-- The hub goes back to the head it accepted at `seq` (`Regress.lean`): not a `Step`, but
  an `RStep`. -/
  | hubRegress (seq : Nat)
  deriving Repr

/-- Whether an action is the hub going back, which only the extended system allows. -/
def Action.goesBack : Action → Bool
  | .hubRegress _ => true
  | _ => false

/-- Check a guard; on failure, report `msg`. -/
def req (c : Bool) (msg : Unit → String) (k : Unit → Except String EState) :
    Except String EState :=
  if c then k () else .error (msg ())

theorem req_ok {c : Bool} {msg : Unit → String} {k : Unit → Except String EState}
    {es' : EState} (h : req c msg k = .ok es') : c = true ∧ k () = .ok es' := by
  unfold req at h
  cases c with
  | false => cases h
  | true => exact ⟨rfl, h⟩

def showL (l : List Nat) : String := toString l

/-- One step, with every guard checked. Errors are `"<action>: <failed guard>"`. -/
def execCore (N : Nat) (es : EState) : Action → Except String EState
  | .userOp n p O =>
    req (decide (n < N)) (fun _ => s!"userOp: node {n} out of range") fun _ =>
    req ((es.nodeOf n).lops.contains p) (fun _ => s!"userOp: parent {p} not local on node {n}")
      fun _ =>
    req (decide (p < es.next)) (fun _ => s!"userOp: parent {p} not created (well-formedness)")
      fun _ =>
    .ok (es.userOp n p O)
  | .merge n L O =>
    req (decide (n < N)) (fun _ => s!"merge: node {n} out of range") fun _ =>
    req (L.all ((es.nodeOf n).heads.contains ·) && (es.nodeOf n).heads.all (L.contains ·))
      (fun _ => s!"merge: parents {showL L} do not enumerate heads {showL (es.nodeOf n).heads}")
      fun _ =>
    req (L.any (fun a => L.any (fun b => a != b)))
      (fun _ => s!"merge: fewer than two heads") fun _ =>
    req (L.all (· < es.next)) (fun _ => s!"merge: parent not created (well-formedness)")
      fun _ =>
    .ok (es.mergeOp n L O)
  | .getHead n =>
    req (decide (n < N)) (fun _ => s!"getHead: node {n} out of range") fun _ =>
    .ok (es.send (.getHead n))
  | .learn n k sq h =>
    req (decide (n < N)) (fun _ => s!"learn: node {n} out of range") fun _ =>
    req (es.inNet (.head n k sq h))
      (fun _ => s!"learn: head message ({sq}, {h}) for node {n} not in net") fun _ =>
    req (decide ((es.nodeOf n).known.1 < sq))
      (fun _ => s!"learn: seq {sq} not greater than known.seq {(es.nodeOf n).known.1}") fun _ =>
    .ok (es.setNode n { es.nodeOf n with known := (sq, h) })
  | .fetchOps n S =>
    req (decide (n < N)) (fun _ => s!"fetchOps: node {n} out of range") fun _ =>
    req (S.all (fun x => ancB es.parF x (es.nodeOf n).known.2))
      (fun _ => s!"fetchOps: {showL S} not all in anc*(known.head = {(es.nodeOf n).known.2})")
      fun _ =>
    .ok (es.send (.getOps n S))
  | .fetchObjs n S =>
    req (decide (n < N)) (fun _ => s!"fetchObjs: node {n} out of range") fun _ =>
    .ok (es.send (.getObjs n S))
  | .recvOps n S =>
    req (decide (n < N)) (fun _ => s!"recvOps: node {n} out of range") fun _ =>
    req (es.inNet (.ops n S)) (fun _ => s!"recvOps: ops reply {showL S} for node {n} not in net")
      fun _ =>
    .ok (es.setNode n { es.nodeOf n with sops := union (es.nodeOf n).sops S })
  | .recvObjs n S =>
    req (decide (n < N)) (fun _ => s!"recvObjs: node {n} out of range") fun _ =>
    req (es.inNet (.objs n S))
      (fun _ => s!"recvObjs: objs reply {showL S} for node {n} not in net") fun _ =>
    .ok (es.setNode n { es.nodeOf n with sobj := union (es.nodeOf n).sobj S })
  | .realize n x =>
    req (decide (n < N)) (fun _ => s!"realize: node {n} out of range") fun _ =>
    req ((es.nodeOf n).sops.contains x) (fun _ => s!"realize: op {x} not staged on node {n}")
      fun _ =>
    req ((es.parF x).all ((es.nodeOf n).lops.contains ·))
      (fun _ => s!"realize: parents {showL (es.parF x)} of op {x} not all local") fun _ =>
    req ((es.objsF x).all (fun o => (es.nodeOf n).lobj.contains o || (es.nodeOf n).sobj.contains o))
      (fun _ => s!"realize: objects {showL (es.objsF x)} of op {x} not all available") fun _ =>
    .ok (es.setNode n { es.nodeOf n with
      lops := union (es.nodeOf n).lops [x]
      lobj := union (es.nodeOf n).lobj (es.objsF x) })
  | .advance n =>
    req (decide (n < N)) (fun _ => s!"advance: node {n} out of range") fun _ =>
    req ((es.nodeOf n).lops.contains (es.nodeOf n).known.2)
      (fun _ => s!"advance: known.head {(es.nodeOf n).known.2} not local") fun _ =>
    req (!((es.nodeOf n).heads.any (fun h => ancB es.parF (es.nodeOf n).known.2 h)))
      (fun _ => s!"advance: known.head {(es.nodeOf n).known.2} already in anc*(heads)") fun _ =>
    .ok (es.setNode n { es.nodeOf n with
      heads := maxL es.parF ((es.nodeOf n).heads ++ [(es.nodeOf n).known.2]) })
  | .uploadOps n S =>
    req (decide (n < N)) (fun _ => s!"uploadOps: node {n} out of range") fun _ =>
    req (S.all ((es.nodeOf n).lops.contains ·))
      (fun _ => s!"uploadOps: {showL S} not all local on node {n}") fun _ =>
    .ok (es.send (.putOps n S))
  | .uploadObjs n S =>
    req (decide (n < N)) (fun _ => s!"uploadObjs: node {n} out of range") fun _ =>
    req (S.all ((es.nodeOf n).lobj.contains ·))
      (fun _ => s!"uploadObjs: {showL S} not all local on node {n}") fun _ =>
    .ok (es.send (.putObjs n S))
  | .push n e d =>
    req (decide (n < N)) (fun _ => s!"push: node {n} out of range") fun _ =>
    req ((es.nodeOf n).lops.contains d) (fun _ => s!"push: op {d} not local on node {n}")
      fun _ =>
    .ok (es.send (.cas n e d))
  | .pushAll n S O e d =>
    req (decide (n < N)) (fun _ => s!"pushAll: node {n} out of range") fun _ =>
    req (S.all ((es.nodeOf n).lops.contains ·))
      (fun _ => s!"pushAll: {showL S} not all local on node {n}") fun _ =>
    req (O.all ((es.nodeOf n).lobj.contains ·))
      (fun _ => s!"pushAll: objects {showL O} not all local on node {n}") fun _ =>
    req ((es.nodeOf n).lops.contains d) (fun _ => s!"pushAll: op {d} not local on node {n}")
      fun _ =>
    .ok (es.send (.push n S O e d))
  | .fetchAll n b H =>
    req (decide (n < N)) (fun _ => s!"fetchAll: node {n} out of range") fun _ =>
    .ok (es.send (.fetch n b H))
  | .crashNode n =>
    req (decide (n < N)) (fun _ => s!"crashNode: node {n} out of range") fun _ => .ok es
  | .loseKnown n =>
    req (decide (n < N)) (fun _ => s!"loseKnown: node {n} out of range") fun _ =>
    .ok (es.setNode n { es.nodeOf n with known := (0, root) })
  | .loseVolatile n =>
    req (decide (n < N)) (fun _ => s!"loseVolatile: node {n} out of range") fun _ =>
    .ok (es.setNode n { es.nodeOf n with known := (0, root), sops := [], sobj := [] })
  | .hubGetHead n =>
    req (es.inNet (.getHead n)) (fun _ => s!"hubGetHead: getHead from node {n} not in net")
      fun _ =>
    .ok (es.send (.head n .head es.hub.seq es.hub.head))
  | .hubPutOps n S =>
    req (es.inNet (.putOps n S))
      (fun _ => s!"hubPutOps: putOps {showL S} from node {n} not in net") fun _ =>
    .ok ((es.hubStoreOps S).send (.stored n))
  | .hubPutObjs n S =>
    req (es.inNet (.putObjs n S))
      (fun _ => s!"hubPutObjs: putObjs {showL S} from node {n} not in net") fun _ =>
    .ok ((es.hubStoreObjs S).send (.stored n))
  | .hubGetOps n S =>
    req (es.inNet (.getOps n S))
      (fun _ => s!"hubGetOps: getOps {showL S} from node {n} not in net") fun _ =>
    .ok (es.send (.ops n (S.filter (es.hub.ops.contains ·))))
  | .hubGetObjs n S =>
    req (es.inNet (.getObjs n S))
      (fun _ => s!"hubGetObjs: getObjs {showL S} from node {n} not in net") fun _ =>
    .ok (es.send (.objs n (S.filter (es.hub.objs.contains ·))))
  | .casIdem n e d =>
    req (es.inNet (.cas n e d)) (fun _ => s!"casIdem: cas({e}, {d}) from node {n} not in net")
      fun _ =>
    req (decide (es.hub.head = d)) (fun _ => s!"casIdem: head {es.hub.head} is not {d}")
      fun _ =>
    .ok (es.send (.head n .accepted es.hub.seq es.hub.head))
  | .casAccept n e d =>
    req (es.inNet (.cas n e d))
      (fun _ => s!"casAccept: cas({e}, {d}) from node {n} not in net") fun _ =>
    req (decide (es.hub.head ≠ d)) (fun _ => s!"casAccept: head is already {d} (idempotent)")
      fun _ =>
    req (decide (es.hub.head = e))
      (fun _ => s!"casAccept: head {es.hub.head} is not expected {e}") fun _ =>
    req (ancB es.parF e d) (fun _ => s!"casAccept: expected {e} not in anc*({d})") fun _ =>
    req (es.closedB d)
      (fun _ => s!"casAccept: closure of {d} not stored at hub ({es.missingMsg d})") fun _ =>
    .ok (((es.hubAccept d).send (.head n .accepted (es.hub.seq + 1) d)).send
      (.notifyAll (es.hub.seq + 1) d))
  | .casReject n e d =>
    req (es.inNet (.cas n e d))
      (fun _ => s!"casReject: cas({e}, {d}) from node {n} not in net") fun _ =>
    req (decide (es.hub.head ≠ d)) (fun _ => s!"casReject: head is already {d} (idempotent)")
      fun _ =>
    req (!(decide (es.hub.head = e) && ancB es.parF e d && es.closedB d))
      (fun _ => s!"casReject: cas({e}, {d}) is acceptable") fun _ =>
    .ok (es.send (.head n .rejected es.hub.seq es.hub.head))
  | .hubPushIdem n S O e d =>
    req (es.inNet (.push n S O e d))
      (fun _ => s!"hubPushIdem: push({e}, {d}) from node {n} not in net") fun _ =>
    req (decide (es.hub.head = d)) (fun _ => s!"hubPushIdem: head {es.hub.head} is not {d}")
      fun _ =>
    .ok ((es.hubStore S O).send (.head n .accepted es.hub.seq es.hub.head))
  | .hubPushAccept n S O e d =>
    req (es.inNet (.push n S O e d))
      (fun _ => s!"hubPushAccept: push({e}, {d}) from node {n} not in net") fun _ =>
    req (decide (es.hub.head ≠ d))
      (fun _ => s!"hubPushAccept: head is already {d} (idempotent)") fun _ =>
    req (decide (es.hub.head = e))
      (fun _ => s!"hubPushAccept: head {es.hub.head} is not expected {e}") fun _ =>
    req (ancB es.parF e d) (fun _ => s!"hubPushAccept: expected {e} not in anc*({d})")
      fun _ =>
    req ((es.hubStore S O).closedB d)
      (fun _ => s!"hubPushAccept: closure of {d} not stored at hub ({(es.hubStore S O).missingMsg d})")
      fun _ =>
    .ok ((((es.hubStore S O).hubAccept d).send (.head n .accepted (es.hub.seq + 1) d)).send
      (.notifyAll (es.hub.seq + 1) d))
  | .hubPushReject n S O e d =>
    req (es.inNet (.push n S O e d))
      (fun _ => s!"hubPushReject: push({e}, {d}) from node {n} not in net") fun _ =>
    req (decide (es.hub.head ≠ d))
      (fun _ => s!"hubPushReject: head is already {d} (idempotent)") fun _ =>
    req (!(decide (es.hub.head = e)) || ((es.hubStore S O).closedB d && !(ancB es.parF e d)))
      (fun _ => s!"hubPushReject: push({e}, {d}) is acceptable or incomplete") fun _ =>
    .ok ((es.hubStore S O).send (.head n .rejected es.hub.seq es.hub.head))
  | .hubPushIncomplete n S O e d =>
    req (es.inNet (.push n S O e d))
      (fun _ => s!"hubPushIncomplete: push({e}, {d}) from node {n} not in net") fun _ =>
    req (decide (es.hub.head ≠ d))
      (fun _ => s!"hubPushIncomplete: head is already {d} (idempotent)") fun _ =>
    req (decide (es.hub.head = e))
      (fun _ => s!"hubPushIncomplete: head {es.hub.head} is not expected {e}") fun _ =>
    req (!(es.hubStore S O).closedB d)
      (fun _ => s!"hubPushIncomplete: closure of {d} is stored at hub") fun _ =>
    .ok ((es.hubStore S O).send (.head n .incomplete es.hub.seq es.hub.head))
  | .hubFetch n b H =>
    req (es.inNet (.fetch n b H))
      (fun _ => s!"hubFetch: fetch({b}) from node {n} not in net") fun _ =>
    .ok (((es.send (.head n .head es.hub.seq es.hub.head)).send (.ops n (es.sinceOpsL b))).send
      (.objs n (es.sinceObjsL b H)))
  | .crashHub => .ok es
  | .hubForget S O =>
    req (S.all es.hub.ops.contains)
      (fun _ => s!"hubForget: ops {showL S} not all stored at hub") fun _ =>
    req (O.all es.hub.objs.contains)
      (fun _ => s!"hubForget: objects {showL O} not all stored at hub") fun _ =>
    req ((es.forget S O).closedB es.hub.head)
      (fun _ => s!"hubForget: closure of head {es.hub.head} not kept ({(es.forget S O).missingMsg es.hub.head})")
      fun _ =>
    .ok (es.forget S O)
  | .hubRegress i =>
    req (decide (i ≤ es.hub.seq))
      (fun _ => s!"hubRegress: seq {i} is above the hub's seq {es.hub.seq}") fun _ =>
    .ok (es.regress i)

/-- The executable step. The well-formedness check (parents below children) holds in every
state reachable from `initE`; it is checked so that `exec_sound` needs no well-formedness
hypothesis. -/
def execStep (N : Nat) (es : EState) (a : Action) : Except String EState :=
  req es.parOK (fun _ => "internal: an operation has a parent not below it") fun _ =>
  execCore N es a

/-- A hive made again, empty (`HubDir::remake`): the hub goes back to the root, then keeps
only the root. -/
def remakeActions : List Action := [.hubRegress 0, .hubForget [root] []]

/-! ## The liveness measure

`measure` and `Converged` of `Liveness.lean`, and `rmeasure` of `Regress.lean`, on a finite
state, with what a policy `Push` uploads. `ExecSound.lean` proves each equal to its relational
counterpart on `abs es`. The conformance test asks the oracle for them while it runs the Rust
policy to convergence (docs/internals/conformance.md, "Liveness"). -/

/-- `cnt` with a decidable predicate. -/
def cntE : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | B + 1, p => cntE B p + (if p B then 1 else 0)

namespace EState

/-- `dirty`: one of node `n`'s heads is not accepted. -/
def dirtyE (es : EState) (n : Nat) : Bool :=
  (es.nodeOf n).heads.any fun h => !ancB es.parF h es.hub.head

/-- `mStale`. -/
def staleE (es : EState) (n : Nat) : Nat := es.hub.seq - (es.nodeOf n).known.1

/-- `mMiss`: the accepted operations node `n` lacks. -/
def missE (es : EState) (n : Nat) : Nat :=
  let A := ancL es.parF es.hub.head
  cntE (es.hub.head + 1) fun x => A.contains x && !(es.nodeOf n).lops.contains x

/-- `mAdv`: whether node `n` has yet to advance to `known.head`. -/
def advE (es : EState) (n : Nat) : Nat :=
  if (es.nodeOf n).heads.any (ancB es.parF (es.nodeOf n).known.2) then 0 else 1

/-- `mMulti`: whether node `n` has two heads to merge. -/
def multiE (es : EState) (n : Nat) : Nat :=
  if (es.nodeOf n).heads.any (fun a => (es.nodeOf n).heads.any (a != ·)) then 1 else 0

/-- `measure`, the measure of `Liveness.lean`. -/
def measureE (N : Nat) (es : EState) : Nat × Nat × Nat × Nat × Nat :=
  (cntE N es.dirtyE, sumN N es.staleE, sumN N es.missE, sumN N es.advE, sumN N es.multiE)

/-- `Converged`: every node's heads are `{hub.head}`, and it knows the hub's head. -/
def convergedE (N : Nat) (es : EState) : Bool :=
  (List.range N).all fun n =>
    (es.nodeOf n).heads.contains es.hub.head && (es.nodeOf n).heads.all (· == es.hub.head) &&
      (es.nodeOf n).known == (es.hub.seq, es.hub.head)

/-- `Consistent`: node `n`'s `known` is in the hub's current history. -/
def consistentE (es : EState) (n : Nat) : Bool :=
  decide ((es.nodeOf n).known.1 ≤ es.hub.seq) &&
    es.hub.histF (es.nodeOf n).known.1 == (es.nodeOf n).known.2

/-- `Settled`: node `n` has one head, accepted and comparable with every head in the hub's
history. -/
def settledE (es : EState) (n : Nat) : Bool :=
  match (es.nodeOf n).heads with
  | [] => false
  | x :: _ =>
    (es.nodeOf n).heads.all (· == x) && ancB es.parF x es.hub.head &&
      (List.range (es.hub.seq + 1)).all fun i =>
        ancB es.parF x (es.hub.histF i) || ancB es.parF (es.hub.histF i) x

/-- `mStaleR`. -/
def staleRE (es : EState) (n : Nat) : Nat :=
  if es.consistentE n then es.hub.seq - (es.nodeOf n).known.1 else 0

/-- `rmeasure`, the measure of `Regress.lean`, for a hub that may have gone back. -/
def rmeasureE (N : Nat) (es : EState) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (cntE N (fun n => !(es.consistentE n && es.settledE n)), cntE N (fun n => !es.consistentE n),
    sumN N es.staleRE, sumN N es.missE, sumN N es.advE, sumN N es.multiE)

/-- `upOps`: what node `n` uploads to push `h`, `anc*(h) \ anc*(known.head)`. -/
def upOpsL (es : EState) (n h : Nat) : List Nat :=
  (ancL es.parF h).filter fun y => !ancB es.parF y (es.nodeOf n).known.2

/-- `upObjs`: the objects of `closure(h) \ closure(known.head)`. -/
def upObjsL (es : EState) (n h : Nat) : List Nat :=
  let below := (ancL es.parF (es.nodeOf n).known.2).flatMap es.objsF
  ((ancL es.parF h).flatMap es.objsF).filter fun o => !below.contains o

end EState

end Musubi.Exec

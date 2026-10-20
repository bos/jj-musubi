/-
The executable model: finite, computable states, an `Action` vocabulary matching
`docs/conformance.md`, and `execStep`, which evaluates every guard of the relational model and
names the guard that failed. `exec_sound` proves that every accepted action is a `Step` of
the relational model between the abstracted states.
-/
import Musubi.Safety

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

/-- The action vocabulary of `docs/conformance.md`: one constructor per relational step
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
  | crashHub
  deriving Repr

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
  | .crashHub => .ok es

/-- The executable step. The well-formedness check (parents below children) holds in every
state reachable from `initE`; it is checked so that `exec_sound` needs no hypothesis. -/
def execStep (N : Nat) (es : EState) (a : Action) : Except String EState :=
  req es.parOK (fun _ => "internal: an operation has a parent not below it") fun _ =>
  execCore N es a

end Musubi.Exec

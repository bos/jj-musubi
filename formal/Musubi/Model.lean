/-
The asynchronous protocol model of `docs/internals/protocol.md`: hub, nodes, environment actions,
sync actions, and a lossy, duplicating, reordering network.
-/
import Musubi.Dag

namespace Musubi

/-! ## Data -/

/-- The universe of canonical operations created so far. Operation ids are `Nat`s; the root
operation is `0`, and a newly created operation gets the fresh id `next`. `par`, `objs` are
immutable once an operation is created. `creator`, `isMerge` and `birth` are ghost state, used
only to state properties. -/
structure Univ where
  /-- The next fresh operation id. Ids `< next` have been created. -/
  next : Nat
  /-- `parents(x)`. -/
  par : Nat → List Nat
  /-- `objs(x)`: the object ids `x` requires (already closed under object reachability). -/
  objs : Nat → List Nat
  /-- Ghost: `creator(x)`; `none` for the root. -/
  creator : Nat → Option Nat
  /-- Ghost: whether `x` was created by `Merge`. -/
  isMerge : Nat → Bool
  /-- Ghost: the hub's `seq` when `x` was created (so `hist (birth x)` was the hub head). -/
  birth : Nat → Nat

/-- Persistent hub state, plus the ghost history of accepted heads. -/
structure Hub where
  ops : OSet
  objs : OSet
  head : Nat
  seq : Nat
  /-- Ghost: `hist i` is the head accepted at sequence number `i` (for `i ≤ seq`). -/
  hist : Nat → Nat

/-- Persistent node state. A node has no volatile state at this level of the model: requests
are fire-and-forget messages, and replies are processed whenever (and however often) they
arrive. Losing in-flight requests on a crash is therefore the same as losing messages. -/
structure Node where
  /-- `local`: canonical ids present in the local op store. -/
  lops : OSet
  /-- Objects present in the local object store. -/
  lobj : OSet
  heads : OSet
  /-- `known = (seq, OpId)`. -/
  known : Nat × Nat
  /-- `staged` operations. -/
  sops : OSet
  /-- `staged` objects. -/
  sobj : OSet

/-- The four hub replies carrying a head, plus the published notification. They are all
handled the same way by `Learn`. `incomplete` answers a push from the hub's head that the
hub still can't close, which only a node lacking what its operation requires sends. -/
inductive HeadKind
  | head
  | accepted
  | rejected
  | incomplete
  | notify
  deriving DecidableEq, Repr

/-- Messages. Requests carry the sending node; replies carry the destination node. Request
ids are not modeled: a node handles any reply addressed to it, which over-approximates
matching replies to outstanding requests.

`push` and `fetch` are the merged requests the implementation sends: `push n S O e d` is
`PutOps(S)`, `PutObjects(O)` and `Cas(e, d)` handled in one critical section, and
`fetch n b H` asks for the hub's head together with the operations accepted since `b` and
their objects, less the haves `H`, replied to with a `head`, an `ops` and an `objs`
message. -/
inductive Msg
  | getHead (n : Nat)
  | putOps (n : Nat) (S : OSet)
  | putObjs (n : Nat) (S : OSet)
  | getOps (n : Nat) (S : OSet)
  | getObjs (n : Nat) (S : OSet)
  | cas (n e d : Nat)
  | head (n : Nat) (k : HeadKind) (sq h : Nat)
  | ops (n : Nat) (S : OSet)
  | objs (n : Nat) (S : OSet)
  | stored (n : Nat)
  | push (n : Nat) (S O : OSet) (e d : Nat)
  | fetch (n b : Nat) (H : OSet)

/-- The global state. `net` is the set of every message ever sent. A message in `net` may be
delivered any number of times (duplication), in any order (reordering), arbitrarily late
(delay), or never (loss). -/
structure State where
  U : Univ
  hub : Hub
  node : Nat → Node
  net : Msg → Prop

/-- The root operation. -/
abbrev root : Nat := 0

def initNode : Node where
  lops := (· = root)
  lobj := fun _ => False
  heads := (· = root)
  known := (0, root)
  sops := fun _ => False
  sobj := fun _ => False

def init : State where
  U := { next := 1, par := fun _ => [], objs := fun _ => [], creator := fun _ => none,
         isMerge := fun _ => false, birth := fun _ => 0 }
  hub := { ops := (· = root), objs := fun _ => False, head := root, seq := 0,
           hist := fun _ => root }
  node := fun _ => initNode
  net := fun _ => False

/-- `x` and its objects are stored at the hub. -/
def HubHas (s : State) (x : Nat) : Prop :=
  s.hub.ops x ∧ ∀ o ∈ s.U.objs x, s.hub.objs o

/-- `closure(d) ⊆ ops ∪ objects` at the hub. -/
def ClosedAt (s : State) (d : Nat) : Prop :=
  ∀ y, Anc s.U.par y d → HubHas s y

namespace State

/-! ## Transition functions -/

def send (s : State) (m : Msg) : State := { s with net := fun m' => s.net m' ∨ m' = m }

def setNode (s : State) (n : Nat) (nd : Node) : State := { s with node := upd s.node n nd }

/-- The universe after creating the fresh operation `next` on node `n`. -/
def create (s : State) (n : Nat) (L O : List Nat) (mg : Bool) : Univ where
  next := s.U.next + 1
  par := upd s.U.par s.U.next L
  objs := upd s.U.objs s.U.next O
  creator := upd s.U.creator s.U.next (some n)
  isMerge := upd s.U.isMerge s.U.next mg
  birth := upd s.U.birth s.U.next s.hub.seq

/-- Node `n` writes the fresh operation `next` with parents `L` and objects `O` (stored
locally), and its heads become `H'`. -/
def createOp (s : State) (n : Nat) (L O : List Nat) (mg : Bool) (H' : OSet) : State :=
  { s with
    U := s.create n L O mg
    node := upd s.node n
      { s.node n with
        lops := fun y => (s.node n).lops y ∨ y = s.U.next
        lobj := fun y => (s.node n).lobj y ∨ y ∈ O
        heads := H' } }

/-- `UserOp(p)`: parents `[p]`; `heads := max(heads \ {p} ∪ {o})`. -/
def userOp (s : State) (n p : Nat) (O : List Nat) : State :=
  s.createOp n [p] O false
    (maxSet (upd s.U.par s.U.next [p])
      (fun y => ((s.node n).heads y ∧ y ≠ p) ∨ y = s.U.next))

/-- `Merge`: parents `L` (an enumeration of `heads`); `heads := {m}`. -/
def mergeOp (s : State) (n : Nat) (L O : List Nat) : State :=
  s.createOp n L O true (· = s.U.next)

/-- `Learn(sq, h)` when `sq > known.seq`. -/
def learn (s : State) (n sq h : Nat) : State :=
  s.setNode n { s.node n with known := (sq, h) }

def recvOps (s : State) (n : Nat) (S : OSet) : State :=
  s.setNode n { s.node n with sops := fun x => (s.node n).sops x ∨ S x }

def recvObjs (s : State) (n : Nat) (S : OSet) : State :=
  s.setNode n { s.node n with sobj := fun x => (s.node n).sobj x ∨ S x }

/-- `Realize(x)`: write the realization; its objects move into the object store. -/
def realize (s : State) (n x : Nat) : State :=
  s.setNode n { s.node n with
    lops := fun y => (s.node n).lops y ∨ y = x
    lobj := fun o => (s.node n).lobj o ∨ o ∈ s.U.objs x }

/-- `Advance`: `heads := max(heads ∪ {known.head})`. -/
def advance (s : State) (n : Nat) : State :=
  s.setNode n { s.node n with
    heads := maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) }

def hubStoreOps (s : State) (S : OSet) : State :=
  { s with hub := { s.hub with ops := fun x => s.hub.ops x ∨ S x } }

def hubStoreObjs (s : State) (S : OSet) : State :=
  { s with hub := { s.hub with objs := fun x => s.hub.objs x ∨ S x } }

/-- The hub stores a `push`'s operations and objects. -/
def hubStore (s : State) (S O : OSet) : State := (s.hubStoreOps S).hubStoreObjs O

/-- What `fetch n b H` returns: the stored operations in `anc*(head) \ anc*(b)`... -/
def sinceOps (s : State) (b : Nat) : OSet :=
  fun x => Anc s.U.par x s.hub.head ∧ ¬ Anc s.U.par x b ∧ s.hub.ops x

/-- ... and the stored objects they require, less the haves `H`. -/
def sinceObjs (s : State) (b : Nat) (H : OSet) : OSet :=
  fun o => (∃ x, s.sinceOps b x ∧ o ∈ s.U.objs x) ∧ ¬ H o ∧ s.hub.objs o

/-- The hub accepts `d`: `head := d`, `seq := seq + 1` (and the ghost history records it). -/
def hubAccept (s : State) (d : Nat) : State :=
  { s with hub := { s.hub with head := d, seq := s.hub.seq + 1,
                               hist := upd s.hub.hist (s.hub.seq + 1) d } }

/-- Publish `Head(sq, h)` to every subscriber. -/
def notifyAll (s : State) (sq h : Nat) : State :=
  { s with net := fun m => s.net m ∨ ∃ n, m = .head n .notify sq h }

end State

/-! ## Steps -/

/-- Environment actions (outside musubi, through `jj`). These are the only actions that
create canonical operations. -/
inductive EnvStep (N : Nat) : State → State → Prop
  | userOp (s : State) (n p : Nat) (O : List Nat) (hn : n < N) (hp : (s.node n).lops p) :
      EnvStep N s (s.userOp n p O)
  | merge (s : State) (n : Nat) (L O : List Nat) (hn : n < N)
      (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
      EnvStep N s (s.mergeOp n L O)

/-- Sync actions of nodes, hub request handling, and crashes.

Node-side guards are deliberately weaker than the policy in `protocol.md` wherever safety
does not need them (Upload may send any local operations/objects; Push may send any
`Cas(e, d)` with `d` local; `GetObjects` may ask for anything). The policy's actions are all
instances. The one load-bearing node-side guard is on `GetOps`: a node only requests
operations in `anc*(known.head)`. -/
inductive SyncStep (N : Nat) : State → State → Prop
  -- node side
  | getHead (s : State) (n : Nat) (hn : n < N) : SyncStep N s (s.send (.getHead n))
  | learn (s : State) (n : Nat) (k : HeadKind) (sq h : Nat) (hn : n < N)
      (hm : s.net (.head n k sq h)) (hs : (s.node n).known.1 < sq) :
      SyncStep N s (s.learn n sq h)
  /-- Relaxation: `Learn` without its staleness filter (may move `known` backwards). -/
  | learnUnfiltered (s : State) (n : Nat) (k : HeadKind) (sq h : Nat) (hn : n < N)
      (hm : s.net (.head n k sq h)) : SyncStep N s (s.learn n sq h)
  | fetchOps (s : State) (n : Nat) (S : OSet) (hn : n < N)
      (hS : ∀ x, S x → Anc s.U.par x (s.node n).known.2) :
      SyncStep N s (s.send (.getOps n S))
  | fetchObjs (s : State) (n : Nat) (S : OSet) (hn : n < N) :
      SyncStep N s (s.send (.getObjs n S))
  | recvOps (s : State) (n : Nat) (S : OSet) (hn : n < N) (hm : s.net (.ops n S)) :
      SyncStep N s (s.recvOps n S)
  | recvObjs (s : State) (n : Nat) (S : OSet) (hn : n < N) (hm : s.net (.objs n S)) :
      SyncStep N s (s.recvObjs n S)
  | realize (s : State) (n x : Nat) (hn : n < N) (hx : (s.node n).sops x)
      (hp : ∀ p ∈ s.U.par x, (s.node n).lops p)
      (ho : ∀ o ∈ s.U.objs x, (s.node n).lobj o ∨ (s.node n).sobj o) :
      SyncStep N s (s.realize n x)
  | advance (s : State) (n : Nat) (hn : n < N) (hk : (s.node n).lops (s.node n).known.2)
      (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
      SyncStep N s (s.advance n)
  | uploadOps (s : State) (n : Nat) (S : OSet) (hn : n < N)
      (hS : ∀ x, S x → (s.node n).lops x) : SyncStep N s (s.send (.putOps n S))
  | uploadObjs (s : State) (n : Nat) (S : OSet) (hn : n < N)
      (hS : ∀ o, S o → (s.node n).lobj o) : SyncStep N s (s.send (.putObjs n S))
  | push (s : State) (n e d : Nat) (hn : n < N) (hd : (s.node n).lops d) :
      SyncStep N s (s.send (.cas n e d))
  /-- The merged `Push`: upload and `Cas` in one request, with the guards of all three. -/
  | pushAll (s : State) (n : Nat) (S O : OSet) (e d : Nat) (hn : n < N)
      (hS : ∀ x, S x → (s.node n).lops x) (hO : ∀ o, O o → (s.node n).lobj o)
      (hd : (s.node n).lops d) :
      SyncStep N s (s.send (.push n S O e d))
  /-- The merged `Fetch`. It needs no guard: the hub chooses the operations, all accepted. -/
  | fetchAll (s : State) (n b : Nat) (H : OSet) (hn : n < N) :
      SyncStep N s (s.send (.fetch n b H))
  | crashNode (s : State) (n : Nat) (hn : n < N) : SyncStep N s s
  /-- Relaxation (stronger than `protocol.md` requires): a restarting node may lose `known`
  while keeping `staged` (what the Rust node does: it persists staged files, not `known`). -/
  | loseKnown (s : State) (n : Nat) (hn : n < N) :
      SyncStep N s (s.setNode n { s.node n with known := (0, root) })
  /-- Relaxation (stronger than `protocol.md` requires): a crash may also lose `known` and
  `staged`, as if they were volatile. -/
  | loseVolatile (s : State) (n : Nat) (hn : n < N) :
      SyncStep N s (s.setNode n { s.node n with known := (0, root), sops := fun _ => False,
                                                sobj := fun _ => False })
  -- hub side
  | hubGetHead (s : State) (n : Nat) (hm : s.net (.getHead n)) :
      SyncStep N s (s.send (.head n .head s.hub.seq s.hub.head))
  | hubPutOps (s : State) (n : Nat) (S : OSet) (hm : s.net (.putOps n S)) :
      SyncStep N s ((s.hubStoreOps S).send (.stored n))
  | hubPutObjs (s : State) (n : Nat) (S : OSet) (hm : s.net (.putObjs n S)) :
      SyncStep N s ((s.hubStoreObjs S).send (.stored n))
  | hubGetOps (s : State) (n : Nat) (S : OSet) (hm : s.net (.getOps n S)) :
      SyncStep N s (s.send (.ops n (fun x => S x ∧ s.hub.ops x)))
  | hubGetObjs (s : State) (n : Nat) (S : OSet) (hm : s.net (.getObjs n S)) :
      SyncStep N s (s.send (.objs n (fun x => S x ∧ s.hub.objs x)))
  | casIdem (s : State) (n e d : Nat) (hm : s.net (.cas n e d)) (hh : s.hub.head = d) :
      SyncStep N s (s.send (.head n .accepted s.hub.seq s.hub.head))
  | casAccept (s : State) (n e d : Nat) (hm : s.net (.cas n e d)) (hne : s.hub.head ≠ d)
      (he : s.hub.head = e) (ha : Anc s.U.par e d) (hc : ClosedAt s d) :
      SyncStep N s
        (((s.hubAccept d).send (.head n .accepted (s.hub.seq + 1) d)).notifyAll
          (s.hub.seq + 1) d)
  | casReject (s : State) (n e d : Nat) (hm : s.net (.cas n e d)) (hne : s.hub.head ≠ d)
      (hrej : ¬ (s.hub.head = e ∧ Anc s.U.par e d ∧ ClosedAt s d)) :
      SyncStep N s (s.send (.head n .rejected s.hub.seq s.hub.head))
  /-- A `push` stores its operations and objects, then is answered as a `Cas`: here `new` is
  the head already. -/
  | hubPushIdem (s : State) (n : Nat) (S O : OSet) (e d : Nat) (hm : s.net (.push n S O e d))
      (hh : s.hub.head = d) :
      SyncStep N s ((s.hubStore S O).send (.head n .accepted s.hub.seq s.hub.head))
  /-- A `push` accepted: the closure is checked after storing, in the same critical section. -/
  | hubPushAccept (s : State) (n : Nat) (S O : OSet) (e d : Nat)
      (hm : s.net (.push n S O e d)) (hne : s.hub.head ≠ d) (he : s.hub.head = e)
      (ha : Anc s.U.par e d) (hc : ClosedAt (s.hubStore S O) d) :
      SyncStep N s
        ((((s.hubStore S O).hubAccept d).send (.head n .accepted (s.hub.seq + 1) d)).notifyAll
          (s.hub.seq + 1) d)
  /-- A `push` rejected: the head isn't the expected one, or `new` doesn't descend from it,
  as far as the stored closure says. -/
  | hubPushReject (s : State) (n : Nat) (S O : OSet) (e d : Nat)
      (hm : s.net (.push n S O e d)) (hne : s.hub.head ≠ d)
      (hrej : s.hub.head ≠ e ∨ (ClosedAt (s.hubStore S O) d ∧ ¬ Anc s.U.par e d)) :
      SyncStep N s ((s.hubStore S O).send (.head n .rejected s.hub.seq s.hub.head))
  /-- A `push` from the head that the hub still can't close, said apart from a lost race. -/
  | hubPushIncomplete (s : State) (n : Nat) (S O : OSet) (e d : Nat)
      (hm : s.net (.push n S O e d)) (hne : s.hub.head ≠ d) (he : s.hub.head = e)
      (hc : ¬ ClosedAt (s.hubStore S O) d) :
      SyncStep N s ((s.hubStore S O).send (.head n .incomplete s.hub.seq s.hub.head))
  /-- A `fetch` answered with the head, and the operations and objects since `b`. -/
  | hubFetch (s : State) (n b : Nat) (H : OSet) (hm : s.net (.fetch n b H)) :
      SyncStep N s (((s.send (.head n .head s.hub.seq s.hub.head)).send
        (.ops n (s.sinceOps b))).send (.objs n (s.sinceObjs b H)))
  | crashHub (s : State) : SyncStep N s s
  /-- Relaxation (stronger than `protocol.md` requires): the hub may lose (or garbage-collect)
  any stored operations and objects outside `closure(head)`. -/
  | hubForget (s : State) (O J : OSet) (hO : ∀ x, O x → s.hub.ops x)
      (hJ : ∀ o, J o → s.hub.objs o)
      (hc : ∀ y, Anc s.U.par y s.hub.head → O y ∧ ∀ o ∈ s.U.objs y, J o) :
      SyncStep N s { s with hub := { s.hub with ops := O, objs := J } }

/-- One step of the full asynchronous system with `N` nodes. -/
def Step (N : Nat) (s s' : State) : Prop := EnvStep N s s' ∨ SyncStep N s s'

inductive Reachable (N : Nat) : State → Prop
  | init : Reachable N init
  | step {s s' : State} : Reachable N s → Step N s s' → Reachable N s'

end Musubi

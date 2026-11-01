/-
The executable model with supersedes (`Supersede.lean`): the finite state of `Exec.lean` with
the hub's records and each node's dropped set, the actions that publish, announce and take
them, and the policy's measure `smeasure`. `SupersedeExecSound.lean` proves every accepted
action a step of `SRStep`, or no step at all.

The hub keeps its dropped set as records, in the order it took them, as the implementation
does, and a push carries the records its node took last with its dropped set
(`sendSup`). The hub refuses a push whose records aren't its own (`hubPushRefuse`): its ids
aren't the hub's. So it does one whose new head it, or the push, dropped. Every push the hub accepts is taken as a supersede (`hubSupAccept`), which
adds a record only if the push drops operations the hub hasn't. A node takes the records the
hub announces (`adopt`), once none of its heads is dropped by them.
-/
import Musubi.Exec
import Musubi.Supersede

namespace Musubi.Exec

open Musubi

/-- A record: operations the hub dropped at once. -/
abbrev Rec := List Nat

/-- The operations a list of records drops. -/
def flat (R : List Rec) : List Nat := R.flatten

/-- Two record lists are the same records, in the same order. -/
def recEq : List Rec → List Rec → Bool
  | [], [] => true
  | a :: A, b :: B => seteq a b && recEq A B
  | _, _ => false

/-- The value for key `i` in an association list, newest entry first. -/
def assocF {α : Type} (l : List (Nat × α)) (i : Nat) (d : α) : α :=
  ((l.find? (fun p => p.1 == i)).map Prod.snd).getD d

/-- The executable state with supersedes. -/
structure SEState where
  es : EState
  /-- The hub's records, oldest first. Its dropped set is what they drop. -/
  recs : List Rec
  /-- Ghost: the hub's records as of the head accepted at each sequence number, newest entry
  first (default none), as `EHub.hist` keeps heads. -/
  recHist : List (Nat × List Rec)
  /-- Each node's dropped set (default empty). -/
  nodeD : List (Nat × List Nat)
  /-- The hub's records each node took last (default none). -/
  applied : List (Nat × List Rec)
  /-- Supersedes sent: the node, the records it took last, and its dropped set. -/
  sups : List (Nat × List Rec × List Nat)
  /-- The hub's records, as announced to a node. -/
  dmsgs : List (Nat × List Rec)
  deriving Repr

def initSE : SEState where
  es := initE
  recs := []
  recHist := []
  nodeD := []
  applied := []
  sups := []
  dmsgs := []

namespace SEState

def nodeDF (ses : SEState) (n : Nat) : List Nat := assocF ses.nodeD n []
def appliedF (ses : SEState) (n : Nat) : List Rec := assocF ses.applied n []
def recHistF (ses : SEState) (i : Nat) : List Rec := assocF ses.recHist i []

/-- The hub's dropped set. -/
def hubDL (ses : SEState) : List Nat := flat ses.recs

end SEState

/-! ## Abstraction -/

/-- The relational state a finite one stands for. -/
def sabs (ses : SEState) : SState where
  s := abs ses.es
  hubD := setP ses.hubDL
  hubDHist := fun i => setP (flat (ses.recHistF i))
  nodeD := fun n => setP (ses.nodeDF n)
  sups := fun n Δ => ∃ e ∈ ses.sups, e.1 = n ∧ Δ = setP e.2.2
  dmsgs := fun n Δ => ∃ e ∈ ses.dmsgs, e.1 = n ∧ Δ = setP (flat e.2)

/-! ## Actions -/

/-- The actions with supersedes: every action of `Exec.lean`, and the steps of
`Supersede.lean`. -/
inductive SAction
  | base (a : Action)
  /-- `jj op abandon` on `node` drops `ops`. -/
  | abandon (node : Nat) (ops : List Nat)
  /-- `node` sends its dropped set, and the records it took last, with a push. -/
  | sendSup (node : Nat)
  /-- The hub announces its records to `node`, with a reply to a fetch. -/
  | sendD (node : Nat)
  /-- `node` takes the records the hub announced. -/
  | adopt (node : Nat) (recs : List Rec)
  /-- The hub accepts a push whose node has its records, dropping what the node dropped. -/
  | hubSupAccept (node : Nat) (ops objs : List Nat) (expected new : Nat) (applied : List Rec)
      (dropped : List Nat)
  /-- The hub refuses a push whose node's records aren't its own, or whose new head is
  dropped. -/
  | hubPushRefuse (node : Nat) (ops objs : List Nat) (expected new : Nat)
      (applied : List Rec) (dropped : List Nat)
  deriving Repr

/-- The sequence number the hub goes back to, for `hubRegress`. -/
def Action.regressSeq : Action → Option Nat
  | .hubRegress i => some i
  | _ => none

/-- Whether an action is the hub going back. -/
def SAction.goesBack : SAction → Bool
  | .base a => a.goesBack
  | _ => false

/-- Check a guard; on failure, report `msg`. -/
def sreq (c : Bool) (msg : Unit → String) (k : Unit → Except String SEState) :
    Except String SEState :=
  if c then k () else .error (msg ())

theorem sreq_ok {c : Bool} {msg : Unit → String} {k : Unit → Except String SEState}
    {ses' : SEState} (h : sreq c msg k = .ok ses') : c = true ∧ k () = .ok ses' := by
  unfold sreq at h
  cases c with
  | false => cases h
  | true => exact ⟨rfl, h⟩

/-- The node indices either state has an entry for: every other node is `ENode.init` in both. -/
def nodeKeys (es es' : EState) : List Nat := es.nodes.map Prod.fst ++ es'.nodes.map Prod.fst

/-- `HeadOK`: the hub's head stays, or moves to one it hasn't dropped. -/
def headOKB (ses : SEState) (es' : EState) : Bool :=
  es'.hub.head == ses.es.hub.head || !ses.hubDL.contains es'.hub.head

/-- `HeadsOK`: each node's new heads are old heads, or ones it hasn't dropped. -/
def headsOKB (ses : SEState) (es' : EState) : Bool :=
  (nodeKeys ses.es es').all fun n =>
    (es'.nodeOf n).heads.all fun x =>
      (ses.es.nodeOf n).heads.contains x || !(ses.nodeDF n).contains x

/-- A protocol step to `es'`, recording the hub's records as of a head it accepts. -/
def SEState.withBase (ses : SEState) (es' : EState) : SEState :=
  { ses with es := es',
             recHist := if es'.hub.seq == ses.es.hub.seq then ses.recHist
                        else (es'.hub.seq, ses.recs) :: ses.recHist }

/-- Node `n`'s dropped set becomes `D`. -/
def SEState.setD (ses : SEState) (n : Nat) (D : List Nat) : SEState :=
  { ses with nodeD := (n, D) :: ses.nodeD.filter (fun p => p.1 != n) }

/-- What the hub drops, from what a push drops, that it hadn't. -/
def newRec (ses : SEState) (Δ : List Nat) : Rec := Δ.filter (fun x => !ses.hubDL.contains x)

/-- The hub's records once it takes `Δ`: a new record, if `Δ` drops anything new. -/
def SEState.takeRecs (ses : SEState) (Δ : List Nat) : List Rec :=
  if (newRec ses Δ).isEmpty then ses.recs else ses.recs ++ [newRec ses Δ]

/-- The hub accepts a push to `es'` that drops `Δ`. -/
def SEState.supAccept (ses : SEState) (es' : EState) (Δ : List Nat) : SEState :=
  { ses with es := es', recs := ses.takeRecs Δ,
             recHist := (es'.hub.seq, ses.takeRecs Δ) :: ses.recHist }

/-- Node `n` takes records `R`. -/
def SEState.adoptR (ses : SEState) (n : Nat) (R : List Rec) : SEState :=
  { ses.setD n (union (ses.nodeDF n) (flat R)) with
    applied := (n, R) :: ses.applied.filter (fun p => p.1 != n) }

/-- One step, with every guard checked. Errors are `"<action>: <failed guard>"`. -/
def sexecCore (N : Nat) (ses : SEState) : SAction → Except String SEState
  | .base a =>
    match execStep N ses.es a with
    | .error e => .error e
    | .ok es' =>
      match a.regressSeq with
      | some i => .ok { ses with es := es', recs := ses.recHistF i }
      | none =>
        sreq (headOKB ses es')
          (fun _ => s!"supersede: the hub's new head {es'.hub.head} is one it dropped") fun _ =>
        sreq (headsOKB ses es')
          (fun _ => "supersede: a node's new head is one it dropped") fun _ =>
        .ok (ses.withBase es')
  | .abandon n D =>
    sreq (decide (n < N)) (fun _ => s!"abandon: node {n} out of range") fun _ =>
    sreq (D.all fun x => (ses.es.nodeOf n).heads.any fun h => ancB ses.es.parF x h)
      (fun _ => s!"abandon: {showL D} not all below node {n}'s heads") fun _ =>
    sreq (D.all fun x => !(ses.es.nodeOf n).heads.contains x)
      (fun _ => s!"abandon: {showL D} drops a head of node {n}") fun _ =>
    sreq (!D.contains root) (fun _ => "abandon: drops the root") fun _ =>
    .ok (ses.setD n (union (ses.nodeDF n) D))
  | .sendSup n =>
    sreq (decide (n < N)) (fun _ => s!"sendSup: node {n} out of range") fun _ =>
    .ok { ses with sups := ses.sups ++ [(n, ses.appliedF n, ses.nodeDF n)] }
  | .sendD n => .ok { ses with dmsgs := ses.dmsgs ++ [(n, ses.recs)] }
  | .adopt n R =>
    sreq (decide (n < N)) (fun _ => s!"adopt: node {n} out of range") fun _ =>
    sreq (ses.dmsgs.any fun e => e.1 == n && recEq e.2 R)
      (fun _ => s!"adopt: records {repr R} not announced to node {n}") fun _ =>
    sreq ((ses.es.nodeOf n).heads.all fun h => !(flat R).contains h)
      (fun _ => s!"adopt: records drop a head of node {n}") fun _ =>
    .ok (ses.adoptR n R)
  | .hubSupAccept n S O e d A Δ =>
    sreq (ses.sups.any fun s => s.1 == n && recEq s.2.1 A && seteq s.2.2 Δ)
      (fun _ => s!"hubSupAccept: no supersede {showL Δ} from node {n} in net") fun _ =>
    sreq (recEq A ses.recs)
      (fun _ => s!"hubSupAccept: node {n}'s records are not the hub's") fun _ =>
    sreq (!ses.hubDL.contains d && !Δ.contains d)
      (fun _ => s!"hubSupAccept: new head {d} is dropped") fun _ =>
    match execStep N ses.es (.hubPushAccept n S O e d) with
    | .error e => .error e
    | .ok es' =>
      sreq (headsOKB ses es')
        (fun _ => "supersede: a node's new head is one it dropped") fun _ =>
      .ok (ses.supAccept es' Δ)
  | .hubPushRefuse n S O e d A Δ =>
    sreq (ses.es.inNet (.push n S O e d))
      (fun _ => s!"hubPushRefuse: push({e}, {d}) from node {n} not in net") fun _ =>
    sreq (ses.sups.any fun s => s.1 == n && recEq s.2.1 A && seteq s.2.2 Δ)
      (fun _ => s!"hubPushRefuse: no supersede {showL Δ} from node {n} in net") fun _ =>
    sreq (!recEq A ses.recs || ses.hubDL.contains d || Δ.contains d)
      (fun _ => s!"hubPushRefuse: node {n}'s records are the hub's, and {d} isn't dropped")
      fun _ =>
    .ok ses

/-- The executable step. -/
def sexecStep (N : Nat) (ses : SEState) (a : SAction) : Except String SEState :=
  sreq ses.es.parOK (fun _ => "internal: an operation has a parent not below it") fun _ =>
  sexecCore N ses a

/-! ## The liveness measure

`smeasure` and `SConverged` of `Supersede.lean` on a finite state. -/

namespace SEState

/-- `mPend`: operations some node has dropped that the hub hasn't. -/
def pendE (N : Nat) (ses : SEState) : Nat :=
  cntE ses.es.next fun x =>
    (List.range N).any (fun n => (ses.nodeDF n).contains x) && !ses.hubDL.contains x

/-- `mLag`: operations the hub has dropped that a node hasn't, summed over nodes. -/
def lagE (N : Nat) (ses : SEState) : Nat :=
  sumN N fun n => cntE ses.es.next fun x => ses.hubDL.contains x && !(ses.nodeDF n).contains x

/-- `smeasure`. -/
def smeasureE (N : Nat) (ses : SEState) :
    Nat × Nat × (Nat × Nat × Nat × Nat × Nat × Nat) :=
  (ses.pendE N, ses.lagE N, ses.es.rmeasureE N)

/-- `SConverged`: the protocol has converged, and every node has the hub's dropped set. -/
def sconvergedE (N : Nat) (ses : SEState) : Bool :=
  ses.es.convergedE N && (List.range N).all fun n => seteq (ses.nodeDF n) ses.hubDL

end SEState

end Musubi.Exec

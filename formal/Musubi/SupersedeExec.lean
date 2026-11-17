/-
The executable model with supersedes (`Supersede.lean`): the finite state of `Exec.lean` with
the hub's records and each node's dropped set, the actions that publish, announce and take
them, and the policy's measure `smeasure`. `SupersedeExecSound.lean` proves every accepted
action a step of `SRStep`, or no step at all.

The hub keeps its dropped set as records, in the order it took them, as the implementation
does, and a push carries the records its node took last, with its dropped set and the head it
pushes (`sendSup` refuses a head that a record the node took drops). The hub refuses a push
(`hubPushRefuse`) if the records it carries aren't the hub's, if its new head is one the hub
remembers dropping, or if its new head is among the operations the push drops beyond those
records (`pendingOf`). Every push the hub accepts is taken as a supersede (`hubSupAccept`),
which adds a record only if the push drops operations the hub hasn't. A node takes the records
the hub announces (`adopt`), once none of its heads is dropped by them.

The hub prunes its first records (`prune`) once every node has taken them, as the reports in
its nodes' requests say: each a list of records its node held when it sent the request, maybe
long before. The implementation keeps of them only what a push's records must match, and
announces them only by their count and digest; here `recs` stays whole and stands for that, and
the hub's guards check a head only against the records after the first `pruned`. So a node
takes announced records only if it has held the ones the hub had pruned (`heldPrefix`): among
its records now, or among records it took before an older announcement gave it fewer, since a
node takes any announcement, however old. The hub prunes a whole list some node reported, so
remembering each list it held, by count and digest, is enough for a node to check that. The
implementation's reply carries only the records after those the node reported; one the node
can't complete from what it holds now, it ignores, and the next one starts from the pruned.
-/
import Musubi.Exec
import Musubi.Supersede
import Musubi.ContractOrder

namespace Musubi.Exec

open Musubi Contract

/-- A record: operations the hub dropped at once. -/
abbrev Rec := List Nat

/-- The operations a list of records drops. -/
def flat (R : List Rec) : List Nat := R.flatten

/-- Two record lists are the same records, in the same order. -/
def recEq : List Rec → List Rec → Bool
  | [], [] => true
  | a :: A, b :: B => seteq a b && recEq A B
  | _, _ => false

/-- A supersede in flight: what a node sent with a push. -/
structure Sup where
  /-- The node that sent it. -/
  node : Nat
  /-- The hub records the node had taken last. -/
  applied : List Rec
  /-- The node's dropped set. -/
  dropped : List Nat
  /-- The head of the push it rides on. -/
  head : Nat
  deriving Repr

/-- The hub's records, and how many of its first records it has pruned. -/
structure RecLog where
  /-- The hub's records, oldest first. -/
  recs : List Rec
  /-- How many of the first `recs` the hub has pruned. -/
  pruned : Nat
  deriving Repr

/-- The hub's records as of the head it accepted at sequence number `seq`. -/
structure HistEntry where
  seq : Nat
  log : RecLog
  deriving Repr

/-- The hub's records as announced to node `node`. -/
structure DropMsg where
  node : Nat
  log : RecLog
  deriving Repr

/-- The records the hub had at sequence number `i`; none if no entry names it. The first entry
for `i` wins, and entries are kept newest first. -/
def logAt (l : List HistEntry) (i : Nat) : RecLog :=
  ((l.find? (fun e => e.seq == i)).map (·.log)).getD ⟨[], 0⟩

/-- The executable state with supersedes. -/
structure SEState where
  es : EState
  /-- The hub's records, oldest first. Its dropped set is what they drop. -/
  recs : List Rec
  /-- How many of its first records the hub has pruned. -/
  pruned : Nat
  /-- Ghost: the hub's records, and how many of them it had pruned, as of the head accepted at
  each sequence number, newest entry first (default none), as `EHub.hist` keeps heads. -/
  recHist : List HistEntry
  /-- Each node's dropped set (default empty). -/
  nodeD : List (Nat × List Nat)
  /-- The hub's records each node took last (default none). -/
  applied : List (Nat × List Rec)
  /-- Every list of the hub's records each node has taken, its last among them (default: none
  but the empty one). Having taken them, it has dropped what they drop. -/
  held : List (Nat × List (List Rec))
  /-- Supersedes sent, with the records each node took last, its dropped set and the head of the
  push they ride on. -/
  sups : List Sup
  /-- The hub's records, as announced to a node, with how many of them it had pruned. -/
  dmsgs : List DropMsg
  deriving Repr

def initSE : SEState where
  es := initE
  recs := []
  pruned := 0
  recHist := []
  nodeD := []
  applied := []
  held := []
  sups := []
  dmsgs := []

namespace SEState

def nodeDF (ses : SEState) (n : Nat) : List Nat := assocF ses.nodeD n []
def appliedF (ses : SEState) (n : Nat) : List Rec := assocF ses.applied n []
def heldF (ses : SEState) (n : Nat) : List (List Rec) := assocF ses.held n [[]]
def recHistF (ses : SEState) (i : Nat) : List Rec := (logAt ses.recHist i).recs
def prunedHistF (ses : SEState) (i : Nat) : Nat := (logAt ses.recHist i).pruned

/-- The hub's dropped set. -/
def hubDL (ses : SEState) : List Nat := flat ses.recs

/-- What the hub has pruned. -/
def hubPL (ses : SEState) : List Nat := flat (ses.recs.take ses.pruned)

/-- What the hub remembers dropping: what it can check a head against. -/
def remDL (ses : SEState) : List Nat := flat (ses.recs.drop ses.pruned)

/-- Whether node `n` has held the first `p` records of `R`: what it checks of records announced
with `p` of them pruned, which it knows only by their count and digest. -/
def heldPrefix (ses : SEState) (n : Nat) (R : List Rec) (p : Nat) : Bool :=
  (ses.heldF n).any fun L => recEq (L.take p) (R.take p)

end SEState

/-! ## Abstraction -/

/-- What a push's supersede drops that the records it carries don't: its pending drops. -/
def pendingOf (A : List Rec) (Δ : List Nat) : List Nat := Δ.filter fun x => !(flat A).contains x

/-- The relational state a finite one stands for. -/
def sabs (ses : SEState) : SState where
  s := abs ses.es
  hubD := setP ses.hubDL
  hubDHist := fun i => setP (flat (ses.recHistF i))
  hubP := setP ses.hubPL
  hubPHist := fun i => setP (flat ((ses.recHistF i).take (ses.prunedHistF i)))
  nodeD := fun n => setP (ses.nodeDF n)
  sups := fun n T Δ h => ∃ e ∈ ses.sups,
    e.node = n ∧ T = setP (flat e.applied) ∧ Δ = setP e.dropped ∧ h = e.head
  dmsgs := fun n Δ => ∃ e ∈ ses.dmsgs, e.node = n ∧ Δ = setP (flat e.log.recs)

/-! ## Actions -/

/-- The actions with supersedes: every action of `Exec.lean`, and the steps of
`Supersede.lean`. -/
inductive SAction
  | base (a : Action)
  /-- `jj op abandon` on `node` drops `ops`. -/
  | abandon (node : Nat) (ops : List Nat)
  /-- `node` sends its dropped set, and the records it took last, with a push to `new`. -/
  | sendSup (node new : Nat)
  /-- The hub announces its records to `node`, with a reply to a fetch. -/
  | sendD (node : Nat)
  /-- `node` takes the records the hub announced. -/
  | adopt (node : Nat) (recs : List Rec)
  /-- The hub accepts a push whose node has its records, dropping what the node dropped. -/
  | hubSupAccept (node : Nat) (ops objs : List Nat) (expected new : Nat) (applied : List Rec)
      (dropped : List Nat)
  /-- The hub refuses a push whose node's records aren't its own, or whose new head it
  remembers dropping. -/
  | hubPushRefuse (node : Nat) (ops objs : List Nat) (expected new : Nat)
      (applied : List Rec) (dropped : List Nat)
  /-- The hub rejects a push whose node has its records, by the comparison it accepts with. -/
  | hubSupReject (node : Nat) (ops objs : List Nat) (expected new : Nat) (applied : List Rec)
      (dropped : List Nat)
  /-- `node` takes announced records that drop one of its heads, replacing its heads by their
  frontier with its known head under the records at once. -/
  | advancePrepared (node : Nat) (records : List Rec)
  /-- The hub prunes its first `count` records, which every node has taken, now or before. -/
  | prune (count : Nat)
  deriving Repr

/-- The sequence number the hub goes back to, for `hubRegress`. -/
def Action.regressSeq : Action → Option Nat
  | .hubRegress i => some i
  | _ => none

/-- Whether an action is the hub going back. -/
def SAction.goesBack : SAction → Bool
  | .base a => a.goesBack
  | _ => false

/-- The node indices either state has an entry for: every other node is `ENode.init` in both. -/
def nodeKeys (es es' : EState) : List Nat := es.nodes.map Prod.fst ++ es'.nodes.map Prod.fst

/-- A push to `h` carries a supersede whose records are the hub's. -/
def carriedB (ses : SEState) (h : Nat) : Bool :=
  ses.sups.any fun e => e.head == h && recEq e.applied ses.recs

/-- `HeadOK`: the hub's head stays, or moves as it accepts a push to a head it doesn't remember
dropping, and, once it has pruned any records, whose records are its own. -/
def headOKB (ses : SEState) (es' : EState) : Bool :=
  es'.hub.head == ses.es.hub.head ||
    (!ses.remDL.contains es'.hub.head && (ses.pruned == 0 || carriedB ses es'.hub.head))

/-- `HeadsOK`: each node's new heads are old heads, or ones it hasn't dropped. -/
def headsOKB (ses : SEState) (es' : EState) : Bool :=
  (nodeKeys ses.es es').all fun n =>
    (es'.nodeOf n).heads.all fun x =>
      (ses.es.nodeOf n).heads.contains x || !(ses.nodeDF n).contains x

/-- A protocol step to `es'`, recording the hub's records as of a head it accepts. -/
def SEState.withBase (ses : SEState) (es' : EState) : SEState :=
  { ses with es := es',
             recHist := if es'.hub.seq == ses.es.hub.seq then ses.recHist
                        else ⟨es'.hub.seq, ⟨ses.recs, ses.pruned⟩⟩ :: ses.recHist }

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
             recHist := ⟨es'.hub.seq, ⟨ses.takeRecs Δ, ses.pruned⟩⟩ :: ses.recHist }

/-- The hub prunes its first `k` records. -/
def SEState.pruneR (ses : SEState) (k : Nat) : SEState :=
  { ses with pruned := k, recHist := ⟨ses.es.hub.seq, ⟨ses.recs, k⟩⟩ :: ses.recHist }

/-- Node `n` takes records `R`. -/
def SEState.adoptR (ses : SEState) (n : Nat) (R : List Rec) : SEState :=
  { ses.setD n (union (ses.nodeDF n) (flat R)) with
    applied := (n, R) :: ses.applied.filter (fun p => p.1 != n)
    held := (n, R :: ses.heldF n) :: ses.held.filter (fun p => p.1 != n) }

/-! ## What the hub compares, and how a node advances, through surviving images -/

/-- What the hub's comparison drops for a push that drops `Δ`: everything its records ever
dropped, pruned or not, and the push's drops. -/
def acceptDrops (ses : SEState) (Δ : List Nat) : List Nat := union ses.hubDL Δ

/-- The hub with a push stored and its new head accepted, the reply sent and every node
notified. -/
def EState.acceptPush (es : EState) (n : Nat) (S O : List Nat) (d : Nat) : EState :=
  (((es.hubStore S O).hubAccept d).send (.head n .accepted (es.hub.seq + 1) d)).send
    (.notifyAll (es.hub.seq + 1) d)

/-- The push's supersede is in flight: from `n`, with records `A`, dropping `Δ`, to `d`. -/
def ledgerB (ses : SEState) (n d : Nat) (A : List Rec) (Δ : List Nat) : Bool :=
  ses.sups.any fun s => s.node == n && recEq s.applied A && seteq s.dropped Δ && s.head == d

/-- What `hubSupAccept` checks: the supersede is in flight with the hub's records and a head
neither they nor the push drops; the push is in flight, from the hub's head to another; every
surviving image of the hub's head, under the hub's drops and the push's, is below the new head
(`Contract.belowB`), whether or not the hub's head itself is; and the hub holds the new head's
closure. -/
def acceptB (ses : SEState) (n : Nat) (S O : List Nat) (e d : Nat) (A : List Rec)
    (Δ : List Nat) : Bool :=
  ledgerB ses n d A Δ && recEq A ses.recs && !ses.remDL.contains d &&
    !(pendingOf A Δ).contains d && ses.es.inNet (.push n S O e d) &&
    decide (ses.es.hub.head ≠ d) && decide (ses.es.hub.head = e) &&
    belowB ses.es.parF (acceptDrops ses Δ).contains e d && (ses.es.hubStore S O).closedB d

/-- Which of `acceptB`'s checks fails first. -/
def acceptError (ses : SEState) (n : Nat) (S O : List Nat) (e d : Nat) (A : List Rec)
    (Δ : List Nat) : String :=
  if !ledgerB ses n d A Δ then
    s!"hubSupAccept: no supersede {showL Δ} from node {n} with {d} in net"
  else if !recEq A ses.recs then s!"hubSupAccept: node {n}'s records are not the hub's"
  else if ses.remDL.contains d || (pendingOf A Δ).contains d then
    s!"hubSupAccept: new head {d} is dropped"
  else if !ses.es.inNet (.push n S O e d) then
    s!"hubSupAccept: push({e}, {d}) from node {n} not in net"
  else if ses.es.hub.head = d then s!"hubSupAccept: head is already {d} (idempotent)"
  else if ses.es.hub.head ≠ e then
    s!"hubSupAccept: head {ses.es.hub.head} is not expected {e}"
  else if !belowB ses.es.parF (acceptDrops ses Δ).contains e d then
    s!"hubSupAccept: a surviving image of {e} is not below {d}"
  else
    s!"hubSupAccept: closure of {d} not stored at hub ({(ses.es.hubStore S O).missingMsg d})"

/-- What `hubSupReject` checks: the push carries the hub's records and a head they don't drop,
and is from another head than the hub's, or complete and not past the hub's head by the
comparison `hubSupAccept` makes. So the hub never both accepts and rejects one push. -/
def rejectB (ses : SEState) (n : Nat) (S O : List Nat) (e d : Nat) (A : List Rec)
    (Δ : List Nat) : Bool :=
  ledgerB ses n d A Δ && recEq A ses.recs && !ses.remDL.contains d &&
    !(pendingOf A Δ).contains d &&
    (!decide (ses.es.hub.head = e) ||
      ((ses.es.hubStore S O).closedB d && !belowB ses.es.parF (acceptDrops ses Δ).contains e d))

/-- What the base actions also check here: a plain rejection is of no push in flight that the
hub would accept; the hub forgets nothing a head it can go back to needs; and it goes back only
to a head whose closure it holds. -/
def baseOutcomeB (ses : SEState) : Action → Bool
  | .hubPushReject n S O e d =>
    !(ses.sups.any fun p => p.node == n && p.head == d && acceptB ses n S O e d p.applied p.dropped)
  | .hubForget S O =>
    (List.range (ses.es.hub.seq + 1)).all fun i =>
      (ancL ses.es.parF (ses.es.hub.histF i)).all (ses.es.forget S O).hub.ops.contains
  | .hubRegress i => ses.es.closedB (ses.es.hub.histF i)
  | _ => true

def baseOutcomeError : Action → String
  | .hubForget .. => "hubForget: an operation needed by retained history is missing"
  | .hubRegress .. => "hubRegress: target incomplete; explicit recovery is required"
  | _ => "hubPushReject: a supersede the hub would accept is in flight"

/-- Node `n`'s heads become their frontier with its known head, under the dropped set `D`. -/
def SEState.advanceTo (ses : SEState) (n : Nat) (D : List Nat) : SEState :=
  { ses with es := ses.es.setNode n { ses.es.nodeOf n with
      heads := frontier ses.es.parF D.contains
        ((ses.es.nodeOf n).heads ++ [(ses.es.nodeOf n).known.head]) } }

/-- An advance of node `n` to its known head when it dropped that head: it advances to what
survives of it. -/
def SEState.droppedKnown (ses : SEState) : Action → Option Nat
  | .advance n => if (ses.nodeDF n).contains (ses.es.nodeOf n).known.head then some n else none
  | _ => none

/-- What an advance to what survives of the known head checks: the head has a surviving image,
no head of the node is past all of them, and the frontier is local. -/
def advanceB (N : Nat) (ses : SEState) (n : Nat) : Bool :=
  let nd := ses.es.nodeOf n
  let D := (ses.nodeDF n).contains
  decide (n < N) && !(exp ses.es.parF D nd.known.head).isEmpty &&
    (frontier ses.es.parF D (nd.heads ++ [nd.known.head])).all nd.lops.contains &&
    !(nd.heads.any (belowB ses.es.parF D nd.known.head))

/-- Node `n` takes records `R`, its heads becoming their frontier with its known head under
what it has dropped with them, in one step: it never shows a head the records drop. -/
def SEState.preparedAdvance (ses : SEState) (n : Nat) (R : List Rec) : SEState :=
  (ses.advanceTo n (union (ses.nodeDF n) (flat R))).adoptR n R

/-- What `advancePrepared` checks: the records were announced to the node, which has held them
as far as they were pruned; they drop one of its heads; and the frontier is local. -/
def preparedB (N : Nat) (ses : SEState) (n : Nat) (R : List Rec) : Bool :=
  let nd := ses.es.nodeOf n
  decide (n < N) &&
    (ses.dmsgs.any fun e =>
      e.node == n && recEq e.log.recs R && ses.heldPrefix n e.log.recs e.log.pruned) &&
    nd.heads.any (flat R).contains &&
    (frontier ses.es.parF (union (ses.nodeDF n) (flat R)).contains
      (nd.heads ++ [nd.known.head])).all nd.lops.contains

/-- A protocol action, with the hub's records kept as of a head it accepts and taken back as of
one it goes back to. -/
def baseCore (N : Nat) (ses : SEState) (a : Action) : Except String SEState :=
  match execStep N ses.es a with
  | .error e => .error e
  | .ok es' =>
    match a.regressSeq with
    | some i => .ok { ses with es := es', recs := ses.recHistF i, pruned := ses.prunedHistF i }
    | none =>
      req (headOKB ses es')
        (fun _ => s!"supersede: the hub's new head {es'.hub.head} comes without its records, \
          or is one it dropped") fun _ =>
      req (headsOKB ses es')
        (fun _ => "supersede: a node's new head is one it dropped") fun _ =>
      .ok (ses.withBase es')

/-- One step, with every guard checked. Errors are `"<action>: <failed guard>"`. -/
def sexecCore (N : Nat) (ses : SEState) : SAction → Except String SEState
  | .base a =>
    match ses.droppedKnown a with
    | some n =>
      req (advanceB N ses n)
        (fun _ => s!"advance: node {n}'s known head has no local surviving frontier, or a head \
          is past it") fun _ =>
      .ok (ses.advanceTo n (ses.nodeDF n))
    | none =>
      match baseCore N ses a with
      | .error e => .error e
      | .ok t => req (baseOutcomeB ses a) (fun _ => baseOutcomeError a) fun _ => .ok t
  | .abandon n D =>
    req (decide (n < N)) (fun _ => s!"abandon: node {n} out of range") fun _ =>
    req (D.all fun x => (ses.es.nodeOf n).heads.any fun h => ancB ses.es.parF x h)
      (fun _ => s!"abandon: {showL D} not all below node {n}'s heads") fun _ =>
    req (D.all fun x => !(ses.es.nodeOf n).heads.contains x)
      (fun _ => s!"abandon: {showL D} drops a head of node {n}") fun _ =>
    req (!D.contains root) (fun _ => "abandon: drops the root") fun _ =>
    .ok (ses.setD n (union (ses.nodeDF n) D))
  | .sendSup n d =>
    req (decide (n < N)) (fun _ => s!"sendSup: node {n} out of range") fun _ =>
    req (!(flat (ses.appliedF n)).contains d)
      (fun _ => s!"sendSup: node {n} pushes {d}, which a record it took drops") fun _ =>
    .ok { ses with sups := ses.sups ++ [⟨n, ses.appliedF n, ses.nodeDF n, d⟩] }
  | .sendD n =>
    req (decide (n < N)) (fun _ => s!"sendD: node {n} out of range") fun _ =>
    .ok { ses with dmsgs := ses.dmsgs ++ [⟨n, ⟨ses.recs, ses.pruned⟩⟩] }
  | .adopt n R =>
    req (decide (n < N)) (fun _ => s!"adopt: node {n} out of range") fun _ =>
    req (ses.dmsgs.any fun e =>
        e.node == n && recEq e.log.recs R && ses.heldPrefix n e.log.recs e.log.pruned)
      (fun _ => s!"adopt: records {repr R} not announced to node {n}, or announced with \
        records pruned that it never took") fun _ =>
    req ((ses.es.nodeOf n).heads.all fun h => !(flat R).contains h)
      (fun _ => s!"adopt: records drop a head of node {n}") fun _ =>
    .ok (ses.adoptR n R)
  | .hubSupAccept n S O e d A Δ =>
    req (acceptB ses n S O e d A Δ) (fun _ => acceptError ses n S O e d A Δ) fun _ =>
    .ok (ses.supAccept (ses.es.acceptPush n S O d) Δ)
  | .hubPushRefuse n S O e d A Δ =>
    req (ses.es.inNet (.push n S O e d))
      (fun _ => s!"hubPushRefuse: push({e}, {d}) from node {n} not in net") fun _ =>
    req (ses.sups.any fun s => s.node == n && recEq s.applied A && seteq s.dropped Δ && s.head == d)
      (fun _ => s!"hubPushRefuse: no supersede {showL Δ} from node {n} with {d} in net")
      fun _ =>
    req (!recEq A ses.recs || ses.remDL.contains d || (pendingOf A Δ).contains d)
      (fun _ => s!"hubPushRefuse: node {n}'s records are the hub's, and {d} isn't dropped")
      fun _ =>
    .ok ses
  | .hubSupReject n S O e d A Δ =>
    req (rejectB ses n S O e d A Δ)
      (fun _ => s!"hubSupReject: push({e}, {d}) from node {n} is acceptable, or not its \
        supersede with the hub's records") fun _ =>
    baseCore N ses (.hubPushReject n S O e d)
  | .advancePrepared n R =>
    req (preparedB N ses n R)
      (fun _ => s!"advancePrepared: records {repr R} not announced to node {n}, dropping none \
        of its heads, or leaving a frontier not local") fun _ =>
    .ok (ses.preparedAdvance n R)
  | .prune k =>
    req (decide (ses.pruned ≤ k))
      (fun _ => s!"prune: pruned {ses.pruned} records already, more than {k}") fun _ =>
    req (decide (k ≤ ses.recs.length))
      (fun _ => s!"prune: {k} records, of {ses.recs.length}") fun _ =>
    req ((List.range N).all fun n => ses.heldPrefix n ses.recs k)
      (fun _ => s!"prune: a node has never taken the first {k} records") fun _ =>
    .ok (ses.pruneR k)

/-- The executable step. -/
def sexecStep (N : Nat) (ses : SEState) (a : SAction) : Except String SEState :=
  req ses.es.parOK (fun _ => "internal: an operation has a parent not below it") fun _ =>
  sexecCore N ses a

/-- Surviving images of the known head that no current head covers. A survivor advance replaces
a dropped known head by several heads, which raises the count of heads `mMulti` counts; this
count falls instead. -/
def uncoveredImages (par : Nat → List Nat) (D : Nat → Bool) (heads : List Nat)
    (known : Nat) : Nat :=
  ((exp par D known).filter (fun p => !heads.any (ancB par p))).length

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

/-- Nodes whose ordered applied records differ from the hub's, even with equal dropped sets. -/
def recordLagE (N : Nat) (ses : SEState) : Nat :=
  sumN N fun n => if recEq (ses.appliedF n) ses.recs then 0 else 1

/-- The set-based measure, followed by record reconciliation. Earlier progress may increase
record lag; a record-only adoption must decrease it. -/
def recordMeasureE (N : Nat) (ses : SEState) := (ses.smeasureE N, ses.recordLagE N)

/-- Concrete convergence also requires the ordered records used by the push guard. -/
def recordConvergedE (N : Nat) (ses : SEState) : Bool :=
  ses.sconvergedE N && (List.range N).all fun n => recEq (ses.appliedF n) ses.recs

/-- `mAdv` through surviving images: what of node `n`'s known head no head covers. -/
def advCE (ses : SEState) (n : Nat) : Nat :=
  uncoveredImages ses.es.parF (ses.nodeDF n).contains
    (ses.es.nodeOf n).heads (ses.es.nodeOf n).known.head

/-- `settledE` through surviving images: one head, accepted, past what survives of its known
head, and comparable with what survives of every head in the hub's history. -/
def settledCE (ses : SEState) (n : Nat) : Bool :=
  match (ses.es.nodeOf n).heads with
  | [] => false
  | x :: _ =>
    (ses.es.nodeOf n).heads.all (· == x) && ancB ses.es.parF x ses.es.hub.head &&
      (!(ses.nodeDF n).contains (ses.es.nodeOf n).known.head ||
        belowB ses.es.parF (ses.nodeDF n).contains (ses.es.nodeOf n).known.head x) &&
      (List.range (ses.es.hub.seq + 1)).all fun i =>
        (exp ses.es.parF (ses.nodeDF n).contains (ses.es.hub.histF i)).all fun p =>
          ancB ses.es.parF x p || ancB ses.es.parF p x

/-- `rmeasureE` through surviving images. -/
def rmeasureCE (N : Nat) (ses : SEState) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (cntE N (fun n => !(ses.es.consistentE n && ses.settledCE n)),
    cntE N (fun n => !ses.es.consistentE n), sumN N ses.es.staleRE,
    sumN N ses.es.missE, sumN N ses.advCE, sumN N ses.es.multiE)

def recordMeasureCE (N : Nat) (ses : SEState) :=
  ((ses.pendE N, ses.lagE N, ses.rmeasureCE N), ses.recordLagE N)

def recordRankCE (N : Nat) (ses : SEState) : List Nat :=
  let ((p, l, a, b, c, d, e, f), records) := ses.recordMeasureCE N
  [p, l, a, b, c, d, e, f, records]

end SEState

/-- The lexicographic order used by the Rust harness's vector comparison. -/
def rankLess : List Nat → List Nat → Bool
  | [], ys => !ys.isEmpty
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then rankLess xs ys else decide (x < y)

end Musubi.Exec

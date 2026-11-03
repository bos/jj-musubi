/-
The hive as one system (`SysStep`), whose node component is NodeSettle's `NS` itself, and the
simulation of each node's core in it (`node_sim`).

Each node keeps its own graph: its labels, numbered as it comes to have the operations, parents
first, and a scoped embedding `emb` of them into the hive's raw operation ids (`Scoped`). A node's
operations are its own writes, each a fresh raw id or one that exists already, identical
canonical content being one raw operation (`GrowR`), and the hub's operations it learns from
replies and notifications naming a head (`Learn`, a primitive law of the adapter).
Another node's writes only grow the raw graph above every id in use: they never touch this
node's component, and its embedding stays scoped (`scoped_raw`). So once the hub has settled and
the node has labels for everything below its head, foreign growth is a literal frame of the node.

The system is the hive after root's RecordEpoch cut (`record_disturbances_stop`): records are
fixed, adoptions and stale-plan reopens have stopped, and a failed call is not an event. Its
adoption steps (`Loc.adopt`, `Loc.advanceTake`) carry `GrowR`, which native record adoption is
not shown to keep: they are in the model for its shape, unreachable in the tail it is used for,
and not claimed for earlier runs.

A core step that sends requests (`Issue`) leaves the node's state as it was, recording the state
after its writes and the immutable push it built from that state, until the replies to its
requests, correlated by slot, come back (`handle`): then the node takes one NodeSettle step. The
hub answers requests one at a time, in any order, from its state when it answers; an accepted
push publishes notifications, which a node takes only between rounds. The hub refuses a push
whose new head is dropped, as natively, and a node never sends one (`issue`'s `hnd`, a primitive
law of the node); it never answers `Incomplete` (`HubLaw`).
-/
import Musubi.EarlyEntry

namespace Musubi.NodeSys

open Musubi Musubi.NodeSettle Musubi.EarlyEntry

/-! ## The system -/

/-- The hub's sequence, head (a raw id) and records, when it answers. -/
structure Snap where
  seq : Nat
  head : Nat
  recs : Nat
  deriving DecidableEq

/-- A push, fixed when it is sent, from the sender's state after its write: its generation of
writes (a ghost), the pair it knows, the new head, its records and its pending drops, in raw
ids. -/
structure Pkt where
  node : Nat
  gen : Nat
  knownSeq : Nat
  expected : Nat
  new : Nat
  recs : Nat
  pending : List Nat
  deriving DecidableEq

inductive Body
  | fetch
  | objs
  | push (p : Pkt)
  deriving DecidableEq

/-- A request in flight from node `node`, under a virtual slot: the logical id the system gives
each call of a step when the step issues them all (`Sys.slot`), not the transport's wire id,
which the transport assigns as it sends each call. A projection of a native run maps the wire
id of each call actually sent, and the call each reply answers, injectively to these slots
(root's `CallBatch`); the map need not keep order, and a call not yet sent has no wire id. So
a step's later call, as the `Objects` call a poll sends only once its `Fetch` has returned, has
its slot from the start, while other nodes' calls take wire ids in between. -/
structure Req where
  node : Nat
  slot : Nat
  body : Body
  deriving DecidableEq

inductive Ans
  | fetched (s : Snap)
  | objects
  | head (s : Snap)
  | refused (recs : Nat)

/-- A reply in flight: the request it answers, by slot and body, the system time it was
answered and whether the hub accepted a push then (ghosts), and the answer. -/
structure Rep where
  node : Nat
  slot : Nat
  time : Nat
  req : Body
  acc : Bool
  ans : Ans

structure Note where
  node : Nat
  time : Nat
  snap : Snap
  deriving DecidableEq

/-- What kind of step sent requests. -/
inductive Kind
  | start
  | fetchPoll
  | fetchObjs
  | differPoll
  | push
  | writePoll
  deriving DecidableEq

/-- A step whose requests are out: their slots, the state after its writes, the new head of a
push, and the embedding after the writes. -/
structure Wait where
  kind : Kind
  slots : List Nat
  post : NS
  new : Nat
  emb : Nat → Nat

structure NodeC where
  ns : NS
  emb : Nat → Nat
  gen : Nat
  wait : Option Wait

/-- The hive: a clock; the raw graph; the hub; the nodes; the requests, replies and
notifications in flight; and the next free virtual slot, every slot below it having been given
to a step's calls (`Req`). -/
structure Sys where
  time : Nat
  next : Nat
  par : Nat → List Nat
  hub : Snap
  node : Nat → NodeC
  reqs : List Req
  reps : List Rep
  notes : List Note
  slot : Nat

/-! ## Graphs: labels and raw ids -/

/-- A node's labels below `σ.next` stand for distinct raw ids in use, whose raw parents are the
images of their parents. -/
structure Scoped (σ : NS) (emb : Nat → Nat) (g : Sys) : Prop where
  inj : ∀ x y, x < σ.next → y < σ.next → emb x = emb y → x = y
  lt : ∀ x, x < σ.next → emb x < g.next
  par : ∀ x, x < σ.next → g.par (emb x) = (σ.par x).map emb

/-- The node has labels for every raw operation below `h`. -/
def Closed (σ : NS) (emb : Nat → Nat) (g : Sys) (h : Nat) : Prop :=
  ∀ y, Anc g.par y h → ∃ x, x < σ.next ∧ emb x = y

/-- A node's own writes: its labels from `σ.next` on stand for fresh raw ids, in order, and
nothing below either moves. -/
structure Grow (g g' : Sys) (σ σ' : NS) (emb emb' : Nat → Nat) : Prop where
  next : σ.next ≤ σ'.next
  rawNext : g'.next = g.next + (σ'.next - σ.next)
  embOld : ∀ x, x < σ.next → emb' x = emb x
  embNew : ∀ x, σ.next ≤ x → x < σ'.next → emb' x = g.next + (x - σ.next)
  parRaw : ∀ y, y < g.next → g'.par y = g.par y
  parNew : ∀ x, σ.next ≤ x → x < σ'.next → g'.par (emb' x) = (σ'.par x).map emb'
  parOld : ∀ x, x < σ.next → σ'.par x = σ.par x

/-- A node's own writes, where a write may COALESCE with an existing operation: identical
canonical content (an own merge another copy also wrote, `canonical_form`) is one raw vertex.
Each new label stands for a raw id below `g'.next`: either one that did not exist (from
`g.next` on), whose parents are the images of its parents, or an existing one with those same
parents that no old label stands for. The new labels stand for distinct ids, and every newly
existing raw id is one of them; nothing below moves. `Grow` is the case that reuses nothing
(`Grow.toR`). -/
structure GrowR (g g' : Sys) (σ σ' : NS) (emb emb' : Nat → Nat) : Prop where
  next : σ.next ≤ σ'.next
  rawGrows : g.next ≤ g'.next
  embOld : ∀ x, x < σ.next → emb' x = emb x
  parRaw : ∀ y, y < g.next → g'.par y = g.par y
  parOld : ∀ x, x < σ.next → σ'.par x = σ.par x
  bound : ∀ x, σ.next ≤ x → x < σ'.next → emb' x < g'.next
  parNew : ∀ x, σ.next ≤ x → x < σ'.next → g'.par (emb' x) = (σ'.par x).map emb'
  reuse : ∀ x, σ.next ≤ x → x < σ'.next → emb' x < g.next → ∀ y, y < σ.next → emb y ≠ emb' x
  injNew : ∀ x y, σ.next ≤ x → x < σ'.next → σ.next ≤ y → y < σ'.next → emb' x = emb' y →
    x = y
  cover : ∀ y, g.next ≤ y → y < g'.next → ∃ x, σ.next ≤ x ∧ x < σ'.next ∧ emb' x = y

/-- Raw growth elsewhere: ids only above every id in use, nothing below moved. -/
def RawGrow (g g' : Sys) : Prop := g.next ≤ g'.next ∧ ∀ y, y < g.next → g'.par y = g.par y

/-- What a reply or notification naming the head `hd` (if it names one) teaches the node of the
hub's graph: labels for raw operations below it it had none for. A primitive law of the adapter:
nothing is learnt when the node has labels for everything below `hd`, the new embedding is
scoped, and a step that wrote nothing still has its state as its state after. -/
structure Learn (g : Sys) (σ post : NS) (emb : Nat → Nat) (hd : Option Nat)
    (σi posti : NS) (embi : Nat → Nat) : Prop where
  nothing : (∀ h, hd = some h → Closed post emb g h) → σi = σ ∧ posti = post ∧ embi = emb
  scope : Scoped posti embi g
  same : post = σ → posti = σi
  /-- Only labels are added: every control field is as it was, and old labels keep their
  parents and raw ids. -/
  ctl : σi = { σ with par := σi.par, next := σi.next } ∧
    posti = { post with par := posti.par, next := posti.next }
  grows : post.next ≤ posti.next ∧ σ.next ≤ σi.next
  parOld : ∀ x, x < post.next → posti.par x = post.par x
  embOld : ∀ x, x < post.next → embi x = emb x
  /-- Labels are added parents first. -/
  parLt : ParLt posti.par

/-- What a reply says of the hub's context. -/
def Fits (emb : Nat → Nat) (next : Nat) (c : Ctx) : Ans → Prop
  | .fetched s => c.S = s.seq ∧ c.H < next ∧ emb c.H = s.head ∧ c.R = s.recs
  | .head s => c.S = s.seq ∧ c.H < next ∧ emb c.H = s.head ∧ c.R = s.recs
  | .refused r => c.R = r
  | .objects => True

/-- The head a reply names, if it names one. -/
def Ans.head? : Ans → Option Nat
  | .fetched s => some s.head
  | .head s => some s.head
  | .refused _ => none
  | .objects => none

/-! ## A node's steps -/

/-- The context for a node's steps that take no reply: only its drops matter (EarlyEntry's
`bctx`, whose pair is never the node's). -/
def lctx (d : Nat → Nat → Prop) (σ : NS) : Ctx := bctx 0 d σ.known

/-- The core's steps that send nothing, in `NodeCore::step`'s order (NodeSettle's `Busy`
constructors that take no reply). -/
inductive Loc (d : Nat → Nat → Prop) : NS → NS → Prop
  | adopt {σ σ' : NS} (A : Nat) (ha : σ.annc = some A) (hne : A ≠ σ.ap)
      (hb : ¬ Blocked (lctx d σ) σ A) (ht : Take (lctx d σ) σ σ' A) : Loc d σ σ'
  | merge {σ σ' : NS} (M : List Nat) (hg : Go (lctx d σ) σ) (h2 : 2 ≤ σ.heads.length)
      (hM : Keeps σ M) (he : σ' = fresh (norm σ) M) : Loc d σ σ'
  | mergeExisting {σ σ' : NS} (M : List Nat) (m : Nat) (hg : Go (lctx d σ) σ)
      (h2 : 2 ≤ σ.heads.length) (hM : Keeps σ M) (hm : m < σ.next)
      (hpar : ∀ y, y ∈ σ.par m ↔ y ∈ M) (he : σ' = mergeTo (norm σ) m) : Loc d σ σ'
  | prune {σ σ' : NS} (x : Nat) (hg : Go (lctx d σ) σ) (h2 : 2 ≤ σ.heads.length)
      (hM : Keeps σ [x]) (he : σ' = pruneTo (norm σ) x) : Loc d σ σ'
  | realizePlan {σ σ' : NS} (x : Nat) (rest : List Nat) (hg : Go (lctx d σ) σ)
      (h1 : σ.heads.length < 2) (hl : ¬ σ.loc σ.known.2) (hp : σ.plan = x :: rest)
      (he : σ' = realize (norm σ) x rest) : Loc d σ σ'
  | realizeSurvey {σ σ' : NS} (x : Nat) (L : List Nat) (hg : Go (lctx d σ) σ)
      (h1 : σ.heads.length < 2) (hl : ¬ σ.loc σ.known.2) (hp : σ.plan = [])
      (hr : Ready σ x) (he : σ' = realize (norm σ) x L) : Loc d σ σ'
  | advanceTake {σ σ' : NS} (A : Nat) (hg : Go (lctx d σ) σ) (h1 : σ.heads.length < 2)
      (hl : σ.loc σ.known.2) (ha : (norm σ).annc = some A)
      (ht : Take (lctx d σ) { norm σ with plan := [] } σ' A) : Loc d σ σ'
  | advance {σ σ' : NS} (hg : Go (lctx d σ) σ) (h1 : σ.heads.length < 2) (hl : σ.loc σ.known.2)
      (hd : ¬ ∃ y ∈ σ.heads, Desc σ y) (ha : (norm σ).annc = none) (hv : Adv (norm σ) σ') :
      Loc d σ σ'

/-- A step that sends requests: the round's first `Fetch`, or a core step that polls, asks for
objects, or pushes, after its write (`WriteRes`), with the state after its write and the new
head. -/
def Issue (d : Nat → Nat → Prop) (σ : NS) : Kind → NS → Nat → Prop
  | .start, post, _ => σ.act = false ∧ post = σ
  | .fetchPoll, post, _ => σ.act = true ∧ Go (lctx d σ) σ ∧ σ.heads.length < 2 ∧
      ¬ σ.loc σ.known.2 ∧ σ.plan = [] ∧ (¬ ∃ x, Ready σ x) ∧ MissOps σ ∧ post = σ
  | .fetchObjs, post, _ => σ.act = true ∧ Go (lctx d σ) σ ∧ σ.heads.length < 2 ∧
      ¬ σ.loc σ.known.2 ∧ σ.plan = [] ∧ (¬ ∃ x, Ready σ x) ∧ ¬ MissOps σ ∧ MissObjs σ ∧
      post = σ
  | .differPoll, post, _ => σ.act = true ∧ Go (lctx d σ) σ ∧ σ.heads.length < 2 ∧
      σ.loc σ.known.2 ∧ (∃ y ∈ σ.heads, Desc σ y) ∧ Differ σ ∧ (norm σ).annc = none ∧ post = σ
  | .push, post, new => σ.act = true ∧ Go (lctx d σ) σ ∧ σ.heads.length < 2 ∧
      σ.loc σ.known.2 ∧ (∃ y ∈ σ.heads, Desc σ y) ∧ (norm σ).annc = none ∧ ¬ Differ σ ∧
      (σ.pending ≠ [] ∨ σ.heads ≠ [σ.known.2]) ∧ WriteRes { norm σ with plan := [] } post new ∧
      new ≠ σ.known.2
  | .writePoll, post, new => σ.act = true ∧ Go (lctx d σ) σ ∧ σ.heads.length < 2 ∧
      σ.loc σ.known.2 ∧ (∃ y ∈ σ.heads, Desc σ y) ∧ (norm σ).annc = none ∧ ¬ Differ σ ∧
      σ.pending ≠ [] ∧ WriteRes { norm σ with plan := [] } post new ∧ new = σ.known.2

/-- A push the hub accepted while records were changing: the node learns the new head, which
stands for operations it has, and notes the new records; its op heads and graph stay. -/
structure AccLearn (c : Ctx) (post σ' : NS) : Prop where
  known : σ'.known = (c.S, c.H)
  hubRecs : σ'.hubRecs = some c.R
  ap : σ'.ap = post.ap
  par : σ'.par = post.par
  next : σ'.next = post.next
  act : σ'.act = post.act
  heads : σ'.heads = post.heads
  imgNe : σ'.img ≠ []
  imgLt : ∀ i ∈ σ'.img, i < post.next

/-- What the replies to a step's requests do, NodeSettle's reply contracts, the context `c`
being what the replies say, and `as` the answers.

A poll that also needs objects is one exchange, as natively: `NodeCore::fetch` builds both
calls from the survey at the exchange's start, the `Objects` call asking for what was missing
then (`MissObjs`); the driver sends them one at a time, taking the `Fetched` reply (which learns
the pair and stages operations) before it sends `Objects`; and no core step or notification
runs in between. So the replies are taken here in that order, `Fetched` then `Objects`, the
objects asked for being those missing at the start. The phase contract this relies on, that
nothing reads a node's state while its exchange is out but the exchange itself, holds in the
system: only `handle` changes a waiting node (`node_waiting`), the node's other steps all need
it not to wait, and no other step mentions its state. -/
def Handle (c : Ctx) (σ : NS) : Kind → NS → List Ans → NS → Prop
  | .start, _, _, σ' => ∃ σ1, FetchedRep c σ σ1 ∧ σ' = { σ1 with act := true }
  | .fetchPoll, _, _, σ' => ∃ σ1, FetchedRep c (norm σ) σ1 ∧
      ((MissObjs σ ∧ ObjRep σ1 σ' (fun x => Walk σ x ∧ ¬ σ.loc x ∧ σ.stg x ∧ ¬ σ.obj x)) ∨
        (¬ MissObjs σ ∧ σ' = σ1))
  | .fetchObjs, _, _, σ' =>
      ObjRep (norm σ) σ' (fun x => Walk σ x ∧ ¬ σ.loc x ∧ σ.stg x ∧ ¬ σ.obj x)
  | .differPoll, _, _, σ' => FetchedRep c { norm σ with plan := [] } σ'
  | .push, post, as, σ' =>
      ((∃ x, .refused x ∈ as) ∧ σ.ap ≠ c.R ∧ σ' = { post with hubRecs := some c.R }) ∨
      ((∃ s, .head s ∈ as) ∧ σ.ap = c.R ∧ HeadRep c post σ') ∨
      ((∃ s, .head s ∈ as) ∧ σ.ap ≠ c.R ∧ AccLearn c post σ')
  | .writePoll, post, _, σ' => FetchedRep c post σ'

/-- The push a step builds, from its state after its write, in raw ids. -/
def pkt (n gen : Nat) (post : NS) (emb : Nat → Nat) (new : Nat) : Pkt :=
  ⟨n, gen, post.known.1, emb post.known.2, emb new, post.ap, post.pending.map emb⟩

/-- The requests a step sends. -/
def Bodies (σ : NS) (k : Kind) (p : Pkt) (bs : List Body) : Prop :=
  match k with
  | .start => bs = [.fetch]
  | .fetchPoll => (MissObjs σ ∧ bs = [.fetch, .objs]) ∨ (¬ MissObjs σ ∧ bs = [.fetch])
  | .fetchObjs => bs = [.objs]
  | .differPoll => bs = [.fetch]
  | .push => bs = [.push p]
  | .writePoll => bs = [.fetch]

/-! ## The hub's law and the system's steps -/

/-- The hub's own law for a push, a primitive contract of `Push.answer` after the record cut:
whether it accepts it, its records after, and that it accepts only with the hub's records, from
the hub's head, to another head with the hub's head in its raw ancestry, the new head not among
its pending drops. Raw ancestry is the guard only once records are fixed: an accept that changes
records checks contracted ancestry, which may jump the raw history, so this is not the native
law for all history.

`dropped R p` is the hub's first check, `is_dropped`: the push's new head is one records `R`
supersede, or among the push's own drops. `Push.answer` refuses such a push even with the hub's
records, as it refuses one with other records. It then answers a push of its own head with that
head, unmoved, and a push from its head whose closure it lacks after the upload with
`Incomplete`, which fails the node's round (`driver.rs`). There is no `Incomplete` here: the
raw hub-side simulation shows that an honest push from the hub's head is closed once uploaded
(`UploadCoversSplit`), so the hub never gives it. -/
structure HubLaw where
  accepts : Snap → (Nat → List Nat) → Pkt → Prop
  recsAfter : Nat → List Nat → Nat
  dropped : Nat → Pkt → Prop
  guards : ∀ h par p, accepts h par p →
    p.recs = h.recs ∧ p.expected = h.head ∧ p.new ≠ h.head ∧ Anc par h.head p.new ∧
      p.new ∉ p.pending

inductive CoreKind
  | busy
  | idle
  | maint

inductive Act
  | core (n : Nat) (k : CoreKind)
  | issue (n : Nat) (k : Kind)
  | answer
  | handle (n : Nat)
  /-- Node `n` takes the notification `nt`: the event names what it processes. -/
  | notice (n : Nat) (nt : Note)
  | ignore (n : Nat)
  | env

/-- Fields of the system other than the nodes, raw graph and clock, as they were. -/
structure Quiet (g g' : Sys) : Prop where
  hub : g'.hub = g.hub
  reqs : g'.reqs = g.reqs
  reps : g'.reps = g.reps
  notes : g'.notes = g.notes
  slot : g'.slot = g.slot

/-- One step of the hive, for `N` nodes with drops `D n` (record identity to dropped label). -/
inductive SysStep (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) :
    Act → Sys → Sys → Prop
  /-- A core step that sends nothing, with the node's writes, each new label a fresh raw id or
  one that exists already (`GrowR`). For an adoption that is a law only after the RecordEpoch
  cut, where there are none. -/
  | busy {g g' : Sys} (n : Nat) (σ' : NS) (emb' : Nat → Nat)
      (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = true)
      (hs : Loc (D n) (g.node n).ns σ')
      (hg : GrowR g g' (g.node n).ns σ' (g.node n).emb emb')
      (hnode : g'.node = upd g.node n ⟨σ', emb', (g.node n).gen, none⟩)
      (hq : Quiet g g') (ht : g'.time = g.time + 1) : SysStep N D law (.core n .busy) g g'
  /-- The core idles, and housekeeping writes nothing: the round ends. -/
  | idle {g g' : Sys} (n : Nat) (σ' : NS)
      (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = true)
      (hs : Idle (lctx (D n) (g.node n).ns) (g.node n).ns σ')
      (hnode : g'.node = upd g.node n ⟨σ', (g.node n).emb, (g.node n).gen, none⟩)
      (hr : g'.next = g.next ∧ g'.par = g.par)
      (hq : Quiet g g') (ht : g'.time = g.time + 1) : SysStep N D law (.core n .idle) g g'
  /-- The core idles, and housekeeping (`when_idle`) writes: the round goes on. -/
  | maint {g g' : Sys} (n : Nat) (σ1 σ' : NS) (emb' : Nat → Nat)
      (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = true)
      (hs : Idle (lctx (D n) (g.node n).ns) (g.node n).ns σ1)
      (hx : Ext { σ1 with act := true } σ')
      (hg : GrowR g g' (g.node n).ns σ' (g.node n).emb emb')
      (hnode : g'.node = upd g.node n
        ⟨σ', emb', (g.node n).gen + (σ'.next - (g.node n).ns.next), none⟩)
      (hq : Quiet g g') (ht : g'.time = g.time + 1) : SysStep N D law (.core n .maint) g g'
  /-- A step that sends requests: its writes are made and its push built, its state kept until
  the replies. A primitive law of the node, not proved here: the head it pushes is not one its
  own records or drops drop (`hnd`), so the hub refuses its push only for other records. -/
  | issue {g g' : Sys} (n : Nat) (k : Kind) (post : NS) (new : Nat) (emb1 : Nat → Nat)
      (rq : List Req)
      (hw : (g.node n).wait = none) (hs : Issue (D n) (g.node n).ns k post new)
      (hg : GrowR g g' (g.node n).ns post (g.node n).emb emb1)
      (hb : Bodies (g.node n).ns k
        (pkt n ((g.node n).gen + (post.next - (g.node n).ns.next)) post emb1 new)
        (rq.map Req.body))
      (hslot : ∀ q ∈ rq, q.node = n ∧ g.slot ≤ q.slot ∧ q.slot < g'.slot)
      (hnodup : (rq.map Req.slot).Nodup)
      (hnode : g'.node = upd g.node n
        ⟨(g.node n).ns, (g.node n).emb, (g.node n).gen + (post.next - (g.node n).ns.next),
          some ⟨k, rq.map Req.slot, post, new, emb1⟩⟩)
      (hreqs : g'.reqs = g.reqs ++ rq) (hslot' : g.slot ≤ g'.slot)
      (hrest : g'.hub = g.hub ∧ g'.reps = g.reps ∧ g'.notes = g.notes)
      (ht : g'.time = g.time + 1)
      (hnd : ∀ q ∈ rq, ∀ p, q.body = .push p → ¬ law.dropped p.recs p) :
      SysStep N D law (.issue n k) g g'
  /-- The hub answers one request in flight, from its state now, which leaves the list: that
  one copy, exactly (`List.erase`), as each call is answered once. An accepted push moves its
  head and publishes a notification to every node. -/
  | answer {g g' : Sys} (r : Req) (ans : Ans)
      (hr : r ∈ g.reqs) (hreqs : g'.reqs = g.reqs.erase r)
      (acc : Bool)
      (hans : (r.body = .fetch ∧ acc = false ∧ ans = .fetched g.hub ∧ g'.hub = g.hub ∧
          g'.notes = g.notes) ∨
        (r.body = .objs ∧ acc = false ∧ ans = .objects ∧ g'.hub = g.hub ∧ g'.notes = g.notes) ∨
        (∃ p, r.body = .push p ∧
          ((law.accepts g.hub g.par p ∧ acc = true ∧
              g'.hub = ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩ ∧
              ans = .head g'.hub ∧
              g'.notes = g.notes ++ (List.range N).map (fun m => ⟨m, g.time, g'.hub⟩)) ∨
            (¬ law.accepts g.hub g.par p ∧ acc = false ∧
              (p.recs ≠ g.hub.recs ∨ law.dropped g.hub.recs p) ∧
              ans = .refused g.hub.recs ∧ g'.hub = g.hub ∧ g'.notes = g.notes) ∨
            (¬ law.accepts g.hub g.par p ∧ acc = false ∧
              (p.recs = g.hub.recs ∧ ¬ law.dropped g.hub.recs p) ∧
              ans = .head g.hub ∧ g'.hub = g.hub ∧ g'.notes = g.notes))))
      (hreps : g'.reps = g.reps ++ [⟨r.node, r.slot, g.time, r.body, acc, ans⟩])
      (hrest : g'.node = g.node ∧ g'.next = g.next ∧ g'.par = g.par ∧ g'.slot = g.slot)
      (ht : g'.time = g.time + 1) : SysStep N D law .answer g g'
  /-- A node takes the replies to the requests of its step, matched by slot, learns what they
  teach of the hub's graph, and takes the NodeSettle step they finish. A head they name is
  labelled after the step's writes (`posti`), as the node's own new head is, when the hub took
  its push. -/
  | handle {g g' : Sys} (n : Nat) (w : Wait) (rs : List Rep) (hd : Option Nat) (c : Ctx)
      (σi posti σ' : NS) (embi : Nat → Nat)
      (hw : (g.node n).wait = some w)
      (hrs : ∀ r ∈ rs, r ∈ g.reps ∧ r.node = n ∧ r.slot ∈ w.slots)
      (hcov : ∀ s ∈ w.slots, ∃ r ∈ rs, r.slot = s)
      (hhd : ∀ r ∈ rs, ∀ h, r.ans.head? = some h → hd = some h)
      (hhd' : ∀ h, hd = some h → ∃ r ∈ rs, r.ans.head? = some h)
      (hl : Learn g (g.node n).ns w.post w.emb hd σi posti embi)
      (hc : c.drops = D n) (hf : ∀ r ∈ rs, Fits embi posti.next c r.ans)
      (hh : Handle c σi w.kind posti (rs.map Rep.ans) σ')
      (hnode : g'.node = upd g.node n ⟨σ', embi, (g.node n).gen, none⟩)
      (hreps : ∀ r, r ∈ g'.reps ↔ (r ∈ g.reps ∧ r ∉ rs))
      (hrest : g'.hub = g.hub ∧ g'.reqs = g.reqs ∧ g'.notes = g.notes ∧ g'.slot = g.slot ∧
        g'.next = g.next ∧ g'.par = g.par)
      (ht : g'.time = g.time + 1) : SysStep N D law (.handle n) g g'
  /-- Between rounds, a node takes a notification, which leaves the list: that one copy,
  exactly (`List.erase`), so a notification is processed at most as often as it was sent. -/
  | notice {g g' : Sys} (n : Nat) (nt : Note) (c : Ctx) (σi posti σ' : NS) (embi : Nat → Nat)
      (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = false)
      (hn : nt ∈ g.notes) (hnn : nt.node = n)
      (hnew : (g.node n).ns.known.1 < nt.snap.seq ∨ (nt.snap.seq = (g.node n).ns.known.1 ∧
        (g.node n).emb (g.node n).ns.known.2 = nt.snap.head))
      (hl : Learn g (g.node n).ns (g.node n).ns (g.node n).emb (some nt.snap.head) σi posti embi)
      (hc : c.drops = D n) (hf : Fits embi σi.next c (.head nt.snap))
      (hh : HeadRep c σi σ')
      (hnode : g'.node = upd g.node n ⟨σ', embi, (g.node n).gen, none⟩)
      (hnotes : g'.notes = g.notes.erase nt)
      (hrest : g'.hub = g.hub ∧ g'.reqs = g.reqs ∧ g'.reps = g.reps ∧ g'.slot = g.slot ∧
        g'.next = g.next ∧ g'.par = g.par)
      (ht : g'.time = g.time + 1) : SysStep N D law (.notice n nt) g g'
  /-- Between rounds, a node drops a notification that tells it nothing newer: an older
  sequence, or its own with another head. That one copy leaves the list, exactly. -/
  | ignore {g g' : Sys} (n : Nat) (nt : Note)
      (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = false)
      (hn : nt ∈ g.notes) (hnn : nt.node = n)
      (hold : nt.snap.seq < (g.node n).ns.known.1 ∨ (nt.snap.seq = (g.node n).ns.known.1 ∧
        (g.node n).emb (g.node n).ns.known.2 ≠ nt.snap.head))
      (hnode : g'.node = g.node)
      (hnotes : g'.notes = g.notes.erase nt)
      (hrest : g'.hub = g.hub ∧ g'.reqs = g.reqs ∧ g'.reps = g.reps ∧ g'.slot = g.slot ∧
        g'.next = g.next ∧ g'.par = g.par)
      (ht : g'.time = g.time + 1) : SysStep N D law (.ignore n) g g'
  /-- Anything else: machines outside the model write operations, growing the raw graph only. -/
  | env {g g' : Sys} (hr : RawGrow g g') (hnode : g'.node = g.node) (hq : Quiet g g')
      (ht : g'.time = g.time + 1) : SysStep N D law .env g g'

/-! ## Graph lemmas -/

/-- Foreign growth leaves a node's embedding scoped: its raw ids are below every new one, and
their parents do not move. -/
theorem scoped_raw {σ : NS} {emb : Nat → Nat} {g g' : Sys} (S : Scoped σ emb g)
    (h : RawGrow g g') : Scoped σ emb g' :=
  ⟨S.inj, fun x hx => Nat.lt_of_lt_of_le (S.lt x hx) h.1,
    fun x hx => by rw [h.2 _ (S.lt x hx)]; exact S.par x hx⟩

theorem Grow.raw {g g' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat} (G : Grow g g' σ σ' emb emb') :
    RawGrow g g' := ⟨by rw [G.rawNext]; omega, G.parRaw⟩

/-- A node's own writes keep its embedding scoped. -/
theorem scoped_grow {σ σ' : NS} {emb emb' : Nat → Nat} {g g' : Sys} (S : Scoped σ emb g)
    (hlt : ParLt σ.par) (G : Grow g g' σ σ' emb emb') : Scoped σ' emb' g' := by
  have hn := G.next
  have hr := G.rawNext
  refine ⟨fun x y hx hy he => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · by_cases hxo : x < σ.next <;> by_cases hyo : y < σ.next
    · rw [G.embOld x hxo, G.embOld y hyo] at he
      exact S.inj x y hxo hyo he
    · rw [G.embOld x hxo, G.embNew y (by omega) hy] at he
      have := S.lt x hxo
      omega
    · rw [G.embNew x (by omega) hx, G.embOld y hyo] at he
      have := S.lt y hyo
      omega
    · rw [G.embNew x (by omega) hx, G.embNew y (by omega) hy] at he
      omega
  · by_cases hxo : x < σ.next
    · rw [G.embOld x hxo]
      have := S.lt x hxo
      omega
    · rw [G.embNew x (by omega) hx]
      omega
  · by_cases hxo : x < σ.next
    · rw [G.embOld x hxo, G.parRaw _ (S.lt x hxo), S.par x hxo, G.parOld x hxo]
      apply List.map_congr_left
      intro p hp
      exact (G.embOld p (Nat.lt_trans (hlt x p hp) hxo)).symm
    · exact G.parNew x (by omega) hx

/-- Writing only fresh operations is a write. -/
theorem Grow.toR {g g' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat} (G : Grow g g' σ σ' emb emb') :
    GrowR g g' σ σ' emb emb' where
  next := G.next
  rawGrows := by rw [G.rawNext]; omega
  embOld := G.embOld
  parRaw := G.parRaw
  parOld := G.parOld
  bound := fun x h1 h2 => by rw [G.embNew x h1 h2, G.rawNext]; omega
  parNew := G.parNew
  reuse := fun x h1 h2 h => by rw [G.embNew x h1 h2] at h; omega
  injNew := fun x y hx1 hx2 hy1 hy2 he => by
    rw [G.embNew x hx1 hx2, G.embNew y hy1 hy2] at he; omega
  cover := fun y h1 h2 => ⟨σ.next + (y - g.next), by omega, by rw [G.rawNext] at h2; omega,
    by rw [G.embNew _ (by omega) (by rw [G.rawNext] at h2; omega)]; omega⟩

theorem GrowR.raw {g g' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat}
    (G : GrowR g g' σ σ' emb emb') : RawGrow g g' := ⟨G.rawGrows, G.parRaw⟩

/-- Writing no new label grows nothing. -/
theorem GrowR.same_next {g g' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat}
    (G : GrowR g g' σ σ' emb emb') (h : σ'.next = σ.next) : g'.next = g.next := by
  apply Nat.le_antisymm _ G.rawGrows
  apply Nat.le_of_not_lt
  intro hlt
  obtain ⟨x, h1, h2, -⟩ := G.cover g.next (Nat.le_refl _) hlt
  omega

/-- Writing one new label: it is the one fresh raw id, or an existing one and nothing grows. -/
theorem GrowR.one {g g' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat}
    (G : GrowR g g' σ σ' emb emb') (h : σ'.next = σ.next + 1) :
    (emb' σ.next = g.next ∧ g'.next = g.next + 1) ∨ (emb' σ.next < g.next ∧ g'.next = g.next) := by
  have only : ∀ y, g.next ≤ y → y < g'.next → emb' σ.next = y := by
    intro y h1 h2
    obtain ⟨x, hx1, hx2, hx⟩ := G.cover y h1 h2
    have : x = σ.next := by omega
    rw [← this]; exact hx
  by_cases hr : emb' σ.next < g.next
  · right
    refine ⟨hr, Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) G.rawGrows⟩
    have := only g.next (Nat.le_refl _) hlt
    omega
  · left
    have hb := G.bound σ.next (Nat.le_refl _) (by omega)
    have h0 := only g.next (Nat.le_refl _) (by omega)
    refine ⟨h0, Nat.le_antisymm (Nat.le_of_not_lt fun hlt => ?_) (by omega)⟩
    have := only (g.next + 1) (by omega) (by omega)
    omega

/-- A node's own writes, coalescing or not, keep its embedding scoped. -/
theorem scoped_growR {σ σ' : NS} {emb emb' : Nat → Nat} {g g' : Sys} (S : Scoped σ emb g)
    (hlt : ParLt σ.par) (G : GrowR g g' σ σ' emb emb') : Scoped σ' emb' g' := by
  refine ⟨fun x y hx hy he => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · by_cases hxo : x < σ.next <;> by_cases hyo : y < σ.next
    · rw [G.embOld x hxo, G.embOld y hyo] at he
      exact S.inj x y hxo hyo he
    · -- an old label and a new one: the new one is fresh, above every old id, or reused, no
      -- old label's
      rw [G.embOld x hxo] at he
      by_cases hr : emb' y < g.next
      · exact absurd he (G.reuse y (by omega) hy hr x hxo)
      · have := S.lt x hxo
        omega
    · rw [G.embOld y hyo] at he
      by_cases hr : emb' x < g.next
      · exact absurd he.symm (G.reuse x (by omega) hx hr y hyo)
      · have := S.lt y hyo
        omega
    · exact G.injNew x y (by omega) hx (by omega) hy he
  · by_cases hxo : x < σ.next
    · rw [G.embOld x hxo]
      have := S.lt x hxo
      have := G.rawGrows
      omega
    · exact G.bound x (by omega) hx
  · by_cases hxo : x < σ.next
    · rw [G.embOld x hxo, G.parRaw _ (S.lt x hxo), S.par x hxo, G.parOld x hxo]
      apply List.map_congr_left
      intro p hp
      exact (G.embOld p (Nat.lt_trans (hlt x p hp) hxo)).symm
    · exact G.parNew x (by omega) hx

/-- With a scoped embedding, a labelled operation's raw ancestors are labelled. -/
theorem labeled_anc {σ : NS} {emb : Nat → Nat} {g : Sys} (S : Scoped σ emb g)
    (hlt : ParLt σ.par) : ∀ {a x : Nat}, Anc g.par a x →
      (∃ l, l < σ.next ∧ emb l = x) → ∃ l, l < σ.next ∧ emb l = a := by
  intro a x hx
  induction hx with
  | refl => exact id
  | @step p x hp _ ih =>
    rintro ⟨l, hl, rfl⟩
    rw [S.par l hl, List.mem_map] at hp
    obtain ⟨l', hl', rfl⟩ := hp
    exact ih ⟨l', Nat.lt_trans (hlt l l' hl') hl, rfl⟩

theorem closed_of {σ : NS} {emb : Nat → Nat} {g : Sys} (S : Scoped σ emb g)
    (hlt : ParLt σ.par) {h : Nat} (hh : ∃ l, l < σ.next ∧ emb l = h) : Closed σ emb g h :=
  fun _ hy => labeled_anc S hlt hy hh

/-! ## Steps that take no reply hold in any context with the node's drops -/

section Transport

variable {c : Ctx} {d : Nat → Nat → Prop}

theorem go_congr {c' : Ctx} {σ : NS} (h : c'.drops = c.drops) (hg : Go c σ) : Go c' σ := by
  intro A ha hne
  obtain ⟨y, hy, hd⟩ := hg A ha hne
  exact ⟨y, hy, by rw [h]; exact hd⟩

theorem blocked_congr {c' : Ctx} {σ : NS} {A : Nat} (h : c'.drops = c.drops)
    (hb : ¬ Blocked c σ A) : ¬ Blocked c' σ A := by
  rintro ⟨y, hy, hd⟩
  exact hb ⟨y, hy, by rw [← h]; exact hd⟩

/-- Taking records holds in another context too, the graph only growing. -/
theorem take_congr {c' : Ctx} {σ σ' : NS} {A : Nat} (T : Take c σ σ' A)
    (I : NodeSettle.SInv c' σ)
    (hn : σ.next ≤ σ'.next) : Take c' σ σ' A where
  ap := T.ap
  plan := T.plan
  known := T.known
  hubRecs := T.hubRecs
  annc := T.annc
  act := T.act
  inv := ⟨T.inv.parLt, T.inv.knownLt, Nat.lt_of_lt_of_le I.hLt hn, T.inv.headsNe,
    T.inv.headsLt, T.inv.imgNe, T.inv.imgLt,
    fun h => by rw [T.hubRecs]; exact I.recs (T.known ▸ h)⟩

theorem loc_busy {σ σ' : NS} (h : Loc d σ σ') (I : NodeSettle.SInv c σ) (hd : c.drops = d)
    (hn : σ.next ≤ σ'.next) : Busy c σ σ' := by
  cases h with
  | adopt A ha hne hb ht => exact .adopt A ha hne (blocked_congr hd hb) (take_congr ht I hn)
  | merge M hg h2 hM he => exact .merge M (go_congr hd hg) h2 hM he
  | mergeExisting M m hg h2 hM hm hpar he =>
    exact .mergeExisting M m (go_congr hd hg) h2 hM hm hpar he
  | prune x hg h2 hM he => exact .prune x (go_congr hd hg) h2 hM he
  | realizePlan x rest hg h1 hl hp he => exact .realizePlan x rest (go_congr hd hg) h1 hl hp he
  | realizeSurvey x L hg h1 hl hp hr he =>
    exact .realizeSurvey x L (go_congr hd hg) h1 hl hp hr he
  | advanceTake A hg h1 hl ha ht =>
    exact .advanceTake A (go_congr hd hg) h1 hl ha (take_congr ht (I.norm.plan []) hn)
  | advance hg h1 hl hdd ha hv => exact .advance (go_congr hd hg) h1 hl hdd ha hv

theorem idle_congr {σ σ' : NS} (h : Idle (lctx d σ) σ σ') (hd : c.drops = d) : Idle c σ σ' := by
  cases h with
  | fetchIdle hg h1 hl hp hr ho hb he => exact .fetchIdle (go_congr hd hg) h1 hl hp hr ho hb he
  | differIdle hg h1 hl hdd hf hnr ha he =>
    exact .differIdle (go_congr hd hg) h1 hl hdd hf hnr ha he
  | goal hg h1 hl hdd hnr hf hp hh he => exact .goal (go_congr hd hg) h1 hl hdd hnr hf hp hh he

/-- A step that sent requests, with the replies, is NodeSettle's step, but for the push branch
of an accepted push that changed the records. -/
theorem issue_busy {σ post σ' : NS} {k : Kind} {new : Nat} {as : List Ans}
    (hi : Issue d σ k post new) (hk : k ≠ .start) (hh : Handle c σ k post as σ')
    (hd : c.drops = d) (hph : k = .push → σ.known ≠ (c.S, c.H))
    (hacc : k = .push → ¬ ((∃ s, .head s ∈ as) ∧ σ.ap ≠ c.R ∧ AccLearn c post σ')) :
    Busy c σ σ' := by
  cases k with
  | start => exact absurd rfl hk
  | fetchPoll =>
    obtain ⟨_, hg, h1, hl, hp, hr, hmo, hpost⟩ := hi
    obtain ⟨σ1, F, ho⟩ := hh
    exact .fetch σ1 (go_congr hd hg) h1 hl hp hr (Or.inl hmo) (Or.inl ⟨hmo, F⟩) ho
  | fetchObjs =>
    obtain ⟨_, hg, h1, hl, hp, hr, hmo, hmb, hpost⟩ := hi
    exact .fetch (norm σ) (go_congr hd hg) h1 hl hp hr (Or.inr hmb) (Or.inr ⟨hmo, rfl⟩)
      (Or.inl ⟨hmb, hh⟩)
  | differPoll =>
    obtain ⟨_, hg, h1, hl, hdd, hf, ha, hpost⟩ := hi
    exact .differPoll (go_congr hd hg) h1 hl hdd hf ha hh
  | push =>
    obtain ⟨_, hg, h1, hl, hdd, hnr, hf, hw, hw', hnew⟩ := hi
    refine .pushStale post new (go_congr hd hg) h1 hl hdd hnr hf hw (hph rfl) hw' hnew ?_
    rcases hh with ⟨-, hne, he⟩ | ⟨-, heq, F⟩ | ⟨hex, hne, A⟩
    · exact Or.inl ⟨hne, he⟩
    · exact Or.inr ⟨heq, F⟩
    · exact absurd ⟨hex, hne, A⟩ (hacc rfl)
  | writePoll =>
    obtain ⟨_, hg, h1, hl, hdd, hnr, hf, hw, hw', hnew⟩ := hi
    exact .writePoll post new (go_congr hd hg) h1 hl hdd hnr hf hw hw' hnew hh

end Transport

/-! ## Invariants -/

/-- What a request or reply for slot `s` of a step carries: a push's records are the state's
after its write; the first request of a step that polls is a `Fetch`. -/
def BodyFor (w : Wait) (s : Nat) (b : Body) : Prop :=
  (w.kind = .push → ∃ p, b = .push p ∧ p.recs = w.post.ap) ∧
    (w.slots.head? = some s → w.kind ≠ .push → w.kind ≠ .fetchObjs → b = .fetch)

/-- A step whose requests are out: it was a step the core could take, its writes keep the
embedding scoped and below them nothing moved, and its requests and replies are its own. -/
structure WaitOK (D : Nat → Nat → Nat → Prop) (n : Nat) (g : Sys) (w : Wait) : Prop where
  issue : Issue (D n) (g.node n).ns w.kind w.post w.new
  scope : Scoped w.post w.emb g
  next : (g.node n).ns.next ≤ w.post.next
  emb : ∀ x, x < (g.node n).ns.next → w.emb x = (g.node n).emb x
  slots : w.slots ≠ []
  reqs : ∀ q ∈ g.reqs, q.node = n → q.slot ∈ w.slots → BodyFor w q.slot q.body
  reps : ∀ r ∈ g.reps, r.node = n → r.slot ∈ w.slots → BodyFor w r.slot r.req

structure NodeOK (D : Nat → Nat → Nat → Prop) (n : Nat) (g : Sys) : Prop where
  inv : LInv (g.node n).ns
  scope : Scoped (g.node n).ns (g.node n).emb g
  wait : ∀ w, (g.node n).wait = some w → WaitOK D n g w

/-- Slots in flight are below the next one, a reply is what the hub's law answers its request
with, and no push in flight drops its own new head, so it is refused only for other records. -/
structure SysOK (law : HubLaw) (g : Sys) : Prop where
  reqs : ∀ q ∈ g.reqs, q.slot < g.slot
  reps : ∀ r ∈ g.reps, r.slot < g.slot
  fetch : ∀ r ∈ g.reps, r.req = .fetch → ∃ s, r.ans = .fetched s
  push : ∀ r ∈ g.reps, ∀ p, r.req = .push p → r.acc = false →
    (∀ x, r.ans = .refused x → p.recs ≠ x) ∧ (∀ s, r.ans = .head s → p.recs = s.recs)
  pushAns : ∀ r ∈ g.reps, ∀ p, r.req = .push p →
    (∃ x, r.ans = .refused x) ∨ (∃ s, r.ans = .head s)
  honest : ∀ q ∈ g.reqs, ∀ p, q.body = .push p → ¬ law.dropped p.recs p

/-- What a stable hub answers. -/
def AnsStable (st : Snap) : Ans → Prop
  | .fetched s => s = st
  | .head s => s = st
  | .refused x => x = st.recs
  | .objects => True

/-- Replies answered since `t0` are a stable hub's, and none accepted a push. -/
def StableReps (t0 : Nat) (st : Snap) (g : Sys) : Prop :=
  ∀ r ∈ g.reps, t0 ≤ r.time → r.acc = false ∧ AnsStable st r.ans

theorem SysStep.time {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act}
    {g g' : Sys} (h : SysStep N D law a g g') : g'.time = g.time + 1 := by
  cases h <;> assumption


/-! ## Helpers for the simulation -/

theorem idle_graph {c : Ctx} {σ σ' : NS} (h : Idle c σ σ') :
    σ'.par = σ.par ∧ σ'.next = σ.next ∧ σ'.act = false := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl, rfl⟩
  | differIdle _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl, rfl⟩
  | goal _ _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl, rfl⟩

/-- The state after a step's write, as its own: well formed, if the step's state is. -/
theorem post_inv {c : Ctx} {d : Nat → Nat → Prop} {σ post : NS} {k : Kind} {new : Nat}
    (hi : Issue d σ k post new) (I : NodeSettle.SInv c σ) : NodeSettle.SInv c post := by
  cases k with
  | start => obtain ⟨_, rfl⟩ := hi; exact I
  | fetchPoll => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hi; exact I
  | fetchObjs => obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hi; exact I
  | differPoll => obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hi; exact I
  | push =>
    obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hi
    exact (I.norm.plan []).writeRes hw'
  | writePoll =>
    obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hi
    exact (I.norm.plan []).writeRes hw'

/-- A step that wrote nothing kept its state. -/
theorem post_same {d : Nat → Nat → Prop} {σ post : NS} {k : Kind} {new : Nat}
    (hi : Issue d σ k post new) (hk : k ≠ .push) (hk' : k ≠ .writePoll) : post = σ := by
  cases k with
  | start => exact hi.2
  | fetchPoll => exact hi.2.2.2.2.2.2.2
  | fetchObjs => exact hi.2.2.2.2.2.2.2.2
  | differPoll => exact hi.2.2.2.2.2.2.2
  | push => exact absurd rfl hk
  | writePoll => exact absurd rfl hk'

theorem write_ap {σ σ1 : NS} {new : Nat} (W : WriteRes σ σ1 new) : σ1.ap = σ.ap := by
  obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
  · exact F.ext.ap
  · subst he; rfl

/-- A reply naming the stable hub fixes the context, the head's label being unique. -/
theorem ctx_of_fits {emb : Nat → Nat} {bound next h : Nat} {c' : Ctx} {st : Snap}
    {d : Nat → Nat → Prop} (hinj : ∀ x y, x < bound → y < bound → emb x = emb y → x = y)
    (hnb : next ≤ bound) (hh : h < bound) (he : emb h = st.head) (hd : c'.drops = d)
    (hf : c'.S = st.seq ∧ c'.H < next ∧ emb c'.H = st.head ∧ c'.R = st.recs) :
    c' = ⟨st.seq, h, st.recs, d⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := hf
  have hH : c'.H = h := hinj _ _ (by omega) hh (h3.trans he.symm)
  cases c'
  simp only at h1 hH h4 hd
  subst h1 hH h4 hd
  rfl

theorem bodies_ne {σ : NS} {k : Kind} {p : Pkt} {bs : List Body} (h : Bodies σ k p bs) :
    bs ≠ [] := by
  cases k <;> simp only [Bodies] at h
  all_goals first
    | (rw [h]; exact List.cons_ne_nil _ _)
    | (rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> exact List.cons_ne_nil _ _)

/-- A wait survives an event that leaves its node alone: the raw graph only grows, requests in
flight for the node are ones there were, and replies for it answer ones there were. -/
theorem waitOK_frame {D : Nat → Nat → Nat → Prop} {n : Nat} {g g' : Sys} {w : Wait}
    (W : WaitOK D n g w) (hn : g'.node n = g.node n) (hr : RawGrow g g')
    (hq : ∀ q ∈ g'.reqs, q.node = n → q ∈ g.reqs)
    (hp : ∀ r ∈ g'.reps, r.node = n → r ∈ g.reps ∨
      ∃ q ∈ g.reqs, q.node = n ∧ q.slot = r.slot ∧ q.body = r.req) : WaitOK D n g' w where
  issue := by rw [hn]; exact W.issue
  scope := scoped_raw W.scope hr
  next := by rw [hn]; exact W.next
  emb := by rw [hn]; exact W.emb
  slots := W.slots
  reqs := fun q hq' hqn hs => W.reqs q (hq q hq' hqn) hqn hs
  reps := by
    intro r hr' hrn hs
    rcases hp r hr' hrn with h | ⟨q, hq', hqn, hqs, hqb⟩
    · exact W.reps r h hrn hs
    · rw [← hqb, ← hqs]
      exact W.reqs q hq' hqn (by rw [hqs]; exact hs)


/-! ## The system invariants are kept -/

theorem sysOK_same {law : HubLaw} {g g' : Sys} (S : SysOK law g) (hq : g'.reqs = g.reqs)
    (hr : g'.reps = g.reps) (hs : g'.slot = g.slot) : SysOK law g' :=
  ⟨by rw [hq, hs]; exact S.reqs, by rw [hr, hs]; exact S.reps, by rw [hr]; exact S.fetch,
    by rw [hr]; exact S.push, by rw [hr]; exact S.pushAns, by rw [hq]; exact S.honest⟩

theorem sysOK_sub {law : HubLaw} {g g' : Sys} (S : SysOK law g) (hq : g'.reqs = g.reqs)
    (hr : ∀ r ∈ g'.reps, r ∈ g.reps) (hs : g'.slot = g.slot) : SysOK law g' :=
  ⟨by rw [hq, hs]; exact S.reqs, fun r h => by rw [hs]; exact S.reps r (hr r h),
    fun r h => S.fetch r (hr r h), fun r h => S.push r (hr r h),
    fun r h => S.pushAns r (hr r h), by rw [hq]; exact S.honest⟩

theorem sysOK_issue {law : HubLaw} {g g' : Sys} {rq : List Req} (S : SysOK law g)
    (hq : g'.reqs = g.reqs ++ rq) (hr : g'.reps = g.reps) (hs : g.slot ≤ g'.slot)
    (hslot : ∀ q ∈ rq, q.slot < g'.slot)
    (hnd : ∀ q ∈ rq, ∀ p, q.body = .push p → ¬ law.dropped p.recs p) : SysOK law g' := by
  refine ⟨fun q h => ?_, by rw [hr]; exact fun r h => by have := S.reps r h; omega,
    by rw [hr]; exact S.fetch, by rw [hr]; exact S.push, by rw [hr]; exact S.pushAns,
    fun q h => ?_⟩
  · rw [hq, List.mem_append] at h
    rcases h with h | h
    · have := S.reqs q h; omega
    · exact hslot q h
  · rw [hq, List.mem_append] at h
    rcases h with h | h
    · exact S.honest q h
    · exact hnd q h

theorem stable_sub {t0 : Nat} {st : Snap} {g g' : Sys} (R : StableReps t0 st g)
    (hr : ∀ r ∈ g'.reps, r ∈ g.reps) : StableReps t0 st g' :=
  fun r h ht => R r (hr r h) ht

section Answer

variable {N : Nat} {law : HubLaw} {g g' : Sys} {r : Req} {ans : Ans} {acc : Bool}

theorem sysOK_answer (S : SysOK law g) (hr : r ∈ g.reqs)
    (hreqs : g'.reqs = g.reqs.erase r)
    (hans : (r.body = .fetch ∧ acc = false ∧ ans = .fetched g.hub ∧ g'.hub = g.hub ∧
          g'.notes = g.notes) ∨
        (r.body = .objs ∧ acc = false ∧ ans = .objects ∧ g'.hub = g.hub ∧ g'.notes = g.notes) ∨
        (∃ p, r.body = .push p ∧
          ((law.accepts g.hub g.par p ∧ acc = true ∧
              g'.hub = ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩ ∧
              ans = .head g'.hub ∧
              g'.notes = g.notes ++ (List.range N).map (fun m => ⟨m, g.time, g'.hub⟩)) ∨
            (¬ law.accepts g.hub g.par p ∧ acc = false ∧
              (p.recs ≠ g.hub.recs ∨ law.dropped g.hub.recs p) ∧
              ans = .refused g.hub.recs ∧ g'.hub = g.hub ∧ g'.notes = g.notes) ∨
            (¬ law.accepts g.hub g.par p ∧ acc = false ∧
              (p.recs = g.hub.recs ∧ ¬ law.dropped g.hub.recs p) ∧
              ans = .head g.hub ∧ g'.hub = g.hub ∧ g'.notes = g.notes))))
    (hreps : g'.reps = g.reps ++ [⟨r.node, r.slot, g.time, r.body, acc, ans⟩])
    (hslot : g'.slot = g.slot) : SysOK law g' := by
  have sub : ∀ q ∈ g'.reqs, q ∈ g.reqs := fun q h =>
    (by rw [hreqs] at h; exact List.mem_of_mem_erase h)
  refine ⟨fun q h => by rw [hslot]; exact S.reqs q (sub q h), ?_, ?_, ?_, ?_,
    fun q h => S.honest q (sub q h)⟩
  · intro x h
    rw [hreps, List.mem_append, List.mem_singleton] at h
    rw [hslot]
    rcases h with h | rfl
    · exact S.reps x h
    · exact S.reqs r hr
  · intro x h hx
    rw [hreps, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact S.fetch x h hx
    · simp only at hx
      rcases hans with ⟨-, -, he, -⟩ | ⟨hb, -⟩ | ⟨p, hb, -⟩
      · exact ⟨_, he⟩
      · rw [hb] at hx; cases hx
      · rw [hb] at hx; cases hx
  · intro x h p hx ha
    rw [hreps, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact S.push x h p hx ha
    · simp only at hx ha
      rcases hans with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨p', hb, hh⟩
      · rw [hb] at hx; cases hx
      · rw [hb] at hx; cases hx
      · rw [hb] at hx
        cases hx
        rcases hh with ⟨-, hacc, -⟩ | ⟨-, -, hne, he, -⟩ | ⟨-, -, heq, he, -⟩
        · rw [hacc] at ha; cases ha
        · refine ⟨fun y hy => ?_, fun s hs => ?_⟩
          · simp only at hy; rw [he] at hy; cases hy
            -- with the hub's records, only a push that drops its own head is refused
            intro hrec
            rcases hne with hne | hd
            · exact hne hrec
            · rw [← hrec] at hd
              exact S.honest _ hr p hb hd
          · simp only at hs; rw [he] at hs; cases hs
        · refine ⟨fun y hy => ?_, fun s hs => ?_⟩
          · simp only at hy; rw [he] at hy; cases hy
          · simp only at hs; rw [he] at hs; cases hs; exact heq.1
  · intro x h p hx
    rw [hreps, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact S.pushAns x h p hx
    · simp only at hx ⊢
      rcases hans with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨p', hb, hh⟩
      · rw [hb] at hx; cases hx
      · rw [hb] at hx; cases hx
      · rcases hh with ⟨-, -, -, he, -⟩ | ⟨-, -, -, he, -⟩ | ⟨-, -, -, he, -⟩
        · exact Or.inr ⟨_, he⟩
        · exact Or.inl ⟨_, he⟩
        · exact Or.inr ⟨_, he⟩

theorem stable_answer {t0 : Nat} {st : Snap} (R : StableReps t0 st g) (hhub : g.hub = st)
    (hhub' : g'.hub = st)
    (hans : (r.body = .fetch ∧ acc = false ∧ ans = .fetched g.hub ∧ g'.hub = g.hub ∧
          g'.notes = g.notes) ∨
        (r.body = .objs ∧ acc = false ∧ ans = .objects ∧ g'.hub = g.hub ∧ g'.notes = g.notes) ∨
        (∃ p, r.body = .push p ∧
          ((law.accepts g.hub g.par p ∧ acc = true ∧
              g'.hub = ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩ ∧
              ans = .head g'.hub ∧
              g'.notes = g.notes ++ (List.range N).map (fun m => ⟨m, g.time, g'.hub⟩)) ∨
            (¬ law.accepts g.hub g.par p ∧ acc = false ∧
              (p.recs ≠ g.hub.recs ∨ law.dropped g.hub.recs p) ∧
              ans = .refused g.hub.recs ∧ g'.hub = g.hub ∧ g'.notes = g.notes) ∨
            (¬ law.accepts g.hub g.par p ∧ acc = false ∧
              (p.recs = g.hub.recs ∧ ¬ law.dropped g.hub.recs p) ∧
              ans = .head g.hub ∧ g'.hub = g.hub ∧ g'.notes = g.notes))))
    (hreps : g'.reps = g.reps ++ [⟨r.node, r.slot, g.time, r.body, acc, ans⟩]) :
    StableReps t0 st g' := by
  intro x h ht
  rw [hreps, List.mem_append, List.mem_singleton] at h
  rcases h with h | rfl
  · exact R x h ht
  · simp only
    rcases hans with ⟨-, ha, he, -⟩ | ⟨-, ha, he, -⟩ | ⟨p, -, hh⟩
    · rw [he, hhub]; exact ⟨ha, rfl⟩
    · rw [he]; exact ⟨ha, trivial⟩
    · rcases hh with ⟨-, -, hh', -⟩ | ⟨-, ha, -, he, -⟩ | ⟨-, ha, -, he, -⟩
      · rw [hhub, hhub'] at hh'
        have := congrArg Snap.seq hh'
        simp only at this
        omega
      · rw [he, hhub]; exact ⟨ha, rfl⟩
      · rw [he, hhub]; exact ⟨ha, rfl⟩

end Answer

/-! ## The node's core, simulated -/

/-- What a system step is to node `n`'s core: its own core step, the reply-taking step that
finishes a step that sent requests (the first `Fetch` of a round being the round's start), a
notification, a push from the stable hub's head (`emit`), or a frame. -/
def labOf (n : Nat) (c : Ctx) (g : Sys) : Act → Lab
  | .core m .busy => if m = n then .busy else .frame
  | .core m .idle => if m = n then .idle else .frame
  | .core m .maint => if m = n then .maint else .frame
  | .issue m k => if m = n ∧ k = .push ∧ (g.node n).ns.known = (c.S, c.H) then .emit
      else .frame
  | .handle m => if m = n then
      (match (g.node n).wait with
        | some w => if w.kind = .start then .start else .busy
        | none => .frame)
    else .frame
  | .notice m _ => if m = n then .notify else .frame
  | .ignore _ => .frame
  | .answer => .frame
  | .env => .frame

/-- What the simulation keeps, once the hub is stable at `st` and the node has `h` for its
head. -/
structure SimInv (law : HubLaw) (D : Nat → Nat → Nat → Prop) (n : Nat) (c : Ctx) (t0 : Nat)
    (st : Snap) (h : Nat) (g : Sys) : Prop where
  node : NodeOK D n g
  sys : SysOK law g
  reps : StableReps t0 st g
  hl : h < (g.node n).ns.next
  he : (g.node n).emb h = st.head
  sinv : NodeSettle.SInv c (g.node n).ns
  nopush : ∀ w, (g.node n).wait = some w → w.kind = .push →
    (g.node n).ns.known ≠ (c.S, c.H)

/-- An event that leaves the node alone is a frame of its core. -/
theorem frame_case {law : HubLaw} {D : Nat → Nat → Nat → Prop} {n t0 h : Nat} {st : Snap}
    {c : Ctx} {g g' : Sys} (I : SimInv law D n c t0 st h g) (hn : g'.node n = g.node n)
    (hr : RawGrow g g')
    (hq : ∀ q ∈ g'.reqs, q.node = n → q ∈ g.reqs)
    (hp : ∀ r ∈ g'.reps, r.node = n → r ∈ g.reps ∨
      ∃ q ∈ g.reqs, q.node = n ∧ q.slot = r.slot ∧ q.body = r.req)
    (hsys : SysOK law g') (hreps : StableReps t0 st g') :
    Ev c .frame (g.node n).ns (g'.node n).ns ∧ SimInv law D n c t0 st h g' := by
  rw [hn]
  refine ⟨.frame, ⟨⟨?_, ?_, ?_⟩, hsys, hreps, ?_, ?_, ?_, ?_⟩⟩
  · rw [hn]; exact I.node.inv
  · rw [hn]; exact scoped_raw I.node.scope hr
  · intro w hw
    rw [hn] at hw
    exact waitOK_frame (I.node.wait w hw) hn hr hq hp
  · rw [hn]; exact I.hl
  · rw [hn]; exact I.he
  · rw [hn]; exact I.sinv
  · rw [hn]; exact I.nopush


theorem scoped_same {σ σ' : NS} {emb : Nat → Nat} {g g' : Sys} (S : Scoped σ emb g)
    (hp : σ'.par = σ.par) (hn : σ'.next = σ.next) (hg : g'.next = g.next) (hgp : g'.par = g.par) :
    Scoped σ' emb g' :=
  ⟨by rw [hn]; exact S.inj, by rw [hn, hg]; exact S.lt, by rw [hn, hp, hgp]; exact S.par⟩

theorem objRep_graph {σ σ' : NS} {M : Nat → Prop} (O : ObjRep σ σ' M) :
    σ'.par = σ.par ∧ σ'.next = σ.next := by
  have h1 := congrArg NS.par O.rest
  have h2 := congrArg NS.next O.rest
  exact ⟨h1, h2⟩

/-- Replies teach the node nothing of the graph that its step did not write. -/
theorem handle_graph {c : Ctx} {d : Nat → Nat → Prop} {σ post σ' : NS} {k : Kind} {new : Nat}
    {as : List Ans} (hi : Issue d σ k post new) (hh : Handle c σ k post as σ') :
    σ'.par = post.par ∧ σ'.next = post.next := by
  cases k with
  | start =>
    obtain ⟨_, rfl⟩ := hi
    obtain ⟨σ1, F, rfl⟩ := hh
    exact ⟨F.par, F.next⟩
  | fetchPoll =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hi
    obtain ⟨σ1, F, ho⟩ := hh
    rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
    · exact ⟨(objRep_graph O).1.trans F.par, (objRep_graph O).2.trans F.next⟩
    · exact ⟨F.par, F.next⟩
  | fetchObjs =>
    obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hi
    have O : ObjRep (norm post) σ'
        (fun x => Walk post x ∧ ¬ post.loc x ∧ post.stg x ∧ ¬ post.obj x) := hh
    have h2 := objRep_graph O
    exact h2
  | differPoll =>
    obtain ⟨_, _, _, _, _, _, _, rfl⟩ := hi
    exact ⟨hh.par, hh.next⟩
  | push =>
    rcases hh with ⟨-, -, rfl⟩ | ⟨-, -, F⟩ | ⟨-, -, A⟩
    · exact ⟨rfl, rfl⟩
    · exact ⟨F.par, F.next⟩
    · exact ⟨A.par, A.next⟩
  | writePoll => exact ⟨hh.par, hh.next⟩

/-- The stable hub's head, named in a reply, fixes the context. -/
theorem fits_stable {emb : Nat → Nat} {bound next h : Nat} {c' : Ctx} {st : Snap}
    {d : Nat → Nat → Prop} (hinj : ∀ x y, x < bound → y < bound → emb x = emb y → x = y)
    (hnb : next ≤ bound) (hh : h < bound) (he : emb h = st.head) (hd : c'.drops = d) {a : Ans}
    (hf : Fits emb next c' a) (hs : AnsStable st a) (hsnap : ∃ s, a = .fetched s ∨ a = .head s) :
    c' = ⟨st.seq, h, st.recs, d⟩ := by
  obtain ⟨s, rfl | rfl⟩ := hsnap
  · have : s = st := hs
    subst this
    exact ctx_of_fits hinj hnb hh he hd hf
  · have : s = st := hs
    subst this
    exact ctx_of_fits hinj hnb hh he hd hf

/-- One step of the system, after the hub has settled at `st`, is a NodeSettle event of node
`n`'s core in the stable context, unless it is a push from the hub's head, and keeps what the
simulation needs. Of the replies and notifications for the node, only those the step takes are
asked to be new: the replies it removes, and the notification it processes. -/
theorem sim_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {n t0 h : Nat}
    {st : Snap} {a : Act} {g g' : Sys} {c : Ctx} (hc : c = ⟨st.seq, h, st.recs, D n⟩)
    (I : SimInv law D n c t0 st h g) (hs : SysStep N D law a g g')
    (hhub : g.hub = st) (hhub' : g'.hub = st)
    (hold : ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → t0 ≤ r.time)
    (hnotes : ∀ nt, a = .notice n nt → nt.snap = st)
    (hne : labOf n c g a ≠ .emit) :
    Ev c (labOf n c g a) (g.node n).ns (g'.node n).ns ∧ SimInv law D n c t0 st h g' := by
  have hcd : c.drops = D n := by rw [hc]
  have hcR : c.R = st.recs := by rw [hc]
  cases hs with
  | busy m σ' emb' hw ha hsl hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨σ', emb', (g.node m).gen, none⟩ := by rw [hnode, upd_same]
      have hb : Busy c (g.node m).ns σ' := loc_busy hsl I.sinv hcd hg.next
      have si : NodeSettle.SInv c σ' := inv_busy I.sinv hb
      have hlab : labOf m c g (.core m .busy) = .busy := by simp [labOf]
      rw [hlab, hn']
      refine ⟨.busy ha hb, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hn']; exact linv_of_sinv si
      · rw [hn']; exact scoped_growR I.node.scope I.node.inv.parLt hg
      · rw [hn']; intro w hw'; cases hw'
      · exact sysOK_same I.sys hq.reqs hq.reps hq.slot
      · intro r hr' ht'; rw [hq.reps] at hr'; exact I.reps r hr' ht'
      · rw [hn']; exact Nat.lt_of_lt_of_le I.hl hg.next
      · rw [hn']; show emb' h = st.head; rw [hg.embOld h I.hl]; exact I.he
      · rw [hn']; exact si
      · rw [hn']; intro w hw'; cases hw'
    · have hn' : g'.node n = g.node n := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hlab : labOf n c g (.core m .busy) = .frame := by simp [labOf, hm]
      rw [hlab]
      exact frame_case I hn' hg.raw (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
        (sysOK_same I.sys hq.reqs hq.reps hq.slot)
        (fun r hr' ht' => by rw [hq.reps] at hr'; exact I.reps r hr' ht')
  | idle m σ' hw ha hsl hnode hr hq ht =>
    have hraw : RawGrow g g' := ⟨Nat.le_of_eq hr.1.symm, fun y _ => by rw [hr.2]⟩
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨σ', (g.node m).emb, (g.node m).gen, none⟩ := by
        rw [hnode, upd_same]
      have hi : Idle c (g.node m).ns σ' := idle_congr hsl hcd
      have si : NodeSettle.SInv c σ' := inv_idle I.sinv hi
      obtain ⟨hgp, hgn, -⟩ := idle_graph hi
      have hlab : labOf m c g (.core m .idle) = .idle := by simp [labOf]
      rw [hlab, hn']
      refine ⟨.idle ha hi, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hn']; exact linv_of_sinv si
      · rw [hn']; exact scoped_same I.node.scope hgp hgn hr.1 hr.2
      · rw [hn']; intro w hw'; cases hw'
      · exact sysOK_same I.sys hq.reqs hq.reps hq.slot
      · intro r hr' ht'; rw [hq.reps] at hr'; exact I.reps r hr' ht'
      · rw [hn']; show h < σ'.next; rw [hgn]; exact I.hl
      · rw [hn']; exact I.he
      · rw [hn']; exact si
      · rw [hn']; intro w hw'; cases hw'
    · have hn' : g'.node n = g.node n := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hlab : labOf n c g (.core m .idle) = .frame := by simp [labOf, hm]
      rw [hlab]
      exact frame_case I hn' hraw (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
        (sysOK_same I.sys hq.reqs hq.reps hq.slot)
        (fun r hr' ht' => by rw [hq.reps] at hr'; exact I.reps r hr' ht')
  | maint m σ1 σ' emb' hw ha hsl hx hg hnode hq ht =>
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m =
          ⟨σ', emb', (g.node m).gen + (σ'.next - (g.node m).ns.next), none⟩ := by
        rw [hnode, upd_same]
      have hi : Idle c (g.node m).ns σ1 := idle_congr hsl hcd
      have ev : Ev c .maint (g.node m).ns σ' := .maint ha hi hx
      have si : NodeSettle.SInv c σ' := inv_ev I.sinv ev (fun h' => Lab.noConfusion h')
      have hlab : labOf m c g (.core m .maint) = .maint := by simp [labOf]
      rw [hlab, hn']
      refine ⟨ev, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hn']; exact linv_of_sinv si
      · rw [hn']; exact scoped_growR I.node.scope I.node.inv.parLt hg
      · rw [hn']; intro w hw'; cases hw'
      · exact sysOK_same I.sys hq.reqs hq.reps hq.slot
      · intro r hr' ht'; rw [hq.reps] at hr'; exact I.reps r hr' ht'
      · rw [hn']; exact Nat.lt_of_lt_of_le I.hl hg.next
      · rw [hn']; show emb' h = st.head; rw [hg.embOld h I.hl]; exact I.he
      · rw [hn']; exact si
      · rw [hn']; intro w hw'; cases hw'
    · have hn' : g'.node n = g.node n := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hlab : labOf n c g (.core m .maint) = .frame := by simp [labOf, hm]
      rw [hlab]
      exact frame_case I hn' hg.raw (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
        (sysOK_same I.sys hq.reqs hq.reps hq.slot)
        (fun r hr' ht' => by rw [hq.reps] at hr'; exact I.reps r hr' ht')
  | issue m k post new emb1 rq hw hissue hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
    have hsys := sysOK_issue I.sys hreqs hrest.2.1 hslot' (fun q hq => (hslot q hq).2.2) hnd
    by_cases hm : m = n
    · subst hm
      have hn' : g'.node m = ⟨(g.node m).ns, (g.node m).emb,
          (g.node m).gen + (post.next - (g.node m).ns.next),
          some ⟨k, rq.map Req.slot, post, new, emb1⟩⟩ := by rw [hnode, upd_same]
      have hnotemit : ¬ (k = .push ∧ (g.node m).ns.known = (c.S, c.H)) := by
        intro hk
        apply hne
        simp [labOf, hk.1, hk.2]
      have hlab : labOf m c g (.issue m k) = .frame := by
        simp only [labOf]
        split
        · rename_i h'
          exact absurd ⟨h'.2.1, h'.2.2⟩ hnotemit
        · rfl
      rw [hlab, hn']
      have hfresh : ∀ x ∈ rq.map Req.slot, g.slot ≤ x := by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact (hslot q hq).2.1
      refine ⟨.frame, ⟨⟨?_, ?_, ?_⟩, hsys, ?_, ?_, ?_, ?_, ?_⟩⟩
      · rw [hn']; exact I.node.inv
      · rw [hn']; exact scoped_raw I.node.scope hg.raw
      · rw [hn']
        intro w hw'
        cases hw'
        refine ⟨by rw [hn']; exact hissue, scoped_growR I.node.scope I.node.inv.parLt hg,
          by rw [hn']; exact hg.next, by rw [hn']; exact hg.embOld, ?_, ?_, ?_⟩
        · intro he
          have := bodies_ne hb
          rw [List.map_eq_nil_iff] at he
          rw [he] at this
          exact this rfl
        · intro q hq' hqn hqs
          rw [hreqs, List.mem_append] at hq'
          rcases hq' with hq' | hq'
          · have := I.sys.reqs q hq'
            have := hfresh _ hqs
            omega
          · refine ⟨fun hk => ?_, fun hh0 hk1 hk2 => ?_⟩
            · subst hk
              have hmem : q.body ∈ rq.map Req.body := List.mem_map_of_mem hq'
              simp only [Bodies] at hb
              rw [hb, List.mem_singleton] at hmem
              exact ⟨_, hmem, rfl⟩
            · have hne' : rq ≠ [] := List.ne_nil_of_mem hq'
              obtain ⟨q0, rest, hq0⟩ := List.exists_cons_of_ne_nil hne'
              subst hq0
              simp only [List.map_cons, List.head?_cons, Option.some.injEq] at hh0
              have hqq : q = q0 := by
                rcases List.mem_cons.1 hq' with h' | h'
                · exact h'
                · exfalso
                  have hnd := hnodup
                  simp only [List.map_cons, List.nodup_cons] at hnd
                  exact hnd.1 (by rw [hh0]; exact List.mem_map_of_mem h')
              subst hqq
              cases k with
              | push => exact absurd rfl hk1
              | fetchObjs => exact absurd rfl hk2
              | start =>
                simp only [Bodies, List.map_cons, List.cons.injEq] at hb; exact hb.1
              | differPoll =>
                simp only [Bodies, List.map_cons, List.cons.injEq] at hb; exact hb.1
              | writePoll =>
                simp only [Bodies, List.map_cons, List.cons.injEq] at hb; exact hb.1
              | fetchPoll =>
                simp only [Bodies, List.map_cons, List.cons.injEq] at hb
                rcases hb with ⟨-, hb, -⟩ | ⟨-, hb, -⟩ <;> exact hb
        · intro r hr' hrn hrs
          rw [hrest.2.1] at hr'
          have := I.sys.reps r hr'
          have := hfresh _ hrs
          omega
      · intro r hr' ht'; rw [hrest.2.1] at hr'; exact I.reps r hr' ht'
      · rw [hn']; exact I.hl
      · rw [hn']; exact I.he
      · rw [hn']; exact I.sinv
      · rw [hn']
        intro w hw' hk
        cases hw'
        exact fun he => hnotemit ⟨hk, he⟩
    · have hn' : g'.node n = g.node n := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hlab : labOf n c g (.issue m k) = .frame := by
        simp only [labOf]
        split
        · rename_i h'; exact absurd h'.1 hm
        · rfl
      rw [hlab]
      refine frame_case I hn' hg.raw (fun q hq' hqn => ?_)
        (fun r hr' _ => Or.inl (by rw [hrest.2.1] at hr'; exact hr')) hsys
        (fun r hr' ht' => by rw [hrest.2.1] at hr'; exact I.reps r hr' ht')
      rw [hreqs, List.mem_append] at hq'
      rcases hq' with hq' | hq'
      · exact hq'
      · exact absurd ((hslot q hq').1.symm.trans hqn) hm
  | answer r ans hr hreqs acc hans hreps hrest ht =>
    have hlab : labOf n c g .answer = .frame := rfl
    rw [hlab]
    refine frame_case I (by rw [hrest.1]) ⟨Nat.le_of_eq hrest.2.1.symm, fun y _ => by
        rw [hrest.2.2.1]⟩
      (fun q hq' _ => (by rw [hreqs] at hq'; exact List.mem_of_mem_erase hq')) (fun x hx hxn => ?_)
      (sysOK_answer I.sys hr hreqs hans hreps hrest.2.2.2)
      (stable_answer I.reps hhub hhub' hans hreps)
    rw [hreps, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact Or.inl hx
    · exact Or.inr ⟨r, hr, hxn, rfl, rfl⟩
  | handle m w rs hd c' σi posti σ' embi hw hrs hcov hhd hhd' hl hc' hf hh hnode hreps hrest
      ht =>
    have hsys : SysOK law g' := sysOK_sub I.sys hrest.2.1 (fun r hr' => ((hreps r).1 hr').1)
      hrest.2.2.2.1
    have hst' : StableReps t0 st g' := stable_sub I.reps (fun r hr' => ((hreps r).1 hr').1)
    by_cases hm : m = n
    · subst hm
      have W := I.node.wait w hw
      have hst : ∀ r ∈ rs, r.acc = false ∧ AnsStable st r.ans := fun r hr' =>
        I.reps r (hrs r hr').1
          (hold r (hrs r hr').1 (fun h => ((hreps r).1 h).2 hr') (hrs r hr').2.1)
      have hpost : NodeSettle.SInv c w.post := post_inv W.issue I.sinv
      have hlab0 : (h < w.post.next) ∧ w.emb h = st.head :=
        ⟨Nat.lt_of_lt_of_le I.hl W.next, (W.emb h I.hl).trans I.he⟩
      have hcl : ∀ h', hd = some h' → Closed w.post w.emb g h' := by
        intro h' hh'
        obtain ⟨r, hr', hrh⟩ := hhd' h' hh'
        have hs := (hst r hr').2
        have : h' = st.head := by
          cases hra : r.ans with
          | fetched s =>
            rw [hra] at hrh hs
            simp only [Ans.head?, Option.some.injEq] at hrh
            have : s = st := hs
            rw [← hrh, this]
          | head s =>
            rw [hra] at hrh hs
            simp only [Ans.head?, Option.some.injEq] at hrh
            have : s = st := hs
            rw [← hrh, this]
          | refused x => rw [hra] at hrh; cases hrh
          | objects => rw [hra] at hrh; cases hrh
        subst this
        exact closed_of W.scope hpost.parLt ⟨h, hlab0.1, hlab0.2⟩
      obtain ⟨rfl, rfl, rfl⟩ := hl.nothing hcl
      have hn' : g'.node m = ⟨σ', w.emb, (g.node m).gen, none⟩ := by rw [hnode, upd_same]
      -- the context, wherever a reply names the hub's head
      have ctxOf : ∀ r ∈ rs, (∃ s, r.ans = .fetched s ∨ r.ans = .head s) → c' = c := by
        intro r hr' hsnap
        rw [hc]
        exact fits_stable W.scope.inj (Nat.le_refl _) hlab0.1 hlab0.2 hc' (hf r hr') (hst r hr').2
          hsnap
      -- a step that polls has a `Fetched` reply
      have fetched : w.kind ≠ .push → w.kind ≠ .fetchObjs → c' = c := by
        intro hk1 hk2
        have hsl := W.slots
        obtain ⟨s0, rest, hs0⟩ := List.exists_cons_of_ne_nil hsl
        obtain ⟨r0, hr0, hr0s⟩ := hcov s0 (by rw [hs0]; exact List.mem_cons_self)
        have hbf := W.reps r0 (hrs r0 hr0).1 (hrs r0 hr0).2.1 (hrs r0 hr0).2.2
        have hreq : r0.req = .fetch :=
          hbf.2 (by rw [hs0, hr0s]; rfl) hk1 hk2
        obtain ⟨s, hs⟩ := I.sys.fetch r0 (hrs r0 hr0).1 hreq
        exact ctxOf r0 hr0 ⟨s, Or.inl hs⟩
      -- the step's NodeSettle event
      have ha_of : w.kind ≠ .start → (g.node m).ns.act = true := by
        intro hk
        have hi := W.issue
        cases hkk : w.kind <;> rw [hkk] at hi
        · exact absurd hkk hk
        all_goals exact hi.1
      have hl0 : labOf m c g (.handle m) = (if w.kind = .start then .start else .busy) := by
        simp [labOf, hw]
      have ev : Ev c (labOf m c g (.handle m)) (g.node m).ns σ' := by
        rw [hl0]
        have hi := W.issue
        have hhh := hh
        cases hkk : w.kind with
        | start =>
          rw [hkk] at hi hhh
          rw [fetched (by rw [hkk]; decide) (by rw [hkk]; decide)] at hhh
          obtain ⟨σ1, F, he⟩ := hhh
          exact .start hi.1 F he
        | fetchPoll =>
          rw [hkk] at hi hhh
          rw [fetched (by rw [hkk]; decide) (by rw [hkk]; decide)] at hhh
          exact .busy (ha_of (by rw [hkk]; decide))
            (issue_busy hi (by decide) hhh hcd (fun h' => by cases h') (fun h' => by cases h'))
        | differPoll =>
          rw [hkk] at hi hhh
          rw [fetched (by rw [hkk]; decide) (by rw [hkk]; decide)] at hhh
          exact .busy (ha_of (by rw [hkk]; decide))
            (issue_busy hi (by decide) hhh hcd (fun h' => by cases h') (fun h' => by cases h'))
        | writePoll =>
          rw [hkk] at hi hhh
          rw [fetched (by rw [hkk]; decide) (by rw [hkk]; decide)] at hhh
          exact .busy (ha_of (by rw [hkk]; decide))
            (issue_busy hi (by decide) hhh hcd (fun h' => by cases h') (fun h' => by cases h'))
        | fetchObjs =>
          rw [hkk] at hi hhh
          have hhc : Handle c (g.node m).ns .fetchObjs w.post (rs.map Rep.ans) σ' := hhh
          exact .busy (ha_of (by rw [hkk]; decide))
            (issue_busy hi (by decide) hhc hcd (fun h' => by cases h') (fun h' => by cases h'))
        | push =>
          rw [hkk] at hi hhh
          have hap : w.post.ap = (g.node m).ns.ap := by
            have := write_ap hi.2.2.2.2.2.2.2.2.1
            exact this
          -- what a reply to the push says of the records
          have headR : ∀ r ∈ rs, ∀ s, r.ans = .head s → (g.node m).ns.ap = st.recs := by
            intro r hr' s hs
            obtain ⟨p, hp, hpr⟩ := (W.reps r (hrs r hr').1 (hrs r hr').2.1
              (hrs r hr').2.2).1 hkk
            have := ((I.sys.push r (hrs r hr').1 p hp (hst r hr').1).2 s hs)
            have hs' := (hst r hr').2
            rw [hs] at hs'
            have : s = st := hs'
            subst this
            rw [← hap, ← hpr]
            exact (I.sys.push r (hrs r hr').1 p hp (hst r hr').1).2 _ hs
          have hph := I.nopush w hw hkk
          have hsl := W.slots
          obtain ⟨s0, rest, hs0⟩ := List.exists_cons_of_ne_nil hsl
          obtain ⟨r0, hr0, hr0s⟩ := hcov s0 (by rw [hs0]; exact List.mem_cons_self)
          obtain ⟨p0, hp0, hp0r⟩ := (W.reps r0 (hrs r0 hr0).1 (hrs r0 hr0).2.1
            (hrs r0 hr0).2.2).1 hkk
          rcases I.sys.pushAns r0 (hrs r0 hr0).1 p0 hp0 with ⟨x, hx⟩ | ⟨s, hs⟩
          · -- refused: the records were not the hub's
            have hxs : x = st.recs := by
              have := (hst r0 hr0).2; rw [hx] at this; exact this
            have hne' : (g.node m).ns.ap ≠ st.recs := by
              have := (I.sys.push r0 (hrs r0 hr0).1 p0 hp0 (hst r0 hr0).1).1 x hx
              rw [hp0r, hap, hxs] at this
              exact this
            have hcR' : c'.R = st.recs := by
              have := hf r0 hr0; rw [hx] at this; exact this.trans hxs
            have hhc : Handle c (g.node m).ns .push w.post (rs.map Rep.ans) σ' := by
              rcases hhh with ⟨hx', -, he⟩ | ⟨⟨s, hs⟩, heq, -⟩ | ⟨⟨s, hs⟩, hne'', -⟩
              · refine Or.inl ⟨hx', by rw [hcR]; exact hne', by rw [hcR, ← hcR']; exact he⟩
              · exact absurd (heq.trans hcR') hne'
              · obtain ⟨r, hr', hra⟩ := List.mem_map.1 hs
                exact absurd ((headR r hr' s hra).trans hcR'.symm) hne''
            exact .busy (ha_of (by rw [hkk]; decide))
              (issue_busy hi (by decide) hhc hcd (fun _ => hph)
                (fun _ ⟨⟨s, hs⟩, hne'', _⟩ => by
                  obtain ⟨r, hr', hra⟩ := List.mem_map.1 hs
                  exact hne'' ((headR r hr' s hra).trans hcR.symm)))
          · -- a head: the stable hub's, which takes the context
            have hcc : c' = c := ctxOf r0 hr0 ⟨s, Or.inr hs⟩
            rw [hcc] at hhh
            have heq : (g.node m).ns.ap = c.R := (headR r0 hr0 s hs).trans hcR.symm
            exact .busy (ha_of (by rw [hkk]; decide))
              (issue_busy hi (by decide) hhh hcd (fun _ => hph)
                (fun _ ⟨_, hne'', _⟩ => hne'' heq))
      have si : NodeSettle.SInv c σ' := inv_ev I.sinv ev (by
        rw [hl0]; split <;> exact fun h' => Lab.noConfusion h')
      obtain ⟨hgp, hgn⟩ := handle_graph W.issue hh
      rw [hn']
      refine ⟨ev, ⟨⟨?_, ?_, ?_⟩, hsys, hst', ?_, ?_, ?_, ?_⟩⟩
      · rw [hn']; exact linv_of_sinv si
      · rw [hn']; exact scoped_same W.scope hgp hgn hrest.2.2.2.2.1 hrest.2.2.2.2.2
      · rw [hn']; intro w' hw'; cases hw'
      · rw [hn']; show h < σ'.next; rw [hgn]; exact hlab0.1
      · rw [hn']; exact hlab0.2
      · rw [hn']; exact si
      · rw [hn']; intro w' hw'; cases hw'
    · have hn' : g'.node n = g.node n := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hlab : labOf n c g (.handle m) = .frame := by simp [labOf, hm]
      rw [hlab]
      exact frame_case I hn' ⟨Nat.le_of_eq hrest.2.2.2.2.1.symm, fun y _ => by
          rw [hrest.2.2.2.2.2]⟩
        (fun q hq' _ => by rw [hrest.2.1] at hq'; exact hq')
        (fun r hr' _ => Or.inl ((hreps r).1 hr').1) hsys hst'
  | notice m nt c' σi posti σ' embi hw ha hn hnn hnew hl hc' hf hh hnode hnotes' hrest ht =>
    have hsys : SysOK law g' := sysOK_same I.sys hrest.2.1 hrest.2.2.1 hrest.2.2.2.1
    have hst' : StableReps t0 st g' := fun r hr' ht' => by
      rw [hrest.2.2.1] at hr'; exact I.reps r hr' ht'
    by_cases hm : m = n
    · subst hm
      have hsnap : nt.snap = st := hnotes nt rfl
      have hcl : ∀ h', some nt.snap.head = some h' → Closed (g.node m).ns (g.node m).emb g h' := by
        intro h' hh'
        simp only [Option.some.injEq] at hh'
        rw [← hh', hsnap]
        exact closed_of I.node.scope I.node.inv.parLt ⟨h, I.hl, I.he⟩
      obtain ⟨rfl, rfl, rfl⟩ := hl.nothing hcl
      have hcc : c' = c := by
        rw [hc]
        exact fits_stable I.node.scope.inj (Nat.le_refl _) I.hl I.he hc' hf
          (by show nt.snap = st; exact hsnap) ⟨nt.snap, Or.inr rfl⟩
      rw [hcc] at hh
      have hn' : g'.node m = ⟨σ', (g.node m).emb, (g.node m).gen, none⟩ := by
        rw [hnode, upd_same]
      have hlab : labOf m c g (.notice m nt) = .notify := by simp [labOf]
      have ev : Ev c .notify (g.node m).ns σ' := .notify hh
      have si : NodeSettle.SInv c σ' := inv_ev I.sinv ev (fun h' => Lab.noConfusion h')
      rw [hlab, hn']
      refine ⟨ev, ⟨⟨?_, ?_, ?_⟩, hsys, hst', ?_, ?_, ?_, ?_⟩⟩
      · rw [hn']; exact linv_of_sinv si
      · rw [hn']
        exact scoped_same I.node.scope hh.par hh.next hrest.2.2.2.2.1 hrest.2.2.2.2.2
      · rw [hn']; intro w' hw'; cases hw'
      · rw [hn']; show h < σ'.next; rw [hh.next]; exact I.hl
      · rw [hn']; exact I.he
      · rw [hn']; exact si
      · rw [hn']; intro w' hw'; cases hw'
    · have hn' : g'.node n = g.node n := by rw [hnode, upd_ne _ _ (Ne.symm hm)]
      have hlab : labOf n c g (.notice m nt) = .frame := by simp [labOf, hm]
      rw [hlab]
      exact frame_case I hn' ⟨Nat.le_of_eq hrest.2.2.2.2.1.symm, fun y _ => by
          rw [hrest.2.2.2.2.2]⟩
        (fun q hq' _ => by rw [hrest.2.1] at hq'; exact hq')
        (fun r hr' _ => Or.inl (by rw [hrest.2.2.1] at hr'; exact hr')) hsys hst'
  | ignore m nt hw ha hn hnn hold' hnode hnotes' hrest ht =>
    have hlab : labOf n c g (.ignore m) = .frame := rfl
    rw [hlab]
    exact frame_case I (by rw [hnode]) ⟨Nat.le_of_eq hrest.2.2.2.2.1.symm, fun y _ => by
        rw [hrest.2.2.2.2.2]⟩
      (fun q hq' _ => by rw [hrest.2.1] at hq'; exact hq')
      (fun r hr' _ => Or.inl (by rw [hrest.2.2.1] at hr'; exact hr'))
      (sysOK_same I.sys hrest.2.1 hrest.2.2.1 hrest.2.2.2.1)
      (fun r hr' ht' => by rw [hrest.2.2.1] at hr'; exact I.reps r hr' ht')
  | env hr hnode hq ht =>
    have hlab : labOf n c g .env = .frame := rfl
    rw [hlab]
    exact frame_case I (by rw [hnode]) hr (fun q hq' _ => by rw [hq.reqs] at hq'; exact hq')
      (fun r hr' _ => Or.inl (by rw [hq.reps] at hr'; exact hr'))
      (sysOK_same I.sys hq.reqs hq.reps hq.slot)
      (fun r hr' ht' => by rw [hq.reps] at hr'; exact I.reps r hr' ht')


/-- A push from the stable hub's head, as the system sends it, is NodeSettle's `Emit`. -/
theorem emit_of_lab {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {n : Nat} {c : Ctx}
    {a : Act} {g g' : Sys} (hcd : c.drops = D n) (hs : SysStep N D law a g g')
    (he : labOf n c g a = .emit) : ∃ post new, Emit c (g.node n).ns post new := by
  cases hs with
  | issue m k post new emb1 rq hw hissue =>
    simp only [labOf] at he
    split at he
    · rename_i h'
      obtain ⟨rfl, rfl, hk⟩ := h'
      obtain ⟨ha, hg, h1, hl, hd, hnr, hf, hw', hwr, hnew⟩ := hissue
      exact ⟨post, new, ha, go_congr hcd hg, h1, hl, hd, hnr, hf, hw', hk, hwr, hnew⟩
    · cases he
  | busy m => simp only [labOf] at he; split at he <;> cases he
  | idle m => simp only [labOf] at he; split at he <;> cases he
  | maint m => simp only [labOf] at he; split at he <;> cases he
  | answer => cases he
  | handle m w =>
    simp only [labOf] at he
    split at he
    · split at he
      · split at he <;> cases he
      · cases he
    · cases he
  | notice m => simp only [labOf] at he; split at he <;> cases he
  | ignore m => cases he
  | env => cases he

/-- The `emit` label is exactly node `n` issuing a push while it knows the context's pair. -/
theorem lab_emit {n : Nat} {c : Ctx} {g : Sys} {a : Act} :
    labOf n c g a = .emit ↔ a = .issue n .push ∧ (g.node n).ns.known = (c.S, c.H) := by
  constructor
  · intro he
    cases a with
    | issue m k =>
      simp only [labOf] at he
      split at he
      · rename_i h'
        obtain ⟨rfl, rfl, hk⟩ := h'
        exact ⟨rfl, hk⟩
      · cases he
    | core m ck => cases ck <;> simp only [labOf] at he <;> split at he <;> cases he
    | handle m =>
      simp only [labOf] at he
      split at he
      · split at he
        · split at he <;> cases he
        · cases he
      · cases he
    | notice m _ => simp only [labOf] at he; split at he <;> cases he
    | ignore m => cases he
    | answer => cases he
    | env => cases he
  · rintro ⟨rfl, hk⟩
    simp [labOf, hk]

/-! ## The node's core in the system is a NodeSettle run -/

/-- Once the hub is stable at `st` from `k`, and from `k'` on every reply node `n` takes was
answered at `k` or after and every notification it processes is the stable hub's, with the
node's head `h` labelled and what the simulation keeps holding at `k'`: node `n`'s core in the
system is a NodeSettle run in the stable context, unless it sends a push from the hub's head: an
actual `issue n .push` labelled `emit` (`lab_emit`), from a state where it is `Emit`, which the
stable hub would accept. Old replies and notifications that are never taken may stay queued
forever: the cuts are on what is taken (only the node's own `handle` removes its replies), not on
the queues. -/
theorem node_sim {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} (ρ : Nat → Sys)
    (acts : Nat → Act) (n k k' h : Nat) (st : Snap)
    (hstep : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (hkk : k ≤ k') (hstable : ∀ i, k ≤ i → (ρ i).hub = st)
    (hold : ∀ i, k' ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ k).time ≤ r.time)
    (hnotes : ∀ i, k' ≤ i → ∀ nt, acts i = .notice n nt → nt.snap = st)
    (h0 : SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ k')) :
    (∃ i, k' ≤ i ∧ labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) = .emit ∧
      ∃ post new, Emit ⟨st.seq, h, st.recs, D n⟩ ((ρ i).node n).ns post new) ∨
      ((∀ i, k' ≤ i → SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ i)) ∧
        ∀ i, k' ≤ i → Ev ⟨st.seq, h, st.recs, D n⟩
          (labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i))
          ((ρ i).node n).ns ((ρ (i + 1)).node n).ns) := by
  by_cases hem : ∃ i, k' ≤ i ∧ labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) = .emit
  · left
    obtain ⟨i, hi, he⟩ := hem
    exact ⟨i, hi, he, emit_of_lab rfl (hstep i (by omega)) he⟩
  · right
    have hne : ∀ i, k' ≤ i → labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) ≠ .emit :=
      fun i hi he => hem ⟨i, hi, he⟩
    have step : ∀ i, k' ≤ i → SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ i) →
        Ev ⟨st.seq, h, st.recs, D n⟩ (labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i))
          ((ρ i).node n).ns ((ρ (i + 1)).node n).ns ∧
        SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ (i + 1)) :=
      fun i hi I => sim_step rfl I (hstep i (by omega)) (hstable i (by omega))
        (hstable (i + 1) (by omega)) (hold i hi) (hnotes i hi) (hne i hi)
    have hinv : ∀ d, SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ (k' + d)) := by
      intro d
      induction d with
      | zero => exact h0
      | succ d ih => exact (step (k' + d) (by omega) ih).2
    have hinv' : ∀ i, k' ≤ i → SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ i) := by
      intro i hi
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
      exact hinv d
    exact ⟨hinv', fun i hi => (step i hi (hinv' i hi)).1⟩


/-! ## From fair scheduling of individual events to NodeSettle's fairness -/

/-- The events that act on node `n`. -/
def Act.about (n : Nat) : Act → Prop
  | .core m _ => m = n
  | .issue m _ => m = n
  | .handle m => m = n
  | .notice m _ => m = n
  | .ignore m => m = n
  | .answer => False
  | .env => False

section Sched

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {n : Nat}

/-- An event that does not act on a node leaves it alone. -/
theorem node_unchanged {a : Act} {g g' : Sys} (hs : SysStep N D law a g g') (ha : ¬ a.about n) :
    g'.node n = g.node n := by
  cases hs with
  | busy m _ _ _ _ _ _ hnode _ _ =>
    rw [hnode, upd_ne _ _ (fun h => ha h.symm)]
  | idle m _ _ _ _ hnode _ _ _ => rw [hnode, upd_ne _ _ (fun h => ha h.symm)]
  | maint m _ _ _ _ _ _ _ _ hnode _ _ => rw [hnode, upd_ne _ _ (fun h => ha h.symm)]
  | issue m _ _ _ _ _ _ _ _ _ _ _ hnode _ _ _ _ => rw [hnode, upd_ne _ _ (fun h => ha h.symm)]
  | answer _ _ _ _ _ _ _ hrest _ => rw [hrest.1]
  | handle m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode _ _ _ =>
    rw [hnode, upd_ne _ _ (fun h => ha h.symm)]
  | notice m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode _ _ _ =>
    rw [hnode, upd_ne _ _ (fun h => ha h.symm)]
  | ignore _ _ _ _ _ _ _ hnode _ _ _ => rw [hnode]
  | env _ hnode _ _ => rw [hnode]

/-- While a node waits on replies, only taking them changes it. -/
theorem node_waiting {a : Act} {g g' : Sys} (hs : SysStep N D law a g g')
    (hw : (g.node n).wait ≠ none) (ha : a ≠ .handle n) : g'.node n = g.node n := by
  by_cases hab : a.about n
  · exfalso
    cases hs with
    | busy m _ _ hw' => exact hw (by simp only [Act.about] at hab; subst hab; exact hw')
    | idle m _ hw' => exact hw (by simp only [Act.about] at hab; subst hab; exact hw')
    | maint m _ _ _ hw' => exact hw (by simp only [Act.about] at hab; subst hab; exact hw')
    | issue m _ _ _ _ _ hw' => exact hw (by simp only [Act.about] at hab; subst hab; exact hw')
    | handle m => simp only [Act.about] at hab; subst hab; exact ha rfl
    | notice m _ _ _ _ _ _ hw' =>
      exact hw (by simp only [Act.about] at hab; subst hab; exact hw')
    | ignore m _ hw' => exact hw (by simp only [Act.about] at hab; subst hab; exact hw')
    | answer => exact hab
    | env => exact hab
  · exact node_unchanged hs hab

theorem reaches_handle (ρ : Nat → Sys) (acts : Nat → Act) (k' : Nat)
    (hstep : ∀ i, k' ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (reply : ∀ i, k' ≤ i → ((ρ i).node n).wait ≠ none → ∃ j, i ≤ j ∧ acts j = .handle n)
    (i : Nat) (hi : k' ≤ i) (hw : ((ρ i).node n).wait ≠ none) :
    ∃ j, i ≤ j ∧ acts j = .handle n ∧ (ρ j).node n = (ρ i).node n := by
  obtain ⟨j, hj, hh⟩ := reply i hi hw
  obtain ⟨d, hd, hmin⟩ := exists_first (P := fun d => acts (i + d) = .handle n)
    ⟨j - i, by rw [show i + (j - i) = j by omega]; exact hh⟩
  have same : ∀ e, e ≤ d → (ρ (i + e)).node n = (ρ i).node n := by
    intro e
    induction e with
    | zero => intro _; rfl
    | succ e ih =>
      intro he
      have h1 := ih (by omega)
      show (ρ (i + e + 1)).node n = (ρ i).node n
      rw [node_waiting (hstep (i + e) (by omega)) (by rw [h1]; exact hw) (hmin e (by omega)), h1]
  exact ⟨i + d, by omega, hd, same d (Nat.le_refl d)⟩

theorem reaches_own (ρ : Nat → Sys) (acts : Nat → Act) (k' : Nat)
    (hstep : ∀ i, k' ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (i : Nat) (hi : k' ≤ i) (hex : ∃ j, i ≤ j ∧ (acts j).about n) :
    ∃ j, i ≤ j ∧ (acts j).about n ∧ (ρ j).node n = (ρ i).node n := by
  obtain ⟨j, hj, hh⟩ := hex
  obtain ⟨d, hd, hmin⟩ := exists_first (P := fun d => (acts (i + d)).about n)
    ⟨j - i, by rw [show i + (j - i) = j by omega]; exact hh⟩
  have same : ∀ e, e ≤ d → (ρ (i + e)).node n = (ρ i).node n := by
    intro e
    induction e with
    | zero => intro _; rfl
    | succ e ih =>
      intro he
      show (ρ (i + e + 1)).node n = (ρ i).node n
      rw [node_unchanged (hstep (i + e) (by omega)) (hmin e (by omega)), ih (by omega)]
  exact ⟨i + d, by omega, hd, same d (Nat.le_refl d)⟩

end Sched

/-- Fair scheduling of node `n`'s own events: a round starts whenever none is running; a
running round's next core step or request happens; and a step's replies, once out, are taken.
Each is about one event, whose call completes; none says a round ends. -/
structure Fair (ρ : Nat → Sys) (acts : Nat → Act) (n k' : Nat) : Prop where
  start : ∀ i, k' ≤ i → ((ρ i).node n).wait = none → ((ρ i).node n).ns.act = false →
    ∃ j, i ≤ j ∧ acts j = .issue n .start
  core : ∀ i, k' ≤ i → ((ρ i).node n).wait = none → ((ρ i).node n).ns.act = true →
    ∃ j, i ≤ j ∧ ((∃ ck, acts j = .core n ck) ∨ (∃ kk, acts j = .issue n kk))
  reply : ∀ i, k' ≤ i → ((ρ i).node n).wait ≠ none → ∃ j, i ≤ j ∧ acts j = .handle n

/-- In the system, once the hub has settled, a fair node settles at its head, or sends a push
from the hub's head with the hub's records: an actual `issue n .push` labelled `emit`
(`lab_emit`), from a state where it is `Emit` (`emit_packet`), which the stable hub would accept.
Housekeeping that writes is assumed to stop; nothing assumes a round ends. -/
theorem node_settles_sys {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (ρ : Nat → Sys) (acts : Nat → Act) (n k k' h : Nat) (st : Snap)
    (hstep : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (hkk : k ≤ k') (hstable : ∀ i, k ≤ i → (ρ i).hub = st)
    (hold : ∀ i, k' ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ k).time ≤ r.time)
    (hnotes : ∀ i, k' ≤ i → ∀ nt, acts i = .notice n nt → nt.snap = st)
    (h0 : SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ k'))
    (hfair : Fair ρ acts n k')
    (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint) :
    (∃ i, k' ≤ i ∧ labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) = .emit ∧
      ∃ post new, Emit ⟨st.seq, h, st.recs, D n⟩ ((ρ i).node n).ns post new) ∨
      ∃ K, ∀ i, K ≤ i → NodeSettle.Settled ⟨st.seq, h, st.recs, D n⟩ ((ρ i).node n).ns := by
  rcases node_sim ρ acts n k k' h st hstep hkk hstable hold hnotes h0 with hem | ⟨hinv, hev⟩
  · exact Or.inl hem
  have hstep' : ∀ i, k' ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)) :=
    fun i hi => hstep i (by omega)
  -- the kind of a step's wait follows from whether the round is running
  have kind_of : ∀ i, k' ≤ i → ∀ w, ((ρ i).node n).wait = some w →
      (w.kind = .start ↔ ((ρ i).node n).ns.act = false) := by
    intro i hi w hw
    have hiss := ((hinv i hi).node.wait w hw).issue
    constructor
    · intro hk
      rw [hk] at hiss
      exact hiss.1
    · intro ha
      cases hkk : w.kind
      · rfl
      all_goals (rw [hkk] at hiss; exact absurd (hiss.1.symm.trans ha) (by decide))
  let c : NodeSettle.Ctx := ⟨st.seq, h, st.recs, D n⟩
  have lab_handle : ∀ j, acts j = .handle n → ∀ w, ((ρ j).node n).wait = some w →
      labOf n c (ρ j) (acts j) = if w.kind = .start then .start else .busy := by
    intro j hj w hw
    rw [hj]
    simp [labOf, hw]
  have hstart : ∀ i, k' ≤ i → ((ρ i).node n).ns.act = false →
      ∃ j, i ≤ j ∧ labOf n c (ρ j) (acts j) = .start := by
    intro i hi ha
    cases hw : ((ρ i).node n).wait with
    | some w =>
      obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k' hstep' hfair.reply i hi
        (by rw [hw]; exact Option.some_ne_none _)
      have hw' : ((ρ j).node n).wait = some w := by rw [hsame]; exact hw
      have hk : w.kind = .start := (kind_of i hi w hw).2 ha
      exact ⟨j, hj, by rw [lab_handle j hh w hw']; simp [hk]⟩
    | none =>
      obtain ⟨j0, hj0, hiss⟩ := hfair.start i hi hw ha
      have h1 := hstep' j0 (by omega)
      rw [hiss] at h1
      cases h1 with
      | issue _ _ post new emb1 rq _ _ _ _ _ _ hnode =>
        have hw1 : ((ρ (j0 + 1)).node n).wait =
            some ⟨.start, rq.map Req.slot, post, new, emb1⟩ := by rw [hnode, upd_same]
        obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k' hstep' hfair.reply (j0 + 1)
          (by omega) (by rw [hw1]; exact Option.some_ne_none _)
        have hw' : ((ρ j).node n).wait = some ⟨.start, rq.map Req.slot, post, new, emb1⟩ := by
          rw [hsame]; exact hw1
        exact ⟨j, by omega, by rw [lab_handle j hh _ hw']; rfl⟩
  have hcore : ∀ i, k' ≤ i → ((ρ i).node n).ns.act = true → ∃ j, i ≤ j ∧
      (labOf n c (ρ j) (acts j) = .busy ∨ labOf n c (ρ j) (acts j) = .idle ∨
        labOf n c (ρ j) (acts j) = .emit ∨ labOf n c (ρ j) (acts j) = .maint) := by
    intro i hi ha
    have busy_after : ∀ i', k' ≤ i' → ((ρ i').node n).ns.act = true →
        ((ρ i').node n).wait ≠ none → ∃ j, i' ≤ j ∧ labOf n c (ρ j) (acts j) = .busy := by
      intro i' hi' ha' hw'
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hw'
      obtain ⟨j, hj, hh, hsame⟩ := reaches_handle ρ acts k' hstep' hfair.reply i' hi' hw'
      have hwj : ((ρ j).node n).wait = some w := by rw [hsame]; exact hw
      have hk : w.kind ≠ .start := fun hk => by
        have := (kind_of i' hi' w hw).1 hk
        rw [ha'] at this
        cases this
      exact ⟨j, hj, by rw [lab_handle j hh w hwj]; simp [hk]⟩
    cases hw : ((ρ i).node n).wait with
    | some w =>
      obtain ⟨j, hj, hl⟩ := busy_after i hi ha (by rw [hw]; exact Option.some_ne_none _)
      exact ⟨j, hj, Or.inl hl⟩
    | none =>
      obtain ⟨j1, hj1, hc⟩ := hfair.core i hi hw ha
      have hab1 : (acts j1).about n := by
        rcases hc with ⟨ck, he⟩ | ⟨kk, he⟩ <;> simp [he, Act.about]
      obtain ⟨j0, hj0, hab, hsame⟩ := reaches_own ρ acts k' hstep' i hi ⟨j1, hj1, hab1⟩
      have hstp := hstep' j0 (by omega)
      cases ha0 : acts j0 with
      | core m ck =>
        rw [ha0] at hab
        simp only [Act.about] at hab
        subst hab
        refine ⟨j0, hj0, ?_⟩
        rw [ha0]
        cases ck <;> simp [labOf]
      | issue m kk =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        by_cases hem : labOf m c (ρ j0) (.issue m kk) = .emit
        · exact ⟨j0, hj0, Or.inr (Or.inr (Or.inl (by rw [ha0]; exact hem)))⟩
        · cases hstp with
          | issue _ _ post new emb1 rq _ _ _ _ _ _ hnode =>
            have hw1 : ((ρ (j0 + 1)).node m).wait =
                some ⟨kk, rq.map Req.slot, post, new, emb1⟩ := by rw [hnode, upd_same]
            have ha1 : ((ρ (j0 + 1)).node m).ns.act = true := by
              rw [hnode, upd_same]; show ((ρ j0).node m).ns.act = true; rw [hsame]; exact ha
            obtain ⟨j, hj, hl⟩ := busy_after (j0 + 1) (by omega) ha1
              (by rw [hw1]; exact Option.some_ne_none _)
            exact ⟨j, by omega, Or.inl hl⟩
      | handle m =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | handle _ _ _ _ _ _ _ _ _ hw' =>
          rw [hsame, hw] at hw'
          cases hw'
      | notice m _ =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | notice _ _ _ _ _ _ _ _ ha' =>
          rw [hsame, ha] at ha'
          cases ha'
      | ignore m =>
        rw [ha0] at hab hstp
        simp only [Act.about] at hab
        subst hab
        cases hstp with
        | ignore _ _ _ ha' =>
          rw [hsame, ha] at ha'
          cases ha'
      | answer => rw [ha0] at hab; exact hab.elim
      | env => rw [ha0] at hab; exact hab.elim
  obtain ⟨kb, hkb⟩ := hmaint
  have hm : ∃ kb, ∀ i, kb ≤ i → labOf n c (ρ i) (acts i) ≠ .maint := by
    refine ⟨kb, fun i hi he => ?_⟩
    cases ha0 : acts i with
    | core m ck =>
      rw [ha0] at he
      cases ck <;> simp only [labOf] at he <;> split at he <;> try cases he
      rename_i hmn
      subst hmn
      exact hkb i hi ha0
    | issue m kk => rw [ha0] at he; simp only [labOf] at he; split at he <;> cases he
    | handle m =>
      rw [ha0] at he
      simp only [labOf] at he
      split at he
      · split at he
        · split at he <;> cases he
        · cases he
      · cases he
    | notice m _ => rw [ha0] at he; simp only [labOf] at he; split at he <;> cases he
    | ignore m => rw [ha0] at he; cases he
    | answer => rw [ha0] at he; cases he
    | env => rw [ha0] at he; cases he
  rcases node_settles c (fun i => (ρ i).node n |>.ns) (fun i => labOf n c (ρ i) (acts i)) k'
      (fun i hi => hev i hi) (hinv k' (Nat.le_refl _)).sinv hm hstart hcore with hem | hset
  · obtain ⟨i, hi, hl, post, new, he⟩ := hem
    exact Or.inl ⟨i, hi, hl, post, new, he⟩
  · exact Or.inr hset


/-! ## The node's repository and its core state -/

/-- The node's repository as the raw hub-side view reads it: after the writes of a step whose
replies are out, else the core's state. The core's state (`ns`) stays the step's pre-state
until the replies, as NodeSettle's steps take them. Its op heads, labels and raw ids are the
repository's own. Its known pair is logical: the pair at the exchange's start until the
exchange's replies are taken, not the native one, which a poll's `Fetched` callback updates
before the exchange's `Objects` call is even sent. Nothing in the system reads it meanwhile
(`Handle`). -/
def NodeC.repo (x : NodeC) : NS :=
  match x.wait with
  | some w => w.post
  | none => x.ns

def NodeC.repoEmb (x : NodeC) : Nat → Nat :=
  match x.wait with
  | some w => w.emb
  | none => x.emb

/-- With no pending drops, a step writes nothing: `Publication.write` has neither a restoring
fix-up nor a neutral tip to write. So its state after has the op heads, known pair and labels it
had. -/
theorem issue_quiet {d : Nat → Nat → Prop} {σ post : NS} {k : Kind} {new : Nat}
    (hi : Issue d σ k post new) (hp : σ.pending = []) :
    post.heads = σ.heads ∧ post.known = σ.known ∧ post.next = σ.next := by
  cases k with
  | push =>
    obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hi
    obtain ⟨y, -, (⟨hwr, -⟩ | ⟨-, he, -⟩)⟩ := hw'
    · exfalso
      have hp' : (norm σ).pending = [] := hp
      simp [pubOf, Retry.Publication.write, Retry.Fixup.write, hp'] at hwr
    · subst he; exact ⟨rfl, rfl, rfl⟩
  | writePoll => exact absurd hp hi.2.2.2.2.2.2.2.1
  | start =>
    have he := post_same hi (by decide) (by decide)
    subst he
    exact ⟨rfl, rfl, rfl⟩
  | fetchPoll =>
    have he := post_same hi (by decide) (by decide)
    subst he
    exact ⟨rfl, rfl, rfl⟩
  | fetchObjs =>
    have he := post_same hi (by decide) (by decide)
    subst he
    exact ⟨rfl, rfl, rfl⟩
  | differPoll =>
    have he := post_same hi (by decide) (by decide)
    subst he
    exact ⟨rfl, rfl, rfl⟩

/-- A node with no pending drops, an explicit premise here and nowhere derived (root's
`eligible_pending_empty` would give it for an eligible node, and is under review), has in its
repository the op heads, logical known pair and raw ids of its core's state, its replies out or
not. Not so in general: a fix-up or tip written for a push is in the repository before the
reply, while the core's state is the step's pre-state. The known pair is the logical one
(`NodeC.repo`), not the native one in the middle of an exchange. -/
theorem repo_agrees {D : Nat → Nat → Nat → Prop} {n : Nat} {g : Sys} (I : NodeOK D n g)
    (hp : (g.node n).ns.pending = []) :
    (g.node n).repo.heads = (g.node n).ns.heads ∧ (g.node n).repo.known = (g.node n).ns.known ∧
      ∀ x, x < (g.node n).ns.next → (g.node n).repoEmb x = (g.node n).emb x := by
  cases hw : (g.node n).wait with
  | none => simp [NodeC.repo, NodeC.repoEmb, hw]
  | some w =>
    have W := I.wait w hw
    obtain ⟨hh, hk, -⟩ := issue_quiet W.issue hp
    simp only [NodeC.repo, NodeC.repoEmb, hw]
    exact ⟨hh, hk, W.emb⟩

end Musubi.NodeSys

/-
Project individual hub and node observations into fine system steps.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.
-/
import Musubi.SysFreshCuts
import Musubi.PacketAcceptance
import Musubi.NodeSysExec

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-! ## Native events, projected

A native event is observed by its own physical data, and its projection into the hive's `Sys`
is built from that data by a theorem, never assumed as a `SysStep`. The first events projected
are the hub's answers. To a `Fetch` and to a `GetObjects`, `handle` answers one request at a
time per hive (hub.rs:1-4), from the hub's `(seq, head)` and records then (`storage.head()`,
`storage.records()`, hub.rs:154-188), and changes nothing the system reads (its `report` of what
the machine took is kept in memory only, and an objects answer only exports). To a `Push`, the
hub first writes (what the push uploads, and contraction bodies it generates), a raw step, unless
it refuses the push first, which writes nothing, then decides from the state that leaves
(`HubAnswer.push_handled`). -/

/-- The hub answering one call, as observed: the call, by node, virtual slot (the call batch's
injective map of its wire id) and body, and the hub's `(seq, head, records)` when it answers,
projected to raw ids and record states. -/
structure HubAnswer where
  req : Req
  snap : Snap

/-- What the observation of that event must bind, the source obligations of its projection: the
call is one in flight, the snapshot is the hub's in the projected state before, and the
projected state after is the one before with the call answered (it leaves the requests, its
reply joins the replies at the system's time, and the clock ticks), nothing else moving. -/
structure HubAnswer.Binds (e : HubAnswer) (g g' : Sys) (ans : Ans) : Prop where
  inFlight : e.req ∈ g.reqs
  snap : e.snap = g.hub
  after : g' = { g with
    reqs := g.reqs.erase e.req
    reps := g.reps ++ [⟨e.req.node, e.req.slot, g.time, e.req.body, false, ans⟩]
    time := g.time + 1 }

/-- The hub's answer to a `Fetch`, projected, is the system's `answer` step. -/
theorem HubAnswer.fetch_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : HubAnswer} {g g' : Sys} (hb : e.req.body = .fetch)
    (B : e.Binds g g' (.fetched e.snap)) : SysStep N D law .answer g g' := by
  obtain ⟨hr, hs, rfl⟩ := B
  exact .answer e.req (.fetched e.snap) hr rfl false
    (Or.inl ⟨hb, rfl, by rw [hs], rfl, rfl⟩) rfl ⟨rfl, rfl, rfl, rfl⟩ rfl

/-- The hub's answer to a `GetObjects`, projected, is the system's `answer` step. -/
theorem HubAnswer.objects_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : HubAnswer} {g g' : Sys} (hb : e.req.body = .objs)
    (B : e.Binds g g' .objects) : SysStep N D law .answer g g' := by
  obtain ⟨hr, -, rfl⟩ := B
  exact .answer e.req .objects hr rfl false
    (Or.inr (Or.inl ⟨hb, rfl, rfl, rfl, rfl⟩)) rfl ⟨rfl, rfl, rfl, rfl⟩ rfl

/-- In the eligible nodes' system: the answer to an eligible node's call, or to one in flight at
the entry cut, is its `answer` step; the answer to another node's call is a raw step. -/
theorem HubAnswer.hive_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : HubAnswer} {g g' : Sys} {ans : Ans}
    (hs : SysStep N D law .answer g g') (B : e.Binds g g' ans) :
    (E e.req.node ∨ e.req ∈ old → HiveStep N D law E old .answer g g') ∧
      (¬ E e.req.node → e.req ∉ old → HiveStep N D law E old .env g g') := by
  obtain ⟨hr, -, hg⟩ := B
  refine ⟨fun hk => .answer hs fun rep hrep => ?_, fun hn hold => ?_⟩
  · have h1 : ([⟨e.req.node, e.req.slot, g.time, e.req.body, false, ans⟩] : List Rep) = [rep] :=
      List.append_cancel_left (as := g.reps) (by rw [← hrep, hg])
    simp only [List.cons.injEq, and_true] at h1
    subst h1
    exact hk
  · subst hg
    exact .answerRaw e.req hr hn hold _ ⟨rfl, rfl, rfl⟩ rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- The system's state after the hub decides the push `r` carrying `p` with the native outcome
`o`, from the state its writes left (`HubAnswer.stored`): an accepted push moves the hub's
`(seq, head)` and records (`set_head`), and publishes the new head to every node; a refused one
gets the hub's records; any other gets the hub's head. The call leaves the requests, its reply
joins the replies, and the clock ticks. The notifications to every node are GHOSTS, potential
notifications: the native hub publishes to its subscribers only, and a node not subscribed
never consumes the one the model sends it (no step needs it to). -/
def pushAfter (N : Nat) (law : HubLaw) (g : Sys) (r : Req) (p : Pkt) (o : RawPublish.Outcome) :
    Sys :=
  if o = .accepted then
    { g with
      hub := ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩
      notes := g.notes ++ (List.range N).map
        (fun m => ⟨m, g.time, ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩⟩)
      reqs := g.reqs.erase r
      reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, true,
        .head ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩⟩]
      time := g.time + 1 }
  else if o = .refused then
    { g with
      reqs := g.reqs.erase r
      reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, false, .refused g.hub.recs⟩]
      time := g.time + 1 }
  else
    { g with
      reqs := g.reqs.erase r
      reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, false, .head g.hub⟩]
      time := g.time + 1 }

/-- `Push::answer` refuses exactly for other records or a dropped head. -/
theorem answer_refused_iff {h : RawPublish.Hub} {q : RawPublish.Push} {c : RawPublish.Checks} :
    RawPublish.answer h q c = .refused ↔ (c.recordsMatch = false ∨ c.dropped = true) := by
  unfold RawPublish.answer
  by_cases hc : c.recordsMatch = false ∨ c.dropped = true
  · simp [hc]
  · simp only [hc, ↓reduceIte, iff_false]
    split
    · simp
    · split
      · simp
      · split <;> simp

/-- `Push::answer` never answers `Incomplete` when, in the one branch that consults it (the
records match, the new head is not dropped and not the hub's, and the push is from the hub's
head), the closure is stored. A refused push is refused before anything is stored, so nothing
is asked of its closure. -/
theorem answer_ne_incomplete {h : RawPublish.Hub} {q : RawPublish.Push} {c : RawPublish.Checks}
    (hc : c.recordsMatch = true → c.dropped = false → q.new ≠ h.head → h.head = q.expected →
      c.closed = true) : RawPublish.answer h q c ≠ .incomplete := by
  unfold RawPublish.answer
  split
  · simp
  · rename_i h1
    split
    · simp
    · rename_i h2
      split
      · rename_i h3
        have hm : c.recordsMatch = true := by
          cases hm : c.recordsMatch
          · exact absurd (Or.inl hm) h1
          · rfl
        have hd : c.dropped = false := by
          cases hd : c.dropped
          · rfl
          · exact absurd (Or.inr hd) h1
        rw [hc hm hd h2 h3.1] at h3
        exact absurd h3.2 (by decide)
      · split <;> simp

/-- The hub's DECISION on a push, projected, from the native decision on that very packet, in
the state after the hub's writes for it (`HubAnswer.push_handled` composes the two): the hub's
checks of it (`RawPublish.Checks`), its records compared and `is_dropped` bound to the law's, its
closure stored in the one branch that consults it (so never `Incomplete`; a refused push is
asked nothing of its closure), and the law accepting exactly when `Push::answer` accepts.
Whatever the outcome, the step is the system's `answer`. -/
theorem HubAnswer.push_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    {r : Req} {p : Pkt} {c : RawPublish.Checks}
    (hr : r ∈ g.reqs) (hb : r.body = .push p)
    (hrec : c.recordsMatch = true ↔ p.recs = g.hub.recs)
    (hdrop : c.dropped = true ↔ law.dropped g.hub.recs p)
    (hclosed : c.recordsMatch = true → c.dropped = false → p.new ≠ g.hub.head →
      g.hub.head = p.expected → c.closed = true)
    (hacc : RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c =
      .accepted ↔ law.accepts g.hub g.par p) :
    RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c ≠ .incomplete ∧
    SysStep N D law .answer g
      (pushAfter N law g r p
        (RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c)) := by
  refine ⟨answer_ne_incomplete hclosed, ?_⟩
  have href := (answer_refused_iff (h := ⟨g.hub.seq, g.hub.head⟩)
    (q := ⟨p.expected, p.new, p.pending⟩) (c := c))
  generalize RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c = o
    at hacc href
  have hnot : o ≠ .accepted → ¬ law.accepts g.hub g.par p := fun h ha => h (hacc.2 ha)
  -- the refusal is the records' or the drop's, and only it
  have href' : o = .refused ↔ (p.recs ≠ g.hub.recs ∨ law.dropped g.hub.recs p) := by
    rw [href]
    constructor
    · rintro (h | h)
      · exact Or.inl fun he => by rw [hrec.2 he] at h; cases h
      · exact Or.inr (hdrop.1 h)
    · rintro (h | h)
      · left
        cases hm : c.recordsMatch
        · rfl
        · exact absurd (hrec.1 hm) h
      · exact Or.inr (hdrop.2 h)
  unfold pushAfter
  by_cases ha : o = .accepted
  · simp only [ha, ↓reduceIte]
    exact .answer r _ hr rfl true
      (Or.inr (Or.inr ⟨p, hb, Or.inl ⟨hacc.1 ha, rfl, rfl, rfl, rfl⟩⟩)) rfl
      ⟨rfl, rfl, rfl, rfl⟩ rfl
  · simp only [ha, ↓reduceIte]
    by_cases hf : o = .refused
    · simp only [hf, ↓reduceIte]
      exact .answer r _ hr rfl false
        (Or.inr (Or.inr ⟨p, hb, Or.inr (Or.inl ⟨hnot ha, rfl, href'.1 hf, rfl, rfl, rfl⟩)⟩))
        rfl ⟨rfl, rfl, rfl, rfl⟩ rfl
    · simp only [hf, ↓reduceIte]
      have hok : p.recs = g.hub.recs ∧ ¬ law.dropped g.hub.recs p :=
        ⟨Classical.byContradiction fun h => hf (href'.2 (Or.inl h)),
          fun h => hf (href'.2 (Or.inr h))⟩
      exact .answer r _ hr rfl false
        (Or.inr (Or.inr ⟨p, hb, Or.inr (Or.inr ⟨hnot ha, rfl, hok, rfl, rfl, rfl⟩)⟩))
        rfl ⟨rfl, rfl, rfl, rfl⟩ rfl

/-- The hub's writes before it decides a push, projected: `store_ops`, `store_objects` and the
contraction bodies it generates itself (`with_contracted`), which it writes even for a push it
then rejects or finds idempotent. A push it refuses (other records, or a dropped head) is refused
before them (hub.rs:264-272): no growth, `next' = g.next` and `par' = g.par`. The raw graph grows
by ids above every one in use, the parents of those in use unchanged; nothing else moves. -/
def HubAnswer.stored (g : Sys) (next' : Nat) (par' : Nat → List Nat) : Sys :=
  { g with next := next', par := par', time := g.time + 1 }

/-- Those writes are a raw step of the system (`env`, raw growth only). -/
theorem HubAnswer.store_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    {next' : Nat} {par' : Nat → List Nat} (hn : g.next ≤ next')
    (hpar : ∀ y, y < g.next → par' y = g.par y) :
    SysStep N D law .env g (HubAnswer.stored g next' par') :=
  .env ⟨hn, hpar⟩ rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- The native `Push` handler, projected: its writes, a raw step, then its decision from the state
they leave, the `answer` step `push_step` builds. Every binding of the decision (the call in
flight, the records compared, `is_dropped`, the closure stored, the law accepting exactly when
`Push::answer` does) is of that post-write state, whose raw graph holds what the push uploaded
and what the hub generated. -/
theorem HubAnswer.push_handled {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    {next' : Nat} {par' : Nat → List Nat} {r : Req} {p : Pkt} {c : RawPublish.Checks}
    (hn : g.next ≤ next') (hpar : ∀ y, y < g.next → par' y = g.par y)
    (hr : r ∈ g.reqs) (hb : r.body = .push p)
    (hrec : c.recordsMatch = true ↔ p.recs = g.hub.recs)
    (hdrop : c.dropped = true ↔ law.dropped g.hub.recs p)
    (hclosed : c.recordsMatch = true → c.dropped = false → p.new ≠ g.hub.head →
      g.hub.head = p.expected → c.closed = true)
    (hacc : RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c =
      .accepted ↔ law.accepts g.hub par' p) :
    SysStep N D law .env g (HubAnswer.stored g next' par') ∧
    SysStep N D law .answer (HubAnswer.stored g next' par')
      (pushAfter N law (HubAnswer.stored g next' par') r p
        (RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c)) :=
  ⟨HubAnswer.store_step hn hpar,
    (HubAnswer.push_step (g := HubAnswer.stored g next' par') hr hb hrec hdrop hclosed hacc).2⟩

/-! ### The answer, as a conformance test observes it

A small computable view of a hub answer, for a native test to compare against: the hub's
`(seq, head, records)` before and after, the reply's kind, and what it carries. A `Fetch` or
`GetObjects` answer passes `checkAnswer` exactly when the hub did not move and the reply is the
one `handle` gives; a passing observation is the system's `answer` step
(`HubAnswer.observed_step`). -/

inductive AnswerKind
  | fetched
  | objects
  | head
  | refused
  deriving DecidableEq, Repr

/-- One hub answer, observed: the hub's snapshot before and after, the reply's kind, and the
snapshot or records it carries. -/
structure AnswerObs where
  before : Snap
  after : Snap
  kind : AnswerKind
  replySnap : Option Snap
  replyRecs : Option Nat
  deriving DecidableEq

/-- The observation of the answer `ans`, the hub's snapshot going from `before` to `after`. -/
def AnswerObs.ofAns (before after : Snap) : Ans → AnswerObs
  | .fetched s => ⟨before, after, .fetched, some s, none⟩
  | .objects => ⟨before, after, .objects, none, none⟩
  | .head s => ⟨before, after, .head, some s, none⟩
  | .refused r => ⟨before, after, .refused, none, some r⟩

/-- What `handle` gives for a call of body `b`, from the hub at `s`, if it is a `Fetch` or a
`GetObjects`: the hub unmoved, and the reply. -/
def expectAnswer (b : Body) (s : Snap) : Option AnswerObs :=
  match b with
  | .fetch => some (AnswerObs.ofAns s s (.fetched s))
  | .objs => some (AnswerObs.ofAns s s .objects)
  | .push _ => none

/-- A `Fetch` or `GetObjects` answer conforms when it is what `handle` gives from the hub's
snapshot before. -/
def checkAnswer (b : Body) (o : AnswerObs) : Bool := expectAnswer b o.before == some o

/-- The system after the hub answers the call `r` with `ans`, the hub's snapshot left as it is. -/
def HubAnswer.apply (g : Sys) (r : Req) (ans : Ans) : Sys :=
  { g with
    reqs := g.reqs.erase r
    reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, false, ans⟩]
    time := g.time + 1 }

/-- An observed `Fetch` or `GetObjects` answer that conforms is the system's `answer` step, the
projected state after being `apply` with the hub's observed snapshot after. -/
theorem HubAnswer.observed_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {g : Sys} {r : Req} {ans : Ans} {after : Snap} (hr : r ∈ g.reqs)
    (hok : checkAnswer r.body (AnswerObs.ofAns g.hub after ans) = true) :
    SysStep N D law .answer g { HubAnswer.apply g r ans with hub := after } := by
  unfold checkAnswer expectAnswer at hok
  cases hb : r.body with
  | fetch =>
    rw [hb] at hok
    cases ans with
    | fetched s =>
      simp only [AnswerObs.ofAns, beq_iff_eq, Option.some.injEq, AnswerObs.mk.injEq,
        true_and, and_true] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact .answer r _ hr rfl false (Or.inl ⟨hb, rfl, rfl, rfl, rfl⟩) rfl
        ⟨rfl, rfl, rfl, rfl⟩ rfl
    | objects => simp [AnswerObs.ofAns] at hok
    | head s => simp [AnswerObs.ofAns] at hok
    | refused x => simp [AnswerObs.ofAns] at hok
  | objs =>
    rw [hb] at hok
    cases ans with
    | objects =>
      simp only [AnswerObs.ofAns, beq_iff_eq, Option.some.injEq, AnswerObs.mk.injEq,
        true_and, and_true] at hok
      subst hok
      exact .answer r _ hr rfl false (Or.inr (Or.inl ⟨hb, rfl, rfl, rfl, rfl⟩)) rfl
        ⟨rfl, rfl, rfl, rfl⟩ rfl
    | fetched s => simp [AnswerObs.ofAns] at hok
    | head s => simp [AnswerObs.ofAns] at hok
    | refused x => simp [AnswerObs.ofAns] at hok
  | push p =>
    rw [hb] at hok
    simp at hok

/-- And `handle`'s own answer passes the check. -/
theorem checkAnswer_expect (b : Body) (s : Snap) (o : AnswerObs)
    (h : expectAnswer b s = some o) : checkAnswer b o = true := by
  unfold checkAnswer
  cases b <;> simp only [expectAnswer, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp [AnswerObs.ofAns, expectAnswer]

/-! ### A node's events

A node's step that sends calls, and its handling of their replies, are observed by the node's own
data: the kind of step and the state its writes leave, its batch of calls by virtual slot and
body, the replies by slot, and the structural projection of its labels into raw ids. A raw id
names one canonical body, so a write that coincides with an operation that exists takes no fresh
raw id, and one the node holds already takes no new label. The projection is checked on the
observation (`NodeSys.Exec.growB`); what is not read off the data is a named law of the native
call that does it, a correspondence obligation: the decision relations (`Issue`, `Handle`, `Loc`,
`Idle`, `HeadRep`) have no checker of their own yet. A label a reply teaches is structure only:
its parents and raw id. What the node holds of it is what it held of that label before, which is
nothing for a state holding nothing above its labels (`Bare`, `learn_new_bare`): a label is new
only for an operation the node did not hold. -/

/-- A node's step that sends calls, as observed: the node, the kind of step, its state after its
writes and their embedding, the head it pushes, and the calls of its batch, by virtual slot (the
batch's injective map of its wire ids) and body. -/
structure NodeIssue where
  node : Nat
  kind : Kind
  post : NS
  new : Nat
  emb : Nat → Nat
  calls : List Req

/-- The node's generation after the step: one more for each label its writes add. -/
def NodeIssue.gen (g : Sys) (e : NodeIssue) : Nat :=
  (g.node e.node).gen + (e.post.next - (g.node e.node).ns.next)

/-- The system after the step: the raw graph as its writes leave it (`next'`, `par'`), the node
waiting on its calls with its state as it was, the calls in flight, and the slots below `slot'`
given out. -/
def NodeIssue.apply (g : Sys) (e : NodeIssue) (next' : Nat) (par' : Nat → List Nat)
    (slot' : Nat) : Sys :=
  { g with
    next := next'
    par := par'
    node := upd g.node e.node ⟨(g.node e.node).ns, (g.node e.node).emb, e.gen g,
      some ⟨e.kind, e.calls.map Req.slot, e.post, e.new, e.emb⟩⟩
    reqs := g.reqs ++ e.calls
    slot := slot'
    time := g.time + 1 }

/-- What the observation of the step must bind, each a law of the native call that does it:
- `idle`: the node has no calls out, the core taking a step only once the last one's replies are
  handled (`NodeCore`);
- `decide`: it is a step the core takes, with its writes (`NodeCore::step`, `Issue`): a
  correspondence obligation of that call, which no checker of this exact relation tests (the
  existing tests cover the core's behaviour in parts) and nothing here proves;
- `grow`: the structural check of its writes passes (`Exec.growB`: each new label a fresh raw id
  or an operation that exists already, labels and raw ids below unmoved);
- `bodies`: the calls are the ones the step returns (`Bodies`);
- `slots`, `nodup`, `slotLe`: the batch's calls take virtual slots of their own, from `g.slot` to
  below `slot'`, none twice (`CallBatch`);
- `notDropped`: the head it pushes is not one its own records or drops drop (the node). -/
structure NodeIssue.Binds (D : Nat → Nat → Nat → Prop) (law : HubLaw) (e : NodeIssue) (g : Sys)
    (next' : Nat) (par' : Nat → List Nat) (slot' : Nat) : Prop where
  idle : (g.node e.node).wait = none
  decide : Issue (D e.node) (g.node e.node).ns e.kind e.post e.new
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe (e.apply g next' par' slot') e.post e.emb) = true
  bodies : Bodies (g.node e.node).ns e.kind (pkt e.node (e.gen g) e.post e.emb e.new)
    (e.calls.map Req.body)
  slots : ∀ q ∈ e.calls, q.node = e.node ∧ g.slot ≤ q.slot ∧ q.slot < slot'
  nodup : (e.calls.map Req.slot).Nodup
  slotLe : g.slot ≤ slot'
  notDropped : ∀ q ∈ e.calls, ∀ p, q.body = .push p → ¬ law.dropped p.recs p

/-- A node's observed step that sends calls is the system's `issue` step. -/
theorem NodeIssue.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {e : NodeIssue}
    {g : Sys} {next' : Nat} {par' : Nat → List Nat} {slot' : Nat}
    (B : e.Binds D law g next' par' slot') :
    SysStep N D law (.issue e.node e.kind) g (e.apply g next' par' slot') :=
  .issue e.node e.kind e.post e.new e.emb e.calls B.idle B.decide (Exec.growB_sound B.grow)
    B.bodies B.slots B.nodup rfl rfl B.slotLe ⟨rfl, rfl, rfl⟩ rfl B.notDropped

/-- In the eligible nodes' system: an eligible node's step is its `issue` step. -/
theorem NodeIssue.hive_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : NodeIssue} {g : Sys} {next' : Nat}
    {par' : Nat → List Nat} {slot' : Nat} (hE : E e.node) (B : e.Binds D law g next' par' slot') :
    HiveStep N D law E old (.issue e.node e.kind) g (e.apply g next' par' slot') :=
  .node e.node hE rfl (NodeIssue.step B)

/-- Another node's step, with the slots as they were, is a raw step: its writes grow the raw
graph (`Exec.growB`'s check on its own labels), and its calls, none of them in flight at the entry
cut, join those in flight. -/
theorem NodeIssue.raw_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : NodeIssue} {g : Sys} {next' : Nat}
    {par' : Nat → List Nat} (hn : ¬ E e.node)
    (hgrow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
      (Exec.observe (e.apply g next' par' g.slot) e.post e.emb) = true)
    (hcalls : ∀ q ∈ e.calls, q.node = e.node ∧ q ∉ old) :
    HiveStep N D law E old .env g (e.apply g next' par' g.slot) := by
  have G := Exec.growB_sound hgrow
  refine .raw e.node hn e.calls ⟨G.rawGrows, G.parRaw⟩ (fun m hm => ?_) rfl hcalls
    ⟨rfl, rfl, rfl, rfl⟩ rfl
  have hmn : m ≠ e.node := fun h => hn (h ▸ hm)
  exact upd_ne _ _ hmn

/-- The head the replies of a step name, if one does. -/
def namedHead (rs : List Rep) : Option Nat := (rs.filterMap fun r => r.ans.head?).head?

/-- At most one of the replies names a head: then it is the head they name. -/
theorem namedHead_of_le {rs : List Rep} (h1 : (rs.filterMap fun r => r.ans.head?).length ≤ 1) :
    (∀ r ∈ rs, ∀ h, r.ans.head? = some h → namedHead rs = some h) ∧
      ∀ h, namedHead rs = some h → ∃ r ∈ rs, r.ans.head? = some h := by
  constructor
  · intro r hr h hh
    have hm : h ∈ rs.filterMap fun r => r.ans.head? := List.mem_filterMap.2 ⟨r, hr, hh⟩
    unfold namedHead
    generalize (rs.filterMap fun r => r.ans.head?) = L at hm h1 ⊢
    match L, h1, hm with
    | [], _, hm => cases hm
    | [x], _, hm => rw [List.mem_singleton.1 hm]; rfl
    | _ :: _ :: _, h1, _ => simp at h1
  · intro h hh
    unfold namedHead at hh
    exact List.mem_filterMap.1 (List.mem_of_mem_head? hh)

/-- What a reply or a notification teaches, from the structural check: the labels it adds are
for raw operations that exist (the raw graph does not grow), with their parents, numbered above
the node's and parents first; the node's other fields are as they were (`ctl`), so what it holds
of a new label (local, staged, objects) is what it held there before (`learn_new_bare`). With the
adapter's laws that it labels only what is missing (`nothing`) and that a step that wrote nothing
has its state as its state after (`same`), that is `Learn`. -/
theorem learn_of_growB {g : Sys} {σ post : NS} {emb : Nat → Nat} {hd : Option Nat}
    {σi posti : NS} {embi : Nat → Nat} (S : Scoped post emb g) (hlt : ParLt post.par)
    (hgrow : Exec.growB (Exec.observe g post emb) (Exec.observe g posti embi) = true)
    (hnothing : (∀ h, hd = some h → Closed post emb g h) → σi = σ ∧ posti = post ∧ embi = emb)
    (hsame : post = σ → posti = σi)
    (hctl : σi = { σ with par := σi.par, next := σi.next } ∧
      posti = { post with par := posti.par, next := posti.next })
    (hgrows : σ.next ≤ σi.next) (hparLt : ParLt posti.par) :
    Learn g σ post emb hd σi posti embi := by
  have G := Exec.growB_sound hgrow
  exact ⟨hnothing, scoped_growR S hlt G, hsame, hctl, ⟨G.next, hgrows⟩, G.parOld, G.embOld,
    hparLt⟩

/-- The node holds nothing from label `k` on: no such operation is local, staged, or has its
objects. -/
def BareFrom (k : Nat) (σ : NS) : Prop := ∀ x, k ≤ x → ¬ σ.loc x ∧ ¬ σ.stg x ∧ ¬ σ.obj x

/-- The node holds nothing above its labels: an operation it has no label for is not local,
not staged, and has no objects. The structural projection builds the node's states so. -/
def Bare (σ : NS) : Prop := BareFrom σ.next σ

/-- A label a reply or a notification teaches is structure only: of a node that holds nothing
above its labels, a new label stands for an operation that is not local, not staged and has no
objects, until its body and objects arrive. -/
theorem learn_new_bare {g : Sys} {σ post : NS} {emb : Nat → Nat} {hd : Option Nat}
    {σi posti : NS} {embi : Nat → Nat} (hl : Learn g σ post emb hd σi posti embi) (hσ : Bare σ)
    (hpost : Bare post) : BareFrom σ.next σi ∧ BareFrom post.next posti := by
  have e1 := hl.ctl.1
  have e2 := hl.ctl.2
  have l1 : σi.loc = σ.loc := by rw [e1]
  have s1 : σi.stg = σ.stg := by rw [e1]
  have o1 : σi.obj = σ.obj := by rw [e1]
  have l2 : posti.loc = post.loc := by rw [e2]
  have s2 : posti.stg = post.stg := by rw [e2]
  have o2 : posti.obj = post.obj := by rw [e2]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [l1, s1, o1]; exact hσ x hx
  · rw [l2, s2, o2]; exact hpost x hx

/-- A node handling the replies to its step's calls, as observed: the node, the replies by slot,
the hub's context they teach, the node's states with what they teach labelled (`σi` before the
step's writes, `posti` after) and its state after, and the embedding with what they teach. -/
structure NodeHandle where
  node : Nat
  replies : List Rep
  ctx : Ctx
  σi : NS
  posti : NS
  after : NS
  embi : Nat → Nat

/-- The system after the node handles the replies: its state after, done waiting, and the
replies in flight `reps'`. -/
def NodeHandle.apply (g : Sys) (e : NodeHandle) (reps' : List Rep) : Sys :=
  { g with
    node := upd g.node e.node ⟨e.after, e.embi, (g.node e.node).gen, none⟩
    reps := reps'
    time := g.time + 1 }

/-- What the observation of the handling must bind, for the step `w` whose calls are out, each a
law of the native call that does it:
- `waiting`: the node waits on the step `w`;
- `replies`, `complete`: the replies are to the step's calls, one for each slot, matched by slot
  (`CallBatch`, which finishes only when every call has its reply);
- `oneHead`: at most one of them names a head, a computable check (a step's batch has one `Fetch`
  or `Push`, and a `GetObjects` reply names none);
- `grow`: the structural check of what they teach passes (`Exec.growB`, on an unmoved raw graph);
- `nothing`, `same`, `ctl`, `grows`, `parLt`: the adapter labels only what is missing below the
  head they name, adds labels and nothing else, parents first, and a step that wrote nothing has
  its state as its state after;
- `drops`, `fits`: the context they teach is the replies' (the head's label, sequence and
  records), with the node's drops;
- `handle`: the core's handling of the replies (`Handle`), a correspondence obligation of that
  handling, which no checker of this exact relation tests;
- `reps`: the replies leave the ones in flight, nothing else. -/
structure NodeHandle.Binds (D : Nat → Nat → Nat → Prop) (e : NodeHandle) (g : Sys) (w : Wait)
    (reps' : List Rep) : Prop where
  waiting : (g.node e.node).wait = some w
  replies : ∀ r ∈ e.replies, r ∈ g.reps ∧ r.node = e.node ∧ r.slot ∈ w.slots
  complete : ∀ s ∈ w.slots, ∃ r ∈ e.replies, r.slot = s
  oneHead : (e.replies.filterMap fun r => r.ans.head?).length ≤ 1
  grow : Exec.growB (Exec.observe g w.post w.emb) (Exec.observe g e.posti e.embi) = true
  nothing : (∀ h, namedHead e.replies = some h → Closed w.post w.emb g h) →
    e.σi = (g.node e.node).ns ∧ e.posti = w.post ∧ e.embi = w.emb
  same : w.post = (g.node e.node).ns → e.posti = e.σi
  ctl : e.σi = { (g.node e.node).ns with par := e.σi.par, next := e.σi.next } ∧
    e.posti = { w.post with par := e.posti.par, next := e.posti.next }
  grows : (g.node e.node).ns.next ≤ e.σi.next
  parLt : ParLt e.posti.par
  drops : e.ctx.drops = D e.node
  fits : ∀ r ∈ e.replies, Fits e.embi e.posti.next e.ctx r.ans
  handle : Handle e.ctx e.σi w.kind e.posti (e.replies.map Rep.ans) e.after
  reps : ∀ r, r ∈ reps' ↔ (r ∈ g.reps ∧ r ∉ e.replies)

/-- A node's observed handling of its step's replies is the system's `handle` step, given the
node's invariants then (`NodeOK`, which a run keeps). -/
theorem NodeHandle.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeHandle} {g : Sys} {w : Wait} {reps' : List Rep} (K : NodeSys.NodeOK D e.node g)
    (B : e.Binds D g w reps') : SysStep N D law (.handle e.node) g (e.apply g reps') := by
  have W := K.wait w B.waiting
  have hpost : LInv w.post := linv_of_sinv (post_inv W.issue (K.inv.sinv 0 (D e.node)))
  obtain ⟨hhd, hhd'⟩ := namedHead_of_le B.oneHead
  exact .handle e.node w e.replies (namedHead e.replies) e.ctx e.σi e.posti e.after e.embi
    B.waiting B.replies B.complete hhd hhd'
    (learn_of_growB W.scope hpost.parLt B.grow B.nothing B.same B.ctl B.grows B.parLt)
    B.drops B.fits B.handle rfl B.reps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- In the eligible nodes' system: an eligible node's handling is its `handle` step. -/
theorem NodeHandle.hive_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : NodeHandle} {g : Sys} {w : Wait} {reps' : List Rep}
    (hE : E e.node) (K : NodeSys.NodeOK D e.node g) (B : e.Binds D g w reps') :
    HiveStep N D law E old (.handle e.node) g (e.apply g reps') :=
  .node e.node hE rfl (NodeHandle.step K B)

/-- A node's core step that sends nothing, as observed: the node, its state after, and the
embedding of what it wrote. -/
structure NodeCore where
  node : Nat
  after : NS
  emb : Nat → Nat

/-- The system after a core step, its writes leaving the raw graph at `next'` and `par'`, and
the node's generation at `gen'`. -/
def NodeCore.apply (g : Sys) (e : NodeCore) (next' : Nat) (par' : Nat → List Nat) (gen' : Nat) :
    Sys :=
  { g with
    next := next'
    par := par'
    node := upd g.node e.node ⟨e.after, e.emb, gen', none⟩
    time := g.time + 1 }

/-- What the observation of a core step that sends nothing must bind: the node has no calls out
and its round runs (`NodeCore`); the step is one the core takes (`NodeCore::step`, `Loc`), a
correspondence obligation of that call, which no checker of this exact relation tests; and the
structural check of its writes passes (`Exec.growB`). -/
structure NodeCore.Binds (D : Nat → Nat → Nat → Prop) (e : NodeCore) (g : Sys) (next' : Nat)
    (par' : Nat → List Nat) : Prop where
  idle : (g.node e.node).wait = none
  active : (g.node e.node).ns.act = true
  decide : Loc (D e.node) (g.node e.node).ns e.after
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe (e.apply g next' par' (g.node e.node).gen) e.after e.emb) = true

/-- A node's observed core step that sends nothing is the system's `busy` step. -/
theorem NodeCore.busy_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeCore} {g : Sys} {next' : Nat} {par' : Nat → List Nat}
    (B : e.Binds D g next' par') :
    SysStep N D law (.core e.node .busy) g (e.apply g next' par' (g.node e.node).gen) :=
  .busy e.node e.after e.emb B.idle B.active B.decide (Exec.growB_sound B.grow) rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- What the observation of the core idling must bind: no calls out, its round running, the
core idling (`NodeCore::step`, `Idle`), and housekeeping (`when_idle`) then writing nothing: the
raw graph does not move. -/
structure NodeCore.IdleBinds (D : Nat → Nat → Nat → Prop) (e : NodeCore) (g : Sys) : Prop where
  idle : (g.node e.node).wait = none
  active : (g.node e.node).ns.act = true
  decide : Idle (lctx (D e.node) (g.node e.node).ns) (g.node e.node).ns e.after
  emb : e.emb = (g.node e.node).emb

/-- The core idling, observed, with nothing written, is the system's `idle` step: the round
ends. -/
theorem NodeCore.idle_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeCore} {g : Sys} (B : e.IdleBinds D g) :
    SysStep N D law (.core e.node .idle) g (e.apply g g.next g.par (g.node e.node).gen) := by
  have h := B.emb
  refine .idle e.node e.after B.idle B.active B.decide ?_ ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
  show upd g.node e.node ⟨e.after, e.emb, (g.node e.node).gen, none⟩ = _
  rw [h]

/-- What the observation of housekeeping that writes must bind: no calls out, its round running,
the core idling first (`Idle`, to `σ1`), then housekeeping (`when_idle`) writing from that state
with the round going on (`Ext`), and the structural check of its writes (`Exec.growB`). -/
structure NodeCore.MaintBinds (D : Nat → Nat → Nat → Prop) (e : NodeCore) (g : Sys) (σ1 : NS)
    (next' : Nat) (par' : Nat → List Nat) : Prop where
  idle : (g.node e.node).wait = none
  active : (g.node e.node).ns.act = true
  decide : Idle (lctx (D e.node) (g.node e.node).ns) (g.node e.node).ns σ1
  writes : Ext { σ1 with act := true } e.after
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe (e.apply g next' par' (g.node e.node).gen) e.after e.emb) = true

/-- Observed housekeeping that writes is the system's `maint` step: the round goes on. -/
theorem NodeCore.maint_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeCore} {g : Sys} {σ1 : NS} {next' : Nat} {par' : Nat → List Nat}
    (B : e.MaintBinds D g σ1 next' par') :
    SysStep N D law (.core e.node .maint) g (e.apply g next' par'
      ((g.node e.node).gen + (e.after.next - (g.node e.node).ns.next))) := by
  have G := Exec.growB_sound B.grow
  exact .maint e.node σ1 e.after e.emb B.idle B.active B.decide B.writes ⟨G.next, G.rawGrows,
    G.embOld, G.parRaw, G.parOld, G.bound, G.parNew, G.reuse, G.injNew, G.cover⟩ rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- A node taking a notification between rounds, as observed: the node, the notification, the
context it teaches, the node's state with what it teaches labelled (`σi`), its state after, and
the embedding with what it teaches. -/
structure NodeNotice where
  node : Nat
  note : Note
  ctx : Ctx
  σi : NS
  after : NS
  embi : Nat → Nat

/-- The system after the node takes the notification: its state after, and the notification
gone from those in flight, that one copy. -/
def NodeNotice.apply (g : Sys) (e : NodeNotice) : Sys :=
  { g with
    node := upd g.node e.node ⟨e.after, e.embi, (g.node e.node).gen, none⟩
    notes := g.notes.erase e.note
    time := g.time + 1 }

/-- What the observation of a notification taken must bind: the node has no calls out and no round
running; the notification is its own and in flight; it names a newer pair than the node knows (the
filter of `NotificationControl`); what it teaches passes the structural check (`Exec.growB`) and
the adapter's laws, as for a reply; its context is the notification's, with the node's drops; and
the core takes it (`HeadRep`), a correspondence obligation of that handling, which no checker of
this exact relation tests. -/
structure NodeNotice.Binds (D : Nat → Nat → Nat → Prop) (e : NodeNotice) (g : Sys) : Prop where
  idle : (g.node e.node).wait = none
  between : (g.node e.node).ns.act = false
  inFlight : e.note ∈ g.notes
  own : e.note.node = e.node
  newer : (g.node e.node).ns.known.1 < e.note.snap.seq ∨
    (e.note.snap.seq = (g.node e.node).ns.known.1 ∧
      (g.node e.node).emb (g.node e.node).ns.known.2 = e.note.snap.head)
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe g e.σi e.embi) = true
  nothing : Closed (g.node e.node).ns (g.node e.node).emb g e.note.snap.head →
    e.σi = (g.node e.node).ns ∧ e.embi = (g.node e.node).emb
  ctl : e.σi = { (g.node e.node).ns with par := e.σi.par, next := e.σi.next }
  parLt : ParLt e.σi.par
  drops : e.ctx.drops = D e.node
  fits : Fits e.embi e.σi.next e.ctx (.head e.note.snap)
  handle : HeadRep e.ctx e.σi e.after

/-- A node's observed notification, taken, is the system's `notice` step, given the node's
invariants then. -/
theorem NodeNotice.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeNotice} {g : Sys} (K : NodeSys.NodeOK D e.node g) (B : e.Binds D g) :
    SysStep N D law (.notice e.node e.note) g (e.apply g) := by
  have G := Exec.growB_sound B.grow
  have hl : Learn g (g.node e.node).ns (g.node e.node).ns (g.node e.node).emb
      (some e.note.snap.head) e.σi e.σi e.embi :=
    learn_of_growB K.scope K.inv.parLt B.grow
      (fun h => by
        obtain ⟨h1, h2⟩ := B.nothing (h _ rfl)
        exact ⟨h1, h1, h2⟩)
      (fun _ => rfl) ⟨B.ctl, B.ctl⟩ G.next B.parLt
  exact .notice e.node e.note e.ctx e.σi e.σi e.after e.embi B.idle B.between B.inFlight B.own
    B.newer hl B.drops B.fits B.handle rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- A node dropping a notification that names no newer pair, observed, is the system's `ignore`
step: between rounds, its own notification in flight leaves, the node unchanged. -/
theorem NodeNotice.ignore_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {g : Sys} {n : Nat} {nt : Note} (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = false)
    (hn : nt ∈ g.notes) (hnn : nt.node = n)
    (hold : nt.snap.seq < (g.node n).ns.known.1 ∨ (nt.snap.seq = (g.node n).ns.known.1 ∧
      (g.node n).emb (g.node n).ns.known.2 ≠ nt.snap.head)) :
    SysStep N D law (.ignore n) g { g with notes := g.notes.erase nt, time := g.time + 1 } :=
  .ignore n nt hw ha hn hnn hold rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

end Musubi.SysAcceptance

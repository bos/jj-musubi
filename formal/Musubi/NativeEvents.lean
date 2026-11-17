/-
Compose observations of individual native events into a run of the eligible system. The input
is per-event data, each event with an explicit boundary obligation for the semantic effect of
its native call. The node invariants needed to handle replies come from the constructed
filtered run.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance

namespace Musubi.NativeEvents

open Musubi NodeSettle NodeSys NodeSysEntry SysAcceptance

variable {E : Nat → Prop} [DecidablePred E] {old : List Req}

/-- Filtering keeps every request and reply of an eligible node, so its local invariant
can be read back from the filtered run. Invariants of other nodes are not required. -/
theorem nodeOK_of_filt {D : Nat → Nat → Nat → Prop} {n : Nat} {g : Sys}
    {frozen : Nat → NodeC} (hE : E n) (K : NodeSys.NodeOK D n (filt E frozen old g)) :
    NodeSys.NodeOK D n g := by
  have hn : (filt E frozen old g).node n = g.node n := filt_node_of hE
  refine ⟨?_, ?_, ?_⟩
  · have h := K.inv
    rw [hn] at h
    exact h
  · have h := K.scope
    rw [hn] at h
    exact scoped_congr h rfl rfl
  · intro w hw
    have W := K.wait w (by rw [hn]; exact hw)
    refine ⟨?_, scoped_congr W.scope rfl rfl, ?_, ?_, W.slots, ?_, ?_⟩
    · simpa only [hn] using W.issue
    · simpa only [hn] using W.next
    · simpa only [hn] using W.emb
    · intro q hq hqn hqs
      exact W.reqs q (List.mem_filter.2 ⟨hq, by simp [keepReq, hqn, hE]⟩) hqn hqs
    · intro r hr hrn hrs
      exact W.reps r (List.mem_filter.2 ⟨hr, by simp [keepRep, hrn, hE]⟩) hrn hrs

section

omit [DecidablePred E]

/-- The eligible observer keeps another node's raw writes and newly sent calls. Its hidden
control slot can change freely, and it leaves retired replies of hidden nodes uncollected. -/
def foreignAfter (g : Sys) (n : Nat) (node : NodeC) (next' : Nat) (par' : Nat → List Nat)
    (calls : List Req) : Sys :=
  { g with
    node := upd g.node n node
    next := next'
    par := par'
    reqs := g.reqs ++ calls
    time := g.time + 1 }

/-- Event data, independent of a proof that a native call obeys its boundary contract. -/
inductive Event where
  | issue (data : NodeIssue) (next' slot' : Nat) (par' : Nat → List Nat)
  | handle (data : NodeHandle) (reps' : List Rep)
  | busy (data : NodeCore) (next' : Nat) (par' : Nat → List Nat)
  | idle (data : NodeCore)
  | maint (data : NodeCore) (next' : Nat) (par' : Nat → List Nat)
  | notice (data : NodeNotice)
  | ignore (node : Nat) (note : Note)
  | read (data : HubAnswer) (ans : Ans)
  | push (call : Req) (packet : Pkt) (checks : RawPublish.Checks)
  | store (next' : Nat) (par' : Nat → List Nat)
  | foreign (node : Nat) (after : NodeC) (next' : Nat) (par' : Nat → List Nat) (calls : List Req)
  | foreignAnswer (call : Req) (reply : Rep) (after : Snap)

def Event.act : Event → Act
  | .issue e _ _ _ => .issue e.node e.kind
  | .handle e _ => .handle e.node
  | .busy e _ _ => .core e.node .busy
  | .idle e => .core e.node .idle
  | .maint e _ _ => .core e.node .maint
  | .notice e => .notice e.node e.note
  | .ignore n _ => .ignore n
  | .read _ _ | .push _ _ _ => .answer
  | .store _ _ | .foreign _ _ _ _ _ | .foreignAnswer _ _ _ => .env

/-- Replay writes only the fields the observed event changes: a reply leaves other nodes
and the global graph as they are. -/
def Event.apply (e : Event) (N : Nat) (law : HubLaw) (g : Sys) : Sys :=
  match e with
  | .issue e nx sl par => e.apply g nx par sl
  | .handle e rs => e.apply g rs
  | .busy e nx par => e.apply g nx par (g.node e.node).gen
  | .idle e => e.apply g g.next g.par (g.node e.node).gen
  | .maint e nx par =>
    e.apply g nx par ((g.node e.node).gen + (e.after.next - (g.node e.node).ns.next))
  | .notice e => e.apply g
  | .ignore _ nt => { g with notes := g.notes.erase nt, time := g.time + 1 }
  | .read e ans => HubAnswer.apply g e.req ans
  | .push r p c => pushAfter N law g r p
      (RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c)
  | .store nx par => HubAnswer.stored g nx par
  | .foreign n node nx par calls => foreignAfter g n node nx par calls
  | .foreignAnswer r rep after =>
    { g with hub := after, reqs := g.reqs.erase r, reps := g.reps ++ [rep], time := g.time + 1 }

/-- The boundary obligation for this event's exact data variant at its replay state.
The request a read removes must be a read. -/
def Event.Binds (e : Event) (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw)
    (E : Nat → Prop) (old : List Req) (g : Sys) : Prop :=
  match e with
  | .issue data nx sl par => E data.node ∧ data.Binds D law g nx par sl
  | .handle data rs => E data.node ∧ ∃ w, data.Binds D g w rs
  | .busy data nx par => E data.node ∧ data.Binds D g nx par
  | .idle data => E data.node ∧ data.IdleBinds D g
  | .maint data nx par => E data.node ∧ ∃ σ1, data.MaintBinds D g σ1 nx par
  | .notice data => E data.node ∧ data.Binds D g
  | .ignore n nt => E n ∧ (g.node n).wait = none ∧ (g.node n).ns.act = false ∧
    nt ∈ g.notes ∧ nt.node = n ∧
    (nt.snap.seq < (g.node n).ns.known.seq ∨ (nt.snap.seq = (g.node n).ns.known.seq ∧
      (g.node n).emb (g.node n).ns.known.head ≠ nt.snap.head))
  | .read data ans => data.Binds g (e.apply N law g) ans ∧
    (E data.req.node ∨ data.req ∈ old) ∧
    ((data.req.body = .fetch ∧ ans = .fetched data.snap) ∨
      (data.req.body = .objs ∧ ans = .objects))
  | .push r p c => r ∈ g.reqs ∧ r.body = .push p ∧ (E r.node ∨ r ∈ old) ∧
    (c.recordsMatch = true ↔ p.recs = g.hub.recs) ∧
    (c.dropped = true ↔ law.dropped g.hub.recs p) ∧
    (c.recordsMatch = true → c.dropped = false → p.new ≠ g.hub.head →
      g.hub.head = p.expected → c.closed = true) ∧
    (RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c =
      .accepted ↔ law.accepts g.hub g.par p)
  | .store nx par => g.next ≤ nx ∧ ∀ y, y < g.next → par y = g.par y
  | .foreign n node nx par calls => ¬ E n ∧
    NodeSys.Exec.growB (NodeSys.Exec.observe g (g.node n).ns (g.node n).emb)
      (NodeSys.Exec.observe (foreignAfter g n node nx par calls) node.ns node.emb) = true ∧
    ∀ q ∈ calls, q.node = n ∧ q ∉ old
  | .foreignAnswer r rep after => r ∈ g.reqs ∧ ¬ E r.node ∧ r ∉ old ∧
    (rep.node = r.node ∧ rep.slot = r.slot ∧ rep.req = r.body) ∧ after = g.hub

/-- The event's exact bindings and the eligible nodes' current invariants give its system
step. Replay derives those invariants by induction. -/
theorem Event.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : Event} {g : Sys} (B : e.Binds N D law E old g)
    (K : ∀ n, E n → NodeSys.NodeOK D n g) :
    HiveStep N D law E old e.act g (e.apply N law g) := by
  cases e with
  | issue data nx sl par => exact NodeIssue.hive_step B.1 B.2
  | handle data rs =>
    obtain ⟨eligible, wait, binds⟩ := B
    exact NodeHandle.hive_step eligible (K data.node eligible) binds
  | busy data nx par => exact .node data.node B.1 rfl (NodeCore.busy_step B.2)
  | idle data => exact .node data.node B.1 rfl (NodeCore.idle_step B.2)
  | maint data nx par =>
    obtain ⟨eligible, intermediate, binds⟩ := B
    exact .node data.node eligible rfl (NodeCore.maint_step binds)
  | notice data => exact .node data.node B.1 rfl (NodeNotice.step (K data.node B.1) B.2)
  | ignore n nt =>
    obtain ⟨eligible, notWaiting, inactive, inFlight, own, stale⟩ := B
    exact .node n eligible rfl (NodeNotice.ignore_step notWaiting inactive inFlight own stale)
  | read data ans =>
    apply (HubAnswer.hive_step (B := B.1) ?_).1 B.2.1
    rcases B.2.2 with ⟨request, rfl⟩ | ⟨request, rfl⟩
    · exact HubAnswer.fetch_step request B.1
    · exact HubAnswer.objects_step request B.1
  | push r p c =>
    obtain ⟨inFlight, packet, kept, records, dropped, closed, accepts⟩ := B
    apply HiveStep.answer (HubAnswer.push_step inFlight packet records dropped closed accepts).2
    intro rep appended
    have corresponds : rep.node = r.node ∧ rep.slot = r.slot ∧ rep.req = r.body := by
      change (pushAfter N law g r p _).reps = g.reps ++ [rep] at appended
      unfold pushAfter at appended
      split at appended
      · have same := List.append_cancel_left (as := g.reps) appended
        simp only [List.cons.injEq, and_true] at same
        subst same
        exact ⟨rfl, rfl, rfl⟩
      · split at appended <;>
          have same := List.append_cancel_left (as := g.reps) appended <;>
          simp only [List.cons.injEq, and_true] at same <;> subst same <;> exact ⟨rfl, rfl, rfl⟩
    rcases kept with eligible | oldRequest
    · exact Or.inl (corresponds.1 ▸ eligible)
    · exact Or.inr (by simpa only [corresponds.1, corresponds.2.1, corresponds.2.2] using oldRequest)
  | store nx par => exact .env (HubAnswer.store_step B.1 B.2)
  | foreign n node nx par calls =>
    obtain ⟨foreignNode, grows, callsOwn⟩ := B
    have growth := NodeSys.Exec.growB_sound grows
    refine .raw n foreignNode calls ⟨growth.rawGrows, growth.parRaw⟩ ?_ rfl callsOwn
      ⟨rfl, rfl, rfl, rfl⟩ rfl
    intro m eligible
    exact upd_ne _ _ (fun same => foreignNode (same ▸ eligible))
  | foreignAnswer r rep after =>
    obtain ⟨inFlight, foreignNode, fresh, corresponds, rfl⟩ := B
    exact .answerRaw r inFlight foreignNode fresh rep corresponds rfl rfl rfl
      ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- Removing a request by one list erasure identifies that exact request. -/
theorem removed_by_erase {q r : Req} {requests : List Req} (hq : q ∈ requests)
    (hne : q ∉ requests.erase r) : q = r := by
  apply Classical.byContradiction
  intro h
  exact hne ((List.mem_erase_of_ne h).2 hq)

theorem pushAfter_reqs (N : Nat) (law : HubLaw) (g : Sys) (r : Req) (p : Pkt)
    (outcome : RawPublish.Outcome) :
    (pushAfter N law g r p outcome).reqs = g.reqs.erase r := by
  unfold pushAfter
  split
  · rfl
  · split <;> rfl

/-- An eligible push request can leave the replay only through the decision event on
that exact request and packet. A read or another node's answer leaves
it in place. This connects per-decision packet witnesses to the run's removal quantifier. -/
theorem Event.removed_eligible_push {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : Event} {g : Sys} {q : Req} {P : Pkt} (B : e.Binds N D law E old g)
    (hq : q ∈ g.reqs) (hne : q ∉ (e.apply N law g).reqs) (hE : E q.node)
    (hp : q.body = .push P) : ∃ c, e = .push q P c := by
  cases e with
  | issue data nx sl par => exact False.elim (hne (List.mem_append_left _ hq))
  | foreign n node nx par calls => exact False.elim (hne (List.mem_append_left _ hq))
  | handle data rs => exact False.elim (hne hq)
  | busy data nx par => exact False.elim (hne hq)
  | idle data => exact False.elim (hne hq)
  | maint data nx par => exact False.elim (hne hq)
  | notice data => exact False.elim (hne hq)
  | ignore n nt => exact False.elim (hne hq)
  | store nx par => exact False.elim (hne hq)
  | read data ans =>
    have he : q = data.req := removed_by_erase hq hne
    subst q
    rcases B.2.2 with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb] at hp <;> cases hp
  | push r p c =>
    change q ∉ (pushAfter N law g r p _).reqs at hne
    rw [pushAfter_reqs] at hne
    have he := removed_by_erase hq hne
    subst q
    have he : P = p := Body.push.inj (hp.symm.trans B.2.1)
    subst P
    exact ⟨c, rfl⟩
  | foreignAnswer r rep after =>
    have he : q = r := removed_by_erase hq hne
    exact False.elim (B.2.1 (he ▸ hE))

end

/-- The run is constructed recursively from the initial snapshot and event data. -/
def observedRun (N : Nat) (law : HubLaw) (initial : Sys) (events : Nat → Event) : Nat → Sys
  | 0 => initial
  | i + 1 => (events i).apply N law (observedRun N law initial events i)


/-- Local and transport invariants follow the replay. A handling event gets its NodeOK
from this induction, so no callback carries a separate invariant premise. -/
theorem observed_invariants {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (initial : Sys) (events : Nat → Event) (frozen : Nat → NodeC)
    (h0 : ∀ n, RunOK law D n (filt E frozen old initial))
    (hb : ∀ i, (events i).Binds N D law E old (observedRun N law initial events i)) :
    ∀ i n, RunOK law D n (filt E frozen old (observedRun N law initial events i)) := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih =>
    have hs := Event.step (hb i)
      (fun n hn => nodeOK_of_filt hn (ih n).node)
    exact fun n => runOK_step (ih n) (filt_step hs)

/-- Every replay event is a HiveStep, derived from the individual call bindings and the
initial snapshot; the construction takes no model run as input. -/
theorem observed_hs {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (initial : Sys) (events : Nat → Event) (frozen : Nat → NodeC)
    (h0 : ∀ n, RunOK law D n (filt E frozen old initial))
    (hb : ∀ i, (events i).Binds N D law E old (observedRun N law initial events i)) :
    ∀ i, HiveStep N D law E old (events i).act (observedRun N law initial events i)
      (observedRun N law initial events (i + 1)) := by
  intro i
  exact Event.step (hb i) (fun n hn =>
    nodeOK_of_filt hn (observed_invariants initial events frozen h0 hb i n).node)

omit [DecidablePred E] in
/-- Decisions of individual push events supply the exact removal-indexed packet decisions
the convergence proof needs. No such obligation is imposed on calls left in flight. -/
theorem observed_decisions {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (initial : Sys) (events : Nat → Event) (M : Nat) (decode : Nat → List Exec.Rec)
    (hb : ∀ i, (events i).Binds N D law E old (observedRun N law initial events i))
    (hd : ∀ i q P c, events i = .push q P c →
      Nonempty (LawfulDecision M decode (observedRun N law initial events i)
        (observedRun N law initial events (i + 1)) P)) :
    ∀ n, E n → ∀ i q, q ∈ (observedRun N law initial events i).reqs →
      q ∉ (observedRun N law initial events (i + 1)).reqs → q.node = n → ∀ P,
      q.body = .push P → Nonempty (LawfulDecision M decode
        (observedRun N law initial events i) (observedRun N law initial events (i + 1)) P) := by
  intro n hn i q hq hne hnode P hp
  obtain ⟨c, he⟩ := Event.removed_eligible_push (hb i) hq hne (hnode ▸ hn) hp
  exact hd i q P c he

section Records

omit [DecidablePred E]

/-- The same native records read by the raw observer, fine node and original-drop view.
These bindings concern identity and custody, not the node's progress or eligibility. -/
structure RecordView {ρ α : Type} (N k : Nat) (run : Nat → Sys)
    (recs : Nat → Exec.SEState) (O : HiveObs ρ α) (label : ρ → Nat)
    (decode : Nat → List Exec.Rec) (origin : Nat → Nat → Nat → Nat) : Prop where
  applied : ∀ n i, n < N → k ≤ i → ((run i).node n).ns.ap = label (O.applied n i)
  records : ∀ n i, n < N → k ≤ i → (recs i).appliedF n = decode ((run i).node n).ns.ap
  custody : ∀ n i, n < N → k ≤ i →
    Recovery.PendingOriginals (recs i) n ((run i).node n).ns (origin n i)

/-- The record view's bindings hold from any later time too. -/
theorem RecordView.mono {ρ α : Type} {N k k' : Nat} {run : Nat → Sys}
    {recs : Nat → Exec.SEState} {O : HiveObs ρ α} {label : ρ → Nat}
    {decode : Nat → List Exec.Rec} {origin : Nat → Nat → Nat → Nat}
    (V : RecordView N k run recs O label decode origin) (h : k ≤ k') :
    RecordView N k' run recs O label decode origin where
  applied := fun n i hn hi => V.applied n i hn (by omega)
  records := fun n i hn hi => V.records n i hn (by omega)
  custody := fun n i hn hi => V.custody n i hn (by omega)

/-- Raw entry fixes the fine node's applied identity too, through the shared native view. -/
theorem RecordView.applied_current {ρ α : Type} {N k : Nat} {run : Nat → Sys}
    {recs : Nat → Exec.SEState} {O : HiveObs ρ α} {label : ρ → Nat}
    {decode : Nat → List Exec.Rec} {origin : Nat → Nat → Nat → Nat}
    (V : RecordView N k run recs O label decode origin) {R : ρ} {w n i : Nat}
    (hn : n < N) (hi : k ≤ i) (he : EarlyEntry.Control.RawEntry R w (O.rawAt n i)) :
    ((run i).node n).ns.ap = label R :=
  (V.applied n i hn hi).trans (congrArg label he.1)

/-- Once records and original drops are fixed, an entered eligible node has no pending
raw names. It follows from custody and unpublished originals. -/
theorem RecordView.pending_empty {ρ α : Type} {N k c : Nat} {run : Nat → Sys}
    {recs : Nat → Exec.SEState} {O : HiveObs ρ α} {label : ρ → Nat}
    {decode : Nat → List Exec.Rec} {origin : Nat → Nat → Nat → Nat}
    (V : RecordView N k run recs O label decode origin) (hck : c ≤ k)
    (hfixed : RecordsFixedFrom N recs c) {R : ρ} {w : Nat}
    (hhub : (recs c).recs = decode (label R))
    (he : ∀ n, n < N → ∀ i, k ≤ i → EarlyEntry.Control.RawEntry R w (O.rawAt n i)) :
    ∀ n, EligibleAt N recs c n → ∀ i, k ≤ i → ((run i).node n).ns.pending = [] := by
  intro n hn i hi
  have hci : c ≤ i := Nat.le_trans hck hi
  have hr : (recs i).recs = (recs c).recs := congrArg Prod.fst (hfixed i hci).1
  apply Recovery.eligible_pending_empty decode (label R) (origin n i)
    (V.records n i hn.1 hi) (V.applied_current hn.1 hi (he n hn.1 i hi))
    (hr.trans hhub) (V.custody n i hn.1 hi)
  intro x
  refine ((hfixed i hci).2 n hn.1 x).trans ?_
  have hx := congrFun (Exec.seteq_setP hn.2) x
  simpa only [Exec.setP, Exec.SEState.hubDL, hr] using Iff.of_eq hx

/-- After raw entry persists, the applied-record effect of an eligible core step is
equality: the applied record `ap` is unchanged. -/
theorem RecordView.applied_stays {ρ α : Type} {N k : Nat} {run : Nat → Sys}
    {recs : Nat → Exec.SEState} {O : HiveObs ρ α} {label : ρ → Nat}
    {decode : Nat → List Exec.Rec} {origin : Nat → Nat → Nat → Nat}
    (V : RecordView N k run recs O label decode origin) {R : ρ} {w : Nat}
    (he : ∀ n, n < N → ∀ i, k ≤ i → EarlyEntry.Control.RawEntry R w (O.rawAt n i)) :
    ∀ n, n < N → ∀ i, k ≤ i →
      ((run (i + 1)).node n).ns.ap = ((run i).node n).ns.ap := by
  intro n hn i hi
  exact (V.applied_current hn (by omega) (he n hn (i + 1) (by omega))).trans
    (V.applied_current hn hi (he n hn i hi)).symm

end Records

end Musubi.NativeEvents

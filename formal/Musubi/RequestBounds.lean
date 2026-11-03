/-
Every issued push names a raw operation already created by the SAME node exchange.
The bound is derived from Issue, WriteRes and the scoped post-write graph, and is retained
by all actual request-list changes. It is not an extra bound on future accepted packets.
-/
import Musubi.HistoryReplies

namespace Musubi.Recovery.HubSys

open Musubi NodeSys NodeSettle EarlyEntry

def RequestBounds (g : Sys) : Prop :=
  ∀ r ∈ g.reqs, ∀ p, r.body = .push p → p.new < g.next

theorem bodies_push_packet {n gen : Nat} {post σ : NS} {emb : Nat → Nat}
    {new : Nat} {k : Kind} {rq : List Req}
    (hb : Bodies σ k (pkt n gen post emb new) (rq.map Req.body))
    {r : Req} (hr : r ∈ rq) {p : Pkt} (hp : r.body = .push p) :
    k = .push ∧ p = pkt n gen post emb new := by
  have hm : Body.push p ∈ rq.map Req.body := List.mem_map.2 ⟨r, hr, hp⟩
  cases k <;> simp only [Bodies] at hb
  · rw [hb] at hm; simp at hm
  · rcases hb with ⟨_, hb⟩ | ⟨_, hb⟩ <;> rw [hb] at hm <;> simp at hm
  · rw [hb] at hm; simp at hm
  · rw [hb] at hm; simp at hm
  · exact ⟨rfl, by simpa [hb] using hm⟩
  · rw [hb] at hm; simp at hm

theorem writeRes_head {σ post : NS} {new : Nat} (h : WriteRes σ post new) :
    new ∈ post.heads := by
  obtain ⟨y, hy, (⟨_, hf⟩ | ⟨_, rfl, rfl⟩)⟩ := h
  · simp [hf.heads]
  · simp [hy]

theorem issued_push_bound {D : Nat → Nat → Nat → Prop}
    {g g' : Sys} {n : Nat} {k : Kind} {post : NS} {new : Nat} {emb : Nat → Nat}
    {rq : List Req} {gen : Nat}
    (hi : NodeSys.NodeOK D n g) (hs : Issue (D n) (g.node n).ns k post new)
    (hg : GrowR g g' (g.node n).ns post (g.node n).emb emb)
    (hb : Bodies (g.node n).ns k (pkt n gen post emb new) (rq.map Req.body)) :
    ∀ r ∈ rq, ∀ p, r.body = .push p → p.new < g'.next := by
  intro r hr p hp
  obtain ⟨rfl, rfl⟩ := bodies_push_packet hb hr hp
  have sp := scoped_growR hi.scope hi.inv.parLt hg
  have ip := post_inv hs (hi.inv.sinv 0 (D n))
  obtain ⟨_, _, _, _, _, _, _, _, hw, _⟩ := hs
  exact sp.lt new (ip.headsLt new (writeRes_head hw))

theorem request_bounds_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {g g' : Sys} {act : Act} (hi : RequestBounds g)
    (hn : ∀ n, NodeSys.NodeOK D n g) (hs : SysStep N D law act g g') : RequestBounds g' := by
  have grow := step_raw_grows hs
  have inherited : (∀ r ∈ g'.reqs, r ∈ g.reqs) → RequestBounds g' := by
    intro hsub r hr p hp
    exact Nat.lt_of_lt_of_le (hi r (hsub r hr) p hp) grow.1
  cases hs with
  | issue n k post new emb rq _ hs hg hb _ _ _ hr _ _ _ _ =>
    intro r hm p hp
    rw [hr, List.mem_append] at hm
    rcases hm with hm | hm
    · exact Nat.lt_of_lt_of_le (hi r hm p hp) grow.1
    · exact issued_push_bound (hn n) hs hg hb r hm p hp
  | answer _ _ _ hr _ _ _ _ _ =>
    exact inherited (fun _ hm => List.mem_of_mem_erase (hr ▸ hm))
  | busy _ _ _ _ _ _ _ _ hq _ | idle _ _ _ _ _ _ _ hq _ =>
    exact inherited (fun _ hm => hq.reqs ▸ hm)
  | maint _ _ _ _ _ _ _ _ _ _ hq _ | env _ _ hq _ =>
    exact inherited (fun _ hm => hq.reqs ▸ hm)
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    exact inherited (fun _ hm => hr.2.1 ▸ hm)
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    exact inherited (fun _ hm => hr.2.1 ▸ hm)
  | ignore _ _ _ _ _ _ _ _ _ hr _ => exact inherited (fun _ hm => hr.2.1 ▸ hm)

theorem request_bounds_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (run : Nat → Sys) (acts : Nat → Act)
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    (hn : ∀ i n, NodeSys.NodeOK D n (run i)) (h0 : RequestBounds (run 0)) :
    ∀ i, RequestBounds (run i) := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih => exact request_bounds_step ih (hn i) (hs i)

end Musubi.Recovery.HubSys

namespace Musubi.Recovery.HubSys

open Musubi NodeSys NodeSysEntry NodeSettle HubSuffix HubNodeSteps

/-- The native laws used at one actual event. No suffix step, decreasing rank, finite
acceptance count or stable hub is a field of this contract. Pending drops are already empty
for eligible nodes; EntryAssembly supplies that fact at their entry cut. -/
structure SuffixStepLaws (E : Nat → Prop) (D : Nat → Nat → Nat → Prop) (law : HubLaw)
    (old : List Req) (w : Nat) (hist : Nat → Nat) (act : Act) (g g' : Sys) : Prop where
  pending : ∀ n, E n → (g.node n).ns.pending = []
  applied : ∀ n, E n → act = .core n .busy → (g'.node n).ns.ap = (g.node n).ns.ap
  unique : ∀ n, E n → act = .core n .busy → (g.node n).ns.heads.Nodup
  advance : ∀ n, E n → act = .core n .busy → AdvGuard (g.node n).ns →
    FullAdv (g.node n).ns (g'.node n).ns
  maintain : ∀ n, E n → act = .core n .maint → MaintLaw (g.node n).ns (g'.node n).ns
  /-- A housekeeping step writes new operations, in order: a premise of the model, not a claim
  about native housekeeping, whose writes can coincide with operations that exist. The hive
  derives it vacuously, its suffix having no housekeeping step (`suffixStepLaws_filt`). -/
  maintFresh : ∀ n, E n → act = .core n .maint →
    Grow g g' (g.node n).ns (g'.node n).ns (g.node n).emb (g'.node n).emb
  replies : ∀ n, E n → ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → ∀ s,
    (r.ans = .fetched s ∨ r.ans = .head s) → HonestSnap w hist g s
  notices : ∀ n, E n → ∀ nt, act = .notice n nt → HonestSnap w hist g nt.snap
  /-- Only the request chosen by an actual moving answer needs alignment. Old requests
  remain in the finite initial ledger, including requests from ineligible senders. -/
  accepted : act = .answer → ∀ r ∈ g.reqs, g'.reqs = g.reqs.erase r →
    ∀ p, r.body = .push p → law.accepts g.hub g.par p → g'.hub.seq = g.hub.seq + 1 →
    E p.node ∨ r ∈ old

theorem nextLedger_foreign {E : Nat → Prop} {g g' : Sys} {act : Act} (pk : List Packet)
    (hf : ∀ n, E n → ¬ act.about n) : nextLedger E g g' act pk = pk := by
  classical
  cases act <;> try rfl
  case issue n k =>
    have hn : ¬ E n := fun he => hf n he rfl
    simp [nextLedger, hn]

/-- Every actual system event expands using its own packet ledger and saved history.
The sender case, the hub's answer, and an event of another node exhaust the system. -/
theorem sys_step_expansion {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {w : Nat} {old : List Req} {act : Act} {g g' : Sys}
    (hist : Nat → Nat) (pk : List Packet)
    (hs : SysStep N D law act g g') (hk : ∀ n, E n → RunOK law D n g)
    (hd : ∀ x, x < g'.next → ∀ p ∈ g'.par x, p < x)
    (hb : RequestBounds g) (hc : Covers E g pk)
    (ho : ∀ r ∈ old, ∀ p, r.body = .push p → ∃ tag, packet p tag ∈ pk)
    (hl : SuffixStepLaws E D law old w hist act g g') :
    Nonempty (Expansion.Path (HubSuffix.Step E w) (view E g hist pk)
      (view E g' (nextHistory g g' hist) (nextLedger E g g' act pk))) := by
  classical
  by_cases ha : act = .answer
  · subst act
    have beforeDag : ∀ x, x < g.next → ∀ p ∈ g.par x, p < x := by
      cases hs with
      | answer _ _ _ _ _ _ _ hr _ =>
        intro x hx p hp
        exact hd x (hr.2.1 ▸ hx) p (by rw [hr.2.2.1]; exact hp)
    apply answer_step_expansion hs hist pk beforeDag hb
    intro r hr her p hp ha hseq
    rcases hl.accepted rfl r hr her p hp ha hseq with he | hold
    · exact hc r hr p hp he
    · exact ho r hold p hp
  · rw [nextHistory_quiet hist (step_hub_quiet hs ha)]
    by_cases own : ∃ n, E n ∧ act.about n
    · obtain ⟨n, hn, hab⟩ := own
      exact own_step_expansion hist pk hn hs hab (hk n hn) hd (hl.applied n hn)
        (hl.unique n hn) (hl.advance n hn) (hl.maintain n hn) (hl.maintFresh n hn)
        (fun _ _ => hl.pending n hn) (hl.replies n hn) (hl.notices n hn)
    · have hf : ∀ n, E n → ¬ act.about n := fun n hn ha => own ⟨n, hn, ha⟩
      rw [nextLedger_foreign pk hf]
      exact foreign_step_expansion hs ha hf hd hist pk

/-- With no pending drops, even publication writes no new operation. -/
theorem issue_next_same {d : Nat → Nat → Prop} {σ post : NS} {k : Kind} {new : Nat}
    (hi : Issue d σ k post new) (hp : σ.pending = []) : post.next = σ.next := by
  by_cases hk : k = .push
  · subst k
    rw [(push_quiet hi hp).1]
    rfl
  · by_cases hw : k = .writePoll
    · subst k
      obtain ⟨_, _, _, _, _, _, _, hne, _⟩ := hi
      exact False.elim (hne hp)
    · rw [post_same hi hk hw]

/-- Actual generations stop changing when eligible nodes have no pending drops and no
housekeeping event occurs. Other nodes may continue writing and exchanging requests. -/
theorem generations_quiet {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {g g' : Sys} {act : Act} (hs : SysStep N D law act g g')
    (hp : ∀ n, E n → (g.node n).ns.pending = [])
    (hm : ∀ n, E n → act ≠ .core n .maint) : generations E g' = generations E g := by
  apply generations_same
  intro n hn
  by_cases ha : act.about n
  · cases hs with
    | busy m _ _ _ _ _ _ hnode _ _ | idle m _ _ _ _ hnode _ _ _ =>
      simp only [Act.about] at ha
      subst ha
      simp [hnode, upd_same]
    | maint m => exact False.elim (hm m (ha ▸ hn) rfl)
    | issue m k post new emb rq _ hi _ _ _ _ hnode =>
      simp only [Act.about] at ha
      subst ha
      simp [hnode, upd_same, issue_next_same hi (hp m hn)]
    | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hr ht =>
      simp only [Act.about] at ha
      subst ha
      simp [hnode, upd_same]
    | notice m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode =>
      simp only [Act.about] at ha
      subst ha
      simp [hnode, upd_same]
    | ignore m _ _ _ _ _ _ hnode =>
      simp only [Act.about] at ha
      subst ha
      simp [hnode]
    | answer => cases ha
    | env => cases ha
  · rw [node_unchanged hs ha]

theorem step_bk_mono {E : Nat → Prop} {w : Nat} {a b : GState}
    (hs : HubSuffix.Step E w a b) (n : Nat) : a.bk n ≤ b.bk n := by
  cases hs <;> simp_all [upd]
  split <;> simp_all

/-- A positive expansion cannot hide maintenance between equal endpoint generations:
every intermediate generation lies between them. -/
theorem path_bk_quiet {E : Nat → Prop} {w : Nat} {a b : GState}
    (p : Expansion.Path (HubSuffix.Step E w) a b) (hb : b.bk = a.bk) :
    ∀ j, j < p.len → (p.st (j + 1)).bk = (p.st j).bk := by
  have mono : ∀ i j, i ≤ j → j ≤ p.len → ∀ n, (p.st i).bk n ≤ (p.st j).bk n := by
    intro i j hij hj n
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      exact Nat.le_trans (ih (by omega) (by omega)) (step_bk_mono (p.step _ (by omega)) n)
  intro j hj
  funext n
  have lo := mono 0 j (Nat.zero_le _) (by omega) n
  have hi := mono (j + 1) p.len (by omega) (Nat.le_refl _) n
  have mid := step_bk_mono (p.step j hj) n
  rw [p.first] at lo
  rw [p.last, hb] at hi
  omega

theorem initial_packets_bound {g : Sys} (hb : RequestBounds g) :
    ∀ p ∈ collectPackets (fun _ => none) g.reqs, p.new < g.next ∧ p.tag = none := by
  intro p hp
  obtain ⟨r, hr, he⟩ := List.mem_filterMap.1 hp
  cases hbody : r.body with
  | push q =>
    simp only [hbody] at he
    have heq : packet q none = p := Option.some.inj he
    subst p
    exact ⟨hb r hr q hbody, rfl⟩
  | fetch | objs => simp [hbody] at he

/-- Initial suffix invariants are just the saved raw history, truthful entry knowledge,
and the actual node and request bounds. Initial packets receive no current generation. -/
theorem sys_suffix_entry {D : Nat → Nat → Nat → Prop} {E : Nat → Prop} {w : Nat}
    {g : Sys} {hist : Nat → Nat} (hi : HistoryWindow w (state g hist))
    (hk : ∀ n, E n → NodeSys.NodeOK D n g)
    (hp : ∀ n, E n → (g.node n).ns.pending = [])
    (hknown : ∀ n, E n → HonestSnap w hist g
      ⟨(known g n).1, (known g n).2, g.hub.recs⟩)
    (hb : RequestBounds g) :
    HubSuffix.Inv E w (view E g hist (collectPackets (fun _ => none) g.reqs)) := by
  apply history_window_enters_suffix hi hknown
  · intro n hn x hx
    obtain ⟨y, hy, he⟩ := ((state_repo_agrees (hk n hn) (hp n hn)).1 x).1 hx
    rw [← he]
    exact (hk n hn).scope.lt y ((hk n hn).inv.headsLt y hy)
  · exact initial_packets_bound hb

/-- Local settling at the hub's current sequence identifies the actual raw head, using
the suffix's truthful knowledge invariant rather than an unretained entry-time label. -/
theorem settled_raw_head {D : Nat → Nat → Nat → Prop} {E : Nat → Prop} {w n H R : Nat}
    {g : Sys} {hist : Nat → Nat} {pk : List Packet}
    (hi : HubSuffix.Inv E w (view E g hist pk)) (hn : E n) (hk : NodeSys.NodeOK D n g)
    (hs : NodeSettle.Settled ⟨g.hub.seq, H, R, D n⟩ (g.node n).ns) :
    (g.node n).emb H = g.hub.head ∧ ∀ x, heads g n x ↔ x = g.hub.head := by
  have agree := state_repo_agrees hk hs.2.2.2.1
  have knownEq : known g n = (g.hub.seq, (g.node n).emb H) := by
    rw [agree.2, hs.1]
  have truthful := (hi.known n hn).2.2
  change hist (known g n).1 = (known g n).2 at truthful
  rw [knownEq] at truthful
  have raw : (g.node n).emb H = g.hub.head := truthful.symm.trans hi.histHead
  refine ⟨raw, fun x => ?_⟩
  rw [agree.1 x, hs.2.2.2.2.1]
  simp [raw, eq_comm]

/-- Hub stabilization of the actual joint system, rather than a separately supplied
suffix run. All model steps, packet coverage and finite maintenance of the expansion are
derived here. Entry knowledge and native per-event laws remain explicit boundaries. -/
theorem hub_stabilizes_sys {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {w : Nat} (run : Nat → Sys) (acts : Nat → Act) (initial : Nat → Nat)
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    (hk : ∀ n, RunOK law D n (run 0))
    (hd : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hb : RequestBounds (run 0))
    (hi : HistoryWindow w (state (run 0) initial))
    (hknown : ∀ n, E n → HonestSnap w initial (run 0)
      ⟨(known (run 0) n).1, (known (run 0) n).2, (run 0).hub.recs⟩)
    (hl : ∀ i, SuffixStepLaws E D law (run 0).reqs w (histories run initial i)
      (acts i) (run i) (run (i + 1)))
    (hN : ∀ n, E n → n < N) (kb : Nat)
    (hm : ∀ i, kb ≤ i → ∀ n, E n → acts i ≠ .core n .maint) :
    ∃ k, (∀ i, HubSuffix.Inv E w
      (view E (run i) (histories run initial i) (ledger E run acts i))) ∧
      ∀ i, k ≤ i →
        (run i).hub.head = (run k).hub.head ∧ (run i).hub.seq = (run k).hub.seq := by
  have K : ∀ i n, RunOK law D n (run i) :=
    fun i n => runOK_run run acts (fun i _ => hs i) (hk n) i (Nat.zero_le _)
  have B := request_bounds_run run acts hs (fun i n => (K i n).node) hb
  let actual := fun i => view E (run i) (histories run initial i) (ledger E run acts i)
  have hp : ∀ i, Nonempty (Expansion.Path (HubSuffix.Step E w) (actual i) (actual (i + 1))) := by
    intro i
    exact sys_step_expansion _ _ (hs i) (fun n _ => K i n) (hd (i + 1)) (B i)
      (ledger_covers E run acts hs i)
      (fun r hr p hp => ⟨none, ledger_keeps_initial E run acts hr hp i⟩) (hl i)
  let p := fun i => Classical.choice (hp i)
  have hinv : ∀ i, HubSuffix.Inv E w (actual i) := by
    intro i
    induction i with
    | zero => exact sys_suffix_entry hi (fun n _ => (hk n).node) (hl 0).pending hknown hb
    | succ i ih =>
      exact (p i).invariant (HubSuffix.Inv E w)
        (fun _ _ hin step => HubSuffix.inv_step hin step) ih
  have hfirst : Expansion.concat p 0 = actual 0 := (p 0).first
  have hbk : ∀ i, Expansion.index p kb ≤ i →
      (Expansion.concat p (i + 1)).bk = (Expansion.concat p i).bk := by
    apply Expansion.concat_tail p (fun a b => b.bk = a.bk) kb
    intro i hki
    apply path_bk_quiet (p i)
    exact generations_quiet (hs i) (hl i).pending (hm i hki)
  have start : HubSuffix.Inv E w (Expansion.concat p 0) := by
    rw [hfirst]
    exact sys_suffix_entry hi (fun n _ => (hk n).node) (hl 0).pending hknown hb
  obtain ⟨k, hstable⟩ := hub_suffix_stabilizes (Expansion.concat p) start
    (Expansion.concat_step p) hN (Expansion.index p kb) hbk
  have stable : ∃ k, ∀ i, k ≤ i →
      ((Expansion.concat p i).s.hub.head, (Expansion.concat p i).s.hub.seq) =
      ((Expansion.concat p k).s.hub.head, (Expansion.concat p k).s.hub.seq) :=
    ⟨k, fun i hi => Prod.ext (hstable i hi).1 (hstable i hi).2⟩
  obtain ⟨k, hk⟩ := Expansion.stabilizes_of_expansion
    (fun g : GState => (g.s.hub.head, g.s.hub.seq)) actual (Expansion.concat p)
    (Expansion.index p) (Expansion.index_lt p) (Expansion.concat_index p) stable
  exact ⟨k, hinv, fun i hi => ⟨congrArg Prod.fst (hk i hi), congrArg Prod.snd (hk i hi)⟩⟩

/-! ## The hub settles in the hive's actual run

The hive's run, observed from the entry cut (`NodeSysEntry.HiveStep`), is read as the eligible
nodes' system (`NodeSysEntry.filt`), every node that is not eligible a dummy on the raw root
and the requests in flight at the cut kept as the initial budget. That system is a run of the
fine system with the actual acts (`NodeSysEntry.filt_run_from`), has the actual hub, raw graph
and eligible nodes, and starts as a run should (`NodeSysEntry.runOK_filt_init`), so
`hub_stabilizes_sys` applies to it, and the actual hub settles (`hub_stabilizes_hive`). The
eligible nodes' laws are taken on the actual steps (`NodeStepLaws`); that only an eligible
node's push, or one in flight at the cut, moves the hub is derived on the filtered run from what
it keeps and from packets naming their senders (`OwnersOrOld`), not assumed. -/

/-- Every push in flight is its sender's packet, or was in flight at the entry cut. -/
def OwnersOrOld (old : List Req) (g : Sys) : Prop :=
  ∀ r ∈ g.reqs, ∀ p, r.body = .push p → p.node = r.node ∨ r ∈ old

theorem ownersOrOld_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {old : List Req} {act : Act} {g g' : Sys} (h : OwnersOrOld old g)
    (hs : SysStep N D law act g g') : OwnersOrOld old g' := by
  intro r hm p hp
  cases hs with
  | issue _ _ _ _ _ _ _ _ _ hb hslot _ _ hr _ _ _ _ =>
    rw [hr, List.mem_append] at hm
    rcases hm with hm | hm
    · exact h r hm p hp
    · exact Or.inl ((bodies_push_owner hb hm hp).trans (hslot r hm).1.symm)
  | answer _ _ _ hr _ _ _ _ _ =>
    rw [hr] at hm
    exact h r (List.mem_of_mem_erase hm) p hp
  | busy _ _ _ _ _ _ _ _ hq _ | idle _ _ _ _ _ _ _ hq _ =>
    rw [hq.reqs] at hm; exact h r hm p hp
  | maint _ _ _ _ _ _ _ _ _ _ hq _ | env _ _ hq _ =>
    rw [hq.reqs] at hm; exact h r hm p hp
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    rw [hr.2.1] at hm; exact h r hm p hp
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    rw [hr.2.1] at hm; exact h r hm p hp
  | ignore _ _ _ _ _ _ _ _ _ hr _ =>
    rw [hr.2.1] at hm; exact h r hm p hp

theorem ownersOrOld_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {old : List Req} (run : Nat → Sys) (acts : Nat → Act)
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    (h0 : OwnersOrOld old (run 0)) : ∀ i, OwnersOrOld old (run i) := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih => exact ownersOrOld_step ih (hs i)

/-- The eligible nodes' laws at one actual event: `SuffixStepLaws` but for which pushes move
the hub, which the filtered run derives; distinct op heads at a merge (`unique`), which it derives
from distinct op heads at its start (`heads_nodup_step`); and `maintFresh`, vacuous with no
housekeeping step. -/
structure NodeStepLaws (E : Nat → Prop) (D : Nat → Nat → Nat → Prop) (w : Nat)
    (hist : Nat → Nat) (act : Act) (g g' : Sys) : Prop where
  pending : ∀ n, E n → (g.node n).ns.pending = []
  applied : ∀ n, E n → act = .core n .busy → (g'.node n).ns.ap = (g.node n).ns.ap
  advance : ∀ n, E n → act = .core n .busy → AdvGuard (g.node n).ns →
    FullAdv (g.node n).ns (g'.node n).ns
  maintain : ∀ n, E n → act = .core n .maint → MaintLaw (g.node n).ns (g'.node n).ns
  replies : ∀ n, E n → ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → ∀ s,
    (r.ans = .fetched s ∨ r.ans = .head s) → HonestSnap w hist g s
  notices : ∀ n, E n → ∀ nt, act = .notice n nt → HonestSnap w hist g nt.snap

section Filtered

variable {E : Nat → Prop} [DecidablePred E] {frozen : Nat → NodeC} {old : List Req}

theorem nodeStepLaws_filt {D : Nat → Nat → Nat → Prop} {w : Nat} {hist : Nat → Nat}
    {act : Act} {g g' : Sys} (h : NodeStepLaws E D w hist act g g') :
    NodeStepLaws E D w hist act (filt E frozen old g) (filt E frozen old g') where
  pending := fun n hE => by rw [filt_node_of hE]; exact h.pending n hE
  applied := fun n hE ha => by rw [filt_node_of hE, filt_node_of hE]; exact h.applied n hE ha
  advance := fun n hE ha hg => by
    rw [filt_node_of hE, filt_node_of hE]
    exact h.advance n hE ha (by rw [filt_node_of hE] at hg; exact hg)
  maintain := fun n hE ha => by
    rw [filt_node_of hE, filt_node_of hE]; exact h.maintain n hE ha
  replies := fun n hE r hr hr' hn s hs => by
    refine h.replies n hE r (List.mem_filter.1 hr).1 (fun h' => hr' ?_) hn s hs
    exact List.mem_filter.2 ⟨h', keepRep_of (by rw [hn]; exact hE)⟩
  notices := fun n hE nt ha => h.notices n hE nt ha

/-- The filtered run's laws: the eligible nodes' from the actual ones; distinct op heads at a
merge (`huniq`); `maintFresh` vacuously, as no eligible node does housekeeping (`hnm`); and that
an accepted push is an eligible node's or was in flight at the entry cut, since the run keeps
only those and every packet in flight names its sender or is old. -/
theorem suffixStepLaws_filt {D : Nat → Nat → Nat → Prop} {law : HubLaw} {w : Nat}
    {hist : Nat → Nat} {act : Act} {g g' : Sys} {initial : List Req}
    (h : NodeStepLaws E D w hist act g g')
    (huniq : ∀ n, E n → act = .core n .busy → (g.node n).ns.heads.Nodup)
    (hnm : ∀ n, E n → act ≠ .core n .maint)
    (hown : OwnersOrOld old (filt E frozen old g)) (hold : ∀ r ∈ old, r ∈ initial) :
    SuffixStepLaws E D law initial w hist act (filt E frozen old g) (filt E frozen old g') := by
  have n := nodeStepLaws_filt (frozen := frozen) (old := old) h
  refine ⟨n.pending, n.applied,
    fun m hE ha => by rw [filt_node_of hE]; exact huniq m hE ha, n.advance, n.maintain,
    fun m hE ha => absurd ha (hnm m hE), n.replies, n.notices, ?_⟩
  intro _ r hr _ p hp _ _
  have hk := (List.mem_filter.1 hr).2
  simp only [keepReq, Bool.or_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hk
  rcases hown r hr p hp with ho | ho
  · rcases hk with hk | hk
    · exact Or.inl (ho ▸ hk)
    · exact Or.inr (hold r hk)
  · exact Or.inr (hold r ho)

theorem histories_filt (run : Nat → Sys) (initial : Nat → Nat) :
    ∀ i, histories (fun i => filt E frozen old (run i)) initial i = histories run initial i
  | 0 => rfl
  | i + 1 => by
    show nextHistory _ _ (histories (fun i => filt E frozen old (run i)) initial i) = _
    rw [histories_filt run initial i]
    rfl

theorem requestBounds_filt {g : Sys} (h : RequestBounds g) :
    RequestBounds (filt E frozen old g) :=
  fun r hr p hp => h r (List.mem_filter.1 hr).1 p hp

end Filtered

/-- The eligible nodes' system read off the hive's run from the entry cut `k`: every node that
is not eligible a dummy on the raw root `rawRoot`, the requests in flight at the cut kept. -/
noncomputable def hiveSys (E : Nat → Prop) [DecidablePred E] (rawRoot : Nat) (run : Nat → Sys)
    (k : Nat) : Nat → Sys :=
  fun j => filt E (fun _ => dummy rawRoot) (run k).reqs (run (k + j))

/-- What the eligible nodes' system has of `hub_stabilizes_sys`'s premises, from what the
observation has at the entry cut (with the eligible nodes' op heads distinct, `hnodup`) and the
eligible nodes' laws at each actual event, none of them housekeeping from the cut: it is a run of
the fine system with the actual acts, starts as a run should, and its laws hold, distinct op
heads at a merge among them, kept from the cut by every step (`heads_nodup_step`). -/
theorem hive_filtered {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {w : Nat} (run : Nat → Sys) (acts : Nat → Act)
    (initial : Nat → Nat) (k rawRoot : Nat)
    (hs : ∀ i, k ≤ i → HiveStep N D law E (run k).reqs (acts i) (run i) (run (i + 1)))
    (hE0 : ∀ n, E n → NodeSys.NodeOK D n (run k) ∧ ObjsOK n (run k))
    (hsys : SysOK law (run k)) (htime : TimeOK (run k))
    (hans : ∀ r ∈ (run k).reps, r.req = .objs → r.ans = .objects)
    (hroot : rawRoot < (run k).next) (hpar : (run k).par rawRoot = [])
    (hb : RequestBounds (run k))
    (hi : HistoryWindow w (state (run k) initial))
    (hknown : ∀ n, E n → HonestSnap w initial (run k)
      ⟨(known (run k) n).1, (known (run k) n).2, (run k).hub.recs⟩)
    (hl : ∀ i, NodeStepLaws E D w (histories (fun j => run (k + j)) initial i) (acts (k + i))
      (run (k + i)) (run (k + i + 1)))
    (hm : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint)
    (hnodup : ∀ n, E n → HeadsNodup (run k) n) :
    let ρ := hiveSys E rawRoot run k
    (∀ j, SysStep N D law (acts (k + j)) (ρ j) (ρ (j + 1))) ∧
      (∀ n, RunOK law D n (ρ 0)) ∧
      RequestBounds (ρ 0) ∧ HistoryWindow w (state (ρ 0) initial) ∧
      (∀ n, E n → HonestSnap w initial (ρ 0)
        ⟨(known (ρ 0) n).1, (known (ρ 0) n).2, (ρ 0).hub.recs⟩) ∧
      (∀ i, SuffixStepLaws E D law (ρ 0).reqs w (histories ρ initial i) (acts (k + i)) (ρ i)
        (ρ (i + 1))) ∧
      (∀ i, histories ρ initial i = histories (fun j => run (k + j)) initial i) := by
  intro ρ
  have hρ : ∀ j, SysStep N D law (acts (k + j)) (ρ j) (ρ (j + 1)) := by
    intro j
    have := filt_run_from (frozen := fun _ => dummy rawRoot) run acts k hs j
    simpa [ρ, hiveSys, Nat.add_assoc] using this
  have hall : (ρ 0).reqs = (run k).reqs := by
    show ((run (k + 0)).reqs).filter _ = _
    rw [Nat.add_zero]
    apply List.filter_eq_self.2
    intro q hq
    simp [keepReq, hq]
  have hown : ∀ j, OwnersOrOld (run k).reqs (ρ j) :=
    ownersOrOld_run ρ (fun j => acts (k + j)) hρ (fun r hr _ _ => Or.inr (hall ▸ hr))
  have hhist : ∀ i, histories ρ initial i = histories (fun j => run (k + j)) initial i :=
    histories_filt (fun j => run (k + j)) initial
  have h0 : ∀ n, RunOK law D n (ρ 0) :=
    runOK_filt_init (E := E) (old := (run k).reqs) hE0 hsys htime hans hroot hpar
  -- distinct op heads: at the start, and kept by every step
  have hnd : ∀ j n, E n → HeadsNodup (ρ j) n := by
    intro j
    induction j with
    | zero =>
      intro n hE
      have hn : (ρ 0).node n = (run k).node n := filt_node_of hE
      unfold HeadsNodup
      rw [hn]
      exact hnodup n hE
    | succ j ih =>
      intro n hE
      have L := nodeStepLaws_filt (frozen := fun _ => dummy rawRoot) (old := (run k).reqs) (hl j)
      exact heads_nodup_step (hρ j)
        (runOK_run ρ (fun j => acts (k + j)) (fun i _ => hρ i) (h0 n) j (Nat.zero_le _))
        (L.applied n hE) (L.advance n hE) (L.maintain n hE) (ih n hE)
  refine ⟨hρ, h0, requestBounds_filt hb, ?_, ?_, ?_, hhist⟩
  · obtain ⟨a, b, c, d, e, f⟩ := hi
    exact ⟨a, b, c, d, e, f⟩
  · intro n hE
    have hn : (ρ 0).node n = (run k).node n := filt_node_of hE
    unfold known
    rw [hn]
    exact hknown n hE
  · intro i
    rw [hhist i, hall]
    refine suffixStepLaws_filt (hl i) (fun n hE _ => ?_)
      (fun n hE => hm (k + i) (Nat.le_add_right k i) n hE) (hown i) (fun r hr => hr)
    have hn : (ρ i).node n = (run (k + i)).node n := filt_node_of hE
    have h1 := (hnd i n hE).1
    rw [hn] at h1
    exact h1

/-- The hive's actual hub settles. Observed from the entry cut `k` (`HiveStep`, the requests in
flight there the initial budget), read as the eligible nodes' system (`hiveSys`): given what the
observation has at the cut (the eligible nodes' invariants, the global ones of requests, replies
and notifications, the root, request bounds, the hub's history window, and the eligible nodes'
honest knowledge and distinct op heads) and the eligible nodes' laws at each actual event, none of
them housekeeping from the cut, the actual hub's head and sequence are eventually constant; and
the hub suffix's invariant holds throughout of the eligible nodes' system. No filtered trace, no
invariant of the other nodes and no stable hub is assumed. -/
theorem hub_stabilizes_hive {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {w : Nat} (run : Nat → Sys) (acts : Nat → Act)
    (initial : Nat → Nat) (k rawRoot : Nat)
    (hs : ∀ i, k ≤ i → HiveStep N D law E (run k).reqs (acts i) (run i) (run (i + 1)))
    (hE0 : ∀ n, E n → NodeSys.NodeOK D n (run k) ∧ ObjsOK n (run k))
    (hsys : SysOK law (run k)) (htime : TimeOK (run k))
    (hans : ∀ r ∈ (run k).reps, r.req = .objs → r.ans = .objects)
    (hroot : rawRoot < (run k).next) (hpar : (run k).par rawRoot = [])
    (hd : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hb : RequestBounds (run k))
    (hi : HistoryWindow w (state (run k) initial))
    (hknown : ∀ n, E n → HonestSnap w initial (run k)
      ⟨(known (run k) n).1, (known (run k) n).2, (run k).hub.recs⟩)
    (hl : ∀ i, NodeStepLaws E D w (histories (fun j => run (k + j)) initial i) (acts (k + i))
      (run (k + i)) (run (k + i + 1)))
    (hN : ∀ n, E n → n < N) (hm : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint)
    (hnodup : ∀ n, E n → HeadsNodup (run k) n) :
    ∃ K, k ≤ K ∧
      (∀ i, HubSuffix.Inv E w (view E (hiveSys E rawRoot run k i)
          (histories (fun j => run (k + j)) initial i)
          (ledger E (hiveSys E rawRoot run k) (fun j => acts (k + j)) i))) ∧
      ∀ i, K ≤ i →
        (run i).hub.head = (run K).hub.head ∧ (run i).hub.seq = (run K).hub.seq := by
  obtain ⟨hρ, hk0, hb0, hi0, hkn0, hl0, hhist⟩ :=
    hive_filtered (N := N) (law := law) run acts initial k rawRoot hs hE0 hsys htime hans hroot
      hpar hb hi hknown hl hm hnodup
  obtain ⟨K, hinv, hK⟩ := hub_stabilizes_sys (E := E) (w := w) (hiveSys E rawRoot run k)
    (fun j => acts (k + j)) initial hρ hk0 (fun i => hd (k + i)) hb0 hi0 hkn0 hl0 hN 0
    (fun i _ n hE => hm (k + i) (Nat.le_add_right k i) n hE)
  refine ⟨k + K, by omega, fun i => by rw [← hhist i]; exact hinv i, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
  exact hK j (by omega)

end Musubi.Recovery.HubSys

/-
The eligible system observed inside a hive run. `HiveStep` records the events the observation
keeps; `filt` freezes foreign control slots and removes their fresh traffic. Filtering preserves
system steps and the initial invariants required by native-event replay.

The convergence proof uses this file.
-/
import Musubi.NodeSysEntry

namespace Musubi.NodeSysEntry

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys

/-! ## The eligible nodes' system, filtered from the hive's run

The observation starts at the entry cut, not at the record cut: a finite cut after it by which
every eligible node has handled a fresh head from after the record cut and taken the current
records, so that its known head is named in the current records' namespace and its embedding is
scoped. Before it, an eligible node may still know an old raw head whose node-space image the
current drops have changed, and its steps are not claimed to be the fine system's. From the entry
cut on, the hive's run is observed coarsely (`HiveStep`): an eligible node's events, the
environment's, and the hub's answers to requests eligible nodes sent or that were in flight at the
entry cut (`old`, finitely many, which may still move the hub) are steps of the fine system; a
node that is not eligible is raw. What it writes only grows the raw graph; it may send requests,
which take no virtual slot from the system's counter (the projection maps each call it actually
sends injectively, apart from the system's); the replies and notifications it takes stay in the
observation as ghosts, its state being unmodelled; and the hub answers its fresh requests without
moving (`answerRaw`'s `hhub`). That is a law of the native run, from the records alone once they
are fixed: an accepted push whose record effect leaves the records as they were has its sender's
raw pending originals among what they drop, which its custody excludes
(`Recovery.raw_pending_empty_of_fixed_records`, from `Recovery.PendingOriginals.unpublished`). It
needs no original history and no embedding. So the observation is not every field of the native
run: it is what the fine system reads of it.

The eligible nodes' system is a function of that observation (`filt`): the other nodes' slots
frozen, their fresh requests and the replies to them left out. Each observed step is a step of
it (`filt_step`), so a run of the hive from the entry cut is a run of the fine system
(`filt_run_from`), with the hub, the raw graph and the eligible nodes as they are.
-/

section Filter

/-- One step of the hive from the entry cut, as the fine system observes it. An answer is the
fine system's own step; the request it answers is the one its reply names, an eligible node's
or one in flight at the entry cut. -/
inductive HiveStep (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    (old : List Req) : Act → Sys → Sys → Prop
  | node {a : Act} {g g' : Sys} (n : Nat) (hE : E n) (ha : a.about n)
      (hs : SysStep N D law a g g') : HiveStep N D law E old a g g'
  | env {g g' : Sys} (hs : SysStep N D law .env g g') : HiveStep N D law E old .env g g'
  | answer {g g' : Sys} (hs : SysStep N D law .answer g g')
      (hk : ∀ rep, g'.reps = g.reps ++ [rep] →
        E rep.node ∨ (⟨rep.node, rep.slot, rep.req⟩ : Req) ∈ old) :
      HiveStep N D law E old .answer g g'
  | raw {g g' : Sys} (n : Nat) (hn : ¬ E n) (rq : List Req) (hr : RawGrow g g')
      (hnode : ∀ m, E m → g'.node m = g.node m) (hreqs : g'.reqs = g.reqs ++ rq)
      (hrq : ∀ q ∈ rq, q.node = n ∧ q ∉ old)
      (hrest : g'.hub = g.hub ∧ g'.reps = g.reps ∧ g'.notes = g.notes ∧ g'.slot = g.slot)
      (ht : g'.time = g.time + 1) : HiveStep N D law E old .env g g'
  | answerRaw {g g' : Sys} (r : Req) (hr : r ∈ g.reqs) (hn : ¬ E r.node) (hold : r ∉ old)
      (rep : Rep) (hrep : rep.node = r.node ∧ rep.slot = r.slot ∧ rep.req = r.body)
      (hreqs : g'.reqs = g.reqs.erase r) (hreps : g'.reps = g.reps ++ [rep])
      (hhub : g'.hub = g.hub)
      (hrest : g'.node = g.node ∧ g'.notes = g.notes ∧ g'.slot = g.slot ∧
        g'.next = g.next ∧ g'.par = g.par)
      (ht : g'.time = g.time + 1) : HiveStep N D law E old .env g g'

variable (E : Nat → Prop) [DecidablePred E] (frozen : Nat → NodeC) (old : List Req)

def keepReq (q : Req) : Bool := decide (E q.node) || old.contains q

def keepRep (r : Rep) : Bool := decide (E r.node) || old.contains ⟨r.node, r.slot, r.req⟩

/-- The eligible nodes' system read off an observation: the other nodes' slots frozen, and
only the requests eligible nodes sent or that were in flight at the entry cut, with their
replies. -/
def filt (g : Sys) : Sys :=
  { g with
    node := fun m => if E m then g.node m else frozen m
    reqs := g.reqs.filter (keepReq E old)
    reps := g.reps.filter (keepRep E old) }

variable {E frozen old}

theorem filter_erase_keep {α : Type} [DecidableEq α] {p : α → Bool} {a : α}
    (h : p a = true) : ∀ l : List α, (l.erase a).filter p = (l.filter p).erase a
  | [] => rfl
  | b :: l => by
    by_cases hb : b = a
    · subst hb
      simp [h]
    · have ih := filter_erase_keep h l
      have e1 : (b :: l).erase a = b :: l.erase a := by simp [hb]
      rw [e1]
      cases hp : p b
      · simp [hp, ih]
      · have e2 : (b :: List.filter p l).erase a = b :: (List.filter p l).erase a := by
          simp [hb]
        simp [hp, ih, e2]

theorem filter_erase_drop {α : Type} [DecidableEq α] {p : α → Bool} {a : α}
    (h : p a = false) : ∀ l : List α, (l.erase a).filter p = l.filter p
  | [] => rfl
  | b :: l => by
    by_cases hb : b = a
    · subst hb
      simp [h]
    · have e1 : (b :: l).erase a = b :: l.erase a := by simp [hb]
      rw [e1]
      simp only [List.filter_cons]
      rw [filter_erase_drop h l]

/-- What reads only the raw graph reads the eligible nodes' system as the hive. -/
theorem scoped_congr {σ : NS} {emb : Nat → Nat} {g h : Sys} (S : Scoped σ emb g)
    (hn : h.next = g.next) (hp : h.par = g.par) : Scoped σ emb h where
  inj := S.inj
  lt := fun x hx => hn ▸ S.lt x hx
  par := fun x hx => hp ▸ S.par x hx

theorem growR_congr {g g' h h' : Sys} {σ σ' : NS} {emb emb' : Nat → Nat}
    (G : GrowR g g' σ σ' emb emb') (hn : h.next = g.next) (hp : h.par = g.par)
    (hn' : h'.next = g'.next) (hp' : h'.par = g'.par) : GrowR h h' σ σ' emb emb' where
  next := G.next
  rawGrows := by rw [hn, hn']; exact G.rawGrows
  embOld := G.embOld
  parRaw := fun y hy => by rw [hp', hp]; exact G.parRaw y (hn ▸ hy)
  parOld := G.parOld
  bound := fun x h1 h2 => by rw [hn']; exact G.bound x h1 h2
  parNew := fun x h1 h2 => by rw [hp']; exact G.parNew x h1 h2
  reuse := fun x h1 h2 hr => G.reuse x h1 h2 (hn ▸ hr)
  injNew := G.injNew
  cover := fun y h1 h2 => G.cover y (hn ▸ h1) (hn' ▸ h2)

theorem learn_congr {g h : Sys} {σ post : NS} {emb : Nat → Nat} {hd : Option Nat}
    {σi posti : NS} {embi : Nat → Nat} (L : Learn g σ post emb hd σi posti embi)
    (hn : h.next = g.next) (hp : h.par = g.par) : Learn h σ post emb hd σi posti embi where
  nothing := fun closed => L.nothing fun x hx y hy => closed x hx y (hp ▸ hy)
  scope := scoped_congr L.scope hn hp
  same := L.same
  ctl := L.ctl
  grows := L.grows
  parOld := L.parOld
  embOld := L.embOld
  parLt := L.parLt

theorem filt_node_of {g : Sys} {n : Nat} (hE : E n) : (filt E frozen old g).node n = g.node n :=
  by simp [filt, hE]

theorem filt_node_upd {g g' : Sys} {n : Nat} {c : NodeC} (hE : E n)
    (h : g'.node = upd g.node n c) :
    (filt E frozen old g').node = upd (filt E frozen old g).node n c := by
  funext m
  by_cases hm : m = n
  · subst hm; simp [filt, hE, h]
  · simp [filt, h, hm]

theorem filt_node_eq {g g' : Sys} (h : ∀ m, E m → g'.node m = g.node m) :
    (filt E frozen old g').node = (filt E frozen old g).node := by
  funext m
  by_cases hm : E m <;> simp [filt, hm, h m]

theorem filt_quiet {g g' : Sys} (h : Quiet g g') :
    Quiet (filt E frozen old g) (filt E frozen old g') :=
  ⟨h.hub, by simp [filt, h.reqs], by simp [filt, h.reps], h.notes, h.slot⟩

theorem keepRep_of {r : Rep} (hE : E r.node) : keepRep E old r = true := by
  simp [keepRep, hE]

/-- Each observed step is a step of the eligible nodes' system. -/
theorem filt_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act}
    {g g' : Sys} (hs : HiveStep N D law E old a g g') :
    SysStep N D law a (filt E frozen old g) (filt E frozen old g') := by
  cases hs with
  | node n hE ha hs =>
    cases hs with
    | busy m σ' emb' hw hac hl hg hnode hq ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .busy m σ' emb' ?_ ?_ ?_ ?_ ?_ (filt_quiet hq) ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hl
      · rw [hf]; exact growR_congr hg rfl rfl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
    | idle m σ' hw hac hl hnode hr hq ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .idle m σ' ?_ ?_ ?_ ?_ hr (filt_quiet hq) ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hl
      · rw [hf]; exact filt_node_upd hE hnode
    | maint m σ1 σ' emb' hw hac hl hx hg hnode hq ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .maint m σ1 σ' emb' ?_ ?_ ?_ hx ?_ ?_ (filt_quiet hq) ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hl
      · rw [hf]; exact growR_congr hg rfl rfl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
    | issue m k post new emb1 rq hw hi hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      have hkeep : ∀ q ∈ rq, keepReq E old q = true := fun q hq => by
        simp [keepReq, (hslot q hq).1, hE]
      refine .issue m k post new emb1 rq ?_ ?_ ?_ ?_ hslot hnodup ?_ ?_ hslot' ⟨hrest.1, ?_,
        hrest.2.2⟩ ht hnd
      · rw [hf]; exact hw
      · rw [hf]; exact hi
      · rw [hf]; exact growR_congr hg rfl rfl rfl rfl
      · rw [hf]; exact hb
      · rw [hf]; exact filt_node_upd hE hnode
      · simp only [filt, hreqs, List.filter_append]
        rw [List.filter_eq_self.2 hkeep]
      · simp [filt, hrest.2.1]
    | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf' hh hnode hreps hrest
        ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .handle m w rs hd c σi posti σ' embi ?_ ?_ hcov hhd hhd' ?_ hc hf' hh ?_ ?_
        ⟨hrest.1, ?_, hrest.2.2⟩ ht
      · rw [hf]; exact hw
      · intro r hr
        obtain ⟨h1, h2, h3⟩ := hrs r hr
        refine ⟨List.mem_filter.2 ⟨h1, ?_⟩, h2, h3⟩
        exact keepRep_of (by rw [h2]; exact hE)
      · rw [hf]; exact learn_congr hl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
      · intro r
        simp only [filt, List.mem_filter, hreps r]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · simp [filt, hrest.2.1]
    | notice m nt c σi posti σ' embi hw hac hn hnn hnew hl hc hf' hh hnode hnotes hrest ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .notice m nt c σi posti σ' embi ?_ ?_ hn hnn ?_ ?_ hc hf' hh ?_ hnotes
        ⟨hrest.1, ?_, ?_, hrest.2.2.2⟩ ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hnew
      · rw [hf]; exact learn_congr hl rfl rfl
      · rw [hf]; exact filt_node_upd hE hnode
      · simp [filt, hrest.2.1]
      · simp [filt, hrest.2.2.1]
    | ignore m nt hw hac hn hnn hold hnode hnotes hrest ht =>
      simp only [Act.about] at ha; subst ha
      have hf := filt_node_of (frozen := frozen) (old := old) (g := g) hE
      refine .ignore m nt ?_ ?_ hn hnn ?_ ?_ hnotes ⟨hrest.1, ?_, ?_, hrest.2.2.2⟩ ht
      · rw [hf]; exact hw
      · rw [hf]; exact hac
      · rw [hf]; exact hold
      · exact filt_node_eq (fun m _ => by rw [hnode])
      · simp [filt, hrest.2.1]
      · simp [filt, hrest.2.2.1]
    | answer => simp [Act.about] at ha
    | env => simp [Act.about] at ha
  | env hs =>
    cases hs with
    | env hr hnode hq ht =>
      exact .env hr (filt_node_eq (fun m _ => by rw [hnode])) (filt_quiet hq) ht
  | answer hs hk =>
    cases hs with
    | answer r ans hr hreqs acc hans hreps hrest ht =>
      have hkr : keepReq E old r = true := by
        rcases hk _ hreps with h | h
        · simp [keepReq, h]
        · cases r; simp [keepReq, h]
      have hkrep : keepRep E old ⟨r.node, r.slot, g.time, r.body, acc, ans⟩ = true := by
        rcases hk _ hreps with h | h
        · exact keepRep_of h
        · simp [keepRep, h]
      refine .answer r ans (List.mem_filter.2 ⟨hr, hkr⟩) ?_ acc hans ?_
        ⟨filt_node_eq (fun m _ => by rw [hrest.1]), hrest.2⟩ ht
      · simp only [filt, hreqs]
        exact filter_erase_keep hkr _
      · simp only [filt, hreps, List.filter_append, List.filter_cons, hkrep, List.filter_nil,
          ite_true]
  | raw n hn rq hr hnode hreqs hrq hrest ht =>
    refine .env hr (filt_node_eq hnode) ⟨hrest.1, ?_, ?_, hrest.2.2.1, hrest.2.2.2⟩ ht
    · simp only [filt, hreqs, List.filter_append]
      have : rq.filter (keepReq E old) = [] := by
        apply List.filter_eq_nil_iff.2
        intro q hq
        obtain ⟨h1, h2⟩ := hrq q hq
        simp [keepReq, h1, hn, h2]
      rw [this, List.append_nil]
    · simp [filt, hrest.2.1]
  | answerRaw r hr hn hold rep hrep hreqs hreps hhub hrest ht =>
    have hkr : keepReq E old r = false := by
      have hc : old.contains r = false := by simpa using hold
      unfold keepReq
      rw [hc]
      simp [hn]
    have hkrep : keepRep E old rep = false := by
      obtain ⟨h1, h2, h3⟩ := hrep
      have he : (⟨rep.node, rep.slot, rep.req⟩ : Req) = r := by cases r; simp_all
      have hc : old.contains ⟨rep.node, rep.slot, rep.req⟩ = false := by
        rw [he]; simpa using hold
      unfold keepRep
      rw [hc, h1]
      simp [hn]
    refine .env ⟨Nat.le_of_eq hrest.2.2.2.1.symm, fun y _ => by
      show g'.par y = g.par y; rw [hrest.2.2.2.2]⟩
      (filt_node_eq (fun m _ => by rw [hrest.1])) ⟨hhub, ?_, ?_, hrest.2.1, hrest.2.2.1⟩ ht
    · simp only [filt, hreqs]
      exact filter_erase_drop hkr _
    · simp only [filt, hreps, List.filter_append, List.filter_cons, hkrep, List.filter_nil]
      simp

/-- The same, for a run observed from the entry cut `k` on, read from there: the steps before
`k` are not claimed. -/
theorem filt_run_from {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (run : Nat → Sys) (acts : Nat → Act) (k : Nat)
    (hs : ∀ i, k ≤ i → HiveStep N D law E old (acts i) (run i) (run (i + 1))) :
    ∀ i, SysStep N D law (acts (k + i)) (filt E frozen old (run (k + i)))
      (filt E frozen old (run (k + i + 1))) :=
  fun i => filt_step (hs (k + i) (Nat.le_add_right _ _))

/-! ### Where the eligible nodes' system starts

A node that is not eligible stands in it as an inactive dummy on the raw root, waiting for
nothing:
none of its core steps ever runs, so its drop relation never matters, and the requests of it in
flight at the entry cut, and their replies, are orphans that only the initial budget counts.
What the system's run keeps (`RunOK`) holds of its start from what the observation has there:
the eligible nodes' own invariants and the global ones of the requests, replies and
notifications, which filtering only thins (`runOK_filt_init`). -/

/-- The dummy's core state: one label, `0`, its known head and only op head, and inactive. -/
def dummyNS : NS where
  known := ⟨0, 0⟩
  plan := []
  hubRecs := none
  annc := none
  ap := 0
  pending := []
  written := false
  heads := [0]
  img := [0]
  par := fun _ => []
  next := 1
  loc := fun x => x = 0
  stg := fun _ => False
  obj := fun _ => False
  act := false

/-- A node that is not eligible, in the eligible nodes' system: the dummy, its one label (`0`)
on the raw root `rawRoot`, waiting for nothing. -/
def dummy (rawRoot : Nat) : NodeC := ⟨dummyNS, fun _ => rawRoot, 0, none⟩

theorem linv_dummy : LInv dummyNS where
  parLt := fun _ _ h => by cases h
  knownLt := by decide
  headsNe := by simp [dummyNS]
  headsLt := by simp [dummyNS]
  imgNe := by simp [dummyNS]
  imgLt := by simp [dummyNS]

theorem scoped_dummy {g : Sys} {rawRoot : Nat} (hroot : rawRoot < g.next)
    (hpar : g.par rawRoot = []) : Scoped dummyNS (fun _ => rawRoot) g where
  inj := fun x y hx hy _ => by
    change x < 1 at hx; change y < 1 at hy; omega
  lt := fun _ _ => hroot
  par := fun _ _ => by simp [dummyNS, hpar]

theorem waitOK_filt {D : Nat → Nat → Nat → Prop} {g : Sys} {n : Nat} {w : Wait} (hE : E n)
    (W : WaitOK D n g w) : WaitOK D n (filt E frozen old g) w where
  issue := by rw [filt_node_of hE]; exact W.issue
  scope := scoped_congr W.scope rfl rfl
  next := by rw [filt_node_of hE]; exact W.next
  emb := by rw [filt_node_of hE]; exact W.emb
  slots := W.slots
  reqs := fun q hq => W.reqs q (List.mem_filter.1 hq).1
  reps := fun r hr => W.reps r (List.mem_filter.1 hr).1

theorem nodeOK_filt {D : Nat → Nat → Nat → Prop} {g : Sys} {n : Nat} (hE : E n)
    (K : NodeSys.NodeOK D n g) : NodeSys.NodeOK D n (filt E frozen old g) where
  inv := by rw [filt_node_of hE]; exact K.inv
  scope := by rw [filt_node_of hE]; exact scoped_congr K.scope rfl rfl
  wait := fun w hw => waitOK_filt hE (K.wait w (by rw [filt_node_of hE] at hw; exact hw))

theorem objsOK_filt {g : Sys} {n : Nat} (hE : E n) (O : ObjsOK n g) :
    ObjsOK n (filt E frozen old g) where
  ans := fun r hr => O.ans r (List.mem_filter.1 hr).1
  reqs := fun w hw hk q hq => O.reqs w (by rw [filt_node_of hE] at hw; exact hw) hk q
    (List.mem_filter.1 hq).1
  reps := fun w hw hk r hr => O.reps w (by rw [filt_node_of hE] at hw; exact hw) hk r
    (List.mem_filter.1 hr).1

theorem sysOK_filt {law : HubLaw} {g : Sys} (S : SysOK law g) :
    SysOK law (filt E frozen old g) where
  reqs := fun q hq => S.reqs q (List.mem_filter.1 hq).1
  reps := fun r hr => S.reps r (List.mem_filter.1 hr).1
  fetch := fun r hr => S.fetch r (List.mem_filter.1 hr).1
  push := fun r hr => S.push r (List.mem_filter.1 hr).1
  pushAns := fun r hr => S.pushAns r (List.mem_filter.1 hr).1
  honest := fun q hq => S.honest q (List.mem_filter.1 hq).1

theorem timeOK_filt {g : Sys} (T : TimeOK g) : TimeOK (filt E frozen old g) where
  reps := fun r hr => T.reps r (List.mem_filter.1 hr).1
  notes := T.notes

/-- Where the eligible nodes' system starts, every node keeps what a run keeps: an eligible
node from its own invariants in the observation, a dummy by construction, given the root, and
the global invariants from the observation's. -/
theorem runOK_filt_init {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    (hE : ∀ n, E n → NodeSys.NodeOK D n g ∧ ObjsOK n g) (hs : SysOK law g) (ht : TimeOK g)
    (hans : ∀ r ∈ g.reps, r.req = .objs → r.ans = .objects)
    {rawRoot : Nat} (hroot : rawRoot < g.next) (hpar : g.par rawRoot = []) :
    ∀ n, RunOK law D n (filt E (fun _ => dummy rawRoot) old g) := by
  intro n
  refine ⟨?_, sysOK_filt hs, timeOK_filt ht, ?_⟩
  · by_cases he : E n
    · exact nodeOK_filt he (hE n he).1
    · have hd : (filt E (fun _ => dummy rawRoot) old g).node n = dummy rawRoot := by
        simp [filt, he]
      exact ⟨by rw [hd]; exact linv_dummy, by rw [hd]; exact scoped_dummy hroot hpar,
        fun w hw => by (rw [hd] at hw; cases hw)⟩
  · by_cases he : E n
    · exact objsOK_filt he (hE n he).2
    · have hd : (filt E (fun _ => dummy rawRoot) old g).node n = dummy rawRoot := by
        simp [filt, he]
      refine ⟨fun r hr => hans r (List.mem_filter.1 hr).1, fun w hw => ?_, fun w hw => ?_⟩
      · rw [hd] at hw; cases hw
      · rw [hd] at hw; cases hw

end Filter

end Musubi.NodeSysEntry

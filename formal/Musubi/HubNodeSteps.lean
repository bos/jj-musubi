/-
An eligible node's own steps in the joint system refine the hub's suffix on the hub-side view
read from the same system (`own_step_expansion`): each is a positive finite path of
`HubSuffix.Step`, with no hub progress, rank or `HubSuffix.Step` assumed.

The node's core steps that write nothing the view reads (realization, idling, a request that
pushes nothing, the replies to a request for objects or to a refused push, an ignored
notification) are frames. A merge is the suffix's `merge`. An advance is the suffix's `advance`,
then its `merge` when the native advance writes one merge of the whole frontier. Housekeeping
that writes is one maintenance generation per operation (`raw_maintenance_expansion`), the
node's generation counting the raw operations written, as `Grow` makes it. A push with no
pending drops writes nothing and is the suffix's `send`, its packet the ledger's. A reply or
notification that names a head teaches the node an honest pair of the hub's history: `learn`.

The view's raw ancestry is the node's, through its scoped embedding (`anc_up`, `anc_down`).
Primitive laws, explicit and per step, not derived: the native full-frontier advance
(`FullAdv`, stronger than NodeSettle's `Adv`), whose known head stands for itself; housekeeping
that writes ending at a single head, its last operation (`MaintLaw`); no adoption after the
record-adoption cut (the applied records stay); the raw graph's acyclicity; no pending drops at
a step that sends calls (under audit); and the hub's answers honest within the window of root's
history (`HonestSnap`). Distinct op heads at a merge are a premise here too, which the hive
derives (`heads_nodup_step`).
-/
import Musubi.HubLedger
import Musubi.NodeSysEntry

namespace Musubi.Recovery.HubNodeSteps

open Musubi NodeSys NodeSettle EarlyEntry HubSuffix NodeSysEntry Recovery.HubSys

/-! ## Paths of one and two steps -/

def single {G : Type} {R : G → G → Prop} {a b : G} (h : R a b) : Expansion.Path R a b :=
  ⟨1, Nat.one_pos, fun j => if j = 0 then a else b, by simp, by simp, fun j hj => by
    have : j = 0 := by omega
    subst this
    simpa using h⟩

def two {G : Type} {R : G → G → Prop} {a m b : G} (h1 : R a m) (h2 : R m b) :
    Expansion.Path R a b :=
  ⟨2, by decide, fun j => if j = 0 then a else if j = 1 then m else b, by simp, by simp,
    fun j hj => by
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
      · simpa using h1
      · simpa using h2⟩

/-! ## Labels and raw ids agree on ancestry -/

/-- A label's ancestry is its raw id's, in the view's normalized raw graph. -/
theorem anc_up {σ : NS} {emb : Nat → Nat} {g : Sys} (S : Scoped σ emb g) (hlt : ParLt σ.par)
    {a x : Nat} (h : Anc σ.par a x) : x < σ.next → Anc (parents g) (emb a) (emb x) := by
  induction h with
  | refl => intro _; exact Anc.refl
  | @step p x hp _ ih =>
    intro hx
    have hpx : p < x := hlt x p hp
    refine Anc.step (p := emb p) ?_ (ih (by omega))
    show emb p ∈ parents g (emb x)
    simp only [parents, S.lt x hx, ↓reduceIte]
    rw [S.par x hx]
    exact List.mem_map_of_mem hp

/-- A raw ancestry between labelled ids is the labels'. -/
theorem anc_down {σ : NS} {emb : Nat → Nat} {g : Sys} (S : Scoped σ emb g) (hlt : ParLt σ.par)
    {y z : Nat} (h : Anc (parents g) y z) :
    ∀ x, x < σ.next → emb x = z → ∀ a, a < σ.next → emb a = y → Anc σ.par a x := by
  induction h with
  | refl =>
    intro x hx hxe a ha himageA
    rw [S.inj a x ha hx (himageA.trans hxe.symm)]
    exact Anc.refl
  | @step p z hp _ ih =>
    intro x hx hxe a ha himageA
    rw [← hxe] at hp
    simp only [parents, S.lt x hx, ↓reduceIte] at hp
    rw [S.par x hx, List.mem_map] at hp
    obtain ⟨l, hl, rfl⟩ := hp
    exact Anc.step hl (ih l (Nat.lt_trans (hlt x l hl) hx) rfl a ha himageA)

/-! ## The native laws -/

/-- The frontier of a node's op heads and its known head: those not below another. -/
def Frontier (σ : NS) : Nat → Prop := maxSet σ.par (fun y => y ∈ σ.heads ∨ y = σ.known.2)

/-- `advance`'s guard in `NodeCore::step` (`Loc.advance`). -/
def AdvGuard (σ : NS) : Prop :=
  σ.heads.length < 2 ∧ σ.loc σ.known.2 ∧ (¬ ∃ y ∈ σ.heads, Desc σ y) ∧ (norm σ).annc = none

/-- The native full-frontier advance, a primitive law of an `advance_to(known)` call that makes no
other semantic write (its working-copy cleanup, `replace_abandoned_working_copies`, writing
nothing; the hive asks it only where no automatic write of the node happens, its cut excluding
them), stronger than NodeSettle's `Adv`: the known head stands for itself (no record drops or
renames it), and the op heads move to the frontier of the heads and the known head. Either nothing
is written, the frontier becoming the op heads, or, the frontier having two operations or more,
one merge of the whole frontier is written and is the only op head after: a new operation, or one
the node holds already (the same canonical content, written by another copy or before), which
takes no new label and becomes local. Never a write when the frontier is a single operation
already present. With nothing written, the op heads are distinct canonical operations: two
physical op heads with one canonical form (an alias) arise only from an interrupted export, a
failure. -/
structure FullAdv (σ σ' : NS) : Prop where
  img : σ.img = [σ.known.2]
  out : (σ'.next = σ.next ∧ (∀ y, y ∈ σ'.heads ↔ Frontier σ y) ∧ σ'.heads.Nodup) ∨
    ((∃ a b, Frontier σ a ∧ Frontier σ b ∧ a ≠ b) ∧ σ'.next = σ.next + 1 ∧
      (∀ y, y ∈ σ'.par σ.next ↔ Frontier σ y) ∧ σ'.heads = [σ.next]) ∨
    ((∃ a b, Frontier σ a ∧ Frontier σ b ∧ a ≠ b) ∧ σ'.next = σ.next ∧
      ∃ x, x < σ.next ∧ (∀ y, y ∈ σ.par x ↔ Frontier σ y) ∧ σ'.heads = [x])

/-- Housekeeping that writes (`when_idle`), a primitive law: it writes at least one operation,
and the last one written is the single op head after. -/
structure MaintLaw (σ σ' : NS) : Prop where
  wrote : σ.next < σ'.next
  last : σ'.heads = [σ'.next - 1]

/-- A pair the hub answered or published, honest within the window of root's history: a
contract of the hub's own answers, not of the node. -/
def HonestSnap (w : Nat) (hist : Nat → Nat) (g : Sys) (s : Snap) : Prop :=
  w ≤ s.seq ∧ s.seq ≤ g.hub.seq ∧ hist s.seq = s.head

/-- The raw frontier of a node's raw heads and raw known head is the image of its labels'. -/
theorem raw_frontier {σ : NS} {emb : Nat → Nat} {g : Sys} (S : Scoped σ emb g) (I : LInv σ)
    {H : Nat → Prop} (hH : ∀ y, H y ↔ ∃ l ∈ σ.heads, emb l = y) (y : Nat) :
    maxSet (parents g) (fun y => H y ∨ y = emb σ.known.2) y ↔
      ∃ l, l < σ.next ∧ emb l = y ∧ Frontier σ l := by
  have inS : ∀ y, (H y ∨ y = emb σ.known.2) ↔
      ∃ l, l < σ.next ∧ emb l = y ∧ (l ∈ σ.heads ∨ l = σ.known.2) := by
    intro y
    rw [hH]
    constructor
    · rintro (⟨l, hl, rfl⟩ | rfl)
      · exact ⟨l, I.headsLt l hl, rfl, Or.inl hl⟩
      · exact ⟨σ.known.2, I.knownLt, rfl, Or.inr rfl⟩
    · rintro ⟨l, -, rfl, hl | rfl⟩
      · exact Or.inl ⟨l, hl, rfl⟩
      · exact Or.inr rfl
  constructor
  · rintro ⟨hs, hmax⟩
    obtain ⟨l, hl, rfl, hlS⟩ := (inS y).1 hs
    refine ⟨l, hl, rfl, hlS, fun l' hl'S hanc => ?_⟩
    have hl' : l' < σ.next := by
      rcases hl'S with h | rfl
      · exact I.headsLt l' h
      · exact I.knownLt
    exact S.inj l l' hl hl' (hmax (emb l') ((inS _).2 ⟨l', hl', rfl, hl'S⟩)
      (anc_up S I.parLt hanc hl'))
  · rintro ⟨l, hl, rfl, hF⟩
    refine ⟨(inS _).2 ⟨l, hl, rfl, hF.1⟩, fun y' hy' hanc => ?_⟩
    obtain ⟨l', hl', rfl, hl'S⟩ := (inS y').1 hy'
    rw [hF.2 l' hl'S (anc_down S I.parLt hanc l' hl' rfl l hl rfl)]

/-! ## The view of a node -/

theorem repo_none {x : NodeC} (hw : x.wait = none) : x.repo = x.ns ∧ x.repoEmb = x.emb := by
  simp [NodeC.repo, NodeC.repoEmb, hw]

theorem repo_some {x : NodeC} {w : Wait} (hw : x.wait = some w) :
    x.repo = w.post ∧ x.repoEmb = w.emb := by
  simp [NodeC.repo, NodeC.repoEmb, hw]

theorem heads_of {g : Sys} {n : Nat} {L : List Nat} {e : Nat → Nat}
    (hr : (g.node n).repo.heads = L) (he : (g.node n).repoEmb = e) (y : Nat) :
    heads g n y ↔ ∃ l ∈ L, e l = y := by
  unfold heads
  rw [hr, he]

theorem known_of {g : Sys} {n : Nat} {K : Nat × Nat} {e : Nat → Nat}
    (hr : (g.node n).repo.known = K) (he : (g.node n).repoEmb = e) : known g n = (K.1, e K.2) := by
  unfold known
  rw [hr, he]

theorem heads_eq {g g' : Sys} {n : Nat} {L : List Nat} {e e' : Nat → Nat}
    (h1 : ∀ y, heads g n y ↔ ∃ l ∈ L, e l = y) (h2 : ∀ y, heads g' n y ↔ ∃ l ∈ L, e' l = y)
    (he : ∀ l ∈ L, e' l = e l) : heads g' n = heads g n := by
  funext y
  apply propext
  rw [h1, h2]
  constructor
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, (he l hl).symm⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨l, hl, he l hl⟩

theorem about_eq {a : Act} {n m : Nat} (h1 : a.about n) (h2 : a.about m) : m = n := by
  cases a <;> simp only [Act.about] at h1 h2 <;> first | exact h2.symm.trans h1 | exact h1.elim

theorem others_same {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {act : Act}
    {g g' : Sys} {n : Nat} (hs : SysStep N D law act g g') (hab : act.about n) :
    ∀ m, m ≠ n → g'.node m = g.node m :=
  fun _ hm => node_unchanged hs (fun h => hm (about_eq hab h))

/-- A node state with its op heads `H` in place of the view's. -/
def withHeads (a : GState) (n : Nat) (H : Nat → Prop) : GState :=
  { a with s := { a.s with node := upd a.s.node n { a.s.node n with heads := H } } }

theorem withHeads_self (a : GState) (n : Nat) : withHeads a n (a.s.node n).heads = a := by
  unfold withHeads
  rw [show ({ a.s.node n with heads := (a.s.node n).heads } : Node) = a.s.node n from rfl,
    upd_current]

theorem state_uext {g g' : Sys} {hist hist' : Nat → Nat} (hn : g'.next = g.next + 1)
    (hp : ∀ x, x < g.next → g'.par x = g.par x) (hnew : ∀ p ∈ g'.par g.next, p < g.next) :
    UExt (state g hist) (state g' hist') := by
  refine ⟨hn, fun x hx => ?_, fun p hp' => ?_⟩
  · change x ≠ g.next at hx
    change parents g' x = parents g x
    by_cases hlt : x < g.next
    · simp only [parents, hlt, show x < g'.next by omega, ↓reduceIte]
      exact hp x hlt
    · simp only [parents, hlt, show ¬ x < g'.next by omega, ↓reduceIte]
  · change p ∈ parents g' g.next at hp'
    simp only [parents, show g.next < g'.next by omega, ↓reduceIte] at hp'
    exact hnew p hp'

section Steps

variable {E : Nat → Prop} {w n : Nat} {g g' : Sys} {hist : Nat → Nat} {pk : List Packet}

theorem gens_same (hother : ∀ m, m ≠ n → g'.node m = g.node m)
    (hgen : (g'.node n).gen = (g.node n).gen) : generations E g' = generations E g :=
  generations_same fun m _ => by
    by_cases hm : m = n
    · subst hm; exact hgen
    · rw [hother m hm]

theorem nodes_same (hother : ∀ m, m ≠ n → g'.node m = g.node m)
    (hh : heads g' n = heads g n) (hk : known g' n = known g n) :
    ∀ m, E m → NodeSame (state g hist) (state g' hist) m := fun m _ => by
  by_cases hm : m = n
  · subst hm; exact ⟨hh, hk⟩
  · exact state_node_same (hother m hm)

/-- A step that changes nothing the suffix reads. -/
theorem view_frame (hn : g'.next = g.next) (hp : ∀ x, x < g.next → g'.par x = g.par x)
    (hhub : g'.hub = g.hub) (hother : ∀ m, m ≠ n → g'.node m = g.node m)
    (hh : heads g' n = heads g n) (hk : known g' n = known g n)
    (hgen : (g'.node n).gen = (g.node n).gen) :
    HubSuffix.Step E w (view E g hist pk) (view E g' hist pk) :=
  .frame (state_usame hn hp) (state_hub_same hhub rfl) (nodes_same hother hh hk)
    (gens_same hother hgen) rfl

/-- A step whose replies or notification teach the node an honest pair of the hub's history. -/
theorem view_learn (hE : E n) (s : Snap) (hon : HonestSnap w hist g s) (hn : g'.next = g.next)
    (hp : ∀ x, x < g.next → g'.par x = g.par x) (hhub : g'.hub = g.hub)
    (hother : ∀ m, m ≠ n → g'.node m = g.node m) (hh : heads g' n = heads g n)
    (hk : known g' n = (s.seq, s.head)) (hgen : (g'.node n).gen = (g.node n).gen) :
    HubSuffix.Step E w (view E g hist pk) (view E g' hist pk) := by
  refine .learn n s.seq hE hon.1 hon.2.1 (state_usame hn hp) (state_hub_same hhub rfl)
    (fun m _ hm => state_node_same (hother m hm)) hh ?_ (gens_same hother hgen) rfl
  show known g' n = (s.seq, hist s.seq)
  rw [hk, hon.2.2]

/-- A push of the node's single head, the packet the ledger records. -/
theorem view_send (hE : E n) (d : Nat) (hd : ∀ y, heads g n y ↔ y = d) (hn : g'.next = g.next)
    (hp : ∀ x, x < g.next → g'.par x = g.par x) (hhub : g'.hub = g.hub)
    (hother : ∀ m, m ≠ n → g'.node m = g.node m) (hh : heads g' n = heads g n)
    (hk : known g' n = known g n) (hgen : (g'.node n).gen = (g.node n).gen) {pk' : List Packet}
    (hpk : pk' = sent (view E g hist pk) n d :: pk) :
    HubSuffix.Step E w (view E g hist pk) (view E g' hist pk') :=
  .send n d hE hd (state_usame hn hp) (state_hub_same hhub rfl) (nodes_same hother hh hk)
    (gens_same hother hgen) hpk

/-- The raw frontier of the node's heads and known head, as the suffix's `advance` takes it. -/
def rawFrontier (g : Sys) (n : Nat) : Nat → Prop :=
  maxSet (parents g) (fun y => heads g n y ∨ y = (known g n).2)

/-- An advance that writes nothing. -/
theorem view_advance (hE : E n) (hna : ¬ ∃ h, heads g n h ∧ Anc (parents g) (known g n).2 h)
    (hn : g'.next = g.next) (hp : ∀ x, x < g.next → g'.par x = g.par x) (hhub : g'.hub = g.hub)
    (hother : ∀ m, m ≠ n → g'.node m = g.node m) (hh : heads g' n = rawFrontier g n)
    (hk : known g' n = known g n) (hgen : (g'.node n).gen = (g.node n).gen) :
    HubSuffix.Step E w (view E g hist pk) (view E g' hist pk) :=
  .advance n hE hna (state_usame hn hp) (state_hub_same hhub rfl)
    (fun m _ hm => state_node_same (hother m hm)) hh hk (gens_same hother hgen) rfl

/-- An advance's move of the op heads to the frontier, before the merge that writes it. -/
theorem view_advance_mid (hE : E n)
    (hna : ¬ ∃ h, heads g n h ∧ Anc (parents g) (known g n).2 h) :
    HubSuffix.Step E w (view E g hist pk) (withHeads (view E g hist pk) n (rawFrontier g n)) := by
  refine .advance n hE hna ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ (fun m _ hm => ?_) ?_ ?_ rfl rfl
  · show (upd (state g hist).node n _ m).heads = _ ∧ (upd (state g hist).node n _ m).known = _
    rw [upd_ne _ _ hm]
    exact ⟨rfl, rfl⟩
  · show (upd (state g hist).node n _ n).heads = _
    rw [upd_same]
    rfl
  · show (upd (state g hist).node n _ n).known = _
    rw [upd_same]

/-- A merge of op heads `H`, two or more, by one fresh operation, the only op head after. -/
theorem mid_merge (hE : E n) {H : Nat → Prop} (h2 : ∃ x y, H x ∧ H y ∧ x ≠ y)
    (hn : g'.next = g.next + 1) (hp : ∀ x, x < g.next → g'.par x = g.par x)
    (hnew : ∀ p ∈ g'.par g.next, p < g.next) (hhub : g'.hub = g.hub)
    (hother : ∀ m, m ≠ n → g'.node m = g.node m) (hh : ∀ y, heads g' n y ↔ y = g.next)
    (hk : known g' n = known g n) (hgen : (g'.node n).gen = (g.node n).gen) :
    HubSuffix.Step E w (withHeads (view E g hist pk) n H) (view E g' hist pk) := by
  refine .merge n hE ?_ (state_uext (hist := hist) (hist' := hist) hn hp hnew)
    (state_hub_same hhub rfl) (fun m _ hm => ?_)
    hh ?_ (gens_same hother hgen) rfl
  · show ∃ a b, (upd (state g hist).node n _ n).heads a ∧ (upd (state g hist).node n _ n).heads b ∧
      a ≠ b
    rw [upd_same]
    exact h2
  · have h := state_node_same (hist := hist) (hist' := hist) (hother m hm)
    show ((state g' hist).node m).heads = (upd (state g hist).node n _ m).heads ∧
      ((state g' hist).node m).known = (upd (state g hist).node n _ m).known
    rw [upd_ne _ _ hm]
    exact h
  · show known g' n = (upd (state g hist).node n _ n).known
    rw [upd_same]
    exact hk

/-- A merge of op heads `H`, two or more, that leaves one operation that exists already (the same
canonical merge another copy wrote, one raw vertex, or the one head jj keeps, the others its
ancestors), the only op head after; the raw graph does not grow. -/
theorem mid_mergeExisting (hE : E n) {H : Nat → Prop} (h2 : ∃ x y, H x ∧ H y ∧ x ≠ y)
    {y : Nat} (hy : y < g.next) (hn : g'.next = g.next)
    (hp : ∀ x, x < g.next → g'.par x = g.par x) (hhub : g'.hub = g.hub)
    (hother : ∀ m, m ≠ n → g'.node m = g.node m) (hh : ∀ y', heads g' n y' ↔ y' = y)
    (hk : known g' n = known g n) (hgen : (g'.node n).gen = (g.node n).gen) :
    HubSuffix.Step E w (withHeads (view E g hist pk) n H) (view E g' hist pk) := by
  refine .mergeExisting n y hE ?_ hy (state_usame (hist := hist) (hist' := hist) hn hp)
    (state_hub_same hhub rfl) (fun m _ hm => ?_) hh ?_ (gens_same hother hgen) rfl
  · show ∃ a b, (upd (state g hist).node n _ n).heads a ∧ (upd (state g hist).node n _ n).heads b ∧
      a ≠ b
    rw [upd_same]
    exact h2
  · have h := state_node_same (hist := hist) (hist' := hist) (hother m hm)
    show ((state g' hist).node m).heads = (upd (state g hist).node n _ m).heads ∧
      ((state g' hist).node m).known = (upd (state g hist).node n _ m).known
    rw [upd_ne _ _ hm]
    exact h
  · show known g' n = (upd (state g hist).node n _ n).known
    rw [upd_same]
    exact hk

end Steps

/-! ## What the node's steps do to the fields the view reads -/

/-- A push with no pending drops writes nothing: it pushes the single op head. -/
theorem push_quiet {d : Nat → Nat → Prop} {σ post : NS} {new : Nat}
    (hi : Issue d σ .push post new) (hp : σ.pending = []) :
    post = { norm σ with plan := [] } ∧ σ.heads = [new] := by
  obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hi
  obtain ⟨y, hy, (⟨hwr, -⟩ | ⟨-, he, rfl⟩)⟩ := hw'
  · exfalso
    have hp' : (norm σ).pending = [] := hp
    simp [pubOf, Retry.Publication.write, Retry.Fixup.write, hp'] at hwr
  · exact ⟨he, hy⟩

theorem idle_same {c : Ctx} {σ σ' : NS} (h : Idle c σ σ') :
    σ'.heads = σ.heads ∧ σ'.known = σ.known := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl⟩
  | differIdle _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl⟩
  | goal _ _ _ _ _ _ _ _ he => subst he; exact ⟨rfl, rfl⟩

/-- Replies leave the op heads of the step's state after its writes. -/
theorem handle_heads {c : Ctx} {d : Nat → Nat → Prop} {σ post σi posti σ' : NS} {k : Kind}
    {new : Nat} {as : List Ans} (hi : Issue d σ k post new) (hci : σi.heads = σ.heads)
    (hcp : posti.heads = post.heads) (hh : Handle c σi k posti as σ') : σ'.heads = post.heads := by
  cases k with
  | start =>
    obtain ⟨σ1, F, rfl⟩ := hh
    show σ1.heads = post.heads
    rw [F.heads, hci, hi.2]
  | fetchPoll =>
    obtain ⟨σ1, F, ho⟩ := hh
    have h1 : σ1.heads = σi.heads := F.heads
    rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
    · have h2 : σ'.heads = σ1.heads := by have h := congrArg NS.heads O.rest; exact h
      rw [h2, h1, hci, hi.2.2.2.2.2.2.2]
    · rw [h1, hci, hi.2.2.2.2.2.2.2]
  | fetchObjs =>
    have O : ObjRep (norm σi) σ'
        (fun x => Walk σi x ∧ ¬ σi.loc x ∧ σi.stg x ∧ ¬ σi.obj x) := hh
    have h2 : σ'.heads = σi.heads := by have h := congrArg NS.heads O.rest; exact h
    rw [h2, hci, hi.2.2.2.2.2.2.2.2]
  | differPoll =>
    have h2 : σ'.heads = σi.heads := hh.heads
    rw [h2, hci, hi.2.2.2.2.2.2.2]
  | push =>
    rcases hh with ⟨-, -, rfl⟩ | ⟨-, -, F⟩ | ⟨-, -, A⟩
    · exact hcp
    · rw [F.heads, hcp]
    · rw [A.heads, hcp]
  | writePoll => rw [hh.heads, hcp]

/-- Replies leave the known pair, or teach the context's, as a reply naming a head says. -/
theorem handle_known {c : Ctx} {d : Nat → Nat → Prop} {σ post σi posti σ' : NS} {k : Kind}
    {new : Nat} {as : List Ans} (hi : Issue d σ k post new) (hck : σi.known = σ.known)
    (hcp : posti.known = post.known) (hh : Handle c σi k posti as σ') :
    σ'.known = post.known ∨
      (σ'.known = (c.S, c.H) ∧ k ≠ .fetchObjs ∧ (k = .push → ∃ s, Ans.head s ∈ as)) := by
  cases k with
  | start =>
    obtain ⟨σ1, F, rfl⟩ := hh
    exact Or.inr ⟨F.known, by decide, fun h => by cases h⟩
  | fetchPoll =>
    obtain ⟨σ1, F, ho⟩ := hh
    refine Or.inr ⟨?_, by decide, fun h => by cases h⟩
    rcases ho with ⟨-, O⟩ | ⟨-, rfl⟩
    · have h : σ'.known = σ1.known := by have h := congrArg NS.known O.rest; exact h
      exact h.trans F.known
    · exact F.known
  | fetchObjs =>
    left
    have O : ObjRep (norm σi) σ'
        (fun x => Walk σi x ∧ ¬ σi.loc x ∧ σi.stg x ∧ ¬ σi.obj x) := hh
    have h : σ'.known = σi.known := by have h := congrArg NS.known O.rest; exact h
    rw [h, hck, hi.2.2.2.2.2.2.2.2]
  | differPoll => exact Or.inr ⟨hh.known, by decide, fun h => by cases h⟩
  | push =>
    rcases hh with ⟨-, -, rfl⟩ | ⟨hs, -, F⟩ | ⟨hs, -, A⟩
    · exact Or.inl hcp
    · exact Or.inr ⟨F.known, by decide, fun _ => hs⟩
    · exact Or.inr ⟨A.known, by decide, fun _ => hs⟩
  | writePoll => exact Or.inr ⟨hh.known, by decide, fun h => by cases h⟩

theorem bodies_nopush {σ : NS} {k : Kind} {p : Pkt} {rq : List Req} (hk : k ≠ .push)
    (hb : Bodies σ k p (rq.map Req.body)) : ∀ r ∈ rq, ∀ p', r.body ≠ .push p' := by
  intro r hr p' he
  have hm : Body.push p' ∈ rq.map Req.body := List.mem_map.2 ⟨r, hr, he⟩
  cases k <;> simp only [Bodies] at hb
  all_goals first
    | exact hk rfl
    | (rw [hb] at hm; simp at hm)
    | (rcases hb with ⟨_, hb⟩ | ⟨_, hb⟩ <;> rw [hb] at hm <;> simp at hm)

theorem collect_nil {tag : Pkt → Option Nat} {rq : List Req}
    (h : ∀ r ∈ rq, ∀ p, r.body ≠ .push p) : collectPackets tag rq = [] := by
  unfold collectPackets
  apply List.filterMap_eq_nil_iff.2
  intro r hr
  cases hb : r.body with
  | push p => exact absurd hb (h r hr p)
  | fetch => simp
  | objs => simp

/-! ## An eligible node's own steps refine the hub's suffix -/

/-- Each of eligible node `n`'s own steps in the joint system is a positive finite path of the
hub's suffix on the hub-side view of the same system, the ledger recording its push. Premises, all
per step and explicit: the system's invariants from a well-formed start (`RunOK`); the raw graph
acyclic (a native contract); no adoption after the record-adoption cut (the applied records stay,
which excludes `adopt` and `advanceTake`); distinct op heads at a merge (`huniq`, which the hive
derives, `heads_nodup_step`); the native full-frontier advance (`FullAdv`); housekeeping that
writes ending at its last operation (`MaintLaw`), its writes new operations in order
(`hmaintFresh`, a premise of the model, not a claim about native housekeeping: the hive takes this
only past its housekeeping cut, where no housekeeping step is left); no pending drops at a step
that sends calls (provisional, under audit); and the replies the node takes and the notification
it processes honest within the window of root's history (`HonestSnap`). No hub progress, rank or
suffix step is assumed. -/
theorem own_step_expansion {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {w n : Nat} {act : Act} {g g' : Sys} (hist : Nat → Nat) (pk : List Packet)
    (hE : E n) (hs : SysStep N D law act g g') (hab : act.about n) (K : RunOK law D n g)
    (hdag : ∀ x, x < g'.next → ∀ p ∈ g'.par x, p < x)
    (hap : act = .core n .busy → (g'.node n).ns.ap = (g.node n).ns.ap)
    (huniq : act = .core n .busy → (g.node n).ns.heads.Nodup)
    (hadv : act = .core n .busy → AdvGuard (g.node n).ns →
      FullAdv (g.node n).ns (g'.node n).ns)
    (hmaint : act = .core n .maint → MaintLaw (g.node n).ns (g'.node n).ns)
    (hmaintFresh : act = .core n .maint →
      Grow g g' (g.node n).ns (g'.node n).ns (g.node n).emb (g'.node n).emb)
    (hpend : ∀ k, act = .issue n k → (g.node n).ns.pending = [])
    (hrep : ∀ r ∈ g.reps, r ∉ g'.reps → r.node = n → ∀ s,
      (r.ans = .fetched s ∨ r.ans = .head s) → HonestSnap w hist g s)
    (hnote : ∀ nt, act = .notice n nt → HonestSnap w hist g nt.snap) :
    Nonempty (Expansion.Path (HubSuffix.Step E w) (view E g hist pk)
      (view E g' hist (nextLedger E g g' act pk))) := by
  have hother := others_same hs hab
  have I := K.node.inv
  have S := K.node.scope
  cases hs with
  | busy m σ' emb' hw ha hsl hg hnode hq ht =>
    simp only [Act.about] at hab
    subst hab
    rw [show nextLedger E g g' (.core m .busy) pk = pk by simp [nextLedger]]
    have e : g'.node m = ⟨σ', emb', (g.node m).gen, none⟩ := by rw [hnode, upd_same]
    have hσ' : (g'.node m).ns = σ' := by rw [e]
    have r0 := repo_none hw
    have r1 : (g'.node m).repo = σ' ∧ (g'.node m).repoEmb = emb' := by rw [e]; exact ⟨rfl, rfl⟩
    have hgen : (g'.node m).gen = (g.node m).gen := by rw [e]
    have h0 : ∀ y, heads g m y ↔ ∃ l ∈ (g.node m).ns.heads, (g.node m).emb l = y :=
      heads_of (congrArg NS.heads r0.1) r0.2
    have h1 : ∀ y, heads g' m y ↔ ∃ l ∈ σ'.heads, emb' l = y :=
      heads_of (congrArg NS.heads r1.1) r1.2
    have k0 : known g m = ((g.node m).ns.known.1, (g.node m).emb (g.node m).ns.known.2) :=
      known_of (congrArg NS.known r0.1) r0.2
    have k1 : known g' m = (σ'.known.1, emb' σ'.known.2) :=
      known_of (congrArg NS.known r1.1) r1.2
    have hpar : ∀ x, x < g.next → g'.par x = g.par x := hg.parRaw
    have kn : ∀ (K' : Nat × Nat), K' = (g.node m).ns.known → known g' m = known g m → True :=
      fun _ _ _ => trivial
    clear kn
    -- the known pair stays, and its label keeps its raw id
    have hkeep : σ'.known = (g.node m).ns.known → known g' m = known g m := by
      intro hk
      rw [k1, k0, hk, hg.embOld _ I.knownLt]
    -- two labelled op heads are two raw ones
    have twoHeads : 2 ≤ (g.node m).ns.heads.length → ∃ x y, heads g m x ∧ heads g m y ∧ x ≠ y := by
      intro h2
      have hnd := huniq rfl
      cases hhs : (g.node m).ns.heads with
      | nil => rw [hhs] at h2; simp at h2
      | cons l1 t =>
        cases t with
        | nil => rw [hhs] at h2; simp at h2
        | cons l2 rest =>
          rw [hhs] at hnd
          have hne : l1 ≠ l2 := fun h => (List.nodup_cons.1 hnd).1 (by rw [h]; simp)
          have hm1 : l1 ∈ (g.node m).ns.heads := by rw [hhs]; simp
          have hm2 : l2 ∈ (g.node m).ns.heads := by rw [hhs]; simp
          exact ⟨_, _, (h0 _).2 ⟨l1, hm1, rfl⟩, (h0 _).2 ⟨l2, hm2, rfl⟩,
            fun h => hne (S.inj l1 l2 (I.headsLt l1 hm1) (I.headsLt l2 hm2) h)⟩
    -- the op heads, two or more, leave one that exists already, nothing new labelled
    have toExisting : ∀ x, x < (g.node m).ns.next → σ'.next = (g.node m).ns.next →
        σ'.heads = [x] → σ'.known = (g.node m).ns.known → 2 ≤ (g.node m).ns.heads.length →
        Nonempty (Expansion.Path (HubSuffix.Step E w) (view E g hist pk)
          (view E g' hist pk)) := by
      intro x hx hnx hhx hkx h2
      have hh : ∀ y, heads g' m y ↔ y = (g.node m).emb x := by
        intro y
        rw [h1, hhx]
        simp only [List.mem_singleton, exists_eq_left, hg.embOld x hx]
        exact eq_comm
      rw [← withHeads_self (view E g hist pk) m]
      exact ⟨single (mid_mergeExisting (E := E) (w := w) (hist := hist) (pk := pk)
        (H := heads g m) hE (twoHeads h2) (S.lt x hx) (hg.same_next hnx) hpar hq.hub hother hh
        (hkeep hkx) hgen)⟩
    cases hsl with
    | adopt A ha' hne hb ht' =>
      exfalso
      have h := hap rfl
      rw [hσ'] at h
      exact hne (ht'.ap.symm.trans h)
    | advanceTake A hg' h1' hl' ha' ht' =>
      exfalso
      have h := hap rfl
      rw [hσ'] at h
      exact (normA_some ha').2 (ht'.ap.symm.trans h)
    | merge M hg' h2 hM he =>
      subst he
      have hpn : (fresh (norm (g.node m).ns) M).par (g.node m).ns.next = M := by
        simp [fresh, norm, upd]
      -- the merge's raw parents are the images of op heads, old raw ids
      have hmp : ∀ p ∈ g'.par (emb' (g.node m).ns.next), p < g.next := by
        intro p hp
        rw [hg.parNew _ (Nat.le_refl _) (by simp [fresh, norm]), hpn, List.mem_map] at hp
        obtain ⟨l, hl, rfl⟩ := hp
        have hl' := I.headsLt l (hM.sub l hl)
        rw [hg.embOld l hl']
        exact S.lt l hl'
      have hd2 := twoHeads h2
      have hh : ∀ y, heads g' m y ↔ y = emb' (g.node m).ns.next := by
        intro y
        rw [h1]
        simp only [fresh, norm, List.mem_singleton, exists_eq_left]
        exact eq_comm
      rw [← withHeads_self (view E g hist pk) m]
      rcases hg.one (by simp [fresh, norm]) with ⟨hemb, hnx'⟩ | ⟨hlt, hnx'⟩
      · -- a fresh operation
        have hnew : ∀ p ∈ g'.par g.next, p < g.next := by
          intro p hp
          rw [← hemb] at hp
          exact hmp p hp
        exact ⟨single (mid_merge (E := E) (w := w) (hist := hist) (pk := pk) (H := heads g m) hE
          hd2 hnx' hpar hnew hq.hub hother (by rw [← hemb]; exact hh) (hkeep rfl) hgen)⟩
      · -- the same canonical merge another copy wrote: one raw vertex, nothing grows
        exact ⟨single (mid_mergeExisting (E := E) (w := w) (hist := hist) (pk := pk)
          (H := heads g m) hE hd2 hlt hnx' hpar hq.hub hother hh (hkeep rfl) hgen)⟩
    | mergeExisting M x hg' h2 hM hx hpx he =>
      subst he
      exact toExisting x hx (by simp [mergeTo, norm]) rfl rfl h2
    | prune x hg' h2 hM he =>
      subst he
      exact toExisting x (I.headsLt x (hM.sub x (List.mem_singleton.2 rfl)))
        (by simp [pruneTo, norm]) rfl rfl h2
    | realizePlan x rest hg' h1' hl' hp' he =>
      subst he
      have hn : g'.next = g.next := hg.same_next (by simp [realize, norm])
      exact ⟨single (view_frame hn hpar hq.hub hother
        (heads_eq h0 h1 (fun l hl => hg.embOld l (I.headsLt l hl))) (hkeep rfl) hgen)⟩
    | realizeSurvey x L hg' h1' hl' hp' hr he =>
      subst he
      have hn : g'.next = g.next := hg.same_next (by simp [realize, norm])
      exact ⟨single (view_frame hn hpar hq.hub hother
        (heads_eq h0 h1 (fun l hl => hg.embOld l (I.headsLt l hl))) (hkeep rfl) hgen)⟩
    | advance hg' h1' hl' hd ha' hv =>
      have FA : FullAdv (g.node m).ns σ' := by
        have h := hadv rfl ⟨h1', hl', hd, ha'⟩
        rw [hσ'] at h
        exact h
      have hk : known g' m = known g m := hkeep hv.ext.known
      have hna : ¬ ∃ h, heads g m h ∧ Anc (parents g) (known g m).2 h := by
        rintro ⟨h, hh, hanc⟩
        obtain ⟨l, hl, rfl⟩ := (h0 h).1 hh
        rw [k0] at hanc
        have ha := anc_down S I.parLt hanc l (I.headsLt l hl) rfl _ I.knownLt rfl
        apply hd
        refine ⟨l, hl, fun i hi => ?_⟩
        rw [FA.img, List.mem_singleton] at hi
        rw [hi]
        exact ha
      have hF : ∀ y, rawFrontier g m y ↔
          ∃ l, l < (g.node m).ns.next ∧ (g.node m).emb l = y ∧ Frontier (g.node m).ns l := by
        intro y
        unfold rawFrontier
        rw [k0]
        exact raw_frontier S I h0 y
      have hFlt : ∀ l, Frontier (g.node m).ns l → l < (g.node m).ns.next := by
        rintro l ⟨hl | rfl, -⟩
        · exact I.headsLt l hl
        · exact I.knownLt
      rcases FA.out with ⟨hnx0, hhd, -⟩ | ⟨⟨a, b, hFa, hFb, hab⟩, hnx1, hpar1, hhd⟩ |
          ⟨⟨a, b, hFa, hFb, hab⟩, hnx0, x, hx, -, hhd⟩
      · have hn : g'.next = g.next := hg.same_next hnx0
        have hh : heads g' m = rawFrontier g m := by
          funext y
          apply propext
          rw [h1, hF]
          constructor
          · rintro ⟨l, hl, rfl⟩
            have hFl := (hhd l).1 hl
            exact ⟨l, hFlt l hFl, (hg.embOld l (hFlt l hFl)).symm, hFl⟩
          · rintro ⟨l, hl, rfl, hFl⟩
            exact ⟨l, (hhd l).2 hFl, hg.embOld l hl⟩
        exact ⟨single (view_advance hE hna hn hpar hq.hub hother hh hk hgen)⟩
      · have hd2 : ∃ x y, rawFrontier g m x ∧ rawFrontier g m y ∧ x ≠ y :=
          ⟨_, _, (hF _).2 ⟨a, hFlt a hFa, rfl, hFa⟩, (hF _).2 ⟨b, hFlt b hFb, rfl, hFb⟩,
            fun h => hab (S.inj a b (hFlt a hFa) (hFlt b hFb) h)⟩
        have hh : ∀ y, heads g' m y ↔ y = emb' (g.node m).ns.next := by
          intro y
          rw [h1, hhd]
          simp only [List.mem_singleton, exists_eq_left]
          exact eq_comm
        -- the merge's raw parents are the frontier's images, old raw ids
        have hmp : ∀ p ∈ g'.par (emb' (g.node m).ns.next), p < g.next := by
          intro p hp
          rw [hg.parNew _ (Nat.le_refl _) (by rw [hnx1]; omega), List.mem_map] at hp
          obtain ⟨l, hl, rfl⟩ := hp
          have hl' := hFlt l ((hpar1 l).1 hl)
          rw [hg.embOld l hl']
          exact S.lt l hl'
        rcases hg.one hnx1 with ⟨hemb, hnx'⟩ | ⟨hlt, hnx'⟩
        · -- a fresh operation
          have hnew : ∀ p ∈ g'.par g.next, p < g.next := by
            intro p hp
            rw [← hemb] at hp
            exact hmp p hp
          exact ⟨two (view_advance_mid hE hna)
            (mid_merge hE hd2 hnx' hpar hnew hq.hub hother (by rw [← hemb]; exact hh) hk hgen)⟩
        · -- the same canonical merge another copy wrote: one raw vertex, nothing grows
          exact ⟨two (view_advance_mid hE hna)
            (mid_mergeExisting hE hd2 hlt hnx' hpar hq.hub hother hh hk hgen)⟩
      · -- the merge is an operation the node holds already: no new label, nothing grows
        have hd2 : ∃ x y, rawFrontier g m x ∧ rawFrontier g m y ∧ x ≠ y :=
          ⟨_, _, (hF _).2 ⟨a, hFlt a hFa, rfl, hFa⟩, (hF _).2 ⟨b, hFlt b hFb, rfl, hFb⟩,
            fun h => hab (S.inj a b (hFlt a hFa) (hFlt b hFb) h)⟩
        have hh : ∀ y, heads g' m y ↔ y = (g.node m).emb x := by
          intro y
          rw [h1, hhd]
          simp only [List.mem_singleton, exists_eq_left, hg.embOld x hx]
          exact eq_comm
        exact ⟨two (view_advance_mid hE hna)
          (mid_mergeExisting hE hd2 (S.lt x hx) (hg.same_next hnx0) hpar hq.hub hother hh hk
            hgen)⟩
  | idle m σ' hw ha hsl hnode hr hq ht =>
    simp only [Act.about] at hab
    subst hab
    rw [show nextLedger E g g' (.core m .idle) pk = pk by simp [nextLedger]]
    have e : g'.node m = ⟨σ', (g.node m).emb, (g.node m).gen, none⟩ := by rw [hnode, upd_same]
    have r0 := repo_none hw
    have r1 : (g'.node m).repo = σ' ∧ (g'.node m).repoEmb = (g.node m).emb := by
      rw [e]; exact ⟨rfl, rfl⟩
    obtain ⟨hhs, hks⟩ := idle_same hsl
    have h0 : ∀ y, heads g m y ↔ ∃ l ∈ (g.node m).ns.heads, (g.node m).emb l = y :=
      heads_of (congrArg NS.heads r0.1) r0.2
    have h1 : ∀ y, heads g' m y ↔ ∃ l ∈ (g.node m).ns.heads, (g.node m).emb l = y := by
      intro y
      rw [heads_of (congrArg NS.heads r1.1) r1.2, hhs]
    have hk : known g' m = known g m := by
      rw [known_of (congrArg NS.known r1.1) r1.2, known_of (congrArg NS.known r0.1) r0.2, hks]
    exact ⟨single (view_frame hr.1 (fun x _ => by rw [hr.2]) hq.hub hother
      (heads_eq h0 h1 (fun _ _ => rfl)) hk (by rw [e]))⟩
  | maint m σ1 σ' emb' hw ha hsl hx hg hnode hq ht =>
    simp only [Act.about] at hab
    subst hab
    rw [show nextLedger E g g' (.core m .maint) pk = pk by simp [nextLedger]]
    have e : g'.node m =
        ⟨σ', emb', (g.node m).gen + (σ'.next - (g.node m).ns.next), none⟩ := by
      rw [hnode, upd_same]
    have ML : MaintLaw (g.node m).ns σ' := by
      have h := hmaint rfl
      rw [e] at h
      exact h
    have r0 := repo_none hw
    have r1 : (g'.node m).repo = σ' ∧ (g'.node m).repoEmb = emb' := by rw [e]; exact ⟨rfl, rfl⟩
    -- the housekeeping step's writes, new and in order, are the premise `hmaintFresh`
    have G : Grow g g' (g.node m).ns σ' (g.node m).emb emb' := by
      have h := hmaintFresh rfl
      rw [e] at h
      exact h
    have hnx := G.rawNext
    have hw0 := ML.wrote
    have hpar : ∀ x, x < g.next → g'.par x = g.par x := hg.parRaw
    have hk : known g' m = known g m := by
      rw [known_of (congrArg NS.known r1.1) r1.2, known_of (congrArg NS.known r0.1) r0.2]
      have h1 : σ'.known = σ1.known := by have h := hx.known; exact h
      rw [h1, (idle_same hsl).2, hg.embOld _ I.knownLt]
    refine ⟨Classical.choice (raw_maintenance_expansion (E := E) (w := w)
      (a := view E g hist pk) (b := view E g' hist pk) (n := m) hE ?_ ?_ ?_ ?_ ?_
      (state_hub_same hq.hub rfl) (fun m' _ hm => state_node_same (hother m' hm)) ?_ hk ?_ ?_ rfl)⟩
    · show g.next < g'.next
      omega
    · intro x hx'
      change x < g.next at hx'
      change parents g' x = parents g x
      simp only [parents, hx', show x < g'.next by omega, ↓reduceIte]
      exact hpar x hx'
    · intro x hx'
      change g.next ≤ x at hx'
      change parents g x = []
      simp [parents, show ¬ x < g.next by omega]
    · intro x hx'
      change g'.next ≤ x at hx'
      change parents g' x = []
      simp [parents, show ¬ x < g'.next by omega]
    · intro x hx' p hp
      change x < g'.next at hx'
      change p ∈ parents g' x at hp
      simp only [parents, hx', ↓reduceIte] at hp
      exact hdag x hx' p hp
    · show heads g' m = (· = g'.next - 1)
      funext y
      apply propext
      rw [heads_of (congrArg NS.heads r1.1) r1.2, ML.last]
      simp only [List.mem_singleton, exists_eq_left]
      rw [G.embNew _ (by omega) (by omega)]
      constructor <;> intro h <;> omega
    · show generations E g' m = generations E g m + (g'.next - g.next)
      simp only [generations, hE, ↓reduceIte, e]
      omega
    · intro m' hm
      show generations E g' m' = generations E g m'
      simp [generations, hother m' hm]
  | issue m k post new emb1 rq hw hissue hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
    simp only [Act.about] at hab
    subst hab
    have hl : nextLedger E g g' (.issue m k) pk =
        collectPackets (fun p => some p.gen) rq ++ pk := by
      simp [nextLedger, hE, hreqs]
    rw [hl]
    have e : g'.node m = ⟨(g.node m).ns, (g.node m).emb,
        (g.node m).gen + (post.next - (g.node m).ns.next),
        some ⟨k, rq.map Req.slot, post, new, emb1⟩⟩ := by rw [hnode, upd_same]
    have r0 := repo_none hw
    have r1 : (g'.node m).repo = post ∧ (g'.node m).repoEmb = emb1 := by
      rw [e]; exact ⟨rfl, rfl⟩
    have h0 : ∀ y, heads g m y ↔ ∃ l ∈ (g.node m).ns.heads, (g.node m).emb l = y :=
      heads_of (congrArg NS.heads r0.1) r0.2
    have k0 : known g m = ((g.node m).ns.known.1, (g.node m).emb (g.node m).ns.known.2) :=
      known_of (congrArg NS.known r0.1) r0.2
    have k1 : known g' m = (post.known.1, emb1 post.known.2) :=
      known_of (congrArg NS.known r1.1) r1.2
    have hpar : ∀ x, x < g.next → g'.par x = g.par x := hg.parRaw
    -- a step that writes nothing: the view's node is as it was
    have quiet : post.heads = (g.node m).ns.heads → post.known = (g.node m).ns.known →
        post.next = (g.node m).ns.next →
        g'.next = g.next ∧ (g'.node m).gen = (g.node m).gen ∧ heads g' m = heads g m ∧
          known g' m = known g m := by
      intro hh hk hn
      refine ⟨hg.same_next hn, by rw [e, hn]; simp, ?_, ?_⟩
      · refine heads_eq h0 (fun y => ?_) (fun l hl => hg.embOld l (I.headsLt l hl))
        rw [heads_of (congrArg NS.heads r1.1) r1.2, hh]
      · rw [k1, k0, hk, hg.embOld _ I.knownLt]
    cases k with
    | push =>
      obtain ⟨hpost, hhd⟩ := push_quiet hissue (hpend _ rfl)
      obtain ⟨hn, hgen, hh, hk⟩ := quiet (by rw [hpost]; rfl) (by rw [hpost]; rfl)
        (by rw [hpost]; rfl)
      have hnew : new < (g.node m).ns.next := I.headsLt new (by rw [hhd]; simp)
      have hd : ∀ y, heads g m y ↔ y = (g.node m).emb new := by
        intro y
        rw [h0, hhd]
        simp only [List.mem_singleton, exists_eq_left]
        exact eq_comm
      obtain ⟨q, hrq, hqb⟩ : ∃ q, rq = [q] ∧ q.body = .push
          (pkt m ((g.node m).gen + (post.next - (g.node m).ns.next)) post emb1 new) := by
        simp only [Bodies] at hb
        cases rq with
        | nil => simp at hb
        | cons q t =>
          cases t with
          | nil => exact ⟨q, rfl, by simpa using hb⟩
          | cons q2 t2 => simp at hb
      have hpk : collectPackets (fun p => some p.gen) rq ++ pk =
          sent (view E g hist pk) m ((g.node m).emb new) :: pk := by
        rw [hrq]
        simp only [collectPackets, List.filterMap_cons, hqb, List.filterMap_nil,
          List.singleton_append]
        congr 1
        have hg0 : post.next - (g.node m).ns.next = 0 := by rw [hpost]; simp [norm]
        simp only [packet, pkt, sent, view, generations, hE, ↓reduceIte, hg0, Nat.add_zero]
        show (⟨m, some (g.node m).gen, post.known.1, emb1 post.known.2, emb1 new⟩ : Packet) =
          ⟨m, some (g.node m).gen, (known g m).1, (known g m).2, (g.node m).emb new⟩
        rw [k0, hpost]
        simp only [norm]
        rw [hg.embOld _ I.knownLt, hg.embOld _ hnew]
      exact ⟨single (view_send hE _ hd hn hpar hrest.1 hother hh hk hgen hpk)⟩
    | writePoll =>
      obtain ⟨_, _, _, _, _, _, _, hp, _⟩ := hissue
      exact absurd (hpend _ rfl) hp
    | start =>
      have hpost := post_same hissue (by decide) (by decide)
      subst hpost
      obtain ⟨hn, hgen, hh, hk⟩ := quiet rfl rfl rfl
      rw [collect_nil (bodies_nopush (by decide) hb), List.nil_append]
      exact ⟨single (view_frame hn hpar hrest.1 hother hh hk hgen)⟩
    | fetchPoll =>
      have hpost := post_same hissue (by decide) (by decide)
      subst hpost
      obtain ⟨hn, hgen, hh, hk⟩ := quiet rfl rfl rfl
      rw [collect_nil (bodies_nopush (by decide) hb), List.nil_append]
      exact ⟨single (view_frame hn hpar hrest.1 hother hh hk hgen)⟩
    | fetchObjs =>
      have hpost := post_same hissue (by decide) (by decide)
      subst hpost
      obtain ⟨hn, hgen, hh, hk⟩ := quiet rfl rfl rfl
      rw [collect_nil (bodies_nopush (by decide) hb), List.nil_append]
      exact ⟨single (view_frame hn hpar hrest.1 hother hh hk hgen)⟩
    | differPoll =>
      have hpost := post_same hissue (by decide) (by decide)
      subst hpost
      obtain ⟨hn, hgen, hh, hk⟩ := quiet rfl rfl rfl
      rw [collect_nil (bodies_nopush (by decide) hb), List.nil_append]
      exact ⟨single (view_frame hn hpar hrest.1 hother hh hk hgen)⟩
  | answer => simp only [Act.about] at hab
  | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hrest ht =>
    simp only [Act.about] at hab
    subst hab
    rw [show nextLedger E g g' (.handle m) pk = pk by simp [nextLedger]]
    have W := K.node.wait w hw
    have e : g'.node m = ⟨σ', embi, (g.node m).gen, none⟩ := by rw [hnode, upd_same]
    have r0 := repo_some hw
    have r1 : (g'.node m).repo = σ' ∧ (g'.node m).repoEmb = embi := by rw [e]; exact ⟨rfl, rfl⟩
    have hgen : (g'.node m).gen = (g.node m).gen := by rw [e]
    have hpostL : LInv w.post := linv_of_sinv (post_inv W.issue (I.sinv 0 (D m)))
    have hci : σi.heads = (g.node m).ns.heads := by
      have h := congrArg NS.heads hl.ctl.1; exact h
    have hcp : posti.heads = w.post.heads := by have h := congrArg NS.heads hl.ctl.2; exact h
    have hck : σi.known = (g.node m).ns.known := by
      have h := congrArg NS.known hl.ctl.1; exact h
    have hcpk : posti.known = w.post.known := by have h := congrArg NS.known hl.ctl.2; exact h
    have h0 : ∀ y, heads g m y ↔ ∃ l ∈ w.post.heads, w.emb l = y :=
      heads_of (congrArg NS.heads r0.1) r0.2
    have hσh := handle_heads W.issue hci hcp hh
    have hheads : heads g' m = heads g m := by
      refine heads_eq h0 (fun y => ?_) (fun l hl' => hl.embOld l (hpostL.headsLt l hl'))
      rw [heads_of (congrArg NS.heads r1.1) r1.2, hσh]
    have hn : g'.next = g.next := hrest.2.2.2.2.1
    have hpar : ∀ x, x < g.next → g'.par x = g.par x := fun x _ => by rw [hrest.2.2.2.2.2]
    have k0 : known g m = (w.post.known.1, w.emb w.post.known.2) :=
      known_of (congrArg NS.known r0.1) r0.2
    have k1 : known g' m = (σ'.known.1, embi σ'.known.2) :=
      known_of (congrArg NS.known r1.1) r1.2
    rcases handle_known W.issue hck hcpk hh with hkn | ⟨hkn, hk1, hk2⟩
    · have hk : known g' m = known g m := by
        rw [k1, k0, hkn, hl.embOld _ hpostL.knownLt]
      exact ⟨single (view_frame hn hpar hrest.1 hother hheads hk hgen)⟩
    · -- a reply naming a head
      obtain ⟨r, hr, s, hs⟩ : ∃ r ∈ rs, ∃ s, r.ans = .fetched s ∨ r.ans = .head s := by
        by_cases hp : w.kind = .push
        · obtain ⟨s, hs⟩ := hk2 hp
          obtain ⟨r, hr, hra⟩ := List.mem_map.1 hs
          exact ⟨r, hr, s, Or.inr hra⟩
        · obtain ⟨s0, rest, hs0⟩ := List.exists_cons_of_ne_nil W.slots
          obtain ⟨r0', hr0, hr0s⟩ := hcov s0 (by rw [hs0]; exact List.mem_cons_self)
          have hbf := W.reps r0' (hrs r0' hr0).1 (hrs r0' hr0).2.1 (hrs r0' hr0).2.2
          have hreq : r0'.req = .fetch := hbf.2 (by rw [hs0, hr0s]; rfl) hp hk1
          obtain ⟨s, hs⟩ := K.sys.fetch r0' (hrs r0' hr0).1 hreq
          exact ⟨r0', hr0, s, Or.inl hs⟩
      have hfit : c.S = s.seq ∧ embi c.H = s.head := by
        have h := hf r hr
        rcases hs with hs | hs <;> rw [hs] at h <;> exact ⟨h.1, h.2.2.1⟩
      have hon := hrep r (hrs r hr).1 (fun h => ((hreps r).1 h).2 hr) (hrs r hr).2.1 s hs
      have hk : known g' m = (s.seq, s.head) := by rw [k1, hkn]; simp only; rw [hfit.1, hfit.2]
      exact ⟨single (view_learn hE s hon hn hpar hrest.1 hother hheads hk hgen)⟩
  | notice m nt c σi posti σ' embi hw ha hn' hnn hnew hl hc hf hh hnode hnotes hrest ht =>
    simp only [Act.about] at hab
    subst hab
    rw [show nextLedger E g g' (.notice m nt) pk = pk by simp [nextLedger]]
    have e : g'.node m = ⟨σ', embi, (g.node m).gen, none⟩ := by rw [hnode, upd_same]
    have r0 := repo_none hw
    have r1 : (g'.node m).repo = σ' ∧ (g'.node m).repoEmb = embi := by rw [e]; exact ⟨rfl, rfl⟩
    have hgen : (g'.node m).gen = (g.node m).gen := by rw [e]
    have hci : σi.heads = (g.node m).ns.heads := by
      have h := congrArg NS.heads hl.ctl.1; exact h
    have h0 : ∀ y, heads g m y ↔ ∃ l ∈ (g.node m).ns.heads, (g.node m).emb l = y :=
      heads_of (congrArg NS.heads r0.1) r0.2
    have hheads : heads g' m = heads g m := by
      refine heads_eq h0 (fun y => ?_) (fun l hl' => hl.embOld l (I.headsLt l hl'))
      rw [heads_of (congrArg NS.heads r1.1) r1.2, hh.heads, hci]
    have hk : known g' m = (nt.snap.seq, nt.snap.head) := by
      rw [known_of (congrArg NS.known r1.1) r1.2, hh.known]
      simp only
      rw [hf.1, hf.2.2.1]
    exact ⟨single (view_learn hE nt.snap (hnote nt rfl) hrest.2.2.2.2.1
      (fun x _ => by rw [hrest.2.2.2.2.2]) hrest.1 hother hheads hk hgen)⟩
  | ignore m nt hw ha hn' hnn hold hnode hnotes hrest ht =>
    simp only [Act.about] at hab
    subst hab
    rw [show nextLedger E g g' (.ignore m) pk = pk by simp [nextLedger]]
    have hh : heads g' m = heads g m := by unfold heads; rw [hnode]
    have hk : known g' m = known g m := by unfold known; rw [hnode]
    exact ⟨single (view_frame hrest.2.2.2.2.1 (fun x _ => by rw [hrest.2.2.2.2.2]) hrest.1 hother
      hh hk (by rw [hnode]))⟩
  | env => simp only [Act.about] at hab

/-! ## Distinct op heads

A node's canonical op heads can repeat: an interrupted export leaves two physical op heads with
one canonical form (an alias), and the core's merge of `[m, m]` writes a child of `m` alone
(`Busy.merge` with `M = [m]`). The suffix needs distinct heads at a merge, to read it as the
hub-side merge of two raw heads, so they are derived, not assumed of each step: distinct once,
and then kept by every step, each leaving the op heads as they were or one, but for the native
advance that writes nothing (`FullAdv`), whose op heads are the frontier's. -/

/-- Node `n`'s op heads are distinct, and so are those of the step whose calls are out. -/
def HeadsNodup (g : Sys) (n : Nat) : Prop :=
  (g.node n).ns.heads.Nodup ∧ ∀ w, (g.node n).wait = some w → w.post.heads.Nodup

theorem nodup_single (x : Nat) : [x].Nodup := List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩

/-- A step that sends calls leaves the op heads as they were, or its write the only one. -/
theorem issue_post_heads {d : Nat → Nat → Prop} {σ post : NS} {k : Kind} {new : Nat}
    (hi : Issue d σ k post new) : post.heads = σ.heads ∨ post.heads = [new] := by
  have write : WriteRes { norm σ with plan := [] } post new →
      post.heads = σ.heads ∨ post.heads = [new] := by
    intro W
    obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
    · exact Or.inr F.heads
    · subst he; exact Or.inl rfl
  cases k with
  | push => obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hi; exact write hw'
  | writePoll => obtain ⟨_, _, _, _, _, _, _, _, hw', _⟩ := hi; exact write hw'
  | start => exact Or.inl (by rw [post_same hi (by decide) (by decide)])
  | fetchPoll => exact Or.inl (by rw [post_same hi (by decide) (by decide)])
  | fetchObjs => exact Or.inl (by rw [post_same hi (by decide) (by decide)])
  | differPoll => exact Or.inl (by rw [post_same hi (by decide) (by decide)])

/-- Every step keeps a node's op heads distinct, from the laws `own_step_expansion` takes of its
own steps: no adoption, the native advance, and housekeeping ending at one head. -/
theorem heads_nodup_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {act : Act}
    {g g' : Sys} {n : Nat} (hs : SysStep N D law act g g') (K : RunOK law D n g)
    (hap : act = .core n .busy → (g'.node n).ns.ap = (g.node n).ns.ap)
    (hadv : act = .core n .busy → AdvGuard (g.node n).ns →
      FullAdv (g.node n).ns (g'.node n).ns)
    (hmaint : act = .core n .maint → MaintLaw (g.node n).ns (g'.node n).ns)
    (h : HeadsNodup g n) : HeadsNodup g' n := by
  by_cases hab : act.about n
  case neg =>
    unfold HeadsNodup
    rw [node_unchanged hs hab]
    exact h
  have setNode : ∀ c : NodeC, g'.node = upd g.node n c → g'.node n = c := by
    intro c hc
    rw [hc, upd_same]
  cases hs with
  | busy m σ' emb' hw ha hsl hg hnode hq ht =>
    simp only [Act.about] at hab
    subst hab
    have e := setNode _ hnode
    have hσ' : (g'.node m).ns = σ' := by rw [e]
    have done : σ'.heads.Nodup → HeadsNodup g' m := by
      intro hnd
      refine ⟨by rw [hσ']; exact hnd, fun w hw => ?_⟩
      rw [e] at hw
      cases hw
    apply done
    cases hsl with
    | adopt A ha' hne hb ht' =>
      exfalso
      have h' := hap rfl
      rw [hσ'] at h'
      exact hne (ht'.ap.symm.trans h')
    | advanceTake A hg' h1' hl' ha' ht' =>
      exfalso
      have h' := hap rfl
      rw [hσ'] at h'
      exact (normA_some ha').2 (ht'.ap.symm.trans h')
    | merge M _ _ _ he => subst he; exact nodup_single _
    | mergeExisting M x _ _ _ _ _ he => subst he; exact nodup_single _
    | prune x _ _ _ he => subst he; exact nodup_single _
    | realizePlan x rest _ _ _ _ he => subst he; exact h.1
    | realizeSurvey x L _ _ _ _ _ he => subst he; exact h.1
    | advance hg' h1' hl' hd ha' hv =>
      have FA : FullAdv (g.node m).ns σ' := by
        have h' := hadv rfl ⟨h1', hl', hd, ha'⟩
        rw [hσ'] at h'
        exact h'
      rcases FA.out with ⟨-, -, hnd⟩ | ⟨-, -, -, hhd⟩ | ⟨-, -, x, -, -, hhd⟩
      · exact hnd
      · rw [hhd]; exact nodup_single _
      · rw [hhd]; exact nodup_single _
  | idle m σ' hw ha hsl hnode hr hq ht =>
    simp only [Act.about] at hab
    subst hab
    have e := setNode _ hnode
    refine ⟨by rw [e]; show σ'.heads.Nodup; rw [(idle_same hsl).1]; exact h.1, fun w hw => ?_⟩
    rw [e] at hw
    cases hw
  | maint m σ1 σ' emb' hw ha hsl hx hg hnode hq ht =>
    simp only [Act.about] at hab
    subst hab
    have e := setNode _ hnode
    have ML : MaintLaw (g.node m).ns σ' := by
      have h' := hmaint rfl
      rw [e] at h'
      exact h'
    refine ⟨by rw [e]; show σ'.heads.Nodup; rw [ML.last]; exact nodup_single _,
      fun w hw => ?_⟩
    rw [e] at hw
    cases hw
  | issue m k post new emb1 rq hw hissue hg hb hslot hnodup hnode hreqs hslot' hrest ht hnd =>
    simp only [Act.about] at hab
    subst hab
    have e := setNode _ hnode
    refine ⟨by rw [e]; exact h.1, fun w hw' => ?_⟩
    rw [e] at hw'
    simp only [Option.some.injEq] at hw'
    subst hw'
    rcases issue_post_heads hissue with hh | hh
    · show post.heads.Nodup
      rw [hh]; exact h.1
    · show post.heads.Nodup
      rw [hh]; exact nodup_single _
  | handle m w rs hd c σi posti σ' embi hw hrs hcov hhd hhd' hl hc hf hh hnode hreps hrest ht =>
    simp only [Act.about] at hab
    subst hab
    have e := setNode _ hnode
    have W := K.node.wait w hw
    have hci : σi.heads = (g.node m).ns.heads := by
      have h' := congrArg NS.heads hl.ctl.1; exact h'
    have hcp : posti.heads = w.post.heads := by have h' := congrArg NS.heads hl.ctl.2; exact h'
    refine ⟨by
      rw [e]; show σ'.heads.Nodup; rw [handle_heads W.issue hci hcp hh]; exact h.2 w hw,
      fun w' hw' => ?_⟩
    rw [e] at hw'
    cases hw'
  | notice m nt c σi posti σ' embi hw ha hn' hnn hnew hl hc hf hh hnode hnotes hrest ht =>
    simp only [Act.about] at hab
    subst hab
    have e := setNode _ hnode
    have hci : σi.heads = (g.node m).ns.heads := by
      have h' := congrArg NS.heads hl.ctl.1; exact h'
    refine ⟨by rw [e]; show σ'.heads.Nodup; rw [hh.heads, hci]; exact h.1, fun w' hw' => ?_⟩
    rw [e] at hw'
    cases hw'
  | ignore m nt hw ha hn' hnn hold hnode hnotes hrest ht =>
    unfold HeadsNodup
    rw [hnode]
    exact h
  | answer => simp only [Act.about] at hab
  | env => simp only [Act.about] at hab

end Musubi.Recovery.HubNodeSteps

/-
The hub-side view of the joint system `Sys`, as a `Musubi.State` that `HubSuffix` reasons about.

- Each node's `heads` and `known` are read from its `NodeC` record, the one the joint system
  steps, using the repository heads as written, including while calls are outstanding.
- The hub's control knowledge is the batch's logical snapshot until its replies are handled.
  Mid-batch it can differ from the repository's physical knowledge; the call-batch
  correspondence must justify that delayed bookkeeping.
- Parent lists of ids at or above `next` (outside the created raw universe) read as empty, so
  changes to those unused function values are not graph changes.
- Store and object fields that `HubSuffix` does not observe stay abstract here. Packet closure
  is checked in `PacketAcceptance`.

The convergence proof uses this file.
-/
import Musubi.NodeSys
import Musubi.Expansion
import Musubi.HistoryWindow
import Musubi.EntryAssembly
import Musubi.RawExpansion
import Musubi.RawMaintenance

namespace Musubi.Recovery.HubSys

open Musubi NodeSys NodeSettle HubSuffix

/-- Parents of raw id `x`; empty for `x` outside the created universe. -/
def parents (g : Sys) (x : Nat) : List Nat := if x < g.next then g.par x else []

/-- `x` is the raw image of one of node `n`'s repository heads. -/
def heads (g : Sys) (n x : Nat) : Prop :=
  ∃ y ∈ (g.node n).repo.heads, (g.node n).repoEmb y = x

/-- Node `n`'s known hub position: its repository's sequence number and the raw image of its
known head. -/
def known (g : Sys) (n : Nat) : Known :=
  ⟨(g.node n).repo.known.seq, (g.node n).repoEmb (g.node n).repo.known.head⟩

/-- The `Musubi.State` of `g`: raw universe, hub head, sequence and history `hist`, and each
node's `heads` and `known`. -/
def state (g : Sys) (hist : Nat → Nat) : Musubi.State :=
  { init with
    U := { init.U with next := g.next, par := parents g }
    hub := { init.hub with head := g.hub.head, seq := g.hub.seq, hist := hist }
    node := fun n => { initNode with heads := heads g n, known := known g n } }

/-- The generation of each node satisfying `E`; zero for the others. -/
noncomputable def generations (E : Nat → Prop) (g : Sys) : Nat → Nat := by
  classical
  exact fun n => if E n then (g.node n).gen else 0

/-- The `GState` of `g` over eligible nodes `E`, history `hist` and packets `pk`. -/
noncomputable def view (E : Nat → Prop) (g : Sys) (hist : Nat → Nat)
    (pk : List Packet) : GState :=
  ⟨state g hist, generations E g, pk⟩

/-- The `Packet` with the fields of `p` and the given tag. -/
def packet (p : Pkt) (tag : Option Nat) : Packet :=
  ⟨p.node, tag, p.knownSeq, p.expected, p.new⟩

/-- Equal `next` and equal parents below it give equal `parents`. -/
theorem parents_same {g g' : Sys} (hn : g'.next = g.next)
    (hp : ∀ x, x < g.next → g'.par x = g.par x) : parents g' = parents g := by
  funext x
  unfold parents
  rw [hn]
  split
  · exact hp x ‹x < g.next›
  · rfl

/-- Steps that keep `next` and the parents below it keep the raw universe of `state`. -/
theorem state_usame {g g' : Sys} {hist hist' : Nat → Nat}
    (hn : g'.next = g.next) (hp : ∀ x, x < g.next → g'.par x = g.par x) :
    USame (state g hist) (state g' hist') :=
  ⟨parents_same hn hp, hn⟩

/-- An unchanged hub and history leave the hub part of `state` unchanged. -/
theorem state_hub_same {g g' : Sys} {hist hist' : Nat → Nat}
    (hh : g'.hub = g.hub) (hi : hist' = hist) :
    HubSame (state g hist) (state g' hist') := by
  exact ⟨congrArg Snap.head hh, congrArg Snap.seq hh, hi⟩

/-- An unchanged node record leaves that node's part of `state` unchanged. -/
theorem state_node_same {g g' : Sys} {hist hist' : Nat → Nat} {n : Nat}
    (hn : g'.node n = g.node n) : NodeSame (state g hist) (state g' hist') n := by
  constructor
  · change heads g' n = heads g n
    funext x
    unfold heads
    rw [hn]
  · change known g' n = known g n
    unfold known
    rw [hn]

/-- When node `n`'s pending list is empty, its hub-side `heads` and `known` equal its control
fields `ns.heads` and `ns.known`, translated by `emb`, even while a request is outstanding.
The pending premise is needed because a waiting state can already hold a fix-up. -/
theorem state_repo_agrees {D : Nat → Nat → Nat → Prop} {g : Sys} {n : Nat}
    (hi : NodeSys.NodeOK D n g) (hp : (g.node n).ns.pending = []) :
    (∀ x, heads g n x ↔ ∃ y ∈ (g.node n).ns.heads, (g.node n).emb y = x) ∧
      known g n = ⟨(g.node n).ns.known.seq, (g.node n).emb (g.node n).ns.known.head⟩ := by
  obtain ⟨hh, hk, he⟩ := repo_agrees hi hp
  constructor
  · intro x
    unfold heads
    rw [hh]
    constructor
    · rintro ⟨y, hy, hraw⟩
      exact ⟨y, hy, (he y (hi.inv.headsLt y hy)).symm.trans hraw⟩
    · rintro ⟨y, hy, hraw⟩
      exact ⟨y, hy, (he y (hi.inv.headsLt y hy)).trans hraw⟩
  · unfold known
    rw [hk, he _ hi.inv.knownLt]

/-- Every `SysStep` only grows the raw universe, keeping existing parents. -/
theorem step_raw_grows {N : Nat} {D : Nat → Nat → Nat → Prop} {law : NodeSys.HubLaw}
    {act : Act} {g g' : Sys} (hs : SysStep N D law act g g') : RawGrow g g' := by
  cases hs with
  | busy _ _ _ _ _ _ hg _ _ _ => exact hg.raw
  | idle _ _ _ _ _ _ hr _ _ =>
    exact ⟨Nat.le_of_eq hr.1.symm, fun x _ => congrFun hr.2 x⟩
  | maint _ _ _ _ _ _ _ _ hg _ _ _ => exact hg.raw
  | issue _ _ _ _ _ _ _ _ hg _ _ _ _ _ _ _ _ _ => exact hg.raw
  | answer _ _ _ _ _ _ _ hr _ =>
    exact ⟨Nat.le_of_eq hr.2.1.symm, fun x _ => congrFun hr.2.2.1 x⟩
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    exact ⟨Nat.le_of_eq hr.2.2.2.2.1.symm, fun x _ => congrFun hr.2.2.2.2.2 x⟩
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ =>
    exact ⟨Nat.le_of_eq hr.2.2.2.2.1.symm, fun x _ => congrFun hr.2.2.2.2.2 x⟩
  | ignore _ _ _ _ _ _ _ _ _ hr _ =>
    exact ⟨Nat.le_of_eq hr.2.2.2.2.1.symm, fun x _ => congrFun hr.2.2.2.2.2 x⟩
  | env hr _ _ _ => exact hr

/-- Equal generations on the eligible nodes give equal `generations`. -/
theorem generations_same {E : Nat → Prop} {g g' : Sys}
    (h : ∀ n, E n → (g'.node n).gen = (g.node n).gen) :
    generations E g' = generations E g := by
  classical
  funext n
  by_cases he : E n <;> simp [generations, he, h]

/-- A step that is not about any eligible node, including a finite write batch, leaves each
eligible node's record unchanged, so the view moves by an `Expansion.Path` of `HubSuffix.Step`.
The step is not a hub answer (`act ≠ .answer`), and the only graph premise is raw DAG validity
of the new state (`hdag`). -/
theorem foreign_step_expansion {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : NodeSys.HubLaw} {E : Nat → Prop} {w : Nat} {act : Act} {g g' : Sys}
    (hs : SysStep N D law act g g') (ha : act ≠ .answer)
    (hforeign : ∀ n, E n → ¬ act.about n)
    (hdag : ∀ x, x < g'.next → ∀ p ∈ g'.par x, p < x)
    (hist : Nat → Nat) (pk : List Packet) :
    Nonempty (Expansion.Path (HubSuffix.Step E w) (view E g hist pk) (view E g' hist pk)) := by
  have grow := step_raw_grows hs
  have hnext : g.next ≤ g'.next := grow.1
  have same : ∀ n, E n → g'.node n = g.node n :=
    fun n hn => node_unchanged hs (hforeign n hn)
  apply raw_growth_expansion
  · exact grow.1
  · intro x hx
    change x < g.next at hx
    change parents g' x = parents g x
    have hx' : x < g'.next := by omega
    simp only [parents, hx, hx', ↓reduceIte]
    exact grow.2 x hx
  · intro x hx
    change g.next ≤ x at hx
    change parents g x = []
    simp [parents, show ¬ x < g.next by omega]
  · intro x hx
    change g'.next ≤ x at hx
    change parents g' x = []
    simp [parents, show ¬ x < g'.next by omega]
  · intro x hx p hp
    change x < g'.next at hx
    change p ∈ parents g' x at hp
    simp only [parents, hx, ↓reduceIte] at hp
    exact hdag x hx p hp
  · exact state_hub_same (hs.nonanswer_effect ha).hub rfl
  · intro n hn; exact state_node_same (same n hn)
  · exact generations_same (fun n hn => congrArg NodeC.gen (same n hn))
  · rfl

end Musubi.Recovery.HubSys

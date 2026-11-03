/-
The hub-side view of the joint system. Node fields are read from the SAME NodeC, using the
post-write repository heads while calls are outstanding. Control knowledge is the batch's
logical snapshot until its replies are handled, so it is not asserted to equal physical
mid-batch knowledge. The call-batch correspondence must justify that delayed bookkeeping.
Parent lists outside the created raw universe are normalized to empty: changes to those unused
function values are not graph changes. Store/object fields not observed by HubSuffix are left
abstract here; packet closure is checked separately by PacketAcceptance.
-/
import Musubi.NodeSys
import Musubi.Expansion
import Musubi.HistoryWindow
import Musubi.EntryAssembly
import Musubi.RawExpansion
import Musubi.RawMaintenance

namespace Musubi.Recovery.HubSys

open Musubi NodeSys NodeSettle HubSuffix

def parents (g : Sys) (x : Nat) : List Nat := if x < g.next then g.par x else []

def heads (g : Sys) (n x : Nat) : Prop :=
  ∃ y ∈ (g.node n).repo.heads, (g.node n).repoEmb y = x

def known (g : Sys) (n : Nat) : Nat × Nat :=
  ((g.node n).repo.known.1, (g.node n).repoEmb (g.node n).repo.known.2)

def state (g : Sys) (hist : Nat → Nat) : Musubi.State :=
  { init with
    U := { init.U with next := g.next, par := parents g }
    hub := { init.hub with head := g.hub.head, seq := g.hub.seq, hist := hist }
    node := fun n => { initNode with heads := heads g n, known := known g n } }

noncomputable def generations (E : Nat → Prop) (g : Sys) : Nat → Nat := by
  classical
  exact fun n => if E n then (g.node n).gen else 0

noncomputable def view (E : Nat → Prop) (g : Sys) (hist : Nat → Nat)
    (pk : List Packet) : GState :=
  ⟨state g hist, generations E g, pk⟩

def packet (p : Pkt) (tag : Option Nat) : Packet :=
  ⟨p.node, tag, p.knownSeq, p.expected, p.new⟩

theorem parents_same {g g' : Sys} (hn : g'.next = g.next)
    (hp : ∀ x, x < g.next → g'.par x = g.par x) : parents g' = parents g := by
  funext x
  unfold parents
  rw [hn]
  split
  · exact hp x ‹x < g.next›
  · rfl

/-- Global raw acyclicity is a native DAG contract, not a consequence of RawGrow alone:
RawGrow only protects old parents, and says nothing about new ones. -/
theorem parents_parLt {g : Sys} (hp : ∀ x, x < g.next → ∀ p ∈ g.par x, p < x) :
    ParLt (parents g) := by
  intro x p h
  by_cases hx : x < g.next
  · simp only [parents, hx, ↓reduceIte] at h
    exact hp x hx p h
  · simp [parents, hx] at h

theorem state_usame {g g' : Sys} {hist hist' : Nat → Nat}
    (hn : g'.next = g.next) (hp : ∀ x, x < g.next → g'.par x = g.par x) :
    USame (state g hist) (state g' hist') :=
  ⟨parents_same hn hp, hn⟩

theorem state_hub_same {g g' : Sys} {hist hist' : Nat → Nat}
    (hh : g'.hub = g.hub) (hi : hist' = hist) :
    HubSame (state g hist) (state g' hist') := by
  exact ⟨congrArg Snap.head hh, congrArg Snap.seq hh, hi⟩

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

/-- Once empty pending has been derived, the hub-side sender fields and the node-control
fields are consistent even during an outstanding request. The general waiting state may
already contain a fix-up, so that simplification would be false without this premise. -/
theorem state_repo_agrees {D : Nat → Nat → Nat → Prop} {g : Sys} {n : Nat}
    (hi : NodeSys.NodeOK D n g) (hp : (g.node n).ns.pending = []) :
    (∀ x, heads g n x ↔ ∃ y ∈ (g.node n).ns.heads, (g.node n).emb y = x) ∧
      known g n = ((g.node n).ns.known.1, (g.node n).emb (g.node n).ns.known.2) := by
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

theorem step_hub_quiet {N : Nat} {D : Nat → Nat → Nat → Prop} {law : NodeSys.HubLaw}
    {act : Act} {g g' : Sys} (hs : SysStep N D law act g g') (ha : act ≠ .answer) :
    g'.hub = g.hub := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => exact hq.hub
  | idle _ _ _ _ _ _ _ hq _ => exact hq.hub
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => exact hq.hub
  | env _ _ hq _ => exact hq.hub
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ => exact hr.1
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ => exact hr.1
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ => exact hr.1
  | ignore _ _ _ _ _ _ _ _ _ hr _ => exact hr.1
  | answer => exact False.elim (ha rfl)

theorem generations_same {E : Nat → Prop} {g g' : Sys}
    (h : ∀ n, E n → (g'.node n).gen = (g.node n).gen) :
    generations E g' = generations E g := by
  classical
  funext n
  by_cases he : E n <;> simp [generations, he, h]

/-- A foreign node's step, including a finite write batch, preserves every eligible node's
observable policy fields by the joint system's own node update rule. Only raw DAG validity
is supplied as a native graph contract; no abstract progress membership is assumed. -/
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
  · exact state_hub_same (step_hub_quiet hs ha) rfl
  · intro n hn; exact state_node_same (same n hn)
  · exact generations_same (fun n hn => congrArg NodeC.gen (same n hn))
  · rfl

end Musubi.Recovery.HubSys

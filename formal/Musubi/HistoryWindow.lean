/-
The strict raw-head history window that begins at the record cut, before eligible nodes have
learned from it, and how it enters the hub suffix. The convergence proof uses this file.
-/
import Musubi.HubSuffix

namespace Musubi.Recovery

open Musubi HubSuffix

structure HistoryWindow (w : Nat) (s : State) : Prop where
  parLt : ParLt s.U.par
  headLt : s.hub.head < s.U.next
  histHead : s.hub.hist s.hub.seq = s.hub.head
  window : w ≤ s.hub.seq
  chain : ∀ i j, w ≤ i → i ≤ j → j ≤ s.hub.seq → Anc s.U.par (s.hub.hist i) (s.hub.hist j)
  strict : ∀ i j, w ≤ i → i < j → j ≤ s.hub.seq → s.hub.hist i < s.hub.hist j

/-- EarlyEntry supplies the window lower bound; the serialized honest response gives the
truthful pair and sequence upper bound. At their common cut, all pre-entry packets get no
current generation, so the strong sender invariant is initially vacuous. -/
theorem history_window_enters_suffix {E : Nat → Prop} {w : Nat} {g : GState}
    (h : HistoryWindow w g.s)
    (hk : ∀ n, E n → w ≤ (g.s.node n).known.seq ∧ (g.s.node n).known.seq ≤ g.s.hub.seq ∧
      g.s.hub.hist (g.s.node n).known.seq = (g.s.node n).known.head)
    (hh : ∀ n, E n → ∀ y, (g.s.node n).heads y → y < g.s.U.next)
    (hpk : ∀ p ∈ g.pk, p.new < g.s.U.next ∧ p.tag = none) : HubSuffix.Inv E w g :=
  inv_entry h.parLt h.headLt h.histHead h.window h.chain h.strict hk hh hpk

end Musubi.Recovery

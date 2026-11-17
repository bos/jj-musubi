/-
A window of the hub's history, from sequence number `w` to the current one, in which the
raw head strictly increases along ancestry; and how such a window yields the hub-suffix
invariant. The convergence proof uses this file.
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

/-- A history window plus the eligible nodes' knowledge gives the hub-suffix invariant at `w`.
EarlyEntry supplies the lower bound `w ≤ known.seq`; the serialized honest response supplies
`known.seq ≤ hub.seq` and the matching head. Packets from before the cut carry no current
generation, so the sender invariant holds vacuously at the cut. -/
theorem history_window_enters_suffix {E : Nat → Prop} {w : Nat} {g : GState}
    (h : HistoryWindow w g.s)
    (hk : ∀ n, E n → w ≤ (g.s.node n).known.seq ∧ (g.s.node n).known.seq ≤ g.s.hub.seq ∧
      g.s.hub.hist (g.s.node n).known.seq = (g.s.node n).known.head)
    (hh : ∀ n, E n → ∀ y, (g.s.node n).heads y → y < g.s.U.next)
    (hpk : ∀ p ∈ g.pk, p.new < g.s.U.next ∧ p.tag = none) : HubSuffix.Inv E w g :=
  inv_entry h.parLt h.headLt h.histHead h.window h.chain h.strict hk hh hpk

end Musubi.Recovery

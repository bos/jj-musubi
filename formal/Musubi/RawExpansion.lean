/-
Expand a finite batch of raw graph growth into one-vertex model steps. The batch may have
zero new vertices, and its length need not have a uniform bound. Unused parent-function
values outside next are normalized to empty. This is a structural simulation, not a premise
that a progress measure decreases or that a sync finishes.
-/
import Musubi.HubSuffix
import Musubi.Expansion

namespace Musubi.Recovery

open Musubi HubSuffix

def rawLimit (g : GState) (next : Nat) : GState :=
  let u := { g.s.U with next := next, par := fun x => if x < next then g.s.U.par x else [] }
  { g with s := { g.s with U := u } }

theorem rawLimit_full (g : GState)
    (hn : ∀ x, g.s.U.next ≤ x → g.s.U.par x = []) : rawLimit g g.s.U.next = g := by
  have hp : (fun x => if x < g.s.U.next then g.s.U.par x else []) = g.s.U.par := by
    funext x
    by_cases hx : x < g.s.U.next
    · simp [hx]
    · simp [hx, hn x (by omega)]
  unfold rawLimit
  rw [hp]

theorem rawLimit_ext (g : GState) (n : Nat)
    (hp : ∀ p ∈ g.s.U.par n, p < n) :
    UExt (rawLimit g n).s (rawLimit g (n + 1)).s := by
  refine ⟨rfl, ?_, ?_⟩
  · intro x hx
    change x ≠ n at hx
    change (if x < n + 1 then g.s.U.par x else []) =
      if x < n then g.s.U.par x else []
    by_cases hb : x < n
    · simp [hb, show x < n + 1 by omega]
    · simp [hb, show ¬ x < n + 1 by omega]
  · simpa [rawLimit] using hp

/-- Other nodes may write arbitrarily many finite batches. Their growth preserves the
eligible nodes' heads/knowledge and the hub, and hence refines grow/frame model steps. -/
theorem raw_growth_expansion {E : Nat → Prop} {w : Nat} {a b : GState}
    (hn : a.s.U.next ≤ b.s.U.next)
    (hold : ∀ x, x < a.s.U.next → b.s.U.par x = a.s.U.par x)
    (haNorm : ∀ x, a.s.U.next ≤ x → a.s.U.par x = [])
    (hbNorm : ∀ x, b.s.U.next ≤ x → b.s.U.par x = [])
    (hpar : ∀ x, x < b.s.U.next → ∀ p ∈ b.s.U.par x, p < x)
    (hh : HubSame a.s b.s) (hnode : ∀ n, E n → NodeSame a.s b.s n)
    (hbk : b.bk = a.bk) (hpk : b.pk = a.pk) :
    Nonempty (Expansion.Path (HubSuffix.Step E w) a b) := by
  let d := b.s.U.next - a.s.U.next
  let st : Nat → GState
    | 0 => a
    | j + 1 => rawLimit b (a.s.U.next + j)
  have hb : a.s.U.next + d = b.s.U.next := by dsimp [d]; omega
  have firstFrame : HubSuffix.Step E w a (rawLimit b a.s.U.next) := by
    apply HubSuffix.Step.frame
    · refine ⟨?_, rfl⟩
      funext x
      change (if x < a.s.U.next then b.s.U.par x else []) = a.s.U.par x
      by_cases hx : x < a.s.U.next
      · simpa [hx] using hold x hx
      · simp [hx, haNorm x (by omega)]
    · exact hh
    · exact hnode
    · exact hbk
    · exact hpk
  refine ⟨⟨d + 1, Nat.zero_lt_succ _, st, rfl, ?_, ?_⟩⟩
  · change rawLimit b (a.s.U.next + d) = b
    rw [hb]
    exact rawLimit_full b hbNorm
  · intro j hj
    cases j with
    | zero => exact firstFrame
    | succ j =>
      change HubSuffix.Step E w (rawLimit b (a.s.U.next + j))
        (rawLimit b (a.s.U.next + (j + 1)))
      rw [show a.s.U.next + (j + 1) = (a.s.U.next + j) + 1 by omega]
      apply HubSuffix.Step.grow
      · exact rawLimit_ext b _ (hpar _ (by omega))
      · exact ⟨rfl, rfl, rfl⟩
      · exact fun _ _ => ⟨rfl, rfl⟩
      · rfl
      · rfl

end Musubi.Recovery

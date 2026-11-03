/-
Expand the finite operations written by one housekeeping call. Each new operation is a
maintenance generation; the final published head is the last one. The graph may contain
arbitrary parent lists within that finite batch, provided they are acyclic. This structural
lemma supplies the multi-operation case of the hub-side simulation.
-/
import Musubi.RawExpansion

namespace Musubi.Recovery

open Musubi HubSuffix

theorem upd_current {α : Type} (f : Nat → α) (n : Nat) : upd f n (f n) = f := by
  funext m
  by_cases hm : m = n <;> simp [upd, hm]

def maintenanceStage (a b : GState) (n j : Nat) : GState :=
  let g := rawLimit b (a.s.U.next + j)
  let H := if j = 0 then (a.s.node n).heads else (· = a.s.U.next + j - 1)
  let nd := { g.s.node n with heads := H, known := (a.s.node n).known }
  { g with s := { g.s with node := upd g.s.node n nd }, bk := upd b.bk n (a.bk n + j) }

theorem maintenanceStage_last {a b : GState} {n d : Nat} (hd : 0 < d)
    (hn : a.s.U.next + d = b.s.U.next)
    (hbNorm : ∀ x, b.s.U.next ≤ x → b.s.U.par x = [])
    (hh : (b.s.node n).heads = (· = b.s.U.next - 1))
    (hk : (b.s.node n).known = (a.s.node n).known)
    (hbk : b.bk n = a.bk n + d) : maintenanceStage a b n d = b := by
  unfold maintenanceStage
  rw [hn, rawLimit_full b hbNorm]
  simp only [show ¬ d = 0 by omega, ↓reduceIte]
  rw [← hh, ← hk, ← hbk]
  rw [upd_current, upd_current]

theorem raw_maintenance_expansion {E : Nat → Prop} {w : Nat} {a b : GState} {n : Nat}
    (hE : E n) (hn : a.s.U.next < b.s.U.next)
    (hold : ∀ x, x < a.s.U.next → b.s.U.par x = a.s.U.par x)
    (haNorm : ∀ x, a.s.U.next ≤ x → a.s.U.par x = [])
    (hbNorm : ∀ x, b.s.U.next ≤ x → b.s.U.par x = [])
    (hpar : ∀ x, x < b.s.U.next → ∀ p ∈ b.s.U.par x, p < x)
    (hh : HubSame a.s b.s)
    (hother : ∀ m, E m → m ≠ n → NodeSame a.s b.s m)
    (hheads : (b.s.node n).heads = (· = b.s.U.next - 1))
    (hknown : (b.s.node n).known = (a.s.node n).known)
    (hbk : b.bk n = a.bk n + (b.s.U.next - a.s.U.next))
    (hbkOther : ∀ m, m ≠ n → b.bk m = a.bk m) (hpk : b.pk = a.pk) :
    Nonempty (Expansion.Path (HubSuffix.Step E w) a b) := by
  let d := b.s.U.next - a.s.U.next
  have hd : 0 < d := by dsimp [d]; omega
  have hb : a.s.U.next + d = b.s.U.next := by dsimp [d]; omega
  let st : Nat → GState
    | 0 => a
    | j + 1 => maintenanceStage a b n j
  have firstFrame : HubSuffix.Step E w a (maintenanceStage a b n 0) := by
    apply HubSuffix.Step.frame
    · refine ⟨?_, by rfl⟩
      funext x
      change (if x < a.s.U.next + 0 then b.s.U.par x else []) = a.s.U.par x
      by_cases hx : x < a.s.U.next
      · simpa [hx] using hold x hx
      · simp [hx, haNorm x (by omega)]
    · exact hh
    · intro m hm
      by_cases he : m = n
      · subst m; simp [NodeSame, maintenanceStage, upd_same]
      · simpa only [NodeSame, maintenanceStage, rawLimit, upd_ne _ _ he] using hother m hm he
    · funext m
      by_cases he : m = n
      · subst m; simp [maintenanceStage]
      · simpa [maintenanceStage, he] using hbkOther m he
    · exact hpk
  refine ⟨⟨d + 1, Nat.zero_lt_succ _, st, rfl,
    maintenanceStage_last hd hb hbNorm hheads hknown hbk, ?_⟩⟩
  intro j hj
  cases j with
  | zero => exact firstFrame
  | succ j =>
    change HubSuffix.Step E w (maintenanceStage a b n j) (maintenanceStage a b n (j + 1))
    apply HubSuffix.Step.maintain n hE
    · change UExt (rawLimit b (a.s.U.next + j)).s
        (rawLimit b (a.s.U.next + (j + 1))).s
      rw [show a.s.U.next + (j + 1) = (a.s.U.next + j) + 1 by omega]
      exact rawLimit_ext b _ (hpar _ (by omega))
    · exact ⟨rfl, rfl, rfl⟩
    · intro m _ hmn
      simp [NodeSame, maintenanceStage, rawLimit, hmn]
    · intro y
      simp only [maintenanceStage, upd_same, show ¬ j + 1 = 0 by omega, ↓reduceIte]
      have he : a.s.U.next + (j + 1) - 1 = a.s.U.next + j := by omega
      rw [he]
      rfl
    · simp [maintenanceStage]
    · funext m
      by_cases hmn : m = n
      · subst m; simp [maintenanceStage, upd_same, Nat.add_assoc]
      · simp [maintenanceStage, hmn]
    · rfl

end Musubi.Recovery

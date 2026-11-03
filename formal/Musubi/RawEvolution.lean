/-
The raw history projection before pending-name reconciliation stops. Local bookkeeping and
record adoption may change node controls, so this relation intentionally reads no node field.
It keeps actual immutable graph growth and the hub's compare-and-swap effects. This lets the
pending-name cutoff be proved before starting NodeSys's finer control simulation.
-/
import Musubi.RequestBounds

namespace Musubi.Recovery.HubSys

open Musubi NodeSys HubSuffix

inductive RawStep : Sys → Sys → Prop
  | quiet {g g' : Sys} (grow : RawGrow g g') (hub : g'.hub = g.hub) : RawStep g g'
  | move {g g' : Sys} (new : Nat) (bound : new < g.next) (different : new ≠ g.hub.head)
      (above : Anc g.par g.hub.head new) (next : g'.next = g.next) (par : g'.par = g.par)
      (head : g'.hub.head = new) (seq : g'.hub.seq = g.hub.seq + 1) : RawStep g g'

theorem RawStep.grows {g g' : Sys} (h : RawStep g g') : RawGrow g g' := by
  cases h with
  | quiet grow _ => exact grow
  | move _ _ _ _ hn hp _ _ => exact ⟨Nat.le_of_eq hn.symm, fun x _ => congrFun hp x⟩

theorem RawStep.seq_mono {g g' : Sys} (h : RawStep g g') : g.hub.seq ≤ g'.hub.seq := by
  cases h with
  | quiet _ hh => rw [hh]; exact Nat.le_refl _
  | move _ _ _ _ _ _ _ hsq => rw [hsq]; exact Nat.le_succ _

theorem raw_quiet_expansion {g g' : Sys} {w : Nat} (hg : RawGrow g g')
    (hh : g'.hub = g.hub)
    (hdag : ∀ x, x < g'.next → ∀ p ∈ g'.par x, p < x) (hist : Nat → Nat) :
    Nonempty (Expansion.Path (HubSuffix.Step (fun _ => False) w)
      (view (fun _ => False) g hist []) (view (fun _ => False) g' hist [])) := by
  apply raw_growth_expansion
  · exact hg.1
  · intro x hx
    change x < g.next at hx
    change parents g' x = parents g x
    have hx' : x < g'.next := Nat.lt_of_lt_of_le hx hg.1
    simp only [parents, hx, hx', ↓reduceIte]
    exact hg.2 x hx
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
  · exact state_hub_same hh rfl
  · intro _ hf; exact False.elim hf
  · funext n; simp [view, generations]
  · rfl

theorem raw_window_step {w : Nat} {g g' : Sys} {hist : Nat → Nat}
    (hi : HistoryWindow w (state g hist)) (hs : RawStep g g')
    (hdag : ∀ x, x < g'.next → ∀ p ∈ g'.par x, p < x) :
    HistoryWindow w (state g' (nextHistory g g' hist)) := by
  cases hs with
  | quiet hg hh =>
    obtain ⟨path⟩ := raw_quiet_expansion (w := w) hg hh hdag hist
    have hgen : generations (fun _ => False) g = fun _ => 0 := by
      funext n; simp [generations]
    have start : HubSuffix.Inv (fun _ => False) w (view (fun _ => False) g hist []) := by
      simpa only [view, hgen] using hi.withPackets [] (by simp)
    have finish := path.invariant (HubSuffix.Inv (fun _ => False) w)
      (fun _ _ hin step => HubSuffix.inv_step hin step) start
    rw [nextHistory_quiet hist hh]
    exact HistoryWindow.ofInv finish
  | move new hb hd ha hn hp hh hsq =>
    have beforeDag : ∀ x, x < g.next → ∀ p ∈ g.par x, p < x := by
      intro x hx p hm
      exact hdag x (by rw [hn]; exact hx) p (by rw [hp]; exact hm)
    apply history_window_step hi
    apply HistoryStep.accept new hb hd (anc_parents beforeDag ha hb)
      (state_usame hn (fun _ _ => congrFun hp _)) hh hsq
    simp [nextHistory, hsq, hh, state]

theorem raw_window_run (run : Nat → Sys) (initial : Nat → Nat)
    (hs : ∀ i, RawStep (run i) (run (i + 1)))
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hhead : (run 0).hub.head < (run 0).next)
    (hfirst : initial (run 0).hub.seq = (run 0).hub.head) :
    ∀ i, HistoryWindow (run 0).hub.seq (state (run i) (histories run initial i)) := by
  intro i
  induction i with
  | zero =>
    exact history_window_init (s := state (run 0) initial) (parents_parLt (hdag 0)) hhead hfirst
  | succ i ih => exact raw_window_step ih (hs i) (hdag (i + 1))

theorem raw_seq_mono {run : Nat → Sys} (hs : ∀ i, RawStep (run i) (run (i + 1)))
    {i j : Nat} (hij : i ≤ j) : (run i).hub.seq ≤ (run j).hub.seq := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (hs (i + d)).seq_mono

theorem raw_histories_saved {run : Nat → Sys} (hs : ∀ i, RawStep (run i) (run (i + 1)))
    (initial : Nat → Nat) {i j q : Nat} (hij : i ≤ j) (hq : q ≤ (run i).hub.seq) :
    histories run initial j q = histories run initial i q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => rfl
  | succ d ih =>
    change nextHistory (run (i + d)) (run (i + d + 1)) (histories run initial (i + d)) q = _
    rw [nextHistory_saved (Nat.le_trans hq (raw_seq_mono hs (Nat.le_add_right _ _)))]
    exact ih

theorem rawStep_of_sys {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {act : Act} {g g' : Sys} (hs : SysStep N D law act g g')
    (hbound : RequestBounds g) : RawStep g g' := by
  have grow := step_raw_grows hs
  by_cases ha : act = .answer
  · subst act
    cases hs with
    | answer r ans hr _ acc hans _ hrest _ =>
      rcases hans with ⟨_, _, _, hh, _⟩ | ⟨_, _, _, hh, _⟩ | ⟨p, hp, hpush⟩
      · exact .quiet grow hh
      · exact .quiet grow hh
      · rcases hpush with ⟨ha, _, hh, _⟩ | ⟨_, _, _, _, hh, _⟩ | ⟨_, _, _, _, hh, _⟩
        · obtain ⟨_, _, hne, hanc, _⟩ := law.guards g.hub g.par p ha
          exact .move p.new (hbound r hr p hp) hne hanc hrest.2.1 hrest.2.2.1
            (congrArg Snap.head hh) (congrArg Snap.seq hh)
        · exact .quiet grow hh
        · exact .quiet grow hh
  · exact .quiet grow (step_hub_quiet hs ha)

end Musubi.Recovery.HubSys

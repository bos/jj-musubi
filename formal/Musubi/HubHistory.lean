/-
The strict raw history window is derived from the SAME joint system before eligible-node
entry. Local work can create finite raw batches; only an actual accepted answer moves the
hub. Initial packets need only name created raw operations. No sender eligibility, node
knowledge or already-stable head is needed for this history invariant.
-/
import Musubi.HubAnswers

namespace Musubi.Recovery.HubSys

open Musubi NodeSys HubSuffix

noncomputable def histories (run : Nat → Sys) (initial : Nat → Nat) : Nat → Nat → Nat
  | 0 => initial
  | i + 1 => nextHistory (run i) (run (i + 1)) (histories run initial i)

theorem step_seq_mono {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {act : Act} {g g' : Sys} (hs : SysStep N D law act g g') :
    g.hub.seq ≤ g'.hub.seq := by
  by_cases ha : act = .answer
  · subst act
    cases hs with
    | answer _ _ _ _ _ hans _ _ _ =>
      rcases hans with ⟨_, _, _, hh, _⟩ | ⟨_, _, _, hh, _⟩ | ⟨_, _, hpush⟩
      · rw [hh]; exact Nat.le_refl _
      · rw [hh]; exact Nat.le_refl _
      · rcases hpush with ⟨_, _, hh, _⟩ | ⟨_, _, _, _, hh, _⟩ | ⟨_, _, _, _, hh, _⟩
        · rw [hh]; exact Nat.le_succ _
        · rw [hh]; exact Nat.le_refl _
        · rw [hh]; exact Nat.le_refl _
  · rw [step_hub_quiet hs ha]; exact Nat.le_refl _

theorem nextHistory_saved {g g' : Sys} {hist : Nat → Nat} {q : Nat}
    (hq : q ≤ g.hub.seq) : nextHistory g g' hist q = hist q := by
  unfold nextHistory
  split
  · rw [upd_ne _ _ (by omega)]
  · rfl

theorem sys_seq_mono {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {run : Nat → Sys} {acts : Nat → Act}
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    {i j : Nat} (hij : i ≤ j) : (run i).hub.seq ≤ (run j).hub.seq := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (step_seq_mono (hs (i + d)))

theorem histories_saved {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {run : Nat → Sys} {acts : Nat → Act}
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    (initial : Nat → Nat) {i j q : Nat} (hij : i ≤ j) (hq : q ≤ (run i).hub.seq) :
    histories run initial j q = histories run initial i q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => rfl
  | succ d ih =>
    change nextHistory (run (i + d)) (run (i + d + 1)) (histories run initial (i + d)) q = _
    rw [nextHistory_saved (Nat.le_trans hq (sys_seq_mono hs (Nat.le_add_right _ _)))]
    exact ih

theorem history_window_sys_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {w : Nat} {g g' : Sys} {act : Act} {hist : Nat → Nat}
    (hi : HistoryWindow w (state g hist)) (hs : SysStep N D law act g g')
    (hdag : ∀ x, x < g'.next → ∀ p ∈ g'.par x, p < x)
    (hbound : ∀ r ∈ g.reqs, ∀ p, r.body = .push p → p.new < g.next) :
    HistoryWindow w (state g' (nextHistory g g' hist)) := by
  by_cases ha : act = .answer
  · subst act
    cases hs with
    | answer r ans hr _ acc hans _ hrest _ =>
      have hu := state_usame (hist := hist) (hist' := nextHistory g g' hist)
        hrest.2.1 (fun _ _ => congrFun hrest.2.2.1 _)
      have quiet : g'.hub = g.hub → HistoryWindow w (state g' (nextHistory g g' hist)) := by
        intro hh
        exact history_window_step hi (.frame hu
          (state_hub_same hh (nextHistory_quiet hist hh)))
      rcases hans with ⟨_, _, _, hh, _⟩ | ⟨_, _, _, hh, _⟩ | ⟨p, hp, haccept⟩
      · exact quiet hh
      · exact quiet hh
      · rcases haccept with ⟨ha, _, hh, _, _⟩ | ⟨_, _, _, _, hh, _⟩ | ⟨_, _, _, _, hh, _⟩
        · obtain ⟨_, _, hne, hanc, _⟩ := law.guards g.hub g.par p ha
          have beforeDag : ∀ x, x < g.next → ∀ q ∈ g.par x, q < x := by
            intro x hx q hq
            rw [← hrest.2.1] at hx
            exact hdag x hx q (by rw [hrest.2.2.1]; exact hq)
          exact history_window_step hi (.accept p.new (hbound r hr p hp) hne
            (anc_parents beforeDag hanc (hbound r hr p hp)) hu
            (congrArg Snap.head hh) (congrArg Snap.seq hh) (nextHistory_accept hist hh))
        · exact quiet hh
        · exact quiet hh
  · have hh := step_hub_quiet hs ha
    have path := foreign_step_expansion (E := fun _ => False) (w := w) hs ha
      (fun _ hf => False.elim hf) hdag hist []
    obtain ⟨path⟩ := path
    have start : HubSuffix.Inv (fun _ => False) w (view (fun _ => False) g hist []) := by
      have he : generations (fun _ => False) g = fun _ => 0 := by
        funext n; simp [generations]
      simpa only [view, he] using hi.withPackets [] (by simp)
    have finish := path.invariant (HubSuffix.Inv (fun _ => False) w)
      (fun _ _ hin step => HubSuffix.inv_step hin step) start
    rw [nextHistory_quiet hist hh]
    exact HistoryWindow.ofInv finish

theorem history_window_sys_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (run : Nat → Sys) (acts : Nat → Act) (initial : Nat → Nat)
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    (hdag : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hbound : ∀ i r, r ∈ (run i).reqs → ∀ p, r.body = .push p → p.new < (run i).next)
    (hhead : (run 0).hub.head < (run 0).next)
    (hfirst : initial (run 0).hub.seq = (run 0).hub.head) :
    ∀ i, HistoryWindow (run 0).hub.seq (state (run i) (histories run initial i)) := by
  intro i
  induction i with
  | zero =>
    exact history_window_init (s := state (run 0) initial)
      (parents_parLt (hdag 0)) hhead hfirst
  | succ i ih => exact history_window_sys_step ih (hs i) (hdag (i + 1)) (hbound i)

end Musubi.Recovery.HubSys

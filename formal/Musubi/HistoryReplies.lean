/-
Fresh replies and notifications name the actual strict history of the joint system.
They stay truthful during arbitrary delay because later answers preserve every earlier
sequence entry. This derives the HonestSnap premises of the hub-side node simulation.
-/
import Musubi.HubHistory
import Musubi.SysFreshCuts

namespace Musubi.Recovery.HubSys

open Musubi NodeSys NodeSysEntry HubNodeSteps

structure HistoryMessages (w t : Nat) (g : Sys) (hist : Nat → Nat) : Prop where
  reps : ∀ r ∈ g.reps, t ≤ r.time → ∀ s,
    (r.ans = .fetched s ∨ r.ans = .head s) → HonestSnap w hist g s
  notes : ∀ nt ∈ g.notes, t ≤ nt.time → HonestSnap w hist g nt.snap

theorem honest_snap_current {w : Nat} {g : Sys} {hist : Nat → Nat}
    (h : HistoryWindow w (state g hist)) : HonestSnap w hist g g.hub :=
  ⟨h.window, Nat.le_refl _, h.histHead⟩

theorem honest_snap_lift {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {act : Act} {g g' : Sys} {hist : Nat → Nat} {w : Nat} {snap : Snap}
    (hs : SysStep N D law act g g') (h : HonestSnap w hist g snap) :
    HonestSnap w (nextHistory g g' hist) g' snap :=
  ⟨h.1, Nat.le_trans h.2.1 (step_seq_mono hs), (nextHistory_saved h.2.1).trans h.2.2⟩

theorem history_messages_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {act : Act} {g g' : Sys} {hist : Nat → Nat} {w t : Nat}
    (hm : HistoryMessages w t g hist) (hs : SysStep N D law act g g')
    (hi : HistoryWindow w (state g hist))
    (hj : HistoryWindow w (state g' (nextHistory g g' hist))) :
    HistoryMessages w t g' (nextHistory g g' hist) := by
  have lift := fun {s} (h : HonestSnap w hist g s) => honest_snap_lift hs h
  have old : (∀ r ∈ g'.reps, r ∈ g.reps) → (∀ nt ∈ g'.notes, nt ∈ g.notes) →
      HistoryMessages w t g' (nextHistory g g' hist) := by
    intro hr hn
    exact ⟨fun r h ht s he => lift (hm.reps r (hr r h) ht s he),
      fun nt h ht => lift (hm.notes nt (hn nt h) ht)⟩
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ | idle _ _ _ _ _ _ _ hq _ =>
    exact old (fun _ h => hq.reps ▸ h) (fun _ h => hq.notes ▸ h)
  | maint _ _ _ _ _ _ _ _ _ _ hq _ | env _ _ hq _ =>
    exact old (fun _ h => hq.reps ▸ h) (fun _ h => hq.notes ▸ h)
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr _ _ =>
    exact old (fun _ h => hr.2.1 ▸ h) (fun _ h => hr.2.2 ▸ h)
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps hr _ =>
    exact old (fun r h => ((hreps r).1 h).1) (fun _ h => hr.2.2.1 ▸ h)
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hn hr _ =>
    exact old (fun _ h => hr.2.2.1 ▸ h)
      (fun _ h => List.mem_of_mem_erase (hn ▸ h))
  | ignore _ _ _ _ _ _ _ _ hn hr _ =>
    exact old (fun _ h => hr.2.2.1 ▸ h)
      (fun _ h => List.mem_of_mem_erase (hn ▸ h))
  | answer r ans _ _ acc hans hreps _ _ =>
    have fresh : ∀ s, (ans = .fetched s ∨ ans = .head s) →
        HonestSnap w (nextHistory g g' hist) g' s := by
      intro s he
      rcases hans with ⟨_, _, ha, _, _⟩ | ⟨_, _, ha, _, _⟩ | ⟨_, _, hpush⟩
      · rw [ha] at he
        rcases he with he | he
        · cases he; exact lift (honest_snap_current hi)
        · cases he
      · rw [ha] at he; rcases he with he | he <;> cases he
      · rcases hpush with ⟨_, _, _, ha, _⟩ | ⟨_, _, _, ha, _, _⟩ | ⟨_, _, _, ha, _, _⟩
        · rw [ha] at he
          rcases he with he | he
          · cases he
          · cases he; exact honest_snap_current hj
        · rw [ha] at he; rcases he with he | he <;> cases he
        · rw [ha] at he
          rcases he with he | he
          · cases he
          · cases he; exact lift (honest_snap_current hi)
    constructor
    · intro x hx ht s he
      rw [hreps, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact lift (hm.reps x hx ht s he)
      · exact fresh s he
    · intro nt hn ht
      rcases hans with ⟨_, _, _, _, hn'⟩ | ⟨_, _, _, _, hn'⟩ | ⟨_, _, hpush⟩
      · exact lift (hm.notes nt (hn' ▸ hn) ht)
      · exact lift (hm.notes nt (hn' ▸ hn) ht)
      · rcases hpush with ⟨_, _, _, _, hn'⟩ | ⟨_, _, _, _, _, hn'⟩ | ⟨_, _, _, _, _, hn'⟩
        · rw [hn', List.mem_append] at hn
          rcases hn with hn | hn
          · exact lift (hm.notes nt hn ht)
          · obtain ⟨n, _, rfl⟩ := List.mem_map.1 hn
            exact honest_snap_current hj
        · exact lift (hm.notes nt (hn' ▸ hn) ht)
        · exact lift (hm.notes nt (hn' ▸ hn) ht)

theorem history_messages_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    (run : Nat → Sys) (acts : Nat → Act) (initial : Nat → Nat)
    (hs : ∀ i, SysStep N D law (acts i) (run i) (run (i + 1)))
    (hw : ∀ i, HistoryWindow (run 0).hub.seq (state (run i) (histories run initial i)))
    (ht : TimeOK (run 0)) :
    ∀ i, HistoryMessages (run 0).hub.seq (run 0).time (run i) (histories run initial i) := by
  intro i
  induction i with
  | zero =>
    exact ⟨fun r hr htime => False.elim (by have := ht.reps r hr; omega),
      fun nt hn htime => False.elim (by have := ht.notes nt hn; omega)⟩
  | succ i ih => exact history_messages_step ih (hs i) (hw i) (hw (i + 1))

end Musubi.Recovery.HubSys

/-
Replies and notifications answered after the cut carry honest hub snapshots. This invariant
is proved along the actual replay, separately from assembling the convergence interface.

The convergence proof uses this file.
-/
import Musubi.NativeEvents

namespace Musubi.FineAssembly

open Musubi NodeSettle NodeSys NodeSysEntry SysAcceptance NativeEvents Recovery.HubSys
  Recovery.HubNodeSteps

/-! ## Honest replies and notifications

A reply the hub gives carries its snapshot then, and a notification the snapshot its accept
leaves; the history the suffix reads (`histories`) records the hub's head at each sequence and
changes only at a new, higher one. So the replies and notifications answered from a time on are
honest snapshots of that history for as long as they are in flight. Replies to other nodes'
calls (`answerRaw`) are not read. -/

/-- From time `t0` on, the hub's head is the history's at its sequence, past the window's start,
and the replies answered to eligible nodes carry honest snapshots, and so do the notifications
naming a state from `t0` on (published at `nt.time`, naming the state right after). -/
structure Honest (E : Nat → Prop) (w t0 : Nat) (hist : Nat → Nat) (g : Sys) : Prop where
  window : w ≤ g.hub.seq
  head : hist g.hub.seq = g.hub.head
  time : t0 ≤ g.time
  reps : ∀ r ∈ g.reps, E r.node → t0 ≤ r.time → ∀ s,
    (r.ans = .fetched s ∨ r.ans = .head s) → HonestSnap w hist g s
  notes : ∀ nt ∈ g.notes, E nt.node → t0 ≤ nt.time + 1 → HonestSnap w hist g nt.snap

/-- An honest snapshot stays so as the hub goes on: the history agrees below its sequence. -/
theorem honestSnap_mono {w : Nat} {hist hist' : Nat → Nat} {g g' : Sys} {s : Snap}
    (h : HonestSnap w hist g s) (hseq : g.hub.seq ≤ g'.hub.seq)
    (hagree : ∀ x, x ≤ g.hub.seq → hist' x = hist x) : HonestSnap w hist' g' s :=
  ⟨h.1, Nat.le_trans h.2.1 hseq, (hagree _ h.2.1).trans h.2.2⟩

/-- The history after a step agrees with the one before up to the sequence before. -/
theorem nextHistory_agree {g g' : Sys} {hist : Nat → Nat} (x : Nat) (hx : x ≤ g.hub.seq) :
    nextHistory g g' hist x = hist x := by
  unfold nextHistory
  split
  · rename_i hlt
    exact upd_ne _ _ (by omega)
  · rfl

/-- Extend honesty through an agreeing history and hub movement. Old traffic is transported
by history agreement; new traffic supplies its own snapshot witness. -/
theorem Honest.extend {E : Nat → Prop} {w t0 : Nat} {hist hist' : Nat → Nat} {g g' : Sys}
    (H : Honest E w t0 hist g) (window : w ≤ g'.hub.seq)
    (head : hist' g'.hub.seq = g'.hub.head) (time : t0 ≤ g'.time)
    (sequence : g.hub.seq ≤ g'.hub.seq) (agree : ∀ x, x ≤ g.hub.seq → hist' x = hist x)
    (replies : ∀ r ∈ g'.reps, r ∈ g.reps ∨
      ∀ s, (r.ans = .fetched s ∨ r.ans = .head s) → HonestSnap w hist' g' s)
    (notices : ∀ nt ∈ g'.notes, nt ∈ g.notes ∨ HonestSnap w hist' g' nt.snap) :
    Honest E w t0 hist' g' where
  window := window
  head := head
  time := time
  reps := by
    intro r hr eligible fresh s carries
    rcases replies r hr with old | observed
    · exact honestSnap_mono (H.reps r old eligible fresh s carries) sequence agree
    · exact observed s carries
  notes := by
    intro nt hn eligible fresh
    rcases notices nt hn with old | observed
    · exact honestSnap_mono (H.notes nt old eligible fresh) sequence agree
    · exact observed

/-- Each step of the hive keeps the replies and notifications answered from `t0` honest. -/
theorem honest_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {E : Nat → Prop}
    {old : List Req} {act : Act} {g g' : Sys} {w t0 : Nat} {hist : Nat → Nat}
    (hs : HiveStep N D law E old act g g') (H : Honest E w t0 hist g) :
    Honest E w t0 (nextHistory g g' hist) g' := by
  have htime0 := H.time
  -- a step that moves no hub, adds no reply to an eligible node, and no notification
  have frame : g'.hub = g.hub → (∀ r ∈ g'.reps, r ∈ g.reps ∨ ¬ E r.node) →
      (∀ nt ∈ g'.notes, nt ∈ g.notes) → g'.time = g.time + 1 →
      Honest E w t0 (nextHistory g g' hist) g' := by
    intro hhub hreps hnotes htime
    have hh : nextHistory g g' hist = hist := nextHistory_quiet hist hhub
    rw [hh]
    have hseq : g.hub.seq ≤ g'.hub.seq := Nat.le_of_eq (by rw [hhub])
    refine ⟨by rw [hhub]; exact H.window, by rw [hhub]; exact H.head, by omega, ?_, ?_⟩
    · intro r hr hE ht s hs'
      rcases hreps r hr with hr | hn
      · exact honestSnap_mono (H.reps r hr hE ht s hs') hseq fun _ _ => rfl
      · exact absurd hE hn
    · intro nt hn hE ht
      exact honestSnap_mono (H.notes nt (hnotes nt hn) hE ht) hseq fun _ _ => rfl
  cases hs with
  | node n hE ha hs =>
    have hna : act ≠ .answer := by rintro rfl; exact ha
    have effect := hs.nonanswer_effect hna
    exact frame effect.hub (fun r h => Or.inl (effect.replies r h)) effect.notices effect.time
  | env hs =>
    have effect := hs.nonanswer_effect (by intro h; cases h)
    exact frame effect.hub (fun r h => Or.inl (effect.replies r h)) effect.notices effect.time
  | raw n hn rq hr hnode hreqs hrq hrest ht =>
    exact frame hrest.1 (fun r h => Or.inl (by rw [hrest.2.1] at h; exact h))
      (fun nt h => by rw [hrest.2.2.1] at h; exact h) ht
  | answerRaw r hr hn hold rep hrep hreqs hreps hhub hrest ht =>
    refine frame hhub (fun r' h => ?_) (fun nt h => by rw [hrest.2.1] at h; exact h) ht
    rw [hreps, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact Or.inl h
    · exact Or.inr (by rw [hrep.1]; exact hn)
  | answer hs hk =>
    cases hs.answer_effect with
    | quiet hub replies notices time =>
      have history : nextHistory g g' hist = hist := nextHistory_quiet hist hub
      have sequence : g.hub.seq ≤ g'.hub.seq := Nat.le_of_eq (congrArg Snap.seq hub.symm)
      have snapshot : HonestSnap w hist g' g.hub := ⟨H.window, sequence, H.head⟩
      rw [history]
      refine H.extend (by rw [hub]; exact H.window) (by rw [hub]; exact H.head)
        (by omega) sequence (fun _ _ => rfl) ?_
        (fun nt hn => Or.inl (notices nt hn))
      intro r hr
      rcases replies r hr with old | observed
      · exact Or.inl old
      · exact Or.inr fun s carries => (observed.2 s carries).symm ▸ snapshot
    | accepted sequence replies notices time =>
      have moved : g.hub.seq < g'.hub.seq := by omega
      have history : nextHistory g g' hist = upd hist g'.hub.seq g'.hub.head := by
        simp [nextHistory, moved]
      have window : w ≤ g'.hub.seq := by have := H.window; omega
      have head : nextHistory g g' hist g'.hub.seq = g'.hub.head := by
        rw [history, upd_same]
      have snapshot : HonestSnap w (nextHistory g g' hist) g' g'.hub :=
        ⟨window, Nat.le_refl _, head⟩
      refine H.extend window head (by omega) (by omega) nextHistory_agree ?_ ?_
      · intro r hr
        rcases replies r hr with old | observed
        · exact Or.inl old
        · exact Or.inr fun s carries => (observed.2 s carries).symm ▸ snapshot
      · intro nt hn
        rcases notices nt hn with old | observed
        · exact Or.inl old
        · exact Or.inr (observed.2.symm ▸ snapshot)

/-- Along a run of the hive, from honest replies and notifications at its start. -/
theorem honest_run {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {E : Nat → Prop}
    {old : List Req} (ρ : Nat → Sys) (acts : Nat → Act) (hist0 : Nat → Nat) {w t0 : Nat}
    (hs : ∀ i, HiveStep N D law E old (acts i) (ρ i) (ρ (i + 1)))
    (h0 : Honest E w t0 hist0 (ρ 0)) : ∀ i, Honest E w t0 (histories ρ hist0 i) (ρ i)
  | 0 => h0
  | i + 1 => honest_step (hs i) (honest_run ρ acts hist0 hs h0 i)

/-- A notification a node takes is its own, in flight. -/
theorem notice_mem {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {E : Nat → Prop}
    {old : List Req} {n : Nat} {nt : Note} {g g' : Sys}
    (hs : HiveStep N D law E old (.notice n nt) g g') : nt ∈ g.notes ∧ nt.node = n := by
  cases hs with
  | node m hE ha hs =>
    cases hs with
    | notice _ _ _ _ _ _ _ _ _ hn hnn _ _ _ _ _ _ _ _ _ => exact ⟨hn, hnn⟩

end Musubi.FineAssembly

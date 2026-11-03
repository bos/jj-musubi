/-
The strict raw-head history window begins at the record cut, before eligible nodes have
learned from it. It must be carried forward to their later entry cut; choosing that later
sequence as a new window would wrongly require every node already to know the latest head.
No node knowledge or packet-sender invariant is needed to grow this history window.
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

theorem history_window_init {s : State} (hp : ParLt s.U.par)
    (hh : s.hub.head < s.U.next) (hist : s.hub.hist s.hub.seq = s.hub.head) :
    HistoryWindow s.hub.seq s := by
  refine ⟨hp, hh, hist, Nat.le_refl _, ?_, ?_⟩
  · intro i j hi hij hj
    have he : i = j := by omega
    rw [he]; exact Anc.refl
  · intro i j hi hij hj; omega

theorem HistoryWindow.withPackets {w : Nat} {s : State} (h : HistoryWindow w s)
    (pk : List Packet) (hb : ∀ p ∈ pk, p.new < s.U.next ∧ p.tag = none) :
    HubSuffix.Inv (fun _ => False) w ⟨s, fun _ => 0, pk⟩ := by
  exact inv_entry h.parLt h.headLt h.histHead h.window h.chain h.strict
    (fun _ he => False.elim he) (fun _ he => False.elim he) hb

theorem HistoryWindow.ofInv {w : Nat} {g : GState}
    (h : HubSuffix.Inv (fun _ => False) w g) : HistoryWindow w g.s :=
  ⟨h.parLt, h.headLt, h.histHead, h.window, h.chain, h.strict⟩

/-- Primitive raw-graph changes after records stop renaming current ids. The node-side
actions are unrestricted here: only their effect on the universe and hub history matters. -/
inductive HistoryStep : State → State → Prop
  | frame {s t : State} (hU : USame s t) (hh : HubSame s t) : HistoryStep s t
  | grow {s t : State} (hU : UExt s t) (hh : HubSame s t) : HistoryStep s t
  | accept {s t : State} (new : Nat) (hn : new < s.U.next)
      (hne : new ≠ s.hub.head) (ha : Anc s.U.par s.hub.head new)
      (hU : USame s t) (hh : t.hub.head = new) (hs : t.hub.seq = s.hub.seq + 1)
      (hist : t.hub.hist = upd s.hub.hist (s.hub.seq + 1) new) : HistoryStep s t

theorem history_step_seq_mono {s t : State} (h : HistoryStep s t) :
    s.hub.seq ≤ t.hub.seq := by
  cases h with
  | frame _ hh | grow _ hh => rw [hh.2.1]; exact Nat.le_refl _
  | accept _ _ _ _ _ _ hs _ => rw [hs]; omega

theorem history_step_saved {s t : State} (h : HistoryStep s t)
    {q : Nat} (hq : q ≤ s.hub.seq) : t.hub.hist q = s.hub.hist q := by
  cases h with
  | frame _ hh | grow _ hh => rw [hh.2.2]
  | accept _ _ _ _ _ _ _ hist => rw [hist, upd_ne _ _ (by omega)]

theorem history_run_seq_mono {run : Nat → State}
    (hs : ∀ i, HistoryStep (run i) (run (i + 1))) {i j : Nat} (hij : i ≤ j) :
    (run i).hub.seq ≤ (run j).hub.seq := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.le_trans ih (history_step_seq_mono (hs (i + d)))

theorem history_run_saved {run : Nat → State}
    (hs : ∀ i, HistoryStep (run i) (run (i + 1))) {i j q : Nat}
    (hij : i ≤ j) (hq : q ≤ (run i).hub.seq) :
    (run j).hub.hist q = (run i).hub.hist q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => rfl
  | succ d ih =>
    have hb := Nat.le_trans hq (history_run_seq_mono hs (Nat.le_add_right i d))
    exact (history_step_saved (hs (i + d)) hb).trans ih

theorem history_window_step {w : Nat} {s t : State}
    (h : HistoryWindow w s) (step : HistoryStep s t) : HistoryWindow w t := by
  cases step with
  | frame hU hh =>
    have hi := h.withPackets [] (by simp)
    have hs : HubSuffix.Step (fun _ => False) w
        ⟨s, fun _ => 0, []⟩ ⟨t, fun _ => 0, []⟩ :=
      .frame hU hh (fun _ he => False.elim he) rfl rfl
    exact HistoryWindow.ofInv (HubSuffix.inv_step hi hs)
  | grow hU hh =>
    have hi := h.withPackets [] (by simp)
    have hs : HubSuffix.Step (fun _ => False) w
        ⟨s, fun _ => 0, []⟩ ⟨t, fun _ => 0, []⟩ :=
      .grow hU hh (fun _ he => False.elim he) rfl rfl
    exact HistoryWindow.ofInv (HubSuffix.inv_step hi hs)
  | accept new hn hne ha hU hh hs hist =>
    let p : Packet := ⟨0, none, s.hub.seq, s.hub.head, new⟩
    have hi := h.withPackets [p] (by
      intro q hq
      have he : q = p := List.mem_singleton.1 hq
      subst q
      exact ⟨hn, rfl⟩)
    have he : HubSuffix.Step (fun _ => False) w
        ⟨s, fun _ => 0, [p]⟩ ⟨t, fun _ => 0, [p]⟩ :=
      .accept p (by simp) rfl hne ha hU hh hs hist (fun _ hf => False.elim hf) rfl rfl
    exact HistoryWindow.ofInv (HubSuffix.inv_step hi he)

theorem history_window_run (run : Nat → State)
    (hp : ParLt (run 0).U.par) (hh : (run 0).hub.head < (run 0).U.next)
    (hist : (run 0).hub.hist (run 0).hub.seq = (run 0).hub.head)
    (hs : ∀ i, HistoryStep (run i) (run (i + 1))) :
    ∀ i, HistoryWindow (run 0).hub.seq (run i) := by
  intro i
  induction i with
  | zero => exact history_window_init hp hh hist
  | succ i ih => exact history_window_step ih (hs i)

/-- An honest reply computed after the cut remains a truthful window pair at delayed
receipt, despite intervening acceptances. This is the history fact the serial handler uses. -/
theorem history_reply_stays_truthful {run : Nat → State}
    (hs : ∀ i, HistoryStep (run i) (run (i + 1)))
    (hw : ∀ i, HistoryWindow (run 0).hub.seq (run i))
    {sent received : Nat} (horder : sent ≤ received) :
    (run 0).hub.seq ≤ (run sent).hub.seq ∧
      (run sent).hub.seq ≤ (run received).hub.seq ∧
      (run received).hub.hist (run sent).hub.seq = (run sent).hub.head :=
  ⟨(hw sent).window, history_run_seq_mono hs horder,
    (history_run_saved hs horder (Nat.le_refl _)).trans (hw sent).histHead⟩

theorem history_step_head_mono {s t : State} (hp : ParLt s.U.par)
    (h : HistoryStep s t) : s.hub.head ≤ t.hub.head ∧
      (s.hub.seq < t.hub.seq → s.hub.head < t.hub.head) := by
  cases h with
  | frame _ hh | grow _ hh =>
    rw [hh.1, hh.2.1]
    exact ⟨Nat.le_refl _, fun h => False.elim (Nat.lt_irrefl _ h)⟩
  | accept new _ hne ha _ hh _ _ =>
    rw [hh]
    have hl := ha.lt_of_ne hp (Ne.symm hne)
    exact ⟨Nat.le_of_lt hl, fun _ => hl⟩

/-- Retired old requests may still reach the hub, independently of live reply slots. Their
finite target set can move a strict raw history only finitely often. They need not drain
from a replayable network to stop affecting the hub. -/
theorem history_old_targets_stop (run : Nat → State) (B : Nat)
    (hp : ∀ i, ParLt (run i).U.par)
    (hs : ∀ i, HistoryStep (run i) (run (i + 1))) :
    ∃ k, ∀ i, k ≤ i → ¬ ((run (i + 1)).hub.head < B ∧
      (run i).hub.seq < (run (i + 1)).hub.seq) := by
  have hm := fun i => history_step_head_mono (hp i) (hs i)
  have hc : ∀ i, B - (run (i + 1)).hub.head ≤ B - (run i).hub.head := by
    intro i
    have := (hm i).1
    omega
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => B - (run i).hub.head) hc
  refine ⟨k, fun i hi ⟨hb, hseq⟩ => ?_⟩
  have hl := (hm i).2 hseq
  have hd : B - (run (i + 1)).hub.head < B - (run i).hub.head := by omega
  rw [hk i hi, hk (i + 1) (by omega)] at hd
  exact Nat.lt_irrefl _ hd

/-- EarlyEntry supplies the window lower bound; the serialized honest response gives the
truthful pair and sequence upper bound. At their common cut, all pre-entry packets get no
current generation, so the strong sender invariant is initially vacuous. -/
theorem history_window_enters_suffix {E : Nat → Prop} {w : Nat} {g : GState}
    (h : HistoryWindow w g.s)
    (hk : ∀ n, E n → w ≤ (g.s.node n).known.1 ∧ (g.s.node n).known.1 ≤ g.s.hub.seq ∧
      g.s.hub.hist (g.s.node n).known.1 = (g.s.node n).known.2)
    (hh : ∀ n, E n → ∀ y, (g.s.node n).heads y → y < g.s.U.next)
    (hpk : ∀ p ∈ g.pk, p.new < g.s.U.next ∧ p.tag = none) : HubSuffix.Inv E w g :=
  inv_entry h.parLt h.headLt h.histHead h.window h.chain h.strict hk hh hpk

end Musubi.Recovery

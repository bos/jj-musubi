/-
The system's cuts on old replies and notifications, derived from its own steps rather than
assumed (`old_replies_stop`, `old_notes_stop`): from some point on, every reply a node takes
and every notification it processes was made at or after a given step. Old ones may stay in
flight forever, never taken: the cuts are on what is taken.

Replies: at the cut every reply in flight has a slot below the slot counter `B` then
(`SysOK`), and a reply made since has a later time. A node waits on one step at a time; a step
it issues since takes slots at the counter or above, which only grows. So a node's wait has a
slot below `B` only if it was issued before the cut, and once that wait's replies are taken it
has none: one credit per node, spent by taking an old reply, and never earned again.

Notifications: removal is exact (`List.erase`), so a node's notifications made before the cut
only ever leave, one each time it processes one, and those made since are later.

With the hub settled at `st` from the cut, no notification is made after it, so every one the
node processes from some point on is the stable hub's. This gives `node_settles_entry` and
`early_entry_sys` without their cut premises (`node_settles_fresh`, `early_entry_fresh`).
-/
import Musubi.NodeSysEntry
import Musubi.AsyncLiveness

namespace Musubi.SysFreshCuts

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry

/-! ## Lists -/

theorem filter_erase_le {α : Type} [DecidableEq α] (p : α → Bool) (a : α) :
    ∀ l : List α, ((l.erase a).filter p).length ≤ (l.filter p).length
  | [] => by simp
  | b :: l => by
    rw [List.erase_cons]
    split
    · simp only [List.filter_cons]
      split <;> simp
    · have ih := filter_erase_le p a l
      simp only [List.filter_cons]
      split <;> simp <;> omega

theorem filter_erase_lt {α : Type} [DecidableEq α] (p : α → Bool) (a : α) (ha : p a = true) :
    ∀ l : List α, a ∈ l → ((l.erase a).filter p).length < (l.filter p).length
  | [], h => absurd h List.not_mem_nil
  | b :: l, h => by
    rw [List.erase_cons]
    split
    · rename_i hb
      have hba : b = a := by simpa using hb
      subst hba
      simp [ha]
    · rename_i hb
      have hne : b ≠ a := by simpa using hb
      have hl : a ∈ l := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hne
        · exact h
      have ih := filter_erase_lt p a ha l hl
      simp only [List.filter_cons]
      split <;> simp <;> omega

/-! ## What a step does to slots, replies and notifications -/

section Steps

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {a : Act} {g g' : Sys}

/-- The slot counter only grows. -/
theorem slot_mono (hs : SysStep N D law a g g') : g.slot ≤ g'.slot := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => exact Nat.le_of_eq hq.slot.symm
  | idle _ _ _ _ _ _ _ hq _ => exact Nat.le_of_eq hq.slot.symm
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => exact Nat.le_of_eq hq.slot.symm
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ hslot' _ _ _ => exact hslot'
  | answer _ _ _ _ _ _ _ hrest _ => exact Nat.le_of_eq hrest.2.2.2.symm
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ =>
    exact Nat.le_of_eq hrest.2.2.2.1.symm
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ => exact Nat.le_of_eq hrest.2.2.2.1.symm
  | ignore _ _ _ _ _ _ _ _ _ hrest _ => exact Nat.le_of_eq hrest.2.2.2.1.symm
  | env _ _ hq _ => exact Nat.le_of_eq hq.slot.symm

/-- A reply made before `t` that is in flight after a step at `t` or later was in flight
before it. -/
theorem reps_old {t : Nat} (hs : SysStep N D law a g g') (ht : t ≤ g.time) :
    ∀ r ∈ g'.reps, r.time < t → r ∈ g.reps := by
  intro r hr hrt
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => rw [hq.reps] at hr; exact hr
  | idle _ _ _ _ _ _ _ hq _ => rw [hq.reps] at hr; exact hr
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => rw [hq.reps] at hr; exact hr
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ => rw [hrest.2.1] at hr; exact hr
  | answer _ _ _ _ _ _ hreps _ _ =>
    rw [hreps, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact hr
    · exact absurd hrt (Nat.not_lt.2 ht)
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps _ _ => exact ((hreps r).1 hr).1
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ => rw [hrest.2.2.1] at hr; exact hr
  | ignore _ _ _ _ _ _ _ _ _ hrest _ => rw [hrest.2.2.1] at hr; exact hr
  | env _ _ hq _ => rw [hq.reps] at hr; exact hr

/-- Node `n` waits on a step with a slot below `B`: issued before the cut. -/
def Old (n B : Nat) (g : Sys) : Prop := ∃ w, (g.node n).wait = some w ∧ ∃ s ∈ w.slots, s < B

/-- One credit while node `n` waits on a step issued before the cut. -/
noncomputable def credit (n B : Nat) (g : Sys) : Nat := by
  classical
  exact if Old n B g then 1 else 0

theorem credit_le {n B : Nat} {g g' : Sys} (h : Old n B g' → Old n B g) :
    credit n B g' ≤ credit n B g := by
  by_cases h' : Old n B g'
  · simp [credit, h', h h']
  · simp [credit, h']

/-- A wait issued before the cut is one there was before the step: a step issued after it,
the slot counter at `B` or above, takes slots from the counter on. -/
theorem old_step {n B : Nat} (hs : SysStep N D law a g g') (hB : B ≤ g.slot) :
    Old n B g' → Old n B g := by
  rintro ⟨w, hw, s, hs', hsB⟩
  by_cases hab : a.about n
  · cases hs with
    | busy m _ _ _ _ _ _ hnode _ _ =>
      simp only [Act.about] at hab; subst hab
      rw [hnode, upd_same] at hw; cases hw
    | idle m _ _ _ _ hnode _ _ _ =>
      simp only [Act.about] at hab; subst hab
      rw [hnode, upd_same] at hw; cases hw
    | maint m _ _ _ _ _ _ _ _ hnode _ _ =>
      simp only [Act.about] at hab; subst hab
      rw [hnode, upd_same] at hw; cases hw
    | issue m k post new emb1 rq _ _ _ _ hslot _ hnode _ _ _ _ _ =>
      simp only [Act.about] at hab; subst hab
      rw [hnode, upd_same] at hw
      cases hw
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hs'
      have := (hslot q hq).2.1
      omega
    | handle m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode _ _ _ =>
      simp only [Act.about] at hab; subst hab
      rw [hnode, upd_same] at hw; cases hw
    | notice m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnode _ _ _ =>
      simp only [Act.about] at hab; subst hab
      rw [hnode, upd_same] at hw; cases hw
    | ignore _ _ _ _ _ _ _ hnode _ _ _ =>
      rw [hnode] at hw
      exact ⟨w, hw, s, hs', hsB⟩
    | answer => exact hab.elim
    | env => exact hab.elim
  · rw [node_unchanged hs hab] at hw
    exact ⟨w, hw, s, hs', hsB⟩

/-- Taking a reply with a slot below `B` spends node `n`'s credit: the reply is one of the
step's it waits on, and once taken it waits on none. -/
theorem take_old {n B : Nat} (hs : SysStep N D law a g g') {r : Rep} (hr : r ∈ g.reps)
    (hr' : r ∉ g'.reps) (hrn : r.node = n) (hB : r.slot < B) : Old n B g ∧ ¬ Old n B g' := by
  cases hs with
  | handle m w rs _ _ _ _ _ _ hw hrs _ _ _ _ _ _ _ hnode hreps _ _ =>
    have hrs' : r ∈ rs := Classical.byContradiction fun h => hr' ((hreps r).2 ⟨hr, h⟩)
    have hm : m = n := ((hrs r hrs').2.1).symm.trans hrn
    subst hm
    refine ⟨⟨w, hw, r.slot, (hrs r hrs').2.2, hB⟩, ?_⟩
    rintro ⟨w', hw', -⟩
    rw [hnode, upd_same] at hw'
    cases hw'
  | answer _ _ _ _ _ _ hreps _ _ =>
    exact absurd (by rw [hreps]; exact List.mem_append_left _ hr) hr'
  | busy _ _ _ _ _ _ _ _ hq _ => exact absurd (by rw [hq.reps]; exact hr) hr'
  | idle _ _ _ _ _ _ _ hq _ => exact absurd (by rw [hq.reps]; exact hr) hr'
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => exact absurd (by rw [hq.reps]; exact hr) hr'
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ =>
    exact absurd (by rw [hrest.2.1]; exact hr) hr'
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ =>
    exact absurd (by rw [hrest.2.2.1]; exact hr) hr'
  | ignore _ _ _ _ _ _ _ _ _ hrest _ => exact absurd (by rw [hrest.2.2.1]; exact hr) hr'
  | env _ _ hq _ => exact absurd (by rw [hq.reps]; exact hr) hr'

/-- Node `n`'s notifications made before `t`. -/
def oldNotes (n t : Nat) (g : Sys) : Nat :=
  (g.notes.filter fun x => x.node == n && decide (x.time < t)).length

/-- A step at `t` or later makes no notification before `t`, and removes one at most: the one
a node processes or drops. -/
theorem oldNotes_step {n t : Nat} (hs : SysStep N D law a g g') (ht : t ≤ g.time) :
    oldNotes n t g' ≤ oldNotes n t g ∧
      ∀ nt, a = .notice n nt → nt.time < t → oldNotes n t g' < oldNotes n t g := by
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ =>
    exact ⟨by simp [oldNotes, hq.notes], fun _ h => by cases h⟩
  | idle _ _ _ _ _ _ _ hq _ =>
    exact ⟨by simp [oldNotes, hq.notes], fun _ h => by cases h⟩
  | maint _ _ _ _ _ _ _ _ _ _ hq _ =>
    exact ⟨by simp [oldNotes, hq.notes], fun _ h => by cases h⟩
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ =>
    exact ⟨by simp [oldNotes, hrest.2.2], fun _ h => by cases h⟩
  | answer _ _ _ _ _ hans _ _ _ =>
    refine ⟨?_, fun _ h => by cases h⟩
    have hn : g'.notes = g.notes ∨
        g'.notes = g.notes ++ (List.range N).map (fun m => ⟨m, g.time, g'.hub⟩) := by
      rcases hans with ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, hn⟩ |
        ⟨p, -, ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩⟩
      all_goals first | exact Or.inl hn | exact Or.inr hn
    rcases hn with hn | hn
    · simp [oldNotes, hn]
    · unfold oldNotes
      rw [hn, List.filter_append, List.length_append]
      have hnil : ((List.range N).map (fun m => (⟨m, g.time, g'.hub⟩ : Note))).filter
          (fun x => x.node == n && decide (x.time < t)) = [] := by
        apply List.filter_eq_nil_iff.2
        intro x hx
        obtain ⟨m, -, rfl⟩ := List.mem_map.1 hx
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _
        exact Nat.not_lt.2 ht
      rw [hnil]
      simp
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ =>
    exact ⟨by simp [oldNotes, hrest.2.2.1], fun _ h => by cases h⟩
  | notice m nt _ _ _ _ _ _ _ hn hnn _ _ _ _ _ _ hnotes _ _ =>
    refine ⟨?_, fun nt' h hlt => ?_⟩
    · unfold oldNotes
      rw [hnotes]
      exact filter_erase_le _ _ _
    · cases h
      unfold oldNotes
      rw [hnotes]
      exact filter_erase_lt _ _ (by simp [hnn, hlt]) _ hn
  | ignore _ _ _ _ _ _ _ _ hnotes _ _ =>
    refine ⟨?_, fun _ h => by cases h⟩
    unfold oldNotes
    rw [hnotes]
    exact filter_erase_le _ _ _
  | env _ _ hq _ => exact ⟨by simp [oldNotes, hq.notes], fun _ h => by cases h⟩

/-- Notifications made from `t` on, while the hub stays at `st`, are the stable hub's: a
stable hub accepts nothing, and makes none. -/
def NotesFrom (t : Nat) (st : Snap) (g : Sys) : Prop :=
  ∀ nt ∈ g.notes, t ≤ nt.time → nt.snap = st

theorem notesFrom_step {t : Nat} {st : Snap} (Nf : NotesFrom t st g)
    (hs : SysStep N D law a g g') (hh : g.hub = st) (hh' : g'.hub = st) :
    NotesFrom t st g' := by
  intro nt hnt ht
  cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => rw [hq.notes] at hnt; exact Nf nt hnt ht
  | idle _ _ _ _ _ _ _ hq _ => rw [hq.notes] at hnt; exact Nf nt hnt ht
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => rw [hq.notes] at hnt; exact Nf nt hnt ht
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ => rw [hrest.2.2] at hnt; exact Nf nt hnt ht
  | answer _ _ _ _ _ hans _ _ _ =>
    rcases hans with ⟨-, -, -, -, hn⟩ | ⟨-, -, -, -, hn⟩ |
      ⟨p, -, ⟨-, -, hg', -, -⟩ | ⟨-, -, -, -, -, hn⟩ | ⟨-, -, -, -, -, hn⟩⟩
    · rw [hn] at hnt; exact Nf nt hnt ht
    · rw [hn] at hnt; exact Nf nt hnt ht
    · exfalso
      rw [hh, hh'] at hg'
      have := congrArg Snap.seq hg'
      simp only at this
      omega
    · rw [hn] at hnt; exact Nf nt hnt ht
    · rw [hn] at hnt; exact Nf nt hnt ht
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ =>
    rw [hrest.2.2.1] at hnt; exact Nf nt hnt ht
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnotes _ _ =>
    rw [hnotes] at hnt; exact Nf nt (List.mem_of_mem_erase hnt) ht
  | ignore _ _ _ _ _ _ _ _ hnotes _ _ =>
    rw [hnotes] at hnt; exact Nf nt (List.mem_of_mem_erase hnt) ht
  | env _ _ hq _ => rw [hq.notes] at hnt; exact Nf nt hnt ht

end Steps

/-! ## The cuts -/

section Cuts

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}

theorem time_from (ρ : Nat → Sys) (acts : Nat → Act) (c : Nat)
    (hstep : ∀ i, c ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1))) :
    ∀ d, (ρ c).time + d = (ρ (c + d)).time := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    have h := (hstep (c + d) (by omega)).time
    show (ρ c).time + (d + 1) = (ρ (c + d + 1)).time
    omega

/-- From some step on, node `n` takes no reply made before step `c`, whichever stay in flight.
Only the slots and reply semantics at `c` (`SysOK`) are used. -/
theorem old_replies_stop (ρ : Nat → Sys) (acts : Nat → Act) (n c : Nat)
    (hstep : ∀ i, c ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1))) (hS : SysOK law (ρ c)) :
    ∃ k1, c ≤ k1 ∧ ∀ i, k1 ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ c).time ≤ r.time := by
  have htime := time_from ρ acts c hstep
  have hslot : ∀ d, (ρ c).slot ≤ (ρ (c + d)).slot := by
    intro d
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih => exact Nat.le_trans ih (slot_mono (hstep (c + d) (by omega)))
  -- replies made before `c` have slots below the counter then
  have hbelow : ∀ d, ∀ r ∈ (ρ (c + d)).reps, r.time < (ρ c).time → r.slot < (ρ c).slot := by
    intro d
    induction d with
    | zero => intro r hr _; exact hS.reps r hr
    | succ d ih =>
      intro r hr hrt
      exact ih r (reps_old (hstep (c + d) (by omega)) (by have := htime d; omega) r hr hrt) hrt
  have hle : ∀ d, credit n (ρ c).slot (ρ (c + (d + 1))) ≤ credit n (ρ c).slot (ρ (c + d)) :=
    fun d => credit_le (old_step (hstep (c + d) (by omega)) (hslot d))
  obtain ⟨d0, hd0⟩ := nat_trace_stabilizes (fun d => credit n (ρ c).slot (ρ (c + d))) hle
  refine ⟨c + d0, by omega, fun i hi r hr hr' hrn => Nat.le_of_not_lt fun hrt => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show c ≤ i by omega)
  obtain ⟨h1, h2⟩ := take_old (hstep (c + d) (by omega)) hr hr' hrn (hbelow d r hr hrt)
  have e1 : credit n (ρ c).slot (ρ (c + d)) = credit n (ρ c).slot (ρ (c + d0)) :=
    hd0 d (by omega)
  have e2 : credit n (ρ c).slot (ρ (c + d + 1)) = credit n (ρ c).slot (ρ (c + d0)) :=
    hd0 (d + 1) (by omega)
  have v1 : credit n (ρ c).slot (ρ (c + d)) = 1 := by simp [credit, h1]
  have v2 : credit n (ρ c).slot (ρ (c + d + 1)) = 0 := by simp [credit, h2]
  omega

/-- From some step on, node `n` processes no notification made before step `c`, whichever
stay in flight. -/
theorem old_notes_stop (ρ : Nat → Sys) (acts : Nat → Act) (n c : Nat)
    (hstep : ∀ i, c ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1))) :
    ∃ k1, c ≤ k1 ∧ ∀ i, k1 ≤ i → ∀ nt, acts i = .notice n nt → (ρ c).time ≤ nt.time := by
  have htime := time_from ρ acts c hstep
  have hstp : ∀ d, oldNotes n (ρ c).time (ρ (c + d + 1)) ≤ oldNotes n (ρ c).time (ρ (c + d)) ∧
      ∀ nt, acts (c + d) = .notice n nt → nt.time < (ρ c).time →
        oldNotes n (ρ c).time (ρ (c + d + 1)) < oldNotes n (ρ c).time (ρ (c + d)) :=
    fun d => oldNotes_step (hstep (c + d) (by omega)) (by have := htime d; omega)
  obtain ⟨d0, hd0⟩ := nat_trace_stabilizes (fun d => oldNotes n (ρ c).time (ρ (c + d)))
    (fun d => (hstp d).1)
  refine ⟨c + d0, by omega, fun i hi nt ha => Nat.le_of_not_lt fun hlt => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show c ≤ i by omega)
  have hl := (hstp d).2 nt ha hlt
  have e1 : oldNotes n (ρ c).time (ρ (c + d)) = oldNotes n (ρ c).time (ρ (c + d0)) :=
    hd0 d (by omega)
  have e2 : oldNotes n (ρ c).time (ρ (c + d + 1)) = oldNotes n (ρ c).time (ρ (c + d0)) :=
    hd0 (d + 1) (by omega)
  omega

/-- Once the hub has settled at `st` at step `k`, every notification made since is the
stable hub's: there are none. -/
theorem notes_from_stable (ρ : Nat → Sys) (acts : Nat → Act) (k : Nat) (st : Snap)
    (hstep : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (hT : TimeOK (ρ k)) (hstable : ∀ i, k ≤ i → (ρ i).hub = st) :
    ∀ i, k ≤ i → NotesFrom (ρ k).time st (ρ i) := by
  intro i hi
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => intro nt hnt ht; exact absurd (hT.notes nt hnt) (Nat.not_lt.2 ht)
  | succ d ih =>
    exact notesFrom_step (ih (by omega)) (hstep (k + d) (by omega)) (hstable _ (by omega))
      (hstable _ (by omega))

theorem fair_mono {ρ : Nat → Sys} {acts : Nat → Act} {n a b : Nat} (hf : Fair ρ acts n a)
    (hab : a ≤ b) : Fair ρ acts n b :=
  ⟨fun i hi => hf.start i (by omega), fun i hi => hf.core i (by omega),
    fun i hi => hf.reply i (by omega)⟩

/-- `node_settles_entry` with its cuts derived: node `n` in the system, from a well-formed
start, once the hub has settled at `st`, under fair scheduling of its events and housekeeping
that writes stopping, settles at the stable hub's head under a label `H` of it, or sends a push
from it that the stable hub would accept. No cut on old replies or notifications is assumed;
they may stay in flight forever. -/
theorem node_settles_fresh (ρ : Nat → Sys) (acts : Nat → Act) (n k0 k kf : Nat) (st : Snap)
    (hstep : ∀ i, k0 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : RunOK law D n (ρ k0)) (hk : k0 ≤ k) (hstable : ∀ i, k ≤ i → (ρ i).hub = st)
    (hfair : Fair ρ acts n kf) (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint) :
    ∃ k' H, k < k' ∧ H < ((ρ k').node n).ns.next ∧ ((ρ k').node n).emb H = st.head ∧
      ((∃ i, k' ≤ i ∧ labOf n ⟨st.seq, H, st.recs, D n⟩ (ρ i) (acts i) = .emit ∧
          ∃ post new, Emit ⟨st.seq, H, st.recs, D n⟩ ((ρ i).node n).ns post new) ∨
        ∃ K, ∀ i, K ≤ i → NodeSettle.Settled ⟨st.seq, H, st.recs, D n⟩ ((ρ i).node n).ns) := by
  have hK := runOK_run ρ acts hstep h0
  have hstepk : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)) :=
    fun i hi => hstep i (by omega)
  obtain ⟨kr, hkr, hold⟩ := old_replies_stop ρ acts n k hstepk (hK k hk).sys
  obtain ⟨kn, hkn, hnold⟩ := old_notes_stop ρ acts n k hstepk
  have hNf := notes_from_stable ρ acts k st hstepk (hK k hk).time hstable
  have hnotes : ∀ i, kr + kn + kf ≤ i → ∀ nt, acts i = .notice n nt → nt.snap = st := by
    intro i hi nt ha
    have hs := hstep i (by omega)
    rw [ha] at hs
    cases hs with
    | notice _ _ _ _ _ _ _ _ _ hn =>
      exact hNf i (by omega) nt hn (hnold i (by omega) nt ha)
  obtain ⟨k', H, hk', hrest⟩ := node_settles_entry ρ acts n k0 k (kr + kn + kf) st hstep h0 hk
    (by omega) hstable (fun i hi => hold i (by omega)) hnotes (fair_mono hfair (by omega))
    hmaint
  exact ⟨k', H, by omega, hrest⟩

/-- `early_entry_sys` with its cuts derived: after the record cut at `kr` (the hub's records
`R` and its sequence at least `sq` from then on), a fair eligible node comes to have `R`
applied and to know a pair from after the cut, and keeps both. No cut on old replies or
notifications is assumed. -/
theorem early_entry_fresh (ρ : Nat → Sys) (acts : Nat → Act) (n k0 kr kf R sq : Nat)
    (hstep : ∀ i, k0 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : RunOK law D n (ρ k0)) (hk : k0 ≤ kr)
    (hrec : ∀ i, kr ≤ i → (ρ i).hub.recs = R ∧ sq ≤ (ρ i).hub.seq)
    (hE : ∀ i, kf ≤ i → ¬ ∃ y ∈ ((ρ i).node n).ns.heads, D n R y)
    (hfair : Fair ρ acts n kf) (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint) :
    ∃ k, kr ≤ k ∧ ∀ i, k ≤ i → Entry R sq ((ρ i).node n).ns := by
  have hK := runOK_run ρ acts hstep h0
  have hstepk : ∀ i, kr ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)) :=
    fun i hi => hstep i (by omega)
  obtain ⟨kc, hkc, hold⟩ := old_replies_stop ρ acts n kr hstepk (hK kr hk).sys
  obtain ⟨kn, hkn, hnold⟩ := old_notes_stop ρ acts n kr hstepk
  obtain ⟨k, hk1, hent⟩ := early_entry_sys ρ acts n k0 kr (kc + kn + kf) R sq hstep h0 hk
    (by omega) hrec (fun i hi => hold i (by omega)) (fun i hi => hnold i (by omega))
    (fun i hi => hE i (by omega)) (fair_mono hfair (by omega)) hmaint
  exact ⟨k, by omega, hent⟩

end Cuts

end Musubi.SysFreshCuts

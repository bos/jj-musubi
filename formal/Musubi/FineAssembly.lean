/-
What the eligible nodes' system takes from the fine cut on (`FineAt`), assembled from the
replay of observed native events (`NativeEvents.observedRun`) and named per-call laws: the
steps are the replay's (`observed_hs`); replies and notifications are honest by an invariant
of the run, not by a law of each step; each push's lawful decision is the decision event's that
removed it (`Event.removed_eligible_push`); and maintenance laws are vacuous, with automatic
writes, housekeeping among them, past.

What stays primitive on the way to `hive_converges_observed`, by where it is stated:
- `HiveContracts`: the record and drop effects (`recStep` … `nodeBound`, `epochStep`); the
  per-call laws of the sampled runs (`entry`, `pending`, and `reopenWhy`, `incHead`, `closure`,
  `keep`); local correspondence of the observation (`inboxStep`, `callIds`, `ownHead`,
  `noteHead`, `notesOld`, `doneIn`, `quietKnown`, `clock`, `maintBind`, `noteBind`, `replyBind`,
  `freshOwn`, `rootSeq`, the `latch` laws, `hubSeqStep`, `histBind`, `answer`, `readyKeep`,
  `readyFail`); the environment (`envFinal`, `failFinal`, `autoWritesStop`, `userFinal`); and
  scheduling (`schedMono`, `idleStart`, `startCore`).
- `hive_converges_observed`'s record bindings: the native records' identity and custody
  (`views`, `NativeEvents.RecordView`), the hub's records at the cut (`hubRecs`), and, past the
  cut, quiet and with no environment loss, the `Sys` hub's records changing only with the native
  records or their pruned prefix (`hubRecsStep`, a local effect law, no encoding of records as a
  whole).
- `FineSource`, at the fine cut: the replay (`events`, `replay`, `replayActs`) and each event's
  bindings (`binds`: per event, the call's decision as a correspondence obligation, `Issue`,
  `Handle`, `Loc`, `Idle`, `HeadRep`, with the structural check `growB` and the batch's slots);
  the snapshot (`hE0` … `hnodup`, `honest0`); the raw graph acyclic (`hd`); the native advance
  (`advance`); each push's lawful decision (`decide`); and fairness (`hf`, `hq`).
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

/-- A step that is no answer moves no hub, adds no reply and no notification. -/
theorem quiet_sub {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {act : Act}
    {g g' : Sys} (hs : SysStep N D law act g g') (ha : act ≠ .answer) :
    g'.hub = g.hub ∧ (∀ r ∈ g'.reps, r ∈ g.reps) ∧ (∀ nt ∈ g'.notes, nt ∈ g.notes) ∧
      g'.time = g.time + 1 := by
  refine ⟨step_hub_quiet hs ha, ?_, ?_, hs.time⟩ <;> cases hs with
  | busy _ _ _ _ _ _ _ _ hq _ => first | (rw [hq.reps]; exact fun _ h => h)
                                       | (rw [hq.notes]; exact fun _ h => h)
  | idle _ _ _ _ _ _ _ hq _ => first | (rw [hq.reps]; exact fun _ h => h)
                                     | (rw [hq.notes]; exact fun _ h => h)
  | maint _ _ _ _ _ _ _ _ _ _ hq _ => first | (rw [hq.reps]; exact fun _ h => h)
                                            | (rw [hq.notes]; exact fun _ h => h)
  | issue _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrest _ _ =>
    first | (rw [hrest.2.1]; exact fun _ h => h) | (rw [hrest.2.2]; exact fun _ h => h)
  | answer => exact absurd rfl ha
  | handle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hreps hrest _ =>
    first | exact fun r h => ((hreps r).1 h).1 | (rw [hrest.2.2.1]; exact fun _ h => h)
  | notice _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnotes hrest _ =>
    first
      | (rw [hrest.2.2.1]; exact fun _ h => h)
      | (rw [hnotes]; exact fun _ h => List.mem_of_mem_erase h)
  | ignore _ _ _ _ _ _ _ _ hnotes hrest _ =>
    first
      | (rw [hrest.2.2.1]; exact fun _ h => h)
      | (rw [hnotes]; exact fun _ h => List.mem_of_mem_erase h)
  | env _ _ hq _ => first | (rw [hq.reps]; exact fun _ h => h) | (rw [hq.notes]; exact fun _ h => h)

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
    obtain ⟨hh, hr, hn, ht⟩ := quiet_sub hs hna
    exact frame hh (fun r h => Or.inl (hr r h)) hn ht
  | env hs =>
    obtain ⟨hh, hr, hn, ht⟩ := quiet_sub hs (by intro h; cases h)
    exact frame hh (fun r h => Or.inl (hr r h)) hn ht
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
    cases hs with
    | answer r ans hr hreqs acc hans hreps hrest ht =>
      -- the snapshot the reply carries is the hub's before (it stays) or after (an accept)
      have hnew : ∀ x : Rep, x ∈ g'.reps →
          x ∈ g.reps ∨ x = ⟨r.node, r.slot, g.time, r.body, acc, ans⟩ := by
        intro x hx
        rw [hreps, List.mem_append, List.mem_singleton] at hx
        exact hx
      rcases hans with ⟨-, -, rfl, hh, hn⟩ | ⟨-, -, rfl, hh, hn⟩ |
          ⟨p, -, (⟨-, -, hh, rfl, hn⟩ | ⟨-, -, -, rfl, hh, hn⟩ | ⟨-, -, -, rfl, hh, hn⟩)⟩
      · -- a `Fetched`: the hub's snapshot, the hub unmoved
        have hhist : nextHistory g g' hist = hist := nextHistory_quiet hist hh
        rw [hhist]
        refine ⟨by rw [hh]; exact H.window, by rw [hh]; exact H.head, by omega, ?_, ?_⟩
        · intro x hx hE ht' s hs'
          rcases hnew x hx with hx | rfl
          · exact honestSnap_mono (H.reps x hx hE ht' s hs') (Nat.le_of_eq (by rw [hh]))
              fun _ _ => rfl
          · rcases hs' with hs' | hs'
            · cases hs'
              exact ⟨H.window, Nat.le_of_eq (by rw [hh]), H.head⟩
            · cases hs'
        · intro nt hn' hE ht'
          rw [hn] at hn'
          exact honestSnap_mono (H.notes nt hn' hE ht') (Nat.le_of_eq (by rw [hh])) fun _ _ => rfl
      · -- a `GetObjects` answer carries no snapshot
        have hhist : nextHistory g g' hist = hist := nextHistory_quiet hist hh
        rw [hhist]
        refine ⟨by rw [hh]; exact H.window, by rw [hh]; exact H.head, by omega, ?_, ?_⟩
        · intro x hx hE ht' s hs'
          rcases hnew x hx with hx | rfl
          · exact honestSnap_mono (H.reps x hx hE ht' s hs') (Nat.le_of_eq (by rw [hh]))
              fun _ _ => rfl
          · rcases hs' with hs' | hs' <;> cases hs'
        · intro nt hn' hE ht'
          rw [hn] at hn'
          exact honestSnap_mono (H.notes nt hn' hE ht') (Nat.le_of_eq (by rw [hh])) fun _ _ => rfl
      · -- an accept: the new snapshot, which the history records
        have hlt : g.hub.seq < g'.hub.seq := by rw [hh]; exact Nat.lt_succ_self _
        have hhist : nextHistory g g' hist = upd hist g'.hub.seq g'.hub.head := by
          simp [nextHistory, hlt]
        have hagree : ∀ x, x ≤ g.hub.seq → nextHistory g g' hist x = hist x :=
          fun x hx => nextHistory_agree x hx
        have hwin : w ≤ g'.hub.seq := by have := H.window; omega
        have hnewSnap : HonestSnap w (nextHistory g g' hist) g' g'.hub := by
          refine ⟨hwin, Nat.le_refl _, ?_⟩
          rw [hhist, upd_same]
        refine ⟨hwin, by rw [hhist, upd_same], by omega, ?_, ?_⟩
        · intro x hx hE ht' s hs'
          rcases hnew x hx with hx | rfl
          · exact honestSnap_mono (H.reps x hx hE ht' s hs') (Nat.le_of_lt hlt) hagree
          · rcases hs' with hs' | hs'
            · cases hs'
            · cases hs'
              exact hnewSnap
        · intro nt hn' hE ht'
          rw [hn, List.mem_append] at hn'
          rcases hn' with hn' | hn'
          · exact honestSnap_mono (H.notes nt hn' hE ht') (Nat.le_of_lt hlt) hagree
          · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hn'
            exact hnewSnap
      · -- a refusal carries records, not a snapshot
        have hhist : nextHistory g g' hist = hist := nextHistory_quiet hist hh
        rw [hhist]
        refine ⟨by rw [hh]; exact H.window, by rw [hh]; exact H.head, by omega, ?_, ?_⟩
        · intro x hx hE ht' s hs'
          rcases hnew x hx with hx | rfl
          · exact honestSnap_mono (H.reps x hx hE ht' s hs') (Nat.le_of_eq (by rw [hh]))
              fun _ _ => rfl
          · rcases hs' with hs' | hs' <;> cases hs'
        · intro nt hn' hE ht'
          rw [hn] at hn'
          exact honestSnap_mono (H.notes nt hn' hE ht') (Nat.le_of_eq (by rw [hh])) fun _ _ => rfl
      · -- a rejection with the hub's head: its snapshot, the hub unmoved
        have hhist : nextHistory g g' hist = hist := nextHistory_quiet hist hh
        rw [hhist]
        refine ⟨by rw [hh]; exact H.window, by rw [hh]; exact H.head, by omega, ?_, ?_⟩
        · intro x hx hE ht' s hs'
          rcases hnew x hx with hx | rfl
          · exact honestSnap_mono (H.reps x hx hE ht' s hs') (Nat.le_of_eq (by rw [hh]))
              fun _ _ => rfl
          · rcases hs' with hs' | hs'
            · cases hs'
            · cases hs'
              exact ⟨H.window, Nat.le_of_eq (by rw [hh]), H.head⟩
        · intro nt hn' hE ht'
          rw [hn] at hn'
          exact honestSnap_mono (H.notes nt hn' hE ht') (Nat.le_of_eq (by rw [hh])) fun _ _ => rfl

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

/-! ## The fine system, assembled -/

/-- What the eligible nodes' system from the fine cut `k` takes, as the replay of observed native
events (`events`, from the actual state at `k`), each bound to its own data
(`Event.Binds`), and the laws no event's data carries, each named by its source:
- the snapshot at `k` (`hE0` … `hnodup`, and `honest0`: replies and notifications answered to
  eligible nodes from `t0` on are honest, with the hub's head the history's at its sequence);
- the raw graph acyclic (`hd`, a native contract: parents exist before their children);
- the eligible nodes' native full-frontier advance (`advance`), a per-call correspondence
  obligation of an `advance_to` call that makes no other semantic write (its working-copy
  cleanup writing nothing: no automatic write of the node then, `auto`, which the hive's cut
  excludes);
- each push decision event, the adapter's lawful decision of that very packet (`decide`: its
  handling in the executable model and the primitives of that same decision);
- fairness (`hf`, `hq`).
The steps, honest replies and notifications, decisions for every removed push, and the
maintenance laws are not fields: `fineAt_of` derives them, from the facts that the hub's records
stay, and no eligible node has pending drops, adopts, makes an automatic write, or takes replies
and notifications from before `t0`, which the hive derives (`hive_converges_observed`). -/
structure FineSource (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    [DecidablePred E] (run : Nat → Sys) (acts : Nat → Act) (k w : Nat) (initial : Nat → Nat)
    (t0 : Nat) (auto : Nat → Nat → Prop) where
  rawRoot : Nat
  M : Nat
  decode : Nat → List Exec.Rec
  events : Nat → Event
  replay : ∀ i, run (k + i) = observedRun N law (run k) events i
  replayActs : ∀ i, acts (k + i) = (events i).act
  binds : ∀ i, (events i).Binds N D law E (run k).reqs (run (k + i))
  hE0 : ∀ n, E n → NodeSys.NodeOK D n (run k) ∧ ObjsOK n (run k)
  hsys : SysOK law (run k)
  htime : TimeOK (run k)
  hans : ∀ r ∈ (run k).reps, r.req = .objs → r.ans = .objects
  hroot : rawRoot < (run k).next
  hpar : (run k).par rawRoot = []
  hb : RequestBounds (run k)
  hi : Recovery.HistoryWindow w (state (run k) initial)
  hnodup : ∀ n, E n → HeadsNodup (run k) n
  honest0 : Honest E w t0 initial (run k)
  hd : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x
  advance : ∀ i, k ≤ i → ∀ n, E n → acts i = .core n .busy → ¬ auto n i →
    AdvGuard ((run i).node n).ns → FullAdv ((run i).node n).ns ((run (i + 1)).node n).ns
  decide : ∀ j q P c, events j = .push q P c →
    Nonempty (LawfulDecision M decode (run (k + j)) (run (k + j + 1)) P)
  hf : ∀ n, E n → ∃ kf, Fair (fun j => run (k + j)) (fun j => acts (k + j)) n kf
  hq : ∀ n, E n → PushFair (fun j => run (k + j)) (fun j => acts (k + j)) n 0

/-- The replay's steps, read on the actual run. -/
theorem FineSource.steps {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {run : Nat → Sys} {acts : Nat → Act} {k w : Nat}
    {initial : Nat → Nat} {t0 : Nat} {auto : Nat → Nat → Prop}
    (S : FineSource N D law E run acts k w initial t0 auto) :
    ∀ j, HiveStep N D law E (run k).reqs (acts (k + j)) (run (k + j)) (run (k + j + 1)) := by
  have h0 := runOK_filt_init (E := E) (old := (run k).reqs) S.hE0 S.hsys S.htime S.hans
    S.hroot S.hpar
  have hb : ∀ i, (S.events i).Binds N D law E (run k).reqs
      (observedRun N law (run k) S.events i) := fun i => S.replay i ▸ S.binds i
  intro j
  rw [S.replayActs j, S.replay j, show k + j + 1 = k + (j + 1) from rfl, S.replay (j + 1)]
  exact observed_hs (run k) S.events (fun _ => dummy S.rawRoot) h0 hb j

/-- The fine system's premises, from the replay and the laws `FineSource` names, given that no
eligible node makes an automatic write (`hnoAuto`), so each advance's cleanup writes nothing, the
hub's records stay (`hr`), no eligible node has pending drops (`pending`), adopts (`applied`) or
does housekeeping (`hm`), and an eligible node takes only head-bearing replies answered, and
notifications naming a state, from `t0` on (`takes`, `notes`). -/
def fineAt_of {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {run : Nat → Sys} {acts : Nat → Act} {k w : Nat}
    {initial : Nat → Nat} {t0 : Nat} {auto : Nat → Nat → Prop}
    (S : FineSource N D law E run acts k w initial t0 auto)
    (hnoAuto : ∀ i, k ≤ i → ∀ n, E n → ¬ auto n i)
    (hr : ∀ i, k ≤ i → (run i).hub.recs = (run k).hub.recs)
    (pending : ∀ i, k ≤ i → ∀ n, E n → ((run i).node n).ns.pending = [])
    (applied : ∀ i, k ≤ i → ∀ n, E n → ((run (i + 1)).node n).ns.ap = ((run i).node n).ns.ap)
    (hm : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint)
    (takes : ∀ i, k ≤ i → ∀ r ∈ (run i).reps, r ∉ (run (i + 1)).reps → E r.node →
      (∃ s, r.ans = .fetched s ∨ r.ans = .head s) → t0 ≤ r.time)
    (notes : ∀ i, k ≤ i → ∀ n nt, acts i = .notice n nt → E n → t0 ≤ nt.time + 1) :
    FineAt N D law E run acts k w initial := by
  have hsteps := S.steps
  have honest := honest_run (fun j => run (k + j)) (fun j => acts (k + j)) initial hsteps
    S.honest0
  refine ⟨S.rawRoot, S.M, S.decode, ?_, S.hE0, S.hsys, S.htime, S.hans, S.hroot, S.hpar, S.hd,
    S.hb, S.hi, ?_, hm, S.hnodup, hr, S.hf, S.hq, ?_⟩
  · intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    exact hsteps j
  · intro i
    refine ⟨fun n hE => pending (k + i) (by omega) n hE,
      fun n hE _ => applied (k + i) (by omega) n hE,
      fun n hE ha hg => S.advance (k + i) (by omega) n hE ha (hnoAuto (k + i) (by omega) n hE) hg,
      fun n hE ha => absurd ha (hm (k + i) (by omega) n hE), ?_, ?_⟩
    · intro n hE r hr hr' hn s hs
      have hEr : E r.node := hn ▸ hE
      exact (honest i).reps r hr hEr (takes (k + i) (by omega) r hr hr' hEr ⟨s, hs⟩) s hs
    · intro n hE nt ha
      obtain ⟨hin, hnn⟩ := notice_mem (ha ▸ hsteps i)
      exact (honest i).notes nt hin (hnn ▸ hE) (notes (k + i) (by omega) n nt ha hE)
  · -- every removed push is its decision event's (`observed_decisions`)
    intro n hE j q hq hq' hn P hP
    have hb : ∀ i, (S.events i).Binds N D law E (run k).reqs
        (observedRun N law (run k) S.events i) := fun i => S.replay i ▸ S.binds i
    have hd : ∀ i q P c, S.events i = .push q P c → Nonempty (LawfulDecision S.M S.decode
        (observedRun N law (run k) S.events i) (observedRun N law (run k) S.events (i + 1)) P) := by
      intro i q P c he
      rw [← S.replay i, ← S.replay (i + 1)]
      exact S.decide i q P c he
    have h := observed_decisions (run k) S.events S.M S.decode hb hd n hE j q
      (by rw [← S.replay j]; exact hq) (by rw [← S.replay (j + 1)]; exact hq') hn P hP
    rw [S.replay j, show k + j + 1 = k + (j + 1) from rfl, S.replay (j + 1)]
    exact h

/-- The record view's bindings hold from any later time too. -/
theorem recordView_mono {ρ α : Type} {N k k' : Nat} {run : Nat → Sys}
    {recs : Nat → Exec.SEState} {O : HiveObs ρ α} {label : ρ → Nat}
    {decode : Nat → List Exec.Rec} {origin : Nat → Nat → Nat → Nat}
    (V : RecordView N k run recs O label decode origin) (h : k ≤ k') :
    RecordView N k' run recs O label decode origin :=
  ⟨fun n i hn hi => V.applied n i hn (by omega), fun n i hn hi => V.records n i hn (by omega),
    fun n i hn hi => V.custody n i hn (by omega)⟩

/-- A node's sampled events start in order. -/
theorem sched_le {ρ α : Type} {O : HiveObs ρ α} {n : Nat}
    (hmono : ∀ p, O.sched n p < O.sched n (p + 1)) {p q : Nat} (h : p ≤ q) :
    O.sched n p ≤ O.sched n q := by
  induction q with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ q ih =>
    rcases Nat.lt_or_ge p (q + 1) with hp | hp
    · exact Nat.le_trans (ih (by omega)) (Nat.le_of_lt (hmono q))
    · rw [Nat.le_antisymm h hp]; exact Nat.le_refl _

/-- An event whose batch completes after another's started after it: batches complete before
the next event. -/
theorem later_event {ρ α : Type} {O : HiveObs ρ α} {n : Nat}
    (hmono : ∀ p, O.sched n p < O.sched n (p + 1))
    (hdone : ∀ p, O.sched n p ≤ O.doneAt n (O.sched n p) ∧
      O.doneAt n (O.sched n p) + 1 < O.sched n (p + 1)) {p q : Nat}
    (h : O.doneAt n (O.sched n q) < O.doneAt n (O.sched n p)) : O.sched n q < O.sched n p := by
  rcases Nat.lt_or_ge q p with hqp | hqp
  · exact Nat.lt_of_lt_of_le (hmono q) (sched_le hmono hqp)
  · exfalso
    rcases Nat.lt_or_ge p q with hpq | hpq
    · have h1 := (hdone p).2
      have h2 := sched_le hmono (show p + 1 ≤ q by omega)
      have h3 := (hdone q).1
      omega
    · rw [Nat.le_antisymm hqp hpq] at h
      exact Nat.lt_irrefl _ h

open Musubi.EarlyEntry.Control in
/-- The hive converges (`hive_converges`), what its eligible nodes' system takes at each fine cut
the proof chooses being the replay of observed native events with the laws `FineSource` names
(`fineAt_of`): no `FineAt`, and no trace of system steps, is a premise. What `fineAt_of` takes
besides is derived here: no eligible node makes an automatic write, its housekeeping and an
advance's cleanup included (`QuietAt`, and `maintBind` for housekeeping steps); it takes only
notifications naming a state from the cut on (`noteBind` and the old-effects cut `OldGone`); only
head-bearing replies answered from the cut on, its batch then being one of an event after that
cut's own (`replyBind`, `OldGone`, `doneIn`, `schedMono`), for a call made from the cut on; an
eligible node has no pending drops and adopts nothing (`RecordView`'s `pending_empty` and
`applied_stays`, through the native records' identity and custody `views`, with the hub's records
the cut's, `hubRecs`, and raw entry); and the hub's records in the `Sys` model stay: past the cut,
quiet and with no environment loss (`QuietAt`), they change only at an event that changes the
native records or their pruned prefix (`hubRecsStep`), which the cut fixes. -/
theorem hive_converges_observed {ρ α : Type} [DecidableEq ρ] {N : Nat}
    {D : Nat → Nat → Nat → Prop} {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act}
    {recs : Nat → Exec.SEState} {B : Nat} {epoch : Nat → Nat → Retry.Records.State}
    {adopts fails : Nat → Nat → Bool} {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat}
    {O : HiveObs ρ α}
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    (label : ρ → Nat) (decodeR : Nat → List Exec.Rec) (origin : Nat → Nat → Nat → Nat)
    (views : ∀ k, CutAt N recs adopts fails k → RecordView N k run recs O label decodeR origin)
    (hubRecs : ∀ k, CutAt N recs adopts fails k → (recs k).recs = decodeR (label (Rof k)))
    (hubRecsStep : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ i, k ≤ i →
      (run (i + 1)).hub.recs = (run i).hub.recs ∨
        ((recs (i + 1)).recs, (recs (i + 1)).pruned) ≠ ((recs i).recs, (recs i).pruned))
    (fine : ∀ k k4, CutAt N recs adopts fails k → QuietAt N O k → k ≤ k4 →
      (∀ n, n < N → ∀ i, k4 ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
      (∃ kG, OldGone N O k kG ∧ ∀ n, n < N → ∃ q, kG ≤ O.sched n q ∧
        O.doneAt n (O.sched n q) < k4 ∧ O.active n (O.sched n q) = true ∧
        ∀ i, O.sched n q ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
      FineSource N D law (EligibleAt N recs k) run acts k4 (run k).hub.seq O.hist k O.autoWrite) :
    ∃ K cut, K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, n < N → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, heads (run i) n x ↔ x = (run K).hub.head := by
  refine hive_converges C fun k k4 hcut hq hle hent hcore => ?_
  obtain ⟨kG, hG, hev⟩ := hcore
  -- no eligible node does housekeeping from the cut, an automatic write
  have hm : ∀ i, k4 ≤ i → ∀ n, EligibleAt N recs k n → acts i ≠ .core n .maint :=
    fun i hi n hE ha => hq.2.1 n hE.1 i (by omega) (C.maintBind n i hE.1 ha)
  -- no automatic write from the cut, inline cleanup and prelude writes included
  have hnoAuto : ∀ i, k4 ≤ i → ∀ n, EligibleAt N recs k n → ¬ O.autoWrite n i :=
    fun i hi n hE => hq.2.1 n hE.1 i (by omega)
  -- the old-effects cut is before each node's completed event, so before `k4`
  have hGle : ∀ n, n < N → kG < k4 := by
    intro n hn
    obtain ⟨q, h1, h2, -⟩ := hev n hn
    have := (C.doneIn n q hn).1
    omega
  have notes : ∀ i, k4 ≤ i → ∀ n nt, acts i = .notice n nt → EligibleAt N recs k n →
      k ≤ nt.time + 1 := by
    intro i hi n nt ha hE
    exact (hG n hE.1 i (by have := hGle n hE.1; omega)).2 _ (C.noteBind n i nt hE.1 ha)
  have takes : ∀ i, k4 ≤ i → ∀ r ∈ (run i).reps, r ∉ (run (i + 1)).reps →
      EligibleAt N recs k r.node → (∃ s, r.ans = .fetched s ∨ r.ans = .head s) →
      k ≤ r.time := by
    intro i hi r hr hr' hE hhd
    obtain ⟨p, t, id, a, hdone, hpt, hown, hcall⟩ :=
      C.replyBind k hcut hq i r (by omega) hr hr' hE.1 hhd
    obtain ⟨q, hGq, hq4, -, -⟩ := hev r.node hE.1
    have hlt : O.sched r.node q < O.sched r.node p :=
      later_event (C.schedMono r.node) (fun p => C.doneIn r.node p hE.1) (by omega)
    exact Nat.le_trans ((hG r.node hE.1 t (by omega)).1 id a hown) hcall
  -- the hub's records stay: each step past the cut keeps them, the native records being fixed
  have hstep : ∀ i, k ≤ i → (run (i + 1)).hub.recs = (run i).hub.recs := by
    intro i hi
    refine (hubRecsStep k hcut hq i hi).resolve_right fun hne => hne ?_
    rw [(hcut.1 (i + 1) (by omega)).1, (hcut.1 i hi).1]
  have hr : ∀ i, k4 ≤ i → (run i).hub.recs = (run k4).hub.recs := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction d with
    | zero => rfl
    | succ d ih => rw [← Nat.add_assoc, hstep _ (by omega), ih (by omega)]
  -- no pending drops and no adoption, through the native records' view
  have V := recordView_mono (views k hcut) hle
  have pending := V.pending_empty hle hcut.1 (hubRecs k hcut) hent
  have applied := V.applied_stays hent
  exact ⟨fineAt_of (fine k k4 hcut hq hle hent ⟨kG, hG, hev⟩) hnoAuto hr
    (fun i hi n hE => pending n hE i hi) (fun i hi n hE => applied n hE.1 i hi) hm takes notes⟩

end Musubi.FineAssembly

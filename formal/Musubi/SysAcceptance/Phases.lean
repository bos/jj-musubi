/-
The successive suffixes used by hive convergence, derived from `HiveContracts`: quiet records,
persistent entry, fresh knowledge, a completed active sample, and eligibility on a stable hub.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance.Contracts
import Musubi.SysAcceptance.Eligible
import Musubi.SysAcceptance.Pending
import Musubi.Schedule

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-- With nothing lost between, the hub's sequence does not go back. -/
theorem seq_chain {run : Nat → Sys} {lost : Nat → Prop}
    (hmono : ∀ t, ¬ lost t → (run t).hub.seq ≤ (run (t + 1)).hub.seq) {a t : Nat}
    (hat : a ≤ t) (hno : ∀ s, a ≤ s → s < t → ¬ lost s) :
    (run a).hub.seq ≤ (run t).hub.seq := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hat
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega) fun s h1 h2 => hno s h1 (by omega))
      (hmono _ (hno _ (by omega) (by omega)))

section Phases

open Musubi.EarlyEntry.Control

variable {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}

/-- From any hive time `c`, a node stops handling own replies to calls it made before `c` and
notices published before `c`: each old call has its slot, which a reply or a reopen retires
(`Retry.old_slots_eventually_stop`, reopens allowed), and old notices are finitely many in
flight and queued (`Retry.Notifications.old_notifications_stop`). Old traffic need not drain
fairly. -/
theorem old_effects_stop
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    (c n : Nat) (hn : n < N) :
    ∃ T, c ≤ T ∧ ∀ t, T ≤ t → (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
      ∀ a, O.note n t = some a → c ≤ a := by
  let c' := (O.inbox n c).next
  have hstep : ∀ i, ∃ b, Retry.InboxStep c' (O.inbox n (c + i)) (O.inbox n (c + i + 1)) b ∧
      ∀ id a, O.own n (c + i) = some (id, a) → id < c' → b = true :=
    fun i => C.inboxStep c' n (c + i) hn
  let old := fun i => Classical.choose (hstep i)
  have hold : ∀ i, Retry.InboxStep c' (O.inbox n (c + i)) (O.inbox n (c + i + 1)) (old i) ∧
      ∀ id a, O.own n (c + i) = some (id, a) → id < c' → old i = true :=
    fun i => Classical.choose_spec (hstep i)
  obtain ⟨replyCutOffset, repliesStopped⟩ := Retry.old_slots_eventually_stop c'
    (fun i => O.inbox n (c + i)) old (Nat.le_refl _) (fun i => (hold i).1)
  have nstep : ∀ i, ∃ h, Retry.Notifications.Step (O.oldNotes c n (c + i))
      (O.oldNotes c n (c + i + 1)) h ∧ ∀ a, O.note n (c + i) = some a → a < c → h = true :=
    fun i => C.notesOld c n (c + i) hn (by omega)
  let oldN := fun i => Classical.choose (nstep i)
  have holdN : ∀ i, Retry.Notifications.Step (O.oldNotes c n (c + i))
      (O.oldNotes c n (c + i + 1)) (oldN i) ∧
      ∀ a, O.note n (c + i) = some a → a < c → oldN i = true :=
    fun i => Classical.choose_spec (nstep i)
  obtain ⟨noticeCutOffset, noticesStopped⟩ := Retry.Notifications.old_notifications_stop
    (fun i => O.oldNotes c n (c + i)) oldN (fun i => (holdN i).1)
  refine ⟨c + max replyCutOffset noticeCutOffset, by omega,
    fun t ht => ⟨fun id a h => ?_, fun a h => ?_⟩⟩
  · obtain ⟨d, rfl⟩ : ∃ d, t = c + d := ⟨t - c, by omega⟩
    have hid : c' ≤ id := Nat.le_of_not_lt fun hlt => by
      have hb := (hold d).2 id a h hlt
      rw [repliesStopped d (by omega)] at hb
      cases hb
    exact C.callIds n c (c + d) id a hn h hid
  · obtain ⟨d, rfl⟩ : ∃ d, t = c + d := ⟨t - c, by omega⟩
    exact Nat.le_of_not_lt fun hlt => by
      have hb := (holdN d).2 a h hlt
      rw [noticesStopped d (by omega)] at hb
      cases hb

/-- `old_effects_stop` for all nodes at once: from some `k ≥ c`, `OldGone N O c k`. -/
theorem old_gone
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    (c : Nat) : ∃ k, c ≤ k ∧ OldGone N O c k := by
  obtain ⟨k, hk⟩ := finite_common_cut N
    (fun n t => (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
      ∀ a, O.note n t = some a → c ≤ a)
    (fun n hn => (old_effects_stop C c n hn).elim fun T h => ⟨T, h.2⟩)
  exact ⟨max c k, Nat.le_max_left _ _, fun n hn t ht => hk t (by omega) n hn⟩

/-- After any chosen horizon, a node past the entry cut eventually knows a hub pair observed
past that horizon, and keeps knowing one. A fresh own reply establishes it; later own replies,
notifications and quiet events preserve it once old effects have stopped. -/
theorem known_after
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {k entryCut : Nat} (hcut : CutAt N recs adopts fails k) (hq : QuietAt N O k)
    (hnr : ∀ n, n < N → ∀ i, max k entryCut ≤ i → ¬ O.reopen n i)
    (horizon n : Nat) (hn : n < N) :
    ∃ tT, ∀ i, tT ≤ i → KnownTrue run O horizon n i := by
  have hschedBound := fun (n : Nat) => Schedule.index_le (C.schedMono n)
  obtain ⟨T, hkT, hT⟩ := old_effects_stop C horizon n hn
  obtain ⟨p, hp⟩ : ∃ p, p = max T (max k entryCut) := ⟨_, rfl⟩
  have L := C.entry _ hcut hq n hn p (by have := hschedBound n p; omega)
  obtain ⟨j, hfresh, -⟩ := raw_entry_reached L fun j _ _ _ i _ =>
    hq.noObjectFailure n hn (O.sched n (p + j + 1 + i))
      (by have := hschedBound n (p + j + 1 + i); omega)
  have htj : p ≤ O.sched n (p + j) := by have := hschedBound n (p + j); omega
  obtain ⟨u, id, a, htu, -, hown, hcall⟩ := C.freshOwn n (O.sched n (p + j)) hn hfresh
  obtain ⟨hca, hau, hkn⟩ := C.ownHead n u id a hn (hnr n hn u (by omega)) hown
  have h0 : KnownTrue run O horizon n (u + 1) := ⟨a, by omega, by omega, by
    rw [hkn]; exact Retry.Serial.own_reply_learns _ _ _ (C.rootSeq a)⟩
  have stay : ∀ d, KnownTrue run O horizon n (u + 1 + d) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih =>
      have hrt : ¬ O.reopen n (u + 1 + d) := hnr n hn _ (by omega)
      have hTt := hT (u + 1 + d) (by omega)
      show KnownTrue run O horizon n (u + 1 + d + 1)
      cases ho : O.own n (u + 1 + d) with
      | some r =>
        obtain ⟨id', a'⟩ := r
        obtain ⟨h1, h1', h2⟩ := C.ownHead n _ id' a' hn hrt ho
        exact ⟨a', Nat.le_trans (hTt.1 id' a' ho) h1, by omega, by
          rw [h2]; exact Retry.Serial.own_reply_learns _ _ _ (C.rootSeq a')⟩
      | none =>
        cases hn' : O.note n (u + 1 + d) with
        | some a' =>
          obtain ⟨ha', h2⟩ := C.noteHead n _ a' hn hrt hn'
          rcases Retry.Serial.handleHead_notice_or O.root
            ⟨O.seq n (u + 1 + d), O.known n (u + 1 + d)⟩
            ⟨(run a').hub.seq, (run a').hub.head⟩ with h | h
          · obtain ⟨b, hb, hbi, he⟩ := ih
            exact ⟨b, hb, by omega, by rw [h2, h, he]⟩
          · exact ⟨a', hTt.2 a' hn', by omega, by rw [h2, h]⟩
        | none =>
          obtain ⟨b, hb, hbi, he⟩ := ih
          exact ⟨b, hb, by omega, by rw [C.quietKnown n _ hn hrt ho hn', he]⟩
  refine ⟨u + 1, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact stay d

/-- Once entered, a node eventually knows a pair observed after the entry cut itself. -/
theorem known_truthful
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {k entryCut : Nat} (hcut : CutAt N recs adopts fails k) (hq : QuietAt N O k)
    (hnr : ∀ n, n < N → ∀ i, max k entryCut ≤ i → ¬ O.reopen n i)
    (n : Nat) (hn : n < N) :
    ∃ tT, ∀ i, tT ≤ i → KnownTrue run O k n i :=
  known_after C hcut hq hnr k n hn

/-- Past the cut, every node has an active sample at or after any of its scheduled
events: one between rounds starts one, fairly, and its next sample is active. -/
theorem active_after
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {kc : Nat} (hcut : CutAt N recs adopts fails kc) (hq : QuietAt N O kc) (n : Nat)
    (hn : n < N) (p : Nat) (hp : kc ≤ O.sched n p) :
    ∃ q, p ≤ q ∧ O.active n (O.sched n q) = true := by
  cases ha : O.active n (O.sched n p)
  · obtain ⟨q, hpq, hs⟩ := C.idleStart _ hcut hq n p hn hp ha
    exact ⟨q + 1, by omega, C.startActive _ hcut hq n q hn
      (Nat.le_trans hp (Schedule.monotone (C.schedMono n) hpq)) hs⟩
  · exact ⟨p, Nat.le_refl _, ha⟩

/-- A node past the cut, entered and never reopened, on a hub stable from `cut`, comes to know
the stable head, by an own reply to a call made after the hub stopped, and keeps it once its
old calls' replies and old notices (from before then) have stopped. -/
theorem knows_stable_head
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {kc entryCut cut K : Nat} (hcut : CutAt N recs adopts fails kc) (hq : QuietAt N O kc)
    (hnr : ∀ n, n < N → ∀ i, max kc entryCut ≤ i → ¬ O.reopen n i)
    (hhub : ∀ i, cut ≤ i → (run i).hub = (run K).hub)
    (n : Nat) (hn : n < N) :
    ∃ tk, ∀ t, tk ≤ t → O.known n t = (run K).hub.head := by
  obtain ⟨tk, hknown⟩ := known_after C hcut hq hnr cut n hn
  refine ⟨tk, fun t ht => ?_⟩
  obtain ⟨a, ha, _, pair⟩ := hknown t ht
  exact (congrArg Known.head pair).trans (congrArg Snap.head (hhub a ha))


/-! ## Records and environmental recovery stop -/

/-- Fixed native records and drops, followed by the old-effect cutoff, force adoptions and
stale-plan failures to stop, giving a `CutAt`. -/
theorem record_control_stabilizes
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O) :
    ∃ cut, CutAt N recs adopts fails cut := by
  obtain ⟨recordCut, fixed⟩ := Exec.record_and_drop_sets_stabilize N B recs C.recStep C.prune
    C.pruneLe C.dropsGrow C.hubBound C.nodeBound
  obtain ⟨oldCut, afterRecords, oldGone⟩ := old_gone C recordCut
  have each : ∀ n, n < N → ∃ cut, ∀ i, cut ≤ i →
      adopts n i = false ∧ fails n i = false := by
    intro n hn
    obtain ⟨offset, stopped⟩ := Retry.Records.record_disturbances_stop (recLabel recordCut)
      (fun i => epoch n (oldCut + i)) (fun i => adopts n (oldCut + i))
      (fun i => fails n (oldCut + i)) (fun i => by
        have := C.epochStep recordCut oldCut fixed afterRecords oldGone n hn (oldCut + i)
          (by omega)
        simpa [Nat.add_assoc] using this)
    refine ⟨oldCut + offset, fun i hi => ?_⟩
    have := stopped (i - oldCut) (by omega)
    simpa [show oldCut + (i - oldCut) = i by omega] using this
  obtain ⟨controlCut, stopped⟩ := finite_common_cut N
    (fun n i => adopts n i = false ∧ fails n i = false) each
  let cut := max recordCut controlCut
  refine ⟨cut, { records := ?_, control := fun n hn i hi => stopped i (by omega) n hn }⟩
  intro i hi
  obtain ⟨records, drops⟩ := fixed i (by omega)
  obtain ⟨atCut, dropsAtCut⟩ := fixed cut (by omega)
  exact ⟨records.trans atCut.symm, fun n hn x => (drops n hn x).trans (dropsAtCut n hn x).symm⟩

/-- After the last environment loss, object credit can be spent only once per node, so failed
object replies stop. -/
theorem object_failures_stop
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O) :
    ∃ cut, ∀ t, cut ≤ t → ∀ n, n < N → ¬ O.objFail n t := by
  obtain ⟨lossCut, noLoss⟩ := C.envFinal
  apply finite_common_cut N (fun n t => ¬ O.objFail n t)
  intro n hn
  classical
  obtain ⟨offset, stopped⟩ := Retry.Serial.object_recoveries_stop
    (fun i => O.objReady n (lossCut + i)) (fun i => decide (O.objFail n (lossCut + i)))
    (fun i h => C.readyKeep n (lossCut + i) hn (noLoss _ (by omega)) h)
    (fun i h => C.readyFail n (lossCut + i) hn (noLoss _ (by omega)) (of_decide_eq_true h))
  refine ⟨lossCut + offset, fun t ht failure => ?_⟩
  have h := stopped (t - lossCut) (by omega)
  rw [show lossCut + (t - lossCut) = t by omega] at h
  exact absurd failure (of_decide_eq_false h)

omit [DecidableEq ρ] in
/-- Once object failures stop, each node has at most one last recovery reopen. Beyond it,
any old object failure already has an intervening reopen and cannot justify another. -/
theorem recovering_reopens_stop {objectCut : Nat}
    (noFailures : ∀ t, objectCut ≤ t → ∀ n, n < N → ¬ O.objFail n t) :
    ∃ cut, ∀ i, cut ≤ i → ∀ n, n < N → O.reopen n i → ∀ t, t ≤ i →
      O.objFail n t → ∃ between, t < between ∧ between < i ∧ O.reopen n between := by
  apply finite_common_cut N
    (fun n i => O.reopen n i → ∀ t, t ≤ i → O.objFail n t →
      ∃ between, t < between ∧ between < i ∧ O.reopen n between)
  intro n hn
  by_cases hasReopen : ∃ time, objectCut ≤ time ∧ O.reopen n time
  · obtain ⟨last, afterFailures, reopened⟩ := hasReopen
    refine ⟨last + 1, fun i hi _ t _ failure => ⟨last, ?_, by omega, reopened⟩⟩
    exact Nat.lt_of_lt_of_le
      (Nat.lt_of_not_le fun ht => noFailures t ht n hn failure) afterFailures
  · exact ⟨objectCut, fun i hi reopened => absurd ⟨i, hi, reopened⟩ hasReopen⟩

/-- Join the derived record and recovery cutoffs with the environment assumptions. On the
resulting suffix only an incomplete push can reopen a node. -/
theorem entry_phase
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O) :
    ∃ cut, EntryPhase N recs adopts fails O cut := by
  obtain ⟨recordCut, records⟩ := record_control_stabilizes C
  obtain ⟨objectCut, noObjects⟩ := object_failures_stop C
  obtain ⟨recoveryCut, recovered⟩ := recovering_reopens_stop noObjects
  obtain ⟨failureCut, noFailure⟩ := C.failFinal
  obtain ⟨writeCut, noWrites⟩ := finite_common_cut N (fun n t => ¬ O.autoWrite n t)
    C.autoWritesStop
  obtain ⟨userCut, noWork⟩ := C.userFinal
  obtain ⟨lossCut, noLoss⟩ := C.envFinal
  let cut := max (max recordCut (max objectCut recoveryCut))
    (max failureCut (max writeCut (max userCut lossCut)))
  have fixed : CutAt N recs adopts fails cut := records.mono (by omega)
  have quiet : QuietAt N O cut := {
    noIOFailure := fun t ht => noFailure t (by omega)
    noAutomaticWrite := fun n hn t ht => noWrites t (by omega) n hn
    noUserWork := fun n hn t ht => noWork t (by omega) n hn
    noObjectFailure := fun n hn t ht => noObjects t (by omega) n hn
    noLoss := fun t ht => noLoss t (by omega)
  }
  refine ⟨cut, { cut := fixed, quiet := quiet, reopenIncomplete := ?_ }⟩
  intro n hn i hi reopened
  rcases C.reopenWhy cut fixed quiet n i hn hi reopened with incomplete | ⟨t, hti, failure, first⟩
  · exact incomplete
  · obtain ⟨between, afterFailure, beforeNow, earlier⟩ :=
      recovered i (by omega) n hn reopened t hti failure
    exact absurd earlier (first between afterFailure beforeNow)

/-! ## Every node enters and completes an active sample -/

/-- The entry laws give every node an actual completed entry event. Entry persists on the
quiet suffix, and its closed push rules out further incomplete reopens. -/
theorem entered_phase
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {recordCut : Nat} (phase : EntryPhase N recs adopts fails O recordCut) :
    ∃ cut, EnteredPhase N Rof wOf O recordCut cut := by
  have sampleBound := fun n => Schedule.index_le (C.schedMono n)
  have each : ∀ n, n < N → ∃ cut, ∀ i, cut ≤ i →
      RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n i) := by
    intro n hn
    have laws := C.entry recordCut phase.cut phase.quiet n hn recordCut
      (sampleBound n recordCut)
    obtain ⟨j, -, applied, records, -, sequence, announcement⟩ := raw_entry_reached laws
      (fun j _ _ _ i _ => phase.quiet.noObjectFailure n hn
        (O.sched n (recordCut + j + 1 + i)) (by have := sampleBound n (recordCut + j + 1 + i); omega))
    have entry : RawEntry (Rof recordCut) (wOf recordCut)
        (O.rawAt n (O.doneAt n (O.sched n (recordCut + j)) + 1)) :=
      ⟨applied, sequence, announcement, records⟩
    have afterRecord : recordCut ≤ O.doneAt n (O.sched n (recordCut + j)) + 1 := by
      have := sampleBound n (recordCut + j)
      have := (C.doneIn n (recordCut + j) hn).1
      omega
    exact ⟨_, raw_entry_persists _ _ (O.rawAt n) (O.reopen n)
      (fun i => O.incomplete n i = true) (O.expectedIsHead n) (O.closed n) _ entry
      (fun i hi => phase.reopenIncomplete n hn i (by omega))
      (fun i hi => C.incHead _ phase.cut n i hn (by omega))
      (fun i hi => C.closure _ phase.cut phase.quiet n i hn (by omega))
      (fun i hi => C.keep _ phase.cut phase.quiet n i hn (by omega))⟩
  obtain ⟨entryCut, entered⟩ := finite_common_cut N
    (fun n i => RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n i)) each
  let cut := max recordCut entryCut
  have entry : ∀ n, n < N → ∀ i, cut ≤ i →
      RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n i) :=
    fun n hn i hi => entered i (by omega) n hn
  refine ⟨cut, { afterRecord := by omega, entry := entry, noReopen := ?_ }⟩
  intro n hn i hi reopened
  obtain ⟨fromHead, notClosed⟩ := C.incHead _ phase.cut n i hn (by omega)
    (phase.reopenIncomplete n hn i (by omega) reopened)
  rw [C.closure _ phase.cut phase.quiet n i hn (by omega) (entry n hn i hi) fromHead]
    at notClosed
  cases notClosed

/-- Past entry, each node learns a truthful pair and completes an active sample beyond
the old-effects cutoff. These are the native boundaries `FineCut` requires. -/
theorem fine_cut
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {recordCut entryCut : Nat} (phase : EntryPhase N recs adopts fails O recordCut)
    (entered : EnteredPhase N Rof wOf O recordCut entryCut) :
    ∃ cut, FineCut N Rof wOf O recordCut cut ∧
      ∀ n, n < N → KnownTrue run O recordCut n (O.latch n cut) := by
  have sampleBound := fun n => Schedule.index_le (C.schedMono n)
  obtain ⟨knowledgeCut, known⟩ := finite_common_cut N
    (fun n i => KnownTrue run O recordCut n (O.latch n i)) (fun n hn => by
      obtain ⟨truthfulCut, truthful⟩ := known_truthful (entryCut := entryCut)
        C phase.cut phase.quiet (fun n hn i hi => entered.noReopen n hn i (by omega)) n hn
      refine ⟨O.sched n truthfulCut, fun i hi => truthful _ ?_⟩
      have latch := C.latchMono n _ _ hn hi
      rw [C.latchAtSample n truthfulCut hn] at latch
      have := sampleBound n truthfulCut
      omega)
  obtain ⟨oldCut, afterRecord, oldGone⟩ := old_gone C recordCut
  obtain ⟨completedCut, completed⟩ := finite_common_cut N
    (fun n i => ∃ q, oldCut ≤ O.sched n q ∧ O.doneAt n (O.sched n q) < i ∧
      O.active n (O.sched n q) = true ∧ ∀ later, O.sched n q ≤ later →
        RawEntry (Rof recordCut) (wOf recordCut) (O.rawAt n later)) (fun n hn => by
      obtain ⟨q, afterStart, active⟩ := active_after C phase.cut phase.quiet n hn
        (max entryCut oldCut) (by
          have := entered.afterRecord
          have := sampleBound n (max entryCut oldCut)
          omega)
      have afterEntry : max entryCut oldCut ≤ O.sched n q := by
        have := sampleBound n q; omega
      exact ⟨O.doneAt n (O.sched n q) + 1, fun i hi =>
        ⟨q, by omega, by omega, active, fun later hl => entered.entry n hn later (by omega)⟩⟩)
  let cut := max entryCut (max knowledgeCut completedCut)
  refine ⟨cut, { afterRecord := ?_, entry := ?_, completed := ?_ }, ?_⟩
  · have := entered.afterRecord; omega
  · exact fun n hn i hi => entered.entry n hn i (by omega)
  · exact ⟨oldCut, oldGone, fun n hn => completed cut (by omega) n hn⟩
  · exact fun n hn => known cut (by omega) n hn

/-- A truthful latched pair at the fine cut is an honest snapshot of the loss-free hub history.
This is the last premise `FineAt.converges` takes. -/
theorem honest_latched_known
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {recordCut cut : Nat} (quiet : QuietAt N O recordCut)
    (truthful : ∀ n, n < N → KnownTrue run O recordCut n (O.latch n cut)) :
    ∀ n, EligibleAt N recs recordCut n →
      Recovery.HubNodeSteps.HonestSnap (run recordCut).hub.seq O.hist (run cut)
        ⟨(Recovery.HubSys.known (run cut) n).seq, (Recovery.HubSys.known (run cut) n).head,
          (run cut).hub.recs⟩ := by
  intro n eligible
  obtain ⟨observed, afterRecord, beforeLatch, pair⟩ := truthful n eligible.1
  have latch := C.latchLe n cut eligible.1
  rw [C.latchKnown n cut eligible.1, pair]
  exact ⟨seq_chain C.hubSeqStep afterRecord (fun s hs _ => quiet.noLoss s hs),
    seq_chain C.hubSeqStep (by omega) (fun s hs _ => quiet.noLoss s (by omega)),
    C.histBind observed (fun s hs => quiet.noLoss s (by omega))⟩

/-! ## A stable hub excludes ineligible nodes -/

/-- Every node eventually knows the stable head. A node still ineligible would then remain
pending forever, contradicting its native round laws and actual push handling. -/
theorem all_eligible
    (C : HiveContracts N run acts recs B epoch adopts fails recLabel Rof wOf O)
    {recordCut entryCut K stableCut : Nat} (phase : EntryPhase N recs adopts fails O recordCut)
    (entered : EnteredPhase N Rof wOf O recordCut entryCut)
    (stable : ∀ i, stableCut ≤ i → (run i).hub = (run K).hub) :
    ∀ n, n < N → EligibleAt N recs recordCut n := by
  have sampleBound := fun n => Schedule.index_le (C.schedMono n)
  have knows : ∀ n, n < N → ∃ cut, ∀ t, cut ≤ t → O.known n t = (run K).hub.head :=
    knows_stable_head (entryCut := entryCut) C phase.cut phase.quiet
      (fun n hn i hi => entered.noReopen n hn i (by omega)) stable
  intro n hn
  apply Classical.byContradiction
  intro ineligible
  obtain ⟨knowledgeCut, known⟩ := knows n hn
  let start := max stableCut (max entryCut knowledgeCut)
  obtain ⟨p, afterStart, active⟩ := active_after C phase.cut phase.quiet n hn start (by
    have := entered.afterRecord
    have := sampleBound n start
    omega)
  have sample := sampleBound n p
  have afterRecord := entered.afterRecord
  have hubStays : ∀ i, O.sched n p ≤ i → (run i).hub = (run (O.sched n p)).hub :=
    fun i hi => (stable i (by omega)).trans (stable _ (by omega)).symm
  have knownHead : ∀ i, O.sched n p ≤ i → O.known n i = (run (O.sched n p)).hub.head :=
    fun i hi => (known i (by omega)).trans (by rw [stable (O.sched n p) (by omega)])
  apply (C.pending _ phase.cut phase.quiet n p hn (by omega) hubStays knownHead
    (fun i hi => entered.entry n hn i (by omega)) ineligible).absurd
    (HiveObs.roundActive_zero O active) _
    (fun j _ => phase.quiet.noObjectFailure n hn (O.sched n (p + j))
      (by have := sampleBound n (p + j); omega))
  intro j pushed
  have later := Schedule.monotone (C.schedMono n) (Nat.le_add_right p j)
  obtain ⟨afterSend, handled⟩ := C.answer _ phase.cut phase.quiet n (O.sched n (p + j))
    hn (by omega) pushed
  rw [hubStays (O.answerAt n (O.sched n (p + j))) (by omega),
    hubStays (O.answerAt n (O.sched n (p + j)) + 1) (by omega)] at handled
  exact handled.symm

end Phases

end Musubi.SysAcceptance

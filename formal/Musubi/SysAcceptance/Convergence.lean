/-
Derive old-effect and knowledge cuts, then assemble convergence of every participating node.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.
-/
import Musubi.SysAcceptance.Contracts

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

section Phases

open Musubi.EarlyEntry.Control

variable {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}

/-- From any hive time `c`, a node stops handling own replies to calls it made before `c` and
notices published before `c`: each old call has its slot, which a reply or a reopen retires
(`Retry.old_slots_eventually_stop`, reopens allowed), and old notices are finitely many in
flight and queued (`Retry.Notifications.old_notifications_stop`). No fair draining is assumed. -/
theorem old_effects_stop
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
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
  obtain ⟨T2, hT2⟩ := Retry.old_slots_eventually_stop c' (fun i => O.inbox n (c + i)) old
    (Nat.le_refl _) (fun i => (hold i).1)
  have nstep : ∀ i, ∃ h, Retry.Notifications.Step (O.oldNotes c n (c + i))
      (O.oldNotes c n (c + i + 1)) h ∧ ∀ a, O.note n (c + i) = some a → a < c → h = true :=
    fun i => C.notesOld c n (c + i) hn (by omega)
  let oldN := fun i => Classical.choose (nstep i)
  have holdN : ∀ i, Retry.Notifications.Step (O.oldNotes c n (c + i))
      (O.oldNotes c n (c + i + 1)) (oldN i) ∧
      ∀ a, O.note n (c + i) = some a → a < c → oldN i = true :=
    fun i => Classical.choose_spec (nstep i)
  obtain ⟨T3, hT3⟩ := Retry.Notifications.old_notifications_stop
    (fun i => O.oldNotes c n (c + i)) oldN (fun i => (holdN i).1)
  refine ⟨c + max T2 T3, by omega, fun t ht => ⟨fun id a h => ?_, fun a h => ?_⟩⟩
  · obtain ⟨d, rfl⟩ : ∃ d, t = c + d := ⟨t - c, by omega⟩
    have hid : c' ≤ id := Nat.le_of_not_lt fun hlt => by
      have hb := (hold d).2 id a h hlt
      rw [hT2 d (by omega)] at hb
      cases hb
    exact C.callIds n c (c + d) id a hn h hid
  · obtain ⟨d, rfl⟩ : ∃ d, t = c + d := ⟨t - c, by omega⟩
    exact Nat.le_of_not_lt fun hlt => by
      have hb := (holdN d).2 a h hlt
      rw [hT3 d (by omega)] at hb
      cases hb

/-- So, for all nodes at once. -/
theorem old_gone
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    (c : Nat) : ∃ k, c ≤ k ∧ OldGone N O c k := by
  obtain ⟨k, hk⟩ := Recovery.finite_common_cut N
    (fun n t => (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
      ∀ a, O.note n t = some a → c ≤ a)
    (fun n hn => (old_effects_stop C c n hn).elim fun T h => ⟨T, h.2⟩)
  exact ⟨max c k, Nat.le_max_left _ _, fun n hn t ht => hk t (by omega) n hn⟩

/-- An entered node never reopened, past the cut, comes to know a pair the hub had past the
cut, by a fresh own reply once its old calls' replies and old notices have stopped, and keeps
knowing one: own replies and notices then name such pairs, and nothing else moves it. -/
theorem known_truthful
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    {k k4' kS : Nat} (hcut : CutAt N recs adopts fails k) (hq : QuietAt N O k)
    (hnr : ∀ n, n < N → ∀ i, max k k4' ≤ i → ¬ O.reopen n i)
    (hkS : ∀ t, kS ≤ t → ∀ n, n < N → ¬ O.objFail n t) (n : Nat) (hn : n < N) :
    ∃ tT, ∀ i, tT ≤ i → KnownTrue run O k n i := by
  have hschedBound := HiveObs.sched_ge C.schedMono
  obtain ⟨T, hkT, hT⟩ := old_effects_stop C k n hn
  obtain ⟨p, hp⟩ : ∃ p, p = max T (max (max k k4') kS) := ⟨_, rfl⟩
  have L := C.entry _ hcut hq n hn p (by have := hschedBound n p; omega)
  obtain ⟨j, hfresh, -⟩ := L.enters fun j _ _ _ i _ =>
    hkS (O.sched n (p + j + 1 + i)) (by have := hschedBound n (p + j + 1 + i); omega) n hn
  have htj : p ≤ O.sched n (p + j) := by have := hschedBound n (p + j); omega
  obtain ⟨u, id, a, htu, -, hown, hcall⟩ := C.freshOwn n (O.sched n (p + j)) hn hfresh
  obtain ⟨hca, hau, hkn⟩ := C.ownHead n u id a hn (hnr n hn u (by omega)) hown
  have h0 : KnownTrue run O k n (u + 1) := ⟨a, by omega, by omega, by
    rw [hkn]; exact Retry.Serial.own_reply_learns _ _ _ (C.rootSeq a)⟩
  have stay : ∀ d, KnownTrue run O k n (u + 1 + d) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih =>
      have hrt : ¬ O.reopen n (u + 1 + d) := hnr n hn _ (by omega)
      have hTt := hT (u + 1 + d) (by omega)
      show KnownTrue run O k n (u + 1 + d + 1)
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
          rcases handleHead_notice_or O.root (O.seq n (u + 1 + d), O.known n (u + 1 + d))
            ((run a').hub.seq, (run a').hub.head) with h | h
          · obtain ⟨b, hb, hbi, he⟩ := ih
            exact ⟨b, hb, by omega, by rw [h2, h, he]⟩
          · exact ⟨a', hTt.2 a' hn', by omega, by rw [h2, h]⟩
        | none =>
          obtain ⟨b, hb, hbi, he⟩ := ih
          exact ⟨b, hb, by omega, by rw [C.quietKnown n _ hn hrt ho hn', he]⟩
  refine ⟨u + 1, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact stay d

/-- Past the cut, every node has a core step of a running round at or after any of its scheduled
events: one between rounds starts one, fairly, and the round's first event is a core step. -/
theorem active_after
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    {kc : Nat} (hcut : CutAt N recs adopts fails kc) (hq : QuietAt N O kc) (n : Nat)
    (hn : n < N) (p : Nat) (hp : kc ≤ O.sched n p) :
    ∃ q, p ≤ q ∧ O.active n (O.sched n q) = true := by
  cases ha : O.active n (O.sched n p)
  · obtain ⟨q, hpq, hs⟩ := C.idleStart _ hcut hq n p hn hp ha
    exact ⟨q + 1, by omega, C.startCore _ hcut hq n q hn
      (Nat.le_trans hp (HiveObs.sched_le C.schedMono n hpq)) hs⟩
  · exact ⟨p, Nat.le_refl _, ha⟩

/-- A node past the cut, entered and never reopened, on a hub stable from `cut`, comes to know
the stable head, by an own reply to a call made after the hub stopped, and keeps it once its
old calls' replies and old notices (from before then) have stopped. -/
theorem knows_stable_head
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    {kc k4' kS cut K : Nat} (hcut : CutAt N recs adopts fails kc) (hq : QuietAt N O kc)
    (hnr : ∀ n, n < N → ∀ i, max kc k4' ≤ i → ¬ O.reopen n i)
    (hhub : ∀ i, cut ≤ i → (run i).hub = (run K).hub)
    (hkS : ∀ t, kS ≤ t → ∀ n, n < N → ¬ O.objFail n t) (n : Nat) (hn : n < N) :
    ∃ tk, ∀ t, tk ≤ t → O.known n t = (run K).hub.head := by
  have hschedBound := HiveObs.sched_ge C.schedMono
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = max cut (max (max kc k4') kS) := ⟨_, rfl⟩
  obtain ⟨Tq, hTq1, hT⟩ := old_effects_stop C T1 n hn
  have L := C.entry _ hcut hq n hn Tq (by have := hschedBound n Tq; omega)
  obtain ⟨j, hfresh, -⟩ := L.enters fun j _ _ _ i _ =>
    hkS (O.sched n (Tq + j + 1 + i)) (by have := hschedBound n (Tq + j + 1 + i); omega) n hn
  have htj : Tq ≤ O.sched n (Tq + j) := by have := hschedBound n (Tq + j); omega
  obtain ⟨u, id, a, htu, -, hown, hcall⟩ := C.freshOwn n (O.sched n (Tq + j)) hn hfresh
  obtain ⟨hca, -, hkn⟩ := C.ownHead n u id a hn (hnr n hn u (by omega)) hown
  let P : Retry.Serial.Head := ((run K).hub.seq, (run K).hub.head)
  have hP : (O.seq n (u + 1), O.known n (u + 1)) = P := by
    rw [hkn, hhub a (by omega)]
    exact Retry.Serial.own_reply_learns _ _ P (C.rootSeq K)
  have stay : ∀ d, (O.seq n (u + 1 + d), O.known n (u + 1 + d)) = P := by
    intro d
    induction d with
    | zero => exact hP
    | succ d ih =>
      have hrt : ¬ O.reopen n (u + 1 + d) := hnr n hn _ (by omega)
      have hTt := hT (u + 1 + d) (by omega)
      show (O.seq n (u + 1 + d + 1), O.known n (u + 1 + d + 1)) = P
      cases ho : O.own n (u + 1 + d) with
      | some r =>
        obtain ⟨id', a'⟩ := r
        obtain ⟨h1, -, h2⟩ := C.ownHead n _ id' a' hn hrt ho
        rw [h2, hhub a' (by have := hTt.1 id' a' ho; omega), ih]
        exact handleHead_same _ P
      | none =>
        cases hn' : O.note n (u + 1 + d) with
        | some a' =>
          rw [(C.noteHead n _ a' hn hrt hn').2, hhub a' (by have := hTt.2 a' hn'; omega), ih]
          exact handleHead_notice_le _ P P (Nat.le_refl _)
        | none => rw [C.quietKnown n _ hn hrt ho hn', ih]
  refine ⟨u + 1, fun t ht => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact congrArg Prod.snd (stay d)

end Phases

open Musubi.EarlyEntry.Control Musubi.Recovery.HubSys in
/-- The hive converges: from the native laws of its actual run, its hub settles, and every node
settles at the hub's head, its physical raw heads that head. The phases, in order: records and
drops stop changing; then the effects of old calls and notices from before that; then
adoptions and stale-plan failures, failed `GetObjects` replies and their recovering reopens,
ordinary failures, automatic writes and user work; every node enters, raw, and stays entered;
every node comes to know a pair the hub had past the cut; the eligible nodes' system converges,
so the hub is stable; every node comes to know its head; and a node that is not eligible is
impossible there. What the eligible nodes' system takes at the fine cut the proof chooses, once
every node has entered and completed a core step since, past the old-effects cut of calls and
notices from before the cut (`OldGone`), is a premise apart from the contracts (`fine`):
`FineAssembly.hive_converges_observed` builds it from the replay of observed native events. -/
theorem hive_converges {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    (fine : ∀ k k4, CutAt N recs adopts fails k → QuietAt N O k → k ≤ k4 →
      (∀ n, n < N → ∀ i, k4 ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
      (∃ kG, OldGone N O k kG ∧ ∀ n, n < N → ∃ q, kG ≤ O.sched n q ∧
        O.doneAt n (O.sched n q) < k4 ∧ O.active n (O.sched n q) = true ∧
        ∀ i, O.sched n q ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
      Nonempty (FineAt N D law (EligibleAt N recs k) run acts k4 (run k).hub.seq O.hist)) :
    ∃ K cut, K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, n < N → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, heads (run i) n x ↔ x = (run K).hub.head := by
  -- records and drops stop changing
  obtain ⟨k1, hk1⟩ := Exec.record_and_drop_sets_stabilize N B recs C.recStep C.prune C.pruneLe
    C.dropsGrow C.hubBound C.nodeBound
  -- then the effects of old calls and notices from before that stop
  obtain ⟨kO, hkO1, hkO⟩ := old_gone C k1
  -- then adoptions and stale-plan failures
  have each : ∀ n, n < N → ∃ c, ∀ i, c ≤ i →
      adopts n i = false ∧ fails n i = false := by
    intro n hn
    obtain ⟨c, hc⟩ := Retry.Records.record_disturbances_stop (recLabel k1)
      (fun i => epoch n (kO + i)) (fun i => adopts n (kO + i)) (fun i => fails n (kO + i))
      (fun i => by
        have := C.epochStep k1 kO hk1 hkO1 hkO n hn (kO + i) (by omega)
        simpa [Nat.add_assoc] using this)
    refine ⟨kO + c, fun i hi => ?_⟩
    have := hc (i - kO) (by omega)
    simpa [show kO + (i - kO) = i by omega] using this
  obtain ⟨k2, hk2⟩ := Recovery.finite_common_cut N
    (fun n i => adopts n i = false ∧ fails n i = false) each
  -- past the environment's last loss, each node's object credit is spent at most once, so its
  -- failed `GetObjects` replies stop
  obtain ⟨kE, hkE⟩ := C.envFinal
  have S : ∀ n, n < N → ∃ c, ∀ t, c ≤ t → ¬ O.objFail n t := by
    intro n hn
    classical
    obtain ⟨c, hc⟩ := Retry.Serial.object_recoveries_stop (fun i => O.objReady n (kE + i))
      (fun i => decide (O.objFail n (kE + i)))
      (fun i h => C.readyKeep n (kE + i) hn (hkE _ (by omega)) h)
      (fun i h => C.readyFail n (kE + i) hn (hkE _ (by omega)) (of_decide_eq_true h))
    refine ⟨kE + c, fun t ht hf => ?_⟩
    have h := hc (t - kE) (by omega)
    rw [show kE + (t - kE) = t by omega] at h
    exact absurd hf (of_decide_eq_false h)
  obtain ⟨kS, hkS⟩ := Recovery.finite_common_cut N (fun n t => ¬ O.objFail n t) S
  -- then each node reopens to recover from a failed `GetObjects` once more at most
  have recov : ∀ n, n < N → ∃ kR, ∀ i, kR ≤ i → O.reopen n i → ∀ t, t ≤ i →
      O.objFail n t → ∃ s, t < s ∧ s < i ∧ O.reopen n s := by
    intro n hn
    by_cases h : ∃ s, kS ≤ s ∧ O.reopen n s
    · obtain ⟨s0, hs0, hr0⟩ := h
      refine ⟨s0 + 1, fun i hi _ t _ hf => ⟨s0, ?_, by omega, hr0⟩⟩
      exact Nat.lt_of_lt_of_le (Nat.lt_of_not_le fun ht => hkS t ht n hn hf) hs0
    · exact ⟨kS, fun i hi hr => absurd ⟨i, hi, hr⟩ h⟩
  obtain ⟨kR, hkR⟩ := Recovery.finite_common_cut N (fun n i => O.reopen n i → ∀ t, t ≤ i →
    O.objFail n t → ∃ s, t < s ∧ s < i ∧ O.reopen n s) recov
  -- ordinary failures and automatic writes stop: explicit premises, joined into the cut
  obtain ⟨kF, hkF⟩ := C.failFinal
  obtain ⟨kH, hkH⟩ := Recovery.finite_common_cut N (fun n t => ¬ O.autoWrite n t)
    C.autoWritesStop
  obtain ⟨kU, hkU⟩ := C.userFinal
  obtain ⟨kc, hkc⟩ : ∃ kc,
      kc = max (max k1 (max kO k2)) (max (max kF (max kH kU)) (max kS (max kR kE))) :=
    ⟨_, rfl⟩
  have hcut : CutAt N recs adopts fails kc := by
    refine ⟨fun i hi => ?_, fun n hn i hi => hk2 i (by omega) n hn⟩
    obtain ⟨h1, h2⟩ := hk1 i (by omega)
    obtain ⟨h3, h4⟩ := hk1 kc (by omega)
    exact ⟨h1.trans h3.symm, fun n hn x => (h2 n hn x).trans (h4 n hn x).symm⟩
  have hq : QuietAt N O kc :=
    ⟨fun t ht => hkF t (by omega), fun n hn t ht => hkH t (by omega) n hn,
      fun n hn t ht => hkU t (by omega) n hn, fun n hn t ht => hkS t (by omega) n hn,
      fun t ht => hkE t (by omega)⟩
  have hschedBound := HiveObs.sched_ge C.schedMono
  -- past the cut, only `Incomplete` reopens a node
  have reopenInc : ∀ n i, n < N → kc ≤ i → O.reopen n i → O.incomplete n i = true := by
    intro n i hn hi hr
    rcases C.reopenWhy _ hcut hq n i hn hi hr with h | ⟨t, hti, hf, hno⟩
    · exact h
    · obtain ⟨s, hts, hbetween, hrs⟩ := hkR i (by omega) n hn hr t hti hf
      exact absurd hrs (hno s hts hbetween)
  have serve : ∀ n, n < N → ∀ p, kS ≤ p → ∀ j, Before (O.entryData n p).reply j →
      (O.entryData n p).fetchCall j → (O.entryData n p).reply j = .fresh → ∀ i,
      ((O.entryData n p).round j).active i = true → ¬ ((O.entryData n p).round j).failed i :=
    fun n hn p hp j _ _ _ i _ =>
      hkS (O.sched n (p + j + 1 + i)) (by have := hschedBound n (p + j + 1 + i); omega) n hn
  -- every node enters, at an actual event of its own, and stays entered
  have hentered : ∀ n, n < N → ∃ j, ∀ i, j ≤ i →
      RawEntry (Rof kc) (wOf kc) (O.rawAt n i) := by
    intro n hn
    let p0 := max kc kS
    have L := C.entry _ hcut hq n hn p0 (by have := hschedBound n p0; omega)
    obtain ⟨j, -, hap, hrec, -, hseq, hann⟩ := L.enters (serve n hn p0 (by omega))
    have hej : RawEntry (Rof kc) (wOf kc) (O.rawAt n (O.doneAt n (O.sched n (p0 + j)) + 1)) :=
      ⟨hap, hseq, hann, hrec⟩
    have hle : kc ≤ O.doneAt n (O.sched n (p0 + j)) + 1 := by
      have := hschedBound n (p0 + j); have := (C.doneIn n (p0 + j) hn).1; omega
    exact ⟨_, raw_entry_persists _ _ (O.rawAt n) (O.reopen n) (fun i => O.incomplete n i = true)
      (O.expectedIsHead n) (O.closed n) _ hej
      (fun i hi => reopenInc n i hn (by omega))
      (fun i hi => C.incHead _ hcut n i hn (by omega))
      (fun i hi => C.closure _ hcut hq n i hn (by omega))
      (fun i hi => C.keep _ hcut hq n i hn (by omega))⟩
  obtain ⟨k4', hk4'⟩ := Recovery.finite_common_cut N
    (fun n i => RawEntry (Rof kc) (wOf kc) (O.rawAt n i)) hentered
  have hk4 : ∀ n, n < N → ∀ i, max kc k4' ≤ i → RawEntry (Rof kc) (wOf kc) (O.rawAt n i) :=
    fun n hn i hi => hk4' i (by omega) n hn
  -- an entered node is not reopened: only `Incomplete` reopens it, and its push is closed
  have hnr : ∀ n, n < N → ∀ i, max kc k4' ≤ i → ¬ O.reopen n i := by
    intro n hn i hi hr
    obtain ⟨hh, hc⟩ := C.incHead _ hcut n i hn (by omega)
      (reopenInc n i hn (by omega) hr)
    rw [C.closure _ hcut hq n i hn (by omega) (hk4 n hn i hi) hh] at hc
    cases hc
  -- every node comes to know a pair the hub had past the cut, and keeps knowing one; so does the
  -- Sys model's latched snapshot of it, from the node's sampled event past that on
  obtain ⟨k5, hk5⟩ := Recovery.finite_common_cut N
    (fun n i => KnownTrue run O kc n (O.latch n i))
    (fun n hn => by
      obtain ⟨tT, htT⟩ := known_truthful C hcut hq hnr hkS n hn
      refine ⟨O.sched n tT, fun i hi => htT _ ?_⟩
      have h1 := C.latchMono n _ _ hn hi
      rw [C.latchAtSample n tT hn] at h1
      have := hschedBound n tT
      omega)
  -- the effects of calls and notices from before the cut itself stop
  obtain ⟨kG, hkG, hG⟩ := old_gone C kc
  -- every node has, once entered and past those, a COMPLETED core step of a running round,
  -- whose prelude completes any realignment its records' taking left unfinished, after which
  -- its canonical op heads are distinct (an alias forces a merge, which leaves one)
  obtain ⟨k6, hk6⟩ := Recovery.finite_common_cut N
    (fun n i => ∃ q, kG ≤ O.sched n q ∧ O.doneAt n (O.sched n q) < i ∧
      O.active n (O.sched n q) = true ∧
      ∀ i', O.sched n q ≤ i' → RawEntry (Rof kc) (wOf kc) (O.rawAt n i'))
    (fun n hn => by
      obtain ⟨q, hpq, hact⟩ := active_after C hcut hq n hn (max (max kc k4') kG)
        (by have := hschedBound n (max (max kc k4') kG); omega)
      have hsq : max (max kc k4') kG ≤ O.sched n q := by have := hschedBound n q; omega
      exact ⟨O.doneAt n (O.sched n q) + 1, fun i hi =>
        ⟨q, by omega, by omega, hact, fun i' hi' => hk4 n hn i' (by omega)⟩⟩)
  -- the eligible nodes' system converges, so the hub is stable
  obtain ⟨k4, hk4d⟩ : ∃ k4, k4 = max (max (max kc k4') k5) k6 := ⟨_, rfl⟩
  obtain ⟨F⟩ := fine kc k4 hcut hq (by omega) (fun n hn i hi => hk4 n hn i (by omega))
    ⟨kG, hG, fun n hn => (hk6 k4 (by omega) n hn).elim fun q h =>
      ⟨q, h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  -- the Sys model's known pair at k4 is an honest snapshot of the hub's history from the cut
  have hknownF : ∀ n, EligibleAt N recs kc n →
      Recovery.HubNodeSteps.HonestSnap (run kc).hub.seq O.hist (run k4)
        ⟨(Recovery.HubSys.known (run k4) n).1, (Recovery.HubSys.known (run k4) n).2,
          (run k4).hub.recs⟩ := by
    intro n hE
    obtain ⟨a, hka, hal, he⟩ := hk5 k4 (by omega) n hE.1
    have hl := C.latchLe n k4 hE.1
    have hnl : ∀ s, kc ≤ s → ¬ O.lost s := fun s hs => hkE s (by omega)
    rw [C.latchKnown n k4 hE.1, he]
    exact ⟨seq_chain C.hubSeqStep hka (fun s h1 _ => hnl s h1),
      seq_chain C.hubSeqStep (by omega) (fun s h1 _ => hnl s (by omega)),
      C.histBind a (fun s h => hnl s (by omega))⟩
  obtain ⟨K, cut, -, hKc, hhub, hnodes⟩ := F.converges hknownF (fun n h => h.1)
  have hknows : ∀ n, n < N → ∃ tk, ∀ t, tk ≤ t → O.known n t = (run K).hub.head :=
    knows_stable_head C hcut hq hnr hhub hkS
  -- the laws of a node that is not eligible, on the stable hub it knows, cannot hold
  have hall : ∀ n, n < N → EligibleAt N recs kc n := by
    intro n hn
    apply Classical.byContradiction
    intro hne
    obtain ⟨tk, htk⟩ := hknows n hn
    -- from a core step of a running round, which comes: a node between rounds starts one
    obtain ⟨p0, hp0⟩ : ∃ p0, p0 = max (max cut (max (max kc k4') kS)) tk := ⟨_, rfl⟩
    obtain ⟨p, hpp, hact⟩ := active_after C hcut hq n hn p0 (by have := hschedBound n p0; omega)
    have hp := hschedBound n p
    have hstay : ∀ i, O.sched n p ≤ i → (run i).hub = (run (O.sched n p)).hub :=
      fun i hi => (hhub i (by omega)).trans (hhub _ (by omega)).symm
    have hknown : ∀ i, O.sched n p ≤ i → O.known n i = (run (O.sched n p)).hub.head :=
      fun i hi => (htk i (by omega)).trans (by rw [hhub (O.sched n p) (by omega)])
    apply (C.pending _ hcut hq n p hn hstay hknown (fun i hi => hk4 n hn i (by omega))
      hne).absurd (HiveObs.roundActive_zero O hact) _
      fun j _ => hkS (O.sched n (p + j)) (by have := hschedBound n (p + j); omega) n hn
    -- each push it sends is handled on the stable hub, which the handling leaves as it is
    intro j hpush
    have hsj := HiveObs.sched_le C.schedMono n (Nat.le_add_right p j)
    obtain ⟨hle, heq⟩ := C.answer _ hcut hq n (O.sched n (p + j)) hn (by omega) hpush
    rw [hstay (O.answerAt n (O.sched n (p + j))) (by omega),
      hstay (O.answerAt n (O.sched n (p + j)) + 1) (by omega)] at heq
    exact heq.symm
  exact ⟨K, cut, hKc, hhub, fun n hn => hnodes n (hall n hn)⟩

end Musubi.SysAcceptance

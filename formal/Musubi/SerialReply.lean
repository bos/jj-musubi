/-
The driver's serialized call boundary. Notifications are applied between calls, and a
matching response consumes its own live slot. This ties the finite budget of pre-cut slots to
the effects of calls on the known head. It does not assume that a whole sync loop terminates.

The convergence proof uses `handleHead`, `filteredLearn`, `own_reply_learns`,
`object_recoveries_stop` and `wentBack` from this file. The serialized-call model and its
invariant are not used by the assembly and stand alone.
-/
import Musubi.RetryControl

namespace Musubi.Retry.Serial

/-- The reply is older than the known pair, or has the same sequence number and a different
head. -/
def wentBack (known reply : Known) : Bool :=
  decide (reply.seq < known.seq ∨ (reply.seq = known.seq ∧ reply.head ≠ known.head))

/-- Learn `reply` only if its sequence number is later than the known one. -/
def filteredLearn (known reply : Known) : Known :=
  if known.seq < reply.seq then reply else known

/-- `handle_reply` restarts at `⟨0, root⟩` on an own reply that went back, then learns as
`handle` does. A notification is never read as the answer to a call. -/
def handleHead (root : Nat) (own notify : Bool) (known reply : Known) : Known :=
  let before := if own && !notify && wentBack known reply then ⟨0, root⟩ else known
  filteredLearn before reply

/-- An own reply sets the known pair to the reply, whatever the known pair was, even one from
before the window or from an obsolete history. A reply with sequence 0 names the root; a
positive sequence is learned after any reset. -/
theorem own_reply_learns (root : Nat) (known reply : Known)
    (hroot : reply.seq = 0 → reply.head = root) :
    handleHead root true false known reply = reply := by
  by_cases hb : reply.seq < known.seq ∨ (reply.seq = known.seq ∧ reply.head ≠ known.head)
  · simp only [handleHead, Bool.not_false, Bool.true_and, wentBack, hb, decide_true,
      ↓reduceIte, filteredLearn]
    by_cases hp : 0 < reply.seq
    · simp [hp]
    · have hz : reply.seq = 0 := by omega
      have hr := hroot hz
      simp only [hp, ↓reduceIte]
      exact (Known.ext hz hr : reply = ⟨0, root⟩).symm
  · simp only [handleHead, Bool.not_false, Bool.true_and, wentBack, hb, decide_false,
      Bool.false_eq_true, ↓reduceIte, filteredLearn]
    by_cases hp : known.seq < reply.seq
    · simp [hp]
    · have hs : known.seq = reply.seq := by omega
      have hh : known.head = reply.head := by
        apply Classical.byContradiction
        intro hn
        exact hb (.inr ⟨hs.symm, Ne.symm hn⟩)
      simp only [hp, ↓reduceIte]
      exact Known.ext hs hh

/-- An own reply naming the pair the node knows leaves it. -/
theorem handleHead_same (r : Nat) (P : Known) :
    handleHead r true false P P = P := by
  simp [handleHead, wentBack, filteredLearn]

/-- A notice of a sequence no later than the one the node knows leaves it. -/
theorem handleHead_notice_le (r : Nat) (P q : Known) (h : q.seq ≤ P.seq) :
    handleHead r false true P q = P := by
  simp [handleHead, filteredLearn, Nat.not_lt.2 h]

/-- A notice leaves the known pair, or makes it the notice's. -/
theorem handleHead_notice_or (r : Nat) (P q : Known) :
    handleHead r false true P q = P ∨
      handleHead r false true P q = q := by
  simp only [handleHead, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    filteredLearn]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A call outstanding on the driver. -/
structure Call where
  /-- The request id of the call. -/
  id : Nat
  /-- The known head when the call was sent. -/
  before : Known
  /-- The applied records when the call was sent. -/
  beforeRecords : List (List Nat)

/-- The driver's call state. -/
structure State where
  /-- The root vertex. -/
  root : Nat
  /-- The hub head and sequence number the driver knows. -/
  known : Known
  /-- The ordered record lists applied so far. -/
  applied : List (List Nat)
  /-- The next request id. -/
  next : Nat
  /-- The outstanding call, if any; at most one. -/
  active : Option Call

def State.inbox (s : State) : Inbox :=
  ⟨s.next, match s.active with | none => [] | some call => [call.id]⟩

def State.start (s : State) : Option (State × Nat) :=
  match s.active with
  | some _ => none
  | none =>
    let call := Call.mk s.next s.known s.applied
    some ({ s with next := s.next + 1, active := some call }, s.next)

def State.reserve (s : State) : State := { s with next := s.next + 1 }

/-- Repository adoption runs between calls on this driver, so the applied-records snapshot of
the outstanding call stays unchanged until that call returns or is retired. -/
def State.takeRecords (s : State) (records : List (List Nat)) : Option State :=
  match s.active with
  | some _ => none
  | none => some { s with applied := records }

/-- A timeout has no reply; an unmatched response changes neither knowledge nor the call. -/
def State.finish (s : State) (id : Nat) (reply : Option Known) : State × Bool :=
  match s.active with
  | none => (s, false)
  | some call =>
    if call.id = id then
      ({ s with active := none
                known := match reply with
            | none => s.known
            | some head => handleHead s.root true false s.known head }, true)
    else (s, false)

def State.notice (s : State) (reply : Known) : Option State :=
  match s.active with
  | some _ => none
  | none => some { s with known := handleHead s.root false true s.known reply }

def State.disconnect (s : State) : State := { s with active := none }

/-- While the call is outstanding, its send-time head remains the driver's known head. -/
def Inv (s : State) : Prop :=
  ∀ call, s.active = some call →
    call.before = s.known ∧ call.beforeRecords = s.applied ∧ call.id < s.next

theorem finish_inbox (s : State) (id : Nat) (reply : Option Known) :
    (s.finish id reply).1.inbox = (s.inbox.finish id).1 ∧
      (s.finish id reply).2 = (s.inbox.finish id).2 := by
  cases h : s.active with
  | none => simp [State.finish, State.inbox, Inbox.finish, h]
  | some call =>
    by_cases he : call.id = id
    · simp [State.finish, State.inbox, Inbox.finish, h, he]
    · simp [State.finish, State.inbox, Inbox.finish, h, he, Ne.symm he]

theorem start_inbox {s t : State} {id : Nat} (h : s.start = some (t, id)) :
    t.inbox = s.inbox.start.1 := by
  cases hc : s.active with
  | some call => simp [State.start, hc] at h
  | none =>
    simp only [State.start, hc, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp [State.inbox, Inbox.start, hc]

theorem notice_inbox {s t : State} {reply : Known} (h : s.notice reply = some t) :
    t.inbox = s.inbox := by
  cases hc : s.active with
  | some call => simp [State.notice, hc] at h
  | none =>
    simp only [State.notice, hc, Option.some.injEq] at h
    cases h
    simp [State.inbox, hc]

theorem takeRecords_inbox {s t : State} {records : List (List Nat)}
    (h : s.takeRecords records = some t) : t.inbox = s.inbox := by
  cases hc : s.active with
  | some call => simp [State.takeRecords, hc] at h
  | none =>
    simp only [State.takeRecords, hc, Option.some.injEq] at h
    cases h
    simp [State.inbox, hc]

inductive Step (cut : Nat) : State → State → Bool → Prop
  | start {s t : State} {id : Nat} (h : s.start = some (t, id)) : Step cut s t false
  | reserve (s : State) : Step cut s s.reserve false
  | takeRecords {s t : State} (records : List (List Nat))
      (h : s.takeRecords records = some t) : Step cut s t false
  | finish (s : State) (id : Nat) (reply : Option Known) :
      Step cut s (s.finish id reply).1 ((s.finish id reply).2 && decide (id < cut))
  | notice {s t : State} (reply : Known) (h : s.notice reply = some t) : Step cut s t false
  | disconnect (s : State) : Step cut s s.disconnect false
  | wait (s : State) : Step cut s s false

/-- Every control step is a step of the inbox model: a notification consumes no request and
adds to no slot budget. -/
theorem step_inbox {cut : Nat} {s t : State} {old : Bool} (h : Step cut s t old) :
    InboxStep cut s.inbox t.inbox old := by
  cases h with
  | start h => rw [start_inbox h]; exact .start _
  | reserve => exact .reserve _
  | takeRecords records h => rw [takeRecords_inbox h]; exact .wait _
  | finish id reply =>
    rw [(finish_inbox s id reply).1, (finish_inbox s id reply).2]
    exact .finish _ id
  | notice reply h => rw [notice_inbox h]; exact .wait _
  | disconnect => exact .disconnect _
  | wait => exact .wait _

theorem inv_step {cut : Nat} {s t : State} {old : Bool} (hi : Inv s)
    (h : Step cut s t old) : Inv t := by
  cases h with
  | start h =>
    cases hc : s.active with
    | some call => simp [State.start, hc] at h
    | none =>
      simp only [State.start, hc, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      intro call he
      cases he
      exact ⟨rfl, rfl, Nat.lt_succ_self _⟩
  | reserve =>
    intro call hc
    obtain ⟨hk, hr, hid⟩ := hi call hc
    exact ⟨hk, hr, Nat.lt_succ_of_lt hid⟩
  | takeRecords records h =>
    cases hc : s.active with
    | some call => simp [State.takeRecords, hc] at h
    | none =>
      simp only [State.takeRecords, hc, Option.some.injEq] at h
      cases h
      simp [Inv]
  | finish id reply =>
    cases hc : s.active with
    | none => simpa [State.finish, hc] using hi
    | some call =>
      by_cases he : call.id = id
      · simp [Inv, State.finish, hc, he]
      · simpa [State.finish, hc, he] using hi
  | notice reply h =>
    cases hc : s.active with
    | some call => simp [State.notice, hc] at h
    | none =>
      simp only [State.notice, hc, Option.some.injEq] at h
      cases h
      simp [Inv]
  | disconnect => simp [Inv, State.disconnect]
  | wait => exact hi

theorem active_records_unchanged {s : State} {call : Call}
    (hi : Inv s) (hc : s.active = some call) : call.beforeRecords = s.applied :=
  (hi call hc).2.1

/-- Even if old frames are duplicated forever, only finitely many matched pre-cut calls have
any effect. Notifications need not stop, and no sync round is assumed to complete. -/
theorem old_call_effects_stop (cut : Nat) (run : Nat → State) (old : Nat → Bool)
    (hc : cut ≤ (run 0).next)
    (hs : ∀ i, Step cut (run i) (run (i + 1)) (old i)) :
    ∃ k, ∀ i, k ≤ i → old i = false :=
  old_slots_eventually_stop cut (fun i => (run i).inbox) old hc
    (fun i => step_inbox (hs i))

/-- An honest response handled after the call was sent does not look like a rollback, given
that the hub's sequence number only grows and its history `hist` is stable. By `Inv` the
send-time snapshot is still the known pair at receipt; the hub may have accepted heads in
between. -/
theorem fresh_reply_no_restart {s : State} {call : Call} {reply : Known}
    (hi : Inv s) (hc : s.active = some call) (hist : Nat → Nat) (sentSeq : Nat)
    (hknown : hist call.before.seq = call.before.head)
    (hsent : call.before.seq ≤ sentSeq) (hhandled : sentSeq ≤ reply.seq)
    (hreply : hist reply.seq = reply.head) : wentBack s.known reply = false := by
  have he := (hi call hc).1
  rw [← he]
  simp only [wentBack, decide_eq_false_iff_not]
  intro bad
  rcases bad with hlt | ⟨heq, hne⟩
  · omega
  · apply hne
    rw [← hreply, heq]
    exact hknown

/-- The daemon awaits an entire `driver.sync` before handling another notification. The
per-call model above permits more interleavings; this wrapper adds that scheduling rule, which
a finite local burst of work needs in order to finish. -/
structure RoundState where
  calls : State
  running : Bool

inductive RoundStep (cut : Nat) : RoundState → RoundState → Bool → Prop
  | beginRound (s : RoundState) (hi : s.running = false) (ha : s.calls.active = none) :
      RoundStep cut s { s with running := true } false
  | start {s : RoundState} {t : State} {id : Nat} (hr : s.running = true)
      (h : s.calls.start = some (t, id)) :
      RoundStep cut s { s with calls := t } false
  | reserve (s : RoundState) :
      RoundStep cut s { s with calls := s.calls.reserve } false
  | repository {s : RoundState} {t : State} (hr : s.running = true)
      (records : List (List Nat)) (h : s.calls.takeRecords records = some t) :
      RoundStep cut s { s with calls := t } false
  | finish (s : RoundState) (id : Nat) (reply : Option Known) :
      RoundStep cut s { s with calls := (s.calls.finish id reply).1 }
        ((s.calls.finish id reply).2 && decide (id < cut))
  | notice {s : RoundState} {t : State} (hr : s.running = false) (reply : Known)
      (h : s.calls.notice reply = some t) :
      RoundStep cut s { s with calls := t } false
  | endRound (s : RoundState) (ha : s.calls.active = none) :
      RoundStep cut s { s with running := false } false
  | disconnect (s : RoundState) :
      RoundStep cut s ⟨s.calls.disconnect, false⟩ false
  | wait (s : RoundState) : RoundStep cut s s false

theorem round_step_serial {cut : Nat} {s t : RoundState} {old : Bool}
    (h : RoundStep cut s t old) : Step cut s.calls t.calls old := by
  cases h with
  | beginRound => exact .wait _
  | start _ h => exact .start h
  | reserve => exact .reserve _
  | repository _ records h => exact .takeRecords records h
  | finish id reply => exact .finish _ id reply
  | notice _ reply h => exact .notice reply h
  | endRound => exact .wait _
  | disconnect => exact .disconnect _
  | wait => exact .wait _

theorem round_old_effects_stop (cut : Nat) (run : Nat → RoundState) (old : Nat → Bool)
    (hc : cut ≤ (run 0).calls.next)
    (hs : ∀ i, RoundStep cut (run i) (run (i + 1)) (old i)) :
    ∃ k, ∀ i, k ≤ i → old i = false :=
  old_call_effects_stop cut (fun i => (run i).calls) old hc
    (fun i => round_step_serial (hs i))

/-- Adopting records leaves the known head unchanged, so local repository work between a
round's own RPCs cannot change it. Inside a running round only a matched response can. -/
theorem takeRecords_known {s t : State} {records : List (List Nat)}
    (h : s.takeRecords records = some t) : t.known = s.known := by
  cases hc : s.active with
  | some call => simp [State.takeRecords, hc] at h
  | none =>
    simp only [State.takeRecords, hc, Option.some.injEq] at h
    cases h
    rfl

/-- Object-recovery failures eventually stop. Even after pre-cut effects cease, one object
request left over from before may still fail, because an earlier successful head reply need
not have completed the rest of its request batch. The native invariant `ready` covers the
batch's targets and truthful object-have claims, not only the known head. A recovery clears
the batch and reopens at the root; after that, fresh heads are closed on a healthy hub, which
retains its raw objects. The premises `hkeep` and `hfail` state these two facts: once ready it
stays ready, and a failure happens only when not ready, after which it is ready. -/
theorem object_recoveries_stop (ready failed : Nat → Bool)
    (hkeep : ∀ i, ready i = true → ready (i + 1) = true)
    (hfail : ∀ i, failed i = true → ready i = false ∧ ready (i + 1) = true) :
    ∃ k, ∀ i, k ≤ i → failed i = false := by
  let credit := fun i => if ready i then 0 else 1
  have hle : ∀ i, credit (i + 1) ≤ credit i := by
    intro i
    cases h : ready i
    · simp [credit, h]
      split <;> omega
    · simp [credit, h, hkeep i h]
  obtain ⟨k, hk⟩ := nat_trace_stabilizes credit hle
  refine ⟨k, fun i hi => ?_⟩
  cases hf : failed i
  · rfl
  · obtain ⟨hb, ha⟩ := hfail i hf
    have he := (hk i hi).trans (hk (i + 1) (by omega)).symm
    simp [credit, hb, ha] at he

end Musubi.Retry.Serial

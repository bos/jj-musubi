/-
Retry control as finite debt, within epochs that satisfy explicit constraints. Request ids
are never reused. Completing or retiring a request removes its slot, and calls made after a
cut `cut` get ids at or above it, so they never add to the finitely many slots below it.
Fix-ups are cached across retries. The fix-up bound also requires the pending drops, named by
their immutable original operations, to shrink after a first alignment. The theorems here
bound slot consumption and cached writes within such an epoch; they do not show that a run
eventually enters one.

The convergence proof uses this file except the fix-up write bounds (`fixup_writes_le_one`,
`fixups_eventually_stop`) and the publication facts (`publication_retry`,
`publication_tip_cached`), which are not used by the assembly and stand alone.
-/
import Musubi.AsyncLiveness

namespace Musubi.Retry

/-- One transport's live request slots, not the safety model's replayable message set. -/
structure Inbox where
  next : Nat
  pending : List Nat
  deriving Repr, DecidableEq

def Inbox.start (s : Inbox) : Inbox × Nat :=
  (⟨s.next + 1, s.next :: s.pending⟩, s.next)

/-- Another driver or a subscription allocates from the shared transport counter. It creates
no live slot in this driver's projection, but still advances its next observed request id. -/
def Inbox.reserve (s : Inbox) : Inbox := ⟨s.next + 1, s.pending⟩

def Inbox.project (s : Inbox) (owns : Nat → Bool) : Inbox :=
  ⟨s.next, s.pending.filter owns⟩

theorem project_reserve (s : Inbox) (owns : Nat → Bool) :
    s.reserve.project owns = (s.project owns).reserve := rfl

theorem project_own_start (s : Inbox) (owns : Nat → Bool) (h : owns s.next = true) :
    s.start.1.project owns = (s.project owns).start.1 := by
  simp [Inbox.start, Inbox.project, h]

theorem project_other_start (s : Inbox) (owns : Nat → Bool) (h : owns s.next = false) :
    s.start.1.project owns = (s.project owns).reserve := by
  simp [Inbox.start, Inbox.project, Inbox.reserve, h]

/-- Finishing `id`, by delivery or timeout, retires its slot. The flag is true only if the
slot was live. -/
def Inbox.finish (s : Inbox) (id : Nat) : Inbox × Bool :=
  (⟨s.next, s.pending.filter (· != id)⟩, s.pending.contains id)

theorem project_finish (s : Inbox) (owns : Nat → Bool) (id : Nat) :
    (s.finish id).1.project owns = ((s.project owns).finish id).1 ∧
      ((s.project owns).finish id).2 = ((s.finish id).2 && owns id) := by
  constructor
  · simp [Inbox.finish, Inbox.project, List.filter_filter, Bool.and_comm]
  · simp [Inbox.finish, Inbox.project]

def Inbox.disconnect (s : Inbox) : Inbox := ⟨s.next, []⟩

def Inbox.old (s : Inbox) (cut : Nat) : Nat :=
  (s.pending.filter (· < cut)).length

theorem finish_missing (s : Inbox) (id : Nat) :
    ((s.finish id).1.finish id).2 = false := by
  simp [Inbox.finish]

theorem start_fresh (s : Inbox) (cut : Nat) (hc : cut ≤ s.next) :
    (s.start.1).old cut = s.old cut := by
  simp [Inbox.start, Inbox.old, show ¬ s.next < cut by omega]

theorem filter_remove_le (xs : List Nat) (id cut : Nat) :
    ((xs.filter (· != id)).filter (· < cut)).length ≤ (xs.filter (· < cut)).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases he : x = id <;> by_cases hc : x < cut <;> simp_all <;> omega

theorem filter_remove_lt (xs : List Nat) (id cut : Nat) (hm : id ∈ xs) (hc : id < cut) :
    ((xs.filter (· != id)).filter (· < cut)).length < (xs.filter (· < cut)).length := by
  induction xs with
  | nil => simp at hm
  | cons x xs ih =>
    by_cases he : x = id
    · subst x
      have hle := filter_remove_le xs id cut
      simpa [hc, List.filter_filter] using Nat.lt_succ_of_le hle
    · have hm' : id ∈ xs := (List.mem_cons.1 hm).resolve_left (Ne.symm he)
      have hi := ih hm'
      by_cases hx : x < cut <;> simp_all

theorem finish_old_decreases (s : Inbox) (id cut : Nat)
    (hm : (s.finish id).2 = true) (hc : id < cut) :
    (s.finish id).1.old cut < s.old cut := by
  exact filter_remove_lt s.pending id cut (by simpa [Inbox.finish] using hm) hc

/-- A step of an inbox. The flag is true when the step finished a pending call whose id is
below `cut`. -/
inductive InboxStep (cut : Nat) : Inbox → Inbox → Bool → Prop
  | start (s : Inbox) : InboxStep cut s s.start.1 false
  | reserve (s : Inbox) : InboxStep cut s s.reserve false
  | finish (s : Inbox) (id : Nat) :
      InboxStep cut s (s.finish id).1 ((s.finish id).2 && decide (id < cut))
  | disconnect (s : Inbox) : InboxStep cut s s.disconnect false
  | wait (s : Inbox) : InboxStep cut s s false

theorem inbox_next_monotone {cut : Nat} {s t : Inbox} {old : Bool}
    (h : InboxStep cut s t old) : s.next ≤ t.next := by
  cases h <;> simp [Inbox.start, Inbox.reserve, Inbox.finish, Inbox.disconnect]

theorem inbox_old_credit {cut : Nat} {s t : Inbox} {old : Bool}
    (hc : cut ≤ s.next) (h : InboxStep cut s t old) :
    t.old cut + (if old then 1 else 0) ≤ s.old cut := by
  cases h with
  | start => simp [start_fresh _ _ hc]
  | reserve => simp [Inbox.reserve, Inbox.old]
  | finish id =>
    by_cases hm : (s.finish id).2 = true
    · by_cases hi : id < cut
      · have := finish_old_decreases s id cut hm hi
        simp only [hm, hi, decide_true, Bool.true_and, ↓reduceIte]
        omega
      · simpa [hm, hi, Inbox.finish, Inbox.old] using filter_remove_le s.pending id cut
    · have hz : (s.finish id).2 = false := by
        cases he : (s.finish id).2 <;> simp_all
      simp only [hz, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact filter_remove_le s.pending id cut
  | disconnect => simp [Inbox.disconnect, Inbox.old]
  | wait => simp

/-- Even if the network duplicates frames forever, only finitely many consume request slots
below the cut. Ids allocated later are at or above it. -/
theorem old_slots_eventually_stop (cut : Nat) (run : Nat → Inbox) (old : Nat → Bool)
    (hc : cut ≤ (run 0).next)
    (hs : ∀ i, InboxStep cut (run i) (run (i + 1)) (old i)) :
    ∃ k, ∀ i, k ≤ i → old i = false := by
  have hc' : ∀ i, cut ≤ (run i).next := by
    intro i
    induction i with
    | zero => exact hc
    | succ i ih => exact Nat.le_trans ih (inbox_next_monotone (hs i))
  have hle : ∀ i, (run (i + 1)).old cut ≤ (run i).old cut := by
    intro i
    have := inbox_old_credit (hc' i) (hs i)
    split at this <;> omega
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => (run i).old cut) hle
  refine ⟨k, fun i hi => ?_⟩
  have hp := inbox_old_credit (hc' i) (hs i)
  rw [hk i hi, hk (i + 1) (by omega)] at hp
  cases he : old i <;> simp_all <;> omega

/-- The unbroken portion of a fix-up retry epoch. The first adoption in the epoch may change
`pending` arbitrarily; later adoptions may only remove pending drops. A new abandonment, an
adoption of an obsolete prefix, or an interrupted write ends the epoch, so no step here
models one. -/
structure Fixup where
  /-- Pending drops, named by their original operations, which stay fixed when adoption
  re-keys the hub's ids. -/
  pending : List Nat
  /-- The restoring write has been made and its cache is still held. -/
  written : Bool
  /-- A current-epoch adoption has happened. -/
  aligned : Bool
  deriving Repr, DecidableEq

def Fixup.credit (s : Fixup) : Nat :=
  if s.written || (s.aligned && s.pending.isEmpty) then 0 else 1

def Fixup.write (s : Fixup) : Fixup × Bool :=
  if s.pending.isEmpty || s.written then (s, false)
  else ({ s with written := true }, true)

def Fixup.adopt (s : Fixup) (pending : List Nat) : Option Fixup :=
  if s.aligned && !pending.all s.pending.contains then none
  else some { pending, written := if pending.isEmpty then false else s.written, aligned := true }

theorem fixup_credit_le (s : Fixup) : s.credit ≤ 1 := by
  unfold Fixup.credit
  split <;> omega

theorem fixup_write_credit (s : Fixup) :
    s.write.1.credit + (if s.write.2 then 1 else 0) = s.credit := by
  unfold Fixup.write
  split
  · simp
  · simp_all [Fixup.credit]

theorem fixup_adopt_credit {s t : Fixup} {pending : List Nat}
    (h : s.adopt pending = some t) : t.credit ≤ s.credit := by
  unfold Fixup.adopt at h
  split at h
  · contradiction
  · rename_i hg
    cases h
    cases ha : s.aligned with
    | false =>
      cases hw : s.written <;> cases pending <;> simp [Fixup.credit, ha, hw]
    | true =>
      have hsub : pending.all s.pending.contains = true := by simpa [ha] using hg
      cases hp : s.pending with
      | nil =>
        have he : pending = [] := by
          cases pending with
          | nil => rfl
          | cons x xs =>
            have hx := (List.all_eq_true.1 hsub) x (by simp)
            simp [hp] at hx
        simp [Fixup.credit, ha, hp, he]
      | cons x xs =>
        cases hw : s.written <;> cases pending <;> simp [Fixup.credit, ha, hp, hw]

inductive FixupStep : Fixup → Fixup → Bool → Prop
  | write (s : Fixup) : FixupStep s s.write.1 s.write.2
  | adopt {s t : Fixup} (pending : List Nat) (h : s.adopt pending = some t) :
      FixupStep s t false
  | wait (s : Fixup) : FixupStep s s false

theorem fixup_step_credit {s t : Fixup} {emits : Bool} (h : FixupStep s t emits) :
    t.credit + (if emits then 1 else 0) ≤ s.credit := by
  cases h with
  | write => exact Nat.le_of_eq (fixup_write_credit _)
  | adopt _ h => simpa using fixup_adopt_credit h
  | wait => simp

theorem fixup_writes_bound (run : Nat → Fixup) (emits : Nat → Bool)
    (hs : ∀ i, FixupStep (run i) (run (i + 1)) (emits i)) (k : Nat) :
    sumN k (fun i => if emits i then 1 else 0) + (run k).credit ≤ (run 0).credit := by
  induction k with
  | zero => simp [sumN]
  | succ k ih =>
    have := fixup_step_credit (hs k)
    simp only [sumN]
    omega

theorem fixup_writes_le_one (run : Nat → Fixup) (emits : Nat → Bool)
    (hs : ∀ i, FixupStep (run i) (run (i + 1)) (emits i)) (k : Nat) :
    sumN k (fun i => if emits i then 1 else 0) ≤ 1 := by
  have := fixup_writes_bound run emits hs k
  have := fixup_credit_le (run 0)
  omega

/-- Restoring writes eventually stop in such an epoch; `fixup_writes_le_one` shows there is at
most one. The cache is cleared only once `pending` is empty after alignment, and later
adoptions cannot refill it. A write is a finite saved work list plus a final operation. The
number of retries is unbounded. -/
theorem fixups_eventually_stop (run : Nat → Fixup) (emits : Nat → Bool)
    (hs : ∀ i, FixupStep (run i) (run (i + 1)) (emits i)) :
    ∃ k, ∀ i, k ≤ i → emits i = false := by
  have hle : ∀ i, (run (i + 1)).credit ≤ (run i).credit := by
    intro i
    have := fixup_step_credit (hs i)
    split at this <;> omega
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => (run i).credit) hle
  refine ⟨k, fun i hi => ?_⟩
  have hstep := fixup_step_credit (hs i)
  rw [hk i hi, hk (i + 1) (by omega)] at hstep
  cases he : emits i <;> simp_all <;> omega

/-- A publication keeps two kinds of work apart: restoring saved state, and giving pending
drops a new publication id. The cached restoring write is bounded as for `Fixup`. A neutral
tip is needed when the hub already has the current head but not the pending drops. -/
structure Publication where
  cache : Fixup
  /-- The node's head equals the hub's, as checked at this write; later replies can change it. -/
  headKnown : Bool
  deriving Repr, DecidableEq

/-- One write. The second and third results say whether it was restoring work or a neutral
publication tip. Either writes a child of the head, so the result state has `headKnown` false.
That is this model's reading, not a fact about the real state afterwards: canonical content
has no nonce, so a restoring fix-up can be identical to the known head (NodeSettle's
`write_known`), leaving the head known, and the next write is then a neutral tip that
teaches no new head. NodeSettle reads only the decision and the cache (`pubOf`), not
`headKnown`. -/
def Publication.write (s : Publication) : Publication × Bool × Bool :=
  let (cache, restoring) := s.cache.write
  let tip := !restoring && !cache.pending.isEmpty && s.headKnown
  (⟨cache, s.headKnown && !(restoring || tip)⟩, restoring, tip)

theorem publication_progress (s : Publication) (hp : s.cache.pending ≠ [])
    (hk : s.headKnown = true) : s.write.2.1 || s.write.2.2 = true := by
  cases s with
  | mk cache headKnown =>
    cases cache with
    | mk pending written aligned =>
      cases pending with
      | nil => contradiction
      | cons x xs =>
        cases written <;> simp_all [Publication.write, Fixup.write]

/-- If the cache's pending list is empty, `write` makes neither a restoring write nor a neutral
tip and leaves the state unchanged, whatever head is known. An eligible node's pending list is
empty once it has the hub's current ordered records (`EntryAssembly.eligible_pending_empty`). -/
theorem publication_empty_pending (s : Publication) (hp : s.cache.pending = []) :
    s.write = (s, false, false) := by
  cases s with
  | mk cache headKnown =>
    cases cache with
    | mk pending written aligned =>
      simp only at hp
      subst pending
      cases headKnown <;> simp [Publication.write, Fixup.write]

/-- Writing again from the result state (`s.write.1`, whose head reads as not known) does
neither kind of work. This bounds one repeat only, not tips across arbitrarily many changes
of knowledge, and says nothing about the real state after a write (see `Publication.write`). -/
theorem publication_retry (s : Publication) :
    s.write.1.write.2 = (false, false) := by
  cases s with
  | mk cache headKnown =>
    cases cache with
    | mk pending written aligned =>
      cases pending <;> cases written <;> cases headKnown <;>
        simp [Publication.write, Fixup.write]

/-- A neutral tip does not clear the cache or replay its restoring work. -/
theorem publication_tip_cached (s : Publication) (ht : s.write.2.2 = true) :
    s.cache.written = true ∧ s.write.1.cache = s.cache := by
  cases s with
  | mk cache headKnown =>
    cases cache with
    | mk pending written aligned =>
      cases pending <;> cases written <;>
        simp_all [Publication.write, Fixup.write]

end Musubi.Retry

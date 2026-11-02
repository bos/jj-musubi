/-
Finite retry-control debt under explicit epoch constraints. Request ids are never reused.
Completing or retiring a request removes its slot; once a finite cut is chosen, new calls
cannot create old slots. Fix-ups are cached across retries. The fix-up bound additionally
requires pending drops, named by immutable originals, to shrink after a first alignment.
The tests check slot consumption and cached writes, not eventual entry into such an epoch.
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

/-- Both delivery and timeout retire a slot. Delivery succeeds only for a live slot. -/
def Inbox.finish (s : Inbox) (id : Nat) : Inbox × Bool :=
  (⟨s.next, s.pending.filter (· != id)⟩, s.pending.contains id)

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

inductive InboxStep (cut : Nat) : Inbox → Inbox → Bool → Prop
  | start (s : Inbox) : InboxStep cut s s.start.1 false
  | finish (s : Inbox) (id : Nat) :
      InboxStep cut s (s.finish id).1 ((s.finish id).2 && decide (id < cut))
  | disconnect (s : Inbox) : InboxStep cut s s.disconnect false
  | wait (s : Inbox) : InboxStep cut s s false

theorem inbox_next_monotone {cut : Nat} {s t : Inbox} {old : Bool}
    (h : InboxStep cut s t old) : s.next ≤ t.next := by
  cases h <;> simp [Inbox.start, Inbox.finish, Inbox.disconnect]

theorem inbox_old_credit {cut : Nat} {s t : Inbox} {old : Bool}
    (hc : cut ≤ s.next) (h : InboxStep cut s t old) :
    t.old cut + (if old then 1 else 0) ≤ s.old cut := by
  cases h with
  | start => simp [start_fresh _ _ hc]
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

/-- Even if the network duplicates old frames forever, only finitely many can consume
pre-cut request slots. New ids cannot recharge the old-slot budget. -/
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

/-- The successful, unbroken portion of a fix-up retry epoch. `aligned` records that a
current-epoch adoption has happened; that first adoption may change pending arbitrarily.
Later adoptions must only remove pending drops. New abandonments, obsolete-prefix adoption
and interrupted writes end the epoch and are not silently treated as retries here. -/
structure Fixup where
  /-- Immutable original-operation names, not the hub ids that adoption can re-key. -/
  pending : List Nat
  written : Bool
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

/-- At most one completed restoring-payload invocation per node in such an epoch. Clearing
the cache requires empty pending after alignment, which later adoptions cannot recharge. The
invocation writes its finite saved work list and final operation. Retries are unbounded. -/
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

/-- Restoring saved state and giving pending drops a new publication id are separate work.
The cached restoring write is still bounded above; a neutral tip is needed when the hub
already has the current head without its pending drops. `headKnown` is the equality checked
at this write boundary, not a promise that future replies cannot change it. -/
structure Publication where
  cache : Fixup
  headKnown : Bool
  deriving Repr, DecidableEq

/-- The second and third results distinguish restoring work from a neutral publication tip.
Either creates a new child, so the resulting head differs from the previously known head. -/
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

/-- Retrying the same state without a new learned head or adoption repeats neither work.
This is not a bound on tips across arbitrarily many changes of knowledge. -/
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

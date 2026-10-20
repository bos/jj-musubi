/-
Chunked blob transfer (`protocol.md`, "Chunked blobs"), as a separate model of one session
transferring one blob `b` from a sender to a content-addressed receiver.
-/
import Musubi.Basic

namespace Musubi.Chunks

/-- A chunk `(offset, payload)`; its length is the payload length. One session is modeled,
so the session tag is implicit. -/
structure Chunk where
  off : Nat
  data : List Nat

/-- Receiver state and network. -/
structure CState where
  /-- The bytes received so far, by offset (volatile session state). -/
  got : Nat → Option Nat
  /-- The content-addressed store's entry for the blob id (persistent). -/
  store : Option (List Nat)
  /-- Every chunk ever sent; each may be delivered any number of times, or never. -/
  net : Chunk → Prop

/-- Apply a chunk: only missing bytes are filled; duplicates and overlaps are ignored. -/
def fill (got : Nat → Option Nat) (c : Chunk) : Nat → Option Nat :=
  fun i => (got i).or (if c.off ≤ i then c.data[i - c.off]? else none)

/-- Every byte in `[0, total)` has arrived. -/
def complete (got : Nat → Option Nat) (total : Nat) : Prop := ∀ i, i < total → got i ≠ none

/-- The assembled bytes `[0, total)`. -/
def assembled (got : Nat → Option Nat) (total : Nat) : List Nat :=
  (List.range total).map (fun i => (got i).getD 0)

def initC : CState := { got := fun _ => none, store := none, net := fun _ => False }

section

variable (hash : List Nat → Nat) (b : List Nat) (limit : Nat)

/-- The honest sender's chunk at `off` of length at most `len`. -/
def honest (off len : Nat) : Chunk := ⟨off, (b.drop off).take len⟩

/-- Steps of one session. `inject` lets the network deliver an arbitrary chunk (corrupted,
stale, or from another sender); `protocol.md` rules this out, and the safety proof does not
need it ruled out. `Finish(session, hash b, length b)` succeeds, restarts on a hash mismatch,
or (when incomplete) just reports missing ranges, like `Status`. -/
inductive CStep : CState → CState → Prop
  | send (s : CState) (off len : Nat) (hlen : len ≤ limit) :
      CStep s { s with net := fun c => s.net c ∨ c = honest b off len }
  | inject (s : CState) (c : Chunk) : CStep s { s with net := fun c' => s.net c' ∨ c' = c }
  | recv (s : CState) (c : Chunk) (hc : s.net c) : CStep s { s with got := fill s.got c }
  | status (s : CState) : CStep s s
  | finishOk (s : CState) (hcomp : complete s.got b.length)
      (hh : hash (assembled s.got b.length) = hash b) :
      CStep s { s with store := some (assembled s.got b.length) }
  | finishBad (s : CState) (hcomp : complete s.got b.length)
      (hh : hash (assembled s.got b.length) ≠ hash b) :
      CStep s { s with got := fun _ => none }
  | finishStored (s : CState) (d : List Nat) (hd : s.store = some d) (hh : hash d = hash b) :
      CStep s s
  | crashRecv (s : CState) : CStep s { s with got := fun _ => none }
  | crashSender (s : CState) : CStep s s

inductive CReach : CState → Prop
  | init : CReach initC
  | step {s s' : CState} : CReach s → CStep hash b limit s s' → CReach s'

end

/-! ## Safety: a finished blob is byte-identical to the one sent -/

section safety

variable {hash : List Nat → Nat} {b : List Nat} {limit : Nat}

/-- A successful `Finish` yields exactly the sender's bytes. -/
theorem finish_identical (hinj : ∀ x y, hash x = hash y → x = y)
    {got : Nat → Option Nat} (hh : hash (assembled got b.length) = hash b) :
    assembled got b.length = b := hinj _ _ hh

/-- **Chunk safety**: in every reachable state, a stored (finished) blob is `b`. -/
theorem stored_identical (hinj : ∀ x y, hash x = hash y → x = y) {s : CState}
    (h : CReach hash b limit s) {d : List Nat} (hd : s.store = some d) : d = b := by
  induction h generalizing d with
  | init => simp [initC] at hd
  | step _ hs ih =>
    cases hs with
    | finishOk hcomp hh =>
      simp at hd; subst hd; exact finish_identical hinj hh
    | _ => exact ih hd

end safety

/-! ## Liveness: with eventual delivery every session finishes -/

section liveness

variable (hash : List Nat → Nat) (b : List Nat) (limit : Nat)

/-- Reliable steps: an honest chunk starting at a missing byte is sent and delivered, or the
session finishes (successfully, or by restarting after a mismatch caused by earlier
corrupted chunks). No crashes and no injected chunks. -/
inductive LStep : CState → CState → Prop
  | deliver (s : CState) (i : Nat) (hi : i < b.length) (hm : s.got i = none) :
      LStep s { s with got := fill s.got (honest b i limit),
                       net := fun c => s.net c ∨ c = honest b i limit }
  | finishOk (s : CState) (hs : s.store = none) (hcomp : complete s.got b.length)
      (hh : hash (assembled s.got b.length) = hash b) :
      LStep s { s with store := some (assembled s.got b.length) }
  | finishBad (s : CState) (hs : s.store = none) (hcomp : complete s.got b.length)
      (hh : hash (assembled s.got b.length) ≠ hash b) :
      LStep s { s with got := fun _ => none }

end liveness

section livenessProofs

variable {hash : List Nat → Nat} {b : List Nat} {limit : Nat}

theorem lstep_reach {s s' : CState} (h : CReach hash b limit s) (hs : LStep hash b limit s s') :
    CReach hash b limit s' := by
  cases hs with
  | deliver i hi hm =>
    have h1 := h.step (CStep.send s i limit (Nat.le_refl _))
    exact h1.step (CStep.recv _ (honest b i limit) (Or.inr rfl))
  | finishOk hs hcomp hh => exact h.step (CStep.finishOk s hcomp hh)
  | finishBad hs hcomp hh => exact h.step (CStep.finishBad s hcomp hh)

/-- Some byte below `b.length` is wrong. -/
def corrupt (b : List Nat) (got : Nat → Option Nat) : Prop :=
  ∃ i, i < b.length ∧ ∃ v, got i = some v ∧ b[i]? ≠ some v

/-- An honest chunk only ever supplies correct bytes. -/
theorem fill_honest {got : Nat → Option Nat} {i lim j v : Nat}
    (h : fill got (honest b i lim) j = some v) :
    got j = some v ∨ (got j = none ∧ b[j]? = some v) := by
  unfold fill honest at h
  cases hg : got j with
  | some w => simp [hg] at h; left; rw [h]
  | none =>
    simp only [hg, Option.none_or] at h
    right
    refine ⟨rfl, ?_⟩
    by_cases hij : i ≤ j
    · simp only [hij, ↓reduceIte, List.getElem?_take, List.getElem?_drop] at h
      by_cases hl : j - i < lim
      · simp only [hl, ↓reduceIte, Nat.add_sub_cancel' hij] at h; exact h
      · simp only [hl, ↓reduceIte] at h; cases h
    · simp only [hij, ↓reduceIte] at h; cases h

theorem fill_mono {got : Nat → Option Nat} {c : Chunk} {j v : Nat} (h : got j = some v) :
    fill got c j = some v := by
  simp [fill, h]

theorem fill_honest_self {got : Nat → Option Nat} {i : Nat} (hlim : 0 < limit)
    (hi : i < b.length) (hm : got i = none) : fill got (honest b i limit) i ≠ none := by
  simp [fill, honest, hm, hlim, hi]

theorem assembled_eq {got : Nat → Option Nat} (hcomp : complete got b.length)
    (hnc : ¬ corrupt b got) : assembled got b.length = b := by
  apply List.ext_getElem
  · simp [assembled]
  · intro i h1 h2
    simp only [assembled, List.getElem_map, List.getElem_range]
    have hi : i < b.length := h2
    cases hg : got i with
    | none => exact absurd hg (hcomp i hi)
    | some v =>
      have : b[i]? = some v := by
        refine Classical.byContradiction fun hne => hnc ⟨i, hi, v, hg, hne⟩
      rw [List.getElem?_eq_getElem hi] at this
      simp only [Option.getD_some]
      exact (Option.some.inj this).symm

open Classical in
/-- The measure: (some byte is corrupt, missing bytes, not yet stored). -/
noncomputable def cmeasure (b : List Nat) (s : CState) : Nat × Nat × Nat :=
  (if corrupt b s.got then 1 else 0, cnt b.length (fun i => s.got i = none),
   if s.store = none then 1 else 0)

def Lex3 : Nat × Nat × Nat → Nat × Nat × Nat → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem lex3_wf : WellFounded Lex3 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

open Classical in
theorem cmeasure_decreases (hlim : 0 < limit) {s s' : CState}
    (hs : LStep hash b limit s s') : Lex3 (cmeasure b s') (cmeasure b s) := by
  cases hs with
  | deliver i hi hm =>
    have hcor : corrupt b (fill s.got (honest b i limit)) ↔ corrupt b s.got := by
      constructor
      · rintro ⟨j, hj, v, hv, hne⟩
        rcases fill_honest hv with h | ⟨_, h⟩
        · exact ⟨j, hj, v, h, hne⟩
        · exact absurd h hne
      · rintro ⟨j, hj, v, hv, hne⟩
        exact ⟨j, hj, v, fill_mono hv, hne⟩
    have hlt : cnt b.length (fun j => fill s.got (honest b i limit) j = none) <
        cnt b.length (fun j => s.got j = none) := by
      apply cnt_lt
      · intro j _ hj
        cases hg : s.got j with
        | none => rfl
        | some v => rw [fill_mono hg] at hj; cases hj
      · exact ⟨i, hi, hm, fill_honest_self hlim hi hm⟩
    unfold cmeasure
    simp only [hcor]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ hlt)
  | finishOk hst hcomp hh =>
    unfold cmeasure
    simp only [hst, reduceCtorEq, ↓reduceIte]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Nat.zero_lt_one))
  | finishBad hst hcomp hh =>
    have hc : corrupt b s.got := by
      refine Classical.byContradiction fun hnc => hh ?_
      rw [assembled_eq hcomp hnc]
    have hnc : ¬ corrupt b (fun _ => none) := by
      rintro ⟨j, _, v, hv, _⟩; cases hv
    unfold cmeasure
    simp only [hc, hnc, ↓reduceIte]
    exact Prod.Lex.left _ _ Nat.zero_lt_one

/-- No infinite run of reliable chunk steps. -/
theorem lstep_wf (hlim : 0 < limit) : WellFounded (fun s' s => LStep hash b limit s s') :=
  Subrelation.wf (fun hs => cmeasure_decreases hlim hs) (InvImage.wf (cmeasure b) lex3_wf)

/-- Progress: until the blob is stored, some reliable step is enabled. -/
theorem lprogress {s : CState} (hs : s.store = none) : ∃ s', LStep hash b limit s s' := by
  by_cases hmiss : ∃ i, i < b.length ∧ s.got i = none
  · obtain ⟨i, hi, hm⟩ := hmiss
    exact ⟨_, LStep.deliver s i hi hm⟩
  · have hcomp : complete s.got b.length := fun i hi hn => hmiss ⟨i, hi, hn⟩
    by_cases hh : hash (assembled s.got b.length) = hash b
    · exact ⟨_, LStep.finishOk s hs hcomp hh⟩
    · exact ⟨_, LStep.finishBad s hs hcomp hh⟩

inductive LSteps (hash : List Nat → Nat) (b : List Nat) (limit : Nat) :
    CState → CState → Prop
  | refl (s : CState) : LSteps hash b limit s s
  | head {s t u : CState} : LStep hash b limit s t → LSteps hash b limit t u →
      LSteps hash b limit s u

/-- **Chunk liveness**: from any reachable state (even after corrupted chunks or crashes),
reliable delivery finishes the session with the receiver storing exactly `b`. -/
theorem session_finishes (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit)
    {s : CState} (h : CReach hash b limit s) :
    ∃ s', LSteps hash b limit s s' ∧ s'.store = some b := by
  refine WellFounded.induction (C := fun s => CReach hash b limit s →
    ∃ s', LSteps hash b limit s s' ∧ s'.store = some b) (lstep_wf (hash := hash) (b := b) hlim) s
    (fun s ih h => ?_) h
  cases hst : s.store with
  | some d => exact ⟨s, LSteps.refl s, by rw [hst, stored_identical hinj h hst]⟩
  | none =>
    obtain ⟨s', hs'⟩ := lprogress (hash := hash) (limit := limit) hst
    obtain ⟨u, hu, hus⟩ := ih s' hs' (lstep_reach h hs')
    exact ⟨u, LSteps.head hs' hu, hus⟩

end livenessProofs

end Musubi.Chunks

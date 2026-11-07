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
  /-- The store drops the blob, as a sweep of old blobs does. -/
  | evict (s : CState) : CStep s { s with store := none }
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
    | evict => simp at hd
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

/-! ## The prefix receiver

musubi's receiver, `BlobStore::receive`, follows a narrower design than `CStep`'s: it keeps
only a contiguous prefix of the blob, dropping a chunk that starts past it; reports the
prefix's length rather than the missing ranges; and checks the hash as soon as the prefix
reaches the length the chunk claims, rather than at an explicit `Finish`. A sweep removes the
partial blob, the stored one, or both. Every step it takes is a run of `CStep`s
(`preach_abs`), so `stored_identical` holds of it; and a sender that resends from the prefix
it reports finishes (`prefix_finishes`). -/

/-- The prefix receiver's state: the prefix it has (`partial/<id>`), its store's entry for the
blob (`complete/<id>`), and the network. -/
structure PState where
  pre : List Nat
  store : Option (List Nat)
  net : Chunk → Prop

def initP : PState := { pre := [], store := none, net := fun _ => False }

/-- The state of the full model that a prefix receiver's state stands for. -/
def absP (s : PState) : CState := { got := fun i => s.pre[i]?, store := s.store, net := s.net }

/-- Chunk `c` extends `pre`: it starts within or at the end of it, and ends past it. -/
def Extends (pre : List Nat) (c : Chunk) : Prop :=
  c.off ≤ pre.length ∧ pre.length < c.off + c.data.length

instance (pre : List Nat) (c : Chunk) : Decidable (Extends pre c) := by
  unfold Extends; infer_instance

/-- What the receiver keeps of chunk `c`: the bytes past `pre`, if `c` extends it. -/
def extend (pre : List Nat) (c : Chunk) : List Nat :=
  if Extends pre c then pre ++ c.data.drop (pre.length - c.off) else pre

section prefixDefs

variable (hash : List Nat → Nat) (b : List Nat) (limit : Nat)

/-- `BlobStore::receive`, given chunk `c` of the blob `b`, whose length it is told is `total`.
The reply is `some n` for `Received::Prefix(n)` and `none` for `Received::Complete`. -/
def receive (s : PState) (c : Chunk) (total : Nat) : PState × Option Nat :=
  match s.store with
  | some _ => (s, none)
  | none =>
    let p := extend s.pre c
    if p.length < total then ({ s with pre := p }, some p.length)
    else if hash p = hash b ∧ p.length = total then ({ s with pre := [], store := some p }, none)
    else ({ s with pre := [] }, some 0)

/-- Steps of the prefix receiver. A chunk is delivered with any claimed length, since the
length travels with the chunk. A crash of the receiving process keeps the partial blob, so it
is no step; one in the middle of a write leaves part of a chunk, which `inject` covers. -/
inductive PStep : PState → PState → Prop
  | send (s : PState) (off len : Nat) (hlen : len ≤ limit) :
      PStep s { s with net := fun c => s.net c ∨ c = honest b off len }
  | inject (s : PState) (c : Chunk) : PStep s { s with net := fun c' => s.net c' ∨ c' = c }
  | recv (s : PState) (c : Chunk) (total : Nat) (hc : s.net c) :
      PStep s (receive hash b s c total).1
  | sweepPartial (s : PState) : PStep s { s with pre := [] }
  | sweepStored (s : PState) : PStep s { s with store := none }

inductive PReach : PState → Prop
  | init : PReach initP
  | step {s s' : PState} : PReach s → PStep hash b limit s s' → PReach s'

/-- Reliable steps of the prefix receiver: the sender sends the honest chunk at the prefix
the receiver reports, with the blob's length, and the network delivers it. -/
inductive PLStep : PState → PState → Prop
  | resend (s : PState) (hs : s.store = none) :
      PLStep s (receive hash b { s with net := fun c => s.net c ∨ c = honest b s.pre.length limit }
        (honest b s.pre.length limit) b.length).1

inductive PLSteps : PState → PState → Prop
  | refl (s : PState) : PLSteps s s
  | head {s t u : PState} : PLStep hash b limit s t → PLSteps t u → PLSteps s u

end prefixDefs

section prefixProofs

variable {hash : List Nat → Nat} {b : List Nat} {limit : Nat}

theorem got_nil : (fun (i : Nat) => ([] : List Nat)[i]?) = fun _ => none := by
  funext i; simp

/-- Keeping the bytes of a chunk that extends the prefix is `fill`. -/
theorem extend_fill {pre : List Nat} {c : Chunk} (h : Extends pre c) :
    (fun i => (extend pre c)[i]?) = fill (fun i => pre[i]?) c := by
  funext i
  obtain ⟨h1, _⟩ := h
  simp only [extend, Extends, true_and, *, ↓reduceIte, fill]
  by_cases hi : i < pre.length
  · rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]; rfl
  · have hle : pre.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hle, List.getElem?_drop, List.getElem?_eq_none hle]
    simp only [Option.none_or, Nat.le_trans h1 hle, ↓reduceIte]
    congr 1; omega

theorem assembled_self (l : List Nat) : assembled (fun i => l[i]?) l.length = l := by
  apply List.ext_getElem
  · simp [assembled]
  · intro i h1 h2
    simp [assembled, List.getElem?_eq_getElem h2]

theorem complete_self (l : List Nat) : complete (fun i => l[i]?) l.length := by
  intro i hi; simp [List.getElem?_eq_getElem hi]

/-- **Refinement**: every state the prefix receiver reaches stands for one the full model
reaches, through a run of `CStep`s: `recv` for a chunk taken and none for one dropped,
`finishOk` and `crashRecv` for one that finishes the blob, `crashRecv` for a hash mismatch,
`finishStored` for a chunk of a stored blob, and `crashRecv` and `evict` for sweeps. -/
theorem preach_abs (hinj : ∀ x y, hash x = hash y → x = y) {s : PState}
    (h : PReach hash b limit s) : CReach hash b limit (absP s) := by
  induction h with
  | init =>
    have e : absP initP = initC := by simp only [absP, initP, initC, got_nil]
    rw [e]; exact CReach.init
  | @step s _ _ hs ih =>
    cases hs with
    | send off len hlen => exact ih.step (CStep.send _ off len hlen)
    | inject c => exact ih.step (CStep.inject _ c)
    | sweepPartial =>
      have e : absP { s with pre := [] } = { absP s with got := fun _ => none } := by
        simp only [absP, got_nil]
      rw [e]; exact ih.step (CStep.crashRecv _)
    | sweepStored => exact ih.step (CStep.evict _)
    | recv c total hc =>
      cases hst : s.store with
      | some d =>
        have hd : (absP s).store = some d := hst
        have hdb := stored_identical hinj ih hd
        simp only [receive, hst]
        exact ih.step (CStep.finishStored _ d hd (by rw [hdb]))
      | none =>
        have h1 : CReach hash b limit (absP { s with pre := extend s.pre c }) := by
          by_cases hx : Extends s.pre c
          · have e : absP { s with pre := extend s.pre c } =
                { absP s with got := fill (absP s).got c } := by
              simp only [absP, extend_fill hx]
            rw [e]; exact ih.step (CStep.recv _ c hc)
          · have e : extend s.pre c = s.pre := by simp [extend, hx]
            rw [e]; exact ih
        rw [hst] at h1
        simp only [receive, hst]
        split
        · exact h1
        · split
          · rename_i hok
            obtain ⟨hh, _⟩ := hok
            have hpb := hinj _ _ hh
            have h2 := h1.step (CStep.finishOk _ (by rw [← hpb]; exact complete_self _)
              (by simp only [absP]; rw [← hpb, assembled_self, hpb]))
            have h3 := h2.step (CStep.crashRecv _)
            have e : absP { s with pre := [], store := some (extend s.pre c) } =
                { { absP { s with pre := extend s.pre c } with
                    store := some (assembled (absP { s with pre := extend s.pre c }).got
                      b.length) } with got := fun _ => none } := by
              simp only [absP, got_nil]; rw [← hpb, assembled_self]
            rw [e]; exact h3
          · have e : absP { pre := [], store := none, net := s.net } =
                { absP s with got := fun _ => none } := by
              simp only [absP, got_nil, hst]
            rw [e]; exact ih.step (CStep.crashRecv _)

/-- **Prefix safety**: a blob the prefix receiver stores is `b`. -/
theorem prefix_stored_identical (hinj : ∀ x y, hash x = hash y → x = y) {s : PState}
    (h : PReach hash b limit s) {d : List Nat} (hd : s.store = some d) : d = b :=
  stored_identical (s := absP s) hinj (preach_abs hinj h) hd

theorem plstep_reach {s s' : PState} (h : PReach hash b limit s)
    (hs : PLStep hash b limit s s') : PReach hash b limit s' := by
  cases hs with
  | resend hst =>
    have h1 := h.step (PStep.send s s.pre.length limit (Nat.le_refl _))
    exact h1.step (PStep.recv _ _ b.length (Or.inr rfl))

/-- The honest chunk at the prefix adds the blob's bytes that follow it, if any. -/
theorem extend_honest (p : List Nat) (lim : Nat) :
    extend p (honest b p.length lim) = p ++ (b.drop p.length).take lim := by
  unfold extend honest Extends
  split
  · simp
  · rename_i hx
    have : ((b.drop p.length).take lim).length = 0 := by simp at hx ⊢; omega
    rw [List.length_eq_zero_iff.mp this, List.append_nil]

theorem prefix_extend {p : List Nat} (h : p <+: b) (lim : Nat) :
    p ++ (b.drop p.length).take lim <+: b := by
  rw [List.prefix_iff_eq_take.mp h, List.length_take, Nat.min_eq_left h.length_le,
    ← List.take_add]
  exact List.take_prefix _ _

open Classical in
/-- The measure: (not yet stored, the prefix is not a prefix of `b`, bytes missing). -/
noncomputable def pmeasure (b : List Nat) (s : PState) : Nat × Nat × Nat :=
  (if s.store = none then 1 else 0, if s.pre <+: b then 0 else 1, b.length - s.pre.length)

open Classical in
theorem pmeasure_decreases (hlim : 0 < limit) {s s' : PState}
    (hs : PLStep hash b limit s s') : Lex3 (pmeasure b s') (pmeasure b s) := by
  cases hs with
  | resend hst =>
    simp only [receive, hst, extend_honest]
    generalize hq : s.pre ++ (b.drop s.pre.length).take limit = q
    have hpq : s.pre <+: q := hq ▸ List.prefix_append _ _
    have hqlen : q.length = s.pre.length + min limit (b.length - s.pre.length) := by
      rw [← hq]; simp
    split
    · rename_i hlt
      have hpre : (q <+: b) = (s.pre <+: b) :=
        propext ⟨hpq.trans, fun h => hq ▸ prefix_extend h limit⟩
      unfold pmeasure
      simp only [hst, hpre]
      refine Prod.Lex.right _ (Prod.Lex.right _ ?_)
      omega
    · split
      · unfold pmeasure
        simp only [hst, reduceCtorEq, ↓reduceIte]
        exact Prod.Lex.left _ _ Nat.zero_lt_one
      · rename_i _ hbad
        have hnp : ¬ s.pre <+: b := by
          intro hp
          have hqb : q <+: b := hq ▸ prefix_extend hp limit
          have hqe : q = b := hqb.eq_of_length (by have := hqb.length_le; omega)
          exact hbad ⟨congrArg hash hqe, congrArg List.length hqe⟩
        unfold pmeasure
        simp only [hst, hnp, List.nil_prefix, ↓reduceIte]
        exact Prod.Lex.right _ (Prod.Lex.left _ _ Nat.zero_lt_one)

/-- No infinite run of resends from the prefix. -/
theorem plstep_wf (hlim : 0 < limit) : WellFounded (fun s' s => PLStep hash b limit s s') :=
  Subrelation.wf (fun hs => pmeasure_decreases hlim hs) (InvImage.wf (pmeasure b) lex3_wf)

/-- **Prefix liveness**: from any reachable state, a sender that resends from the prefix the
receiver reports finishes the transfer, with the receiver storing exactly `b`. -/
theorem prefix_finishes (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit)
    {s : PState} (h : PReach hash b limit s) :
    ∃ s', PLSteps hash b limit s s' ∧ s'.store = some b := by
  refine WellFounded.induction (C := fun s => PReach hash b limit s →
    ∃ s', PLSteps hash b limit s s' ∧ s'.store = some b)
    (plstep_wf (hash := hash) (b := b) hlim) s (fun s ih h => ?_) h
  cases hst : s.store with
  | some d => exact ⟨s, PLSteps.refl s, by rw [hst, prefix_stored_identical hinj h hst]⟩
  | none =>
    have hs' := PLStep.resend (hash := hash) (b := b) (limit := limit) s hst
    obtain ⟨u, hu, hus⟩ := ih _ hs' (plstep_reach h hs')
    exact ⟨u, PLSteps.head hs' hu, hus⟩

end prefixProofs

/-! ## Attempts under a deadline

`prefix_finishes` resends one chunk at a time and counts no time. musubi's senders keep a
window of chunks in flight, each request with a deadline from when it was sent, so that a link
too slow to carry a window before the deadline cuts an attempt short. Of an attempt's window
the receiver takes the first `m` chunks, in order, and the sender hears its replies to the
first `k` before the deadline (`attempt`), going on from the furthest prefix they report
(`next`). The chunks it doesn't hear of may still arrive, after it has stopped waiting
(`ARun.late`).

From within the receiver's prefix, an attempt that hears `k` replies takes the prefix at least
`k` chunks on, or to the end (`attempt_progress`). One from the beginning, as musubi's senders
made once, takes it nowhere once the prefix holds the chunks it delivers (`restart_stalls`), as
often as it is made. From any state the receiver reaches, every attempt that hears a reply
brings the transfer nearer its end, and a chunk arriving late never takes it further away
(`attempt_decreases`, `late_le`), so that a run ends with the receiver storing the blob within
a number of attempts fixed by where it starts (`attempts_finish`). -/

/-- `s` once chunk `c` has been sent. -/
def sent (s : PState) (c : Chunk) : PState := { s with net := fun c' => s.net c' ∨ c' = c }

section attemptDefs

variable (hash : List Nat → Nat) (b : List Nat) (limit : Nat)

/-- The honest chunks of a window of `w` from offset `o`, one after another. -/
def windowFrom : Nat → Nat → List Chunk
  | _, 0 => []
  | o, w + 1 => honest b o limit :: windowFrom (o + limit) w

/-- The receiver takes chunks `cs` in order, each sent and then delivered claiming the blob's
length, as `PStep.send` and `PStep.recv` take it: its state after, and its replies. -/
def deliver : PState → List Chunk → PState × List (Option Nat)
  | s, [] => (s, [])
  | s, c :: cs =>
    let r := receive hash b (sent s c) c b.length
    ((deliver r.1 cs).1, r.2 :: (deliver r.1 cs).2)

end attemptDefs

/-- The furthest prefix replies `rs` report, or `none` if one says the receiver has the blob. -/
def furthest : List (Option Nat) → Option Nat
  | [] => some 0
  | r :: rs => r.bind fun n => (furthest rs).map (max n)

/-- Where a sender that started from `o` goes on from, having heard `rs`: the furthest prefix
they report, `o` if it heard none, or `none` once it hears that the receiver has the blob. -/
def next (o : Nat) (rs : List (Option Nat)) : Option Nat :=
  if rs = [] then some o else furthest rs

section attemptRuns

variable (hash : List Nat → Nat) (b : List Nat) (limit : Nat)

/-- An attempt from offset `o`: the receiver takes the first `m` chunks of a window from `o`,
and the sender hears its replies to the first `k` before the deadline. The receiver's state
after, and where the sender goes on from. -/
def attempt (s : PState) (o m k : Nat) : PState × Option Nat :=
  ((deliver hash b s (windowFrom b limit o m)).1,
    next o ((deliver hash b s (windowFrom b limit o m)).2.take k))

/-- A run of a transfer whose link delivers: the receiver, and where its sender goes on from,
through `n` attempts that each hear a reply, chunks of earlier windows that reach the receiver
after their sender stopped waiting for them, and a sender going on from the receiver's prefix,
as a downloader, being the receiver, does before each attempt. -/
inductive ARun : Nat → PState × Nat → PState × Nat → Prop
  | refl (x : PState × Nat) : ARun 0 x x
  | attempt {n : Nat} {s : PState} {o m k : Nat} {z : PState × Nat} (hk : 0 < k)
      (hkm : k ≤ m) (hs : s.store = none) :
      ARun n ((attempt hash b limit s o m k).1, (attempt hash b limit s o m k).2.getD o) z →
      ARun (n + 1) (s, o) z
  | late {n : Nat} {s : PState} {o off : Nat} {z : PState × Nat} :
      ARun n ((deliver hash b s [honest b off limit]).1, o) z → ARun n (s, o) z
  | reread {n : Nat} {s : PState} {o : Nat} {z : PState × Nat} :
      ARun n (s, s.pre.length) z → ARun n (s, o) z

end attemptRuns

open Classical in
/-- The measure: none once the receiver has the blob; otherwise more for a prefix that isn't
`b`'s, then for a sender ahead of the prefix, then for the bytes the sender has still to go. -/
noncomputable def ameasure (b : List Nat) (x : PState × Nat) : Nat :=
  if x.1.store = none then
    1 + (if x.1.pre <+: b then 0 else 3 * (b.length + 1)) +
      (if x.1.pre.length < x.2 then b.length + 1 else 0) + (b.length - x.2)
  else 0

section attemptProofs

variable {hash : List Nat → Nat} {b : List Nat} {limit : Nat}

theorem extend_prefix_of (pre : List Nat) (c : Chunk) : pre <+: extend pre c := by
  unfold extend; split
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

/-- An honest chunk keeps a prefix of `b` one. -/
theorem extend_honest_prefix {p : List Nat} (h : p <+: b) (off lim : Nat) :
    extend p (honest b off lim) <+: b := by
  unfold extend
  split
  · rename_i hx
    have hoff : off ≤ p.length := hx.1
    have e : (honest b off lim).data.drop (p.length - (honest b off lim).off) =
        (b.drop p.length).take (lim - (p.length - off)) := by
      simp only [honest, List.drop_take, List.drop_drop]
      rw [show off + (p.length - off) = p.length by omega]
    rw [e]; exact prefix_extend h _
  · exact h

/-- An honest chunk from within the prefix takes it at least to the chunk's end, or the
blob's. -/
theorem extend_honest_length {p : List Nat} {off : Nat} (ho : off ≤ p.length) (lim : Nat) :
    min (off + lim) b.length ≤ (extend p (honest b off lim)).length := by
  unfold extend Extends honest
  split
  · simp only [List.length_append, List.length_drop, List.length_take]; omega
  · rename_i hx
    simp only [List.length_take, List.length_drop, not_and, Nat.not_lt] at hx
    have := hx ho; omega

/-- A chunk that ends within the prefix adds nothing to it. -/
theorem extend_within {p : List Nat} {c : Chunk} (h : c.off + c.data.length ≤ p.length) :
    extend p c = p := by
  simp only [extend, Extends]; split
  · omega
  · rfl

/-- What the prefix receiver makes of an honest chunk while it hasn't the blob: it stores `b`;
it keeps the chunk's bytes past its prefix, short of the blob's length; or, its prefix not
being `b`'s, it starts over. -/
theorem receive_honest (hinj : ∀ x y, hash x = hash y → x = y) {s : PState}
    (hs : s.store = none) (off lim : Nat) :
    ((receive hash b s (honest b off lim) b.length).1.store = some b ∧
      (receive hash b s (honest b off lim) b.length).2 = none) ∨
    ((receive hash b s (honest b off lim) b.length).1.store = none ∧
      (receive hash b s (honest b off lim) b.length).1.pre = extend s.pre (honest b off lim) ∧
      (extend s.pre (honest b off lim)).length < b.length ∧
      (receive hash b s (honest b off lim) b.length).2 =
        some (extend s.pre (honest b off lim)).length) ∨
    ((receive hash b s (honest b off lim) b.length).1.store = none ∧
      (receive hash b s (honest b off lim) b.length).1.pre = [] ∧ ¬ s.pre <+: b ∧
      (receive hash b s (honest b off lim) b.length).2 = some 0) := by
  simp only [receive, hs]
  split
  · rename_i hlt
    exact Or.inr (Or.inl ⟨rfl, rfl, hlt, rfl⟩)
  · split
    · rename_i _ hok
      exact Or.inl ⟨by rw [hinj _ _ hok.1], rfl⟩
    · rename_i hlt hbad
      refine Or.inr (Or.inr ⟨rfl, rfl, fun hpre => hbad ?_, rfl⟩)
      have hpb := extend_honest_prefix hpre off lim
      have hpeq := hpb.eq_of_length (by have := hpb.length_le; omega)
      exact ⟨congrArg hash hpeq, congrArg List.length hpeq⟩

/-- An honest chunk leaves a prefix of `b` one. -/
theorem receive_honest_prefix {s : PState} (hp : s.pre <+: b) (hs : s.store = none)
    (off lim : Nat) : (receive hash b s (honest b off lim) b.length).1.pre <+: b := by
  simp only [receive, hs]
  split
  · exact extend_honest_prefix hp off lim
  · split
    · exact List.nil_prefix
    · exact List.nil_prefix

theorem deliver_append (s : PState) (xs ys : List Chunk) :
    deliver hash b s (xs ++ ys) =
      ((deliver hash b (deliver hash b s xs).1 ys).1,
        (deliver hash b s xs).2 ++ (deliver hash b (deliver hash b s xs).1 ys).2) := by
  induction xs generalizing s with
  | nil => rfl
  | cons c xs ih => simp only [List.cons_append, deliver, ih]

theorem deliver_length (s : PState) (cs : List Chunk) :
    (deliver hash b s cs).2.length = cs.length := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih => simp only [deliver, List.length_cons, ih]

/-- A receiver that has the blob keeps it, whatever comes. -/
theorem deliver_stored {s : PState} {d : List Nat} (hs : s.store = some d) (cs : List Chunk) :
    (deliver hash b s cs).1.store = some d ∧ (deliver hash b s cs).1.pre = s.pre ∧
      ∀ r ∈ (deliver hash b s cs).2, r = none := by
  induction cs generalizing s with
  | nil => exact ⟨hs, rfl, by simp [deliver]⟩
  | cons c cs ih =>
    have hr : receive hash b (sent s c) c b.length = (sent s c, none) := by
      simp [receive, sent, hs]
    obtain ⟨h1, h2, h3⟩ := ih (s := sent s c) hs
    simp only [deliver, hr]
    refine ⟨h1, h2, ?_⟩
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · rfl
    · exact h3 r hr

/-- Honest chunks keep a prefix of `b` one, and a stored blob `b`. -/
theorem deliver_good (hinj : ∀ x y, hash x = hash y → x = y) :
    ∀ (cs : List Chunk) (s : PState), (∀ c ∈ cs, ∃ off lim, c = honest b off lim) →
    s.pre <+: b → (s.store = none ∨ s.store = some b) →
    (deliver hash b s cs).1.pre <+: b ∧
      ((deliver hash b s cs).1.store = none ∨ (deliver hash b s cs).1.store = some b)
  | [], _, _, hp, hst => ⟨hp, hst⟩
  | c :: cs, s, hcs, hp, hst => by
    obtain ⟨off, lim, rfl⟩ := hcs c List.mem_cons_self
    have hrest : ∀ c ∈ cs, ∃ off lim, c = honest b off lim :=
      fun c hc => hcs c (List.mem_cons_of_mem _ hc)
    simp only [deliver]
    rcases hst with hst | hst
    · rcases receive_honest (b := b) hinj (s := sent s (honest b off lim)) hst off lim with
        ⟨h1, _⟩ | ⟨h1, h2, _⟩ | ⟨_, _, hbad, _⟩
      · obtain ⟨h3, h4, _⟩ := deliver_stored (hash := hash) (b := b) h1 cs
        exact ⟨h4 ▸ receive_honest_prefix (s := sent s (honest b off lim)) hp hst off lim,
          Or.inr h3⟩
      · exact deliver_good hinj cs _ hrest (h2 ▸ extend_honest_prefix hp off lim) (Or.inl h1)
      · exact absurd hp hbad
    · have := deliver_stored (hash := hash) (b := b) (d := b)
        (s := (receive hash b (sent s (honest b off lim)) (honest b off lim) b.length).1)
        (by simp only [receive, sent, hst]) cs
      refine ⟨?_, Or.inr this.1⟩
      rw [this.2.1]; simp only [receive, sent, hst]; exact hp

theorem windowFrom_honest (o w : Nat) :
    ∀ c ∈ windowFrom b limit o w, ∃ off lim, c = honest b off lim := by
  induction w generalizing o with
  | zero => simp [windowFrom]
  | succ w ih =>
    intro c hc
    simp only [windowFrom, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨o, limit, rfl⟩
    · exact ih _ c hc

theorem windowFrom_length (o w : Nat) : (windowFrom b limit o w).length = w := by
  induction w generalizing o with
  | zero => rfl
  | succ w ih => simp only [windowFrom, List.length_cons, ih]

theorem windowFrom_add (o k j : Nat) :
    windowFrom b limit o (k + j) =
      windowFrom b limit o k ++ windowFrom b limit (o + k * limit) j := by
  induction k generalizing o with
  | zero => simp [windowFrom]
  | succ k ih =>
    rw [Nat.add_right_comm]
    simp only [windowFrom, ih, List.cons_append]
    rw [show o + limit + k * limit = o + (k + 1) * limit by rw [Nat.succ_mul]; omega]

/-- An attempt's receiver takes its first `k` chunks, then the rest it delivers; the sender
hears of the first `k`. -/
theorem attempt_split (s : PState) (o : Nat) {m k : Nat} (hkm : k ≤ m) :
    attempt hash b limit s o m k =
      ((deliver hash b (deliver hash b s (windowFrom b limit o k)).1
          (windowFrom b limit (o + k * limit) (m - k))).1,
        next o (deliver hash b s (windowFrom b limit o k)).2) := by
  have e : m = k + (m - k) := by omega
  simp only [attempt]
  rw [e, windowFrom_add, deliver_append, Nat.add_sub_cancel_left]
  congr 2
  rw [List.take_left']
  rw [deliver_length, windowFrom_length]

/-- Delivering honest chunks to a receiver without the blob, whose prefix is short of the
blob's length: it stores `b`; or, its prefix not being `b`'s, it started over, and has one of
`b`'s; or its prefix grew, still short of the blob's length, each reply reporting a prefix it
has had, the last the one it has. -/
theorem deliver_honest (hinj : ∀ x y, hash x = hash y → x = y) :
    ∀ (cs : List Chunk) (s : PState), (∀ c ∈ cs, ∃ off lim, c = honest b off lim) →
    s.store = none → s.pre.length < b.length →
    (deliver hash b s cs).1.store = some b ∨
    ((deliver hash b s cs).1.store = none ∧ ¬ s.pre <+: b ∧
      (deliver hash b s cs).1.pre <+: b) ∨
    ((deliver hash b s cs).1.store = none ∧ s.pre <+: (deliver hash b s cs).1.pre ∧
      (deliver hash b s cs).1.pre.length < b.length ∧
      (s.pre <+: b → (deliver hash b s cs).1.pre <+: b) ∧
      (∀ r ∈ (deliver hash b s cs).2, ∃ n, r = some n ∧ s.pre.length ≤ n ∧
        n ≤ (deliver hash b s cs).1.pre.length) ∧
      (cs ≠ [] → furthest (deliver hash b s cs).2 = some (deliver hash b s cs).1.pre.length))
  | [], s, _, hs, hlen => by
    refine Or.inr (Or.inr ⟨hs, List.prefix_refl _, hlen, id, ?_, fun h => absurd rfl h⟩)
    simp [deliver]
  | c :: cs, s, hcs, hs, hlen => by
    obtain ⟨off, lim, rfl⟩ := hcs c List.mem_cons_self
    have hrest : ∀ c ∈ cs, ∃ off lim, c = honest b off lim :=
      fun c hc => hcs c (List.mem_cons_of_mem _ hc)
    simp only [deliver]
    generalize hr : receive hash b (sent s (honest b off lim)) (honest b off lim) b.length = r
    have hrh := receive_honest (b := b) hinj (s := sent s (honest b off lim)) hs off lim
    rw [hr] at hrh
    rcases hrh with ⟨h1, _⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, hbad, h4⟩
    · exact Or.inl (deliver_stored (hash := hash) (b := b) h1 cs).1
    · have hsp : s.pre <+: r.1.pre := h2 ▸ extend_prefix_of s.pre _
      rcases deliver_honest hinj cs r.1 hrest h1 (h2 ▸ h3) with h | ⟨h5, h6, h7⟩ |
          ⟨h5, h6, h7, h8, h9, h10⟩
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨h5, fun hp => h6 ?_, h7⟩)
        rw [h2]; exact extend_honest_prefix hp off lim
      · refine Or.inr (Or.inr ⟨h5, hsp.trans h6, h7,
          fun hp => h8 (h2 ▸ extend_honest_prefix hp off lim), ?_, fun _ => ?_⟩)
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have := hsp.length_le
            have := h6.length_le
            exact ⟨_, h4, by rw [h2] at *; omega, by rw [h2] at *; omega⟩
          · obtain ⟨n, hn, hn1, hn2⟩ := h9 x hx
            have := hsp.length_le
            exact ⟨n, hn, by omega, hn2⟩
        · rw [h4]
          by_cases hcs : cs = []
          · subst hcs
            simp only [deliver, furthest, Option.bind_some, Option.map_some, h2]
            simp
          · simp only [furthest, Option.bind_some, h10 hcs, Option.map_some]
            have := h6.length_le
            rw [← h2]
            congr 1; omega
    · have hr0 : r.1.pre.length < b.length := by rw [h2]; simp; omega
      rcases deliver_honest hinj cs r.1 hrest h1 hr0 with h | ⟨_, h6, _⟩ | ⟨h5, _, _, h8, _⟩
      · exact Or.inl h
      · exact absurd (h2 ▸ List.nil_prefix) h6
      · exact Or.inr (Or.inl ⟨h5, hbad, h8 (h2 ▸ List.nil_prefix)⟩)

/-- From within the prefix, a window's first `k` chunks take the prefix at least `k` chunks
on, or to the end, unless the receiver stores `b`, or starts over from a prefix not `b`'s. -/
theorem window_reaches (hinj : ∀ x y, hash x = hash y → x = y) :
    ∀ (k : Nat) (s : PState) (o : Nat), s.store = none → s.pre.length < b.length →
    o ≤ s.pre.length →
    (deliver hash b s (windowFrom b limit o k)).1.store = some b ∨
    (¬ s.pre <+: b ∧ (deliver hash b s (windowFrom b limit o k)).1.pre <+: b) ∨
    min (o + k * limit) b.length ≤ (deliver hash b s (windowFrom b limit o k)).1.pre.length
  | 0, s, o, _, _, ho => by
    refine Or.inr (Or.inr ?_)
    simp only [windowFrom, deliver]; omega
  | k + 1, s, o, hs, hlen, ho => by
    simp only [windowFrom, deliver]
    generalize hr : receive hash b (sent s (honest b o limit)) (honest b o limit) b.length = r
    have hrh := receive_honest (b := b) hinj (s := sent s (honest b o limit)) hs o limit
    rw [hr] at hrh
    rcases hrh with ⟨h1, _⟩ | ⟨h1, h2, h3, _⟩ | ⟨h1, h2, hbad, _⟩
    · exact Or.inl (deliver_stored (hash := hash) (b := b) h1 _).1
    · have hext := extend_honest_length (b := b) (p := s.pre) ho limit
      have hsp : s.pre <+: r.1.pre := h2 ▸ extend_prefix_of s.pre _
      have hol : o + limit ≤ r.1.pre.length := by
        change min (o + limit) b.length ≤ (extend (sent s (honest b o limit)).pre _).length at hext
        rw [h2]; omega
      rcases window_reaches hinj k r.1 (o + limit) h1 (h2 ▸ h3) hol with h | ⟨h5, h6⟩ | h
      · exact Or.inl h
      · refine Or.inr (Or.inl ⟨fun hp => h5 ?_, h6⟩)
        rw [h2]; exact extend_honest_prefix hp o limit
      · refine Or.inr (Or.inr ?_)
        rw [show o + (k + 1) * limit = o + limit + k * limit by rw [Nat.succ_mul]; omega]
        exact h
    · have hr0 : r.1.pre.length < b.length := by rw [h2]; simp; omega
      rcases deliver_honest hinj _ r.1 (windowFrom_honest (b := b) (limit := limit) _ _) h1 hr0 with
        h | ⟨_, h6, _⟩ | ⟨h5, _, _, h8, _⟩
      · exact Or.inl h
      · exact absurd (h2 ▸ List.nil_prefix) h6
      · exact Or.inr (Or.inl ⟨hbad, h8 (h2 ▸ List.nil_prefix)⟩)

theorem ameasure_stored {s : PState} {o : Nat} (hs : s.store ≠ none) : ameasure b (s, o) = 0 := by
  simp [ameasure, hs]

/-- A sender going on from the receiver's prefix never takes the transfer further from its end:
not from too far on, nor from further back. -/
theorem ameasure_reread (s : PState) (o : Nat) :
    ameasure b (s, s.pre.length) ≤ ameasure b (s, o) := by
  unfold ameasure
  split
  · simp only [Nat.lt_irrefl, ↓reduceIte]
    split <;> split <;> omega
  · exact Nat.le_refl _

theorem ameasure_pos {s : PState} (o : Nat) (hs : s.store = none) : 0 < ameasure b (s, o) := by
  unfold ameasure
  simp only [hs, ↓reduceIte]
  omega

/-- A receiver without the blob whose prefix is `b`'s weighs at most this much. -/
theorem ameasure_good {s : PState} (o : Nat) (hp : s.pre <+: b) :
    ameasure b (s, o) ≤ 1 + (b.length + 1) + b.length := by
  unfold ameasure
  simp only [hp, ↓reduceIte]
  split
  · split <;> omega
  · omega

/-- A receiver without the blob whose prefix isn't `b`'s weighs at least this much. -/
theorem ameasure_bad {s : PState} (o : Nat) (hs : s.store = none) (hp : ¬ s.pre <+: b) :
    1 + 3 * (b.length + 1) ≤ ameasure b (s, o) := by
  unfold ameasure
  simp only [hs, hp, ↓reduceIte]
  omega

/-- Of a state that delivered honest chunks has made good or stored, from one whose prefix
wasn't `b`'s. -/
theorem ameasure_after_bad {s t : PState} {o o' : Nat}
    (hs : s.store = none) (hp : ¬ s.pre <+: b) (ht : t.pre <+: b ∨ t.store ≠ none) :
    ameasure b (t, o') < ameasure b (s, o) := by
  have := ameasure_bad o hs hp
  rcases ht with ht | ht
  · have := ameasure_good (b := b) o' ht; omega
  · rw [ameasure_stored ht]; omega

/-- **Attempts decrease the measure**: from any state, an attempt that hears a reply brings the
transfer nearer its end. -/
theorem attempt_decreases (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit)
    {s : PState} {o m k : Nat} (hk : 0 < k) (hkm : k ≤ m) (hs : s.store = none) :
    ameasure b ((attempt hash b limit s o m k).1, (attempt hash b limit s o m k).2.getD o) <
      ameasure b (s, o) := by
  have hpos := ameasure_pos (b := b) o hs
  by_cases hlen : s.pre.length < b.length
  · rw [attempt_split s o hkm]
    simp only
    generalize hdk : deliver hash b s (windowFrom b limit o k) = dk
    generalize hdm : deliver hash b dk.1 (windowFrom b limit (o + k * limit) (m - k)) = dm
    have hk' : windowFrom b limit o k ≠ [] := by
      intro h; have := congrArg List.length h
      rw [windowFrom_length] at this; simp at this; omega
    have hrest := windowFrom_honest (b := b) (limit := limit) (o + k * limit) (m - k)
    have hdkh := deliver_honest (b := b) hinj _ s
      (windowFrom_honest (b := b) (limit := limit) o k) hs hlen
    rw [hdk] at hdkh
    rcases hdkh with h1 | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, _, h6⟩
    · have := (deliver_stored (hash := hash) (b := b) h1
        (windowFrom b limit (o + k * limit) (m - k))).1
      rw [hdm] at this
      rw [ameasure_stored (by rw [this]; simp)]; exact hpos
    · have := deliver_good (hash := hash) (b := b) hinj _ dk.1 hrest h3 (Or.inl h1)
      rw [hdm] at this
      exact ameasure_after_bad hs h2 (Or.inl this.1)
    · have hnext : next o dk.2 = some dk.1.pre.length := by
        have := h6 hk'
        unfold next
        have hne : dk.2 ≠ [] := by
          intro h; have := congrArg List.length h
          rw [← hdk, deliver_length, windowFrom_length] at this; simp at this; omega
        simp only [hne, ↓reduceIte, this]
      rw [hnext]; simp only [Option.getD_some]
      have hdmh := deliver_honest (b := b) hinj _ dk.1 hrest h1 h3
      rw [hdm] at hdmh
      rcases hdmh with g1 | ⟨_, g2, g3⟩ | ⟨g1, g2, g3, g4, _, _⟩
      · rw [ameasure_stored (by rw [g1]; simp)]; exact hpos
      · by_cases hp : s.pre <+: b
        · exact absurd (h4 hp) g2
        · exact ameasure_after_bad hs hp (Or.inl g3)
      · -- The prefix grew, and the sender goes on from what it heard of.
        have hgood : (dm.1.pre <+: b) ↔ (s.pre <+: b) :=
          ⟨fun h => (h2.trans g2).trans h, fun h => g4 (h4 h)⟩
        have hfresh : ¬ dm.1.pre.length < dk.1.pre.length := by
          have := g2.length_le; omega
        by_cases ho : o ≤ s.pre.length
        · have hreach := window_reaches (b := b) (limit := limit) hinj k s o hs hlen ho
          rw [hdk] at hreach
          rcases hreach with r1 | ⟨r1, r2⟩ | r1
          · rw [h1] at r1; cases r1
          · exact absurd ((h2.trans r2)) r1
          · have hkl : limit ≤ k * limit := Nat.le_mul_of_pos_left limit hk
            have hstale : ¬ s.pre.length < o := by omega
            unfold ameasure
            simp only [g1, hs, hgood, hfresh, hstale, ↓reduceIte]
            omega
        · have hst : s.pre.length < o := by omega
          unfold ameasure
          simp only [g1, hs, hgood, hfresh, hst, ↓reduceIte]
          split <;> omega
  · -- A prefix as long as the blob: the first chunk stores it, or starts over.
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [attempt, windowFrom, deliver]
    generalize hr : receive hash b (sent s (honest b o limit)) (honest b o limit) b.length = r
    have hrh := receive_honest (b := b) hinj (s := sent s (honest b o limit)) hs o limit
    rw [hr] at hrh
    rcases hrh with ⟨h1, _⟩ | ⟨_, h2, h3, _⟩ | ⟨h1, h2, hbad, _⟩
    · rw [ameasure_stored (by rw [(deliver_stored (hash := hash) (b := b) h1 _).1]; simp)]
      exact hpos
    · have := (extend_prefix_of s.pre (honest b o limit)).length_le
      change (extend s.pre (honest b o limit)).length < b.length at h3
      omega
    · have := deliver_good (hash := hash) (b := b) hinj (windowFrom b limit (o + limit) m') r.1
        (windowFrom_honest (b := b) (limit := limit) _ _) (h2 ▸ List.nil_prefix) (Or.inl h1)
      exact ameasure_after_bad hs hbad (Or.inl this.1)

/-- A chunk arriving late never takes the transfer further from its end. -/
theorem late_le (hinj : ∀ x y, hash x = hash y → x = y) (s : PState) (o off : Nat) :
    ameasure b ((deliver hash b s [honest b off limit]).1, o) ≤ ameasure b (s, o) := by
  cases hst : s.store with
  | some d =>
    rw [ameasure_stored (by rw [(deliver_stored (hash := hash) (b := b) hst _).1]; simp)]
    exact Nat.zero_le _
  | none =>
    by_cases hlen : s.pre.length < b.length
    · rcases deliver_honest (b := b) hinj [honest b off limit] s
          (fun c hc => ⟨off, limit, by simpa using hc⟩) hst hlen with
        h1 | ⟨_, h2, h3⟩ | ⟨h1, h2, _, h4, _, _⟩
      · rw [ameasure_stored (by rw [h1]; simp)]; exact Nat.zero_le _
      · exact Nat.le_of_lt (ameasure_after_bad hst h2 (Or.inl h3))
      · generalize hd : deliver hash b s [honest b off limit] = d at *
        have hgood : (d.1.pre <+: b) ↔ (s.pre <+: b) :=
          ⟨fun h => h2.trans h, fun h => h4 h⟩
        have := h2.length_le
        unfold ameasure
        simp only [h1, hst, hgood, ↓reduceIte]
        by_cases ha : d.1.pre.length < o <;> by_cases hb : s.pre.length < o <;>
          simp only [ha, hb, ↓reduceIte] <;> omega
    · simp only [deliver]
      generalize hr : receive hash b (sent s (honest b off limit)) (honest b off limit)
        b.length = r
      have hrh := receive_honest (b := b) hinj (s := sent s (honest b off limit)) hst off limit
      rw [hr] at hrh
      rcases hrh with ⟨h1, _⟩ | ⟨_, _, h3, _⟩ | ⟨h1, h2, hbad, _⟩
      · rw [ameasure_stored (by rw [h1]; simp)]
        exact Nat.zero_le _
      · have := (extend_prefix_of s.pre (honest b off limit)).length_le
        change (extend s.pre (honest b off limit)).length < b.length at h3
        omega
      · exact Nat.le_of_lt (ameasure_after_bad hst hbad (Or.inl (h2 ▸ List.nil_prefix)))

/-- Each attempt of a run takes the measure down by one at least. -/
theorem arun_measure (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit) {n : Nat}
    {x y : PState × Nat} (h : ARun hash b limit n x y) : ameasure b y + n ≤ ameasure b x := by
  induction h with
  | refl => simp
  | @attempt _ s o m k _ hk hkm hs _ ih =>
    have := attempt_decreases (b := b) (o := o) hinj hlim hk hkm hs; omega
  | @late _ s o off _ _ ih => have := late_le (b := b) (limit := limit) hinj s o off; omega
  | @reread _ s o _ _ ih => have := ameasure_reread (b := b) s o; omega

/-- Delivering honest chunks no longer than `limit` is a run of the prefix receiver's steps. -/
theorem deliver_reach {s : PState} (h : PReach hash b limit s) :
    ∀ cs : List Chunk, (∀ c ∈ cs, ∃ off lim, lim ≤ limit ∧ c = honest b off lim) →
    PReach hash b limit (deliver hash b s cs).1 := by
  intro cs hcs
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih =>
    obtain ⟨off, lim, hlim, rfl⟩ := hcs c List.mem_cons_self
    have h1 := h.step (PStep.send s off lim hlim)
    have h2 := h1.step (PStep.recv _ (honest b off lim) b.length (Or.inr rfl))
    exact ih h2 (fun c hc => hcs c (List.mem_cons_of_mem _ hc))

theorem windowFrom_limit (o w : Nat) :
    ∀ c ∈ windowFrom b limit o w, ∃ off lim, lim ≤ limit ∧ c = honest b off lim := by
  induction w generalizing o with
  | zero => simp [windowFrom]
  | succ w ih =>
    intro c hc
    simp only [windowFrom, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨o, limit, Nat.le_refl _, rfl⟩
    · exact ih _ c hc

theorem arun_reach {n : Nat} {x y : PState × Nat} (h : ARun hash b limit n x y)
    (hx : PReach hash b limit x.1) : PReach hash b limit y.1 := by
  induction h with
  | refl => exact hx
  | attempt _ _ _ _ ih => exact ih (deliver_reach hx _ (windowFrom_limit _ _))
  | late _ ih =>
    exact ih (deliver_reach hx _ (fun c hc => ⟨_, limit, Nat.le_refl _, by simpa using hc⟩))
  | reread _ ih => exact ih hx

/-- **Attempts finish**: from any state the prefix receiver reaches, a run of attempts that each
hear a reply, among chunks arriving late, ends with the receiver storing exactly `b` within as
many attempts as the state's measure. -/
theorem attempts_finish (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit) {n : Nat}
    {x y : PState × Nat} (hx : PReach hash b limit x.1) (h : ARun hash b limit n x y)
    (hn : ameasure b x ≤ n) : y.1.store = some b := by
  have hm := arun_measure hinj hlim h
  have hy : y.1.store ≠ none := by
    intro hy
    have : 0 < ameasure b y := ameasure_pos (b := b) y.2 hy
    omega
  obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hy
  rw [hd, prefix_stored_identical hinj (arun_reach h hx) hd]

/-- The same, the other way about: a run whose receiver hasn't the blob yet has made fewer
attempts than the measure of where it started. -/
theorem attempts_bounded (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit)
    {n : Nat} {x y : PState × Nat} (h : ARun hash b limit n x y) (hy : y.1.store = none) :
    n < ameasure b x := by
  have hm := arun_measure hinj hlim h
  have : 0 < ameasure b y := ameasure_pos (b := b) y.2 hy
  omega

/-- Chunks delivered one after another are as many arriving late. -/
theorem arun_late_all {n : Nat} {o : Nat} {z : PState × Nat} :
    ∀ (cs : List Chunk) (s : PState), (∀ c ∈ cs, ∃ off, c = honest b off limit) →
    ARun hash b limit n ((deliver hash b s cs).1, o) z → ARun hash b limit n (s, o) z
  | [], _, _, h => h
  | c :: cs, s, hcs, h => by
    obtain ⟨off, rfl⟩ := hcs c List.mem_cons_self
    refine ARun.late (off := off) ?_
    have e : deliver hash b s (honest b off limit :: cs) =
        deliver hash b s ([honest b off limit] ++ cs) := rfl
    rw [e, deliver_append] at h
    exact arun_late_all cs _ (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) h

theorem windowFrom_honest_limit (o w : Nat) :
    ∀ c ∈ windowFrom b limit o w, ∃ off, c = honest b off limit := by
  intro c hc
  obtain ⟨off, lim, hlim, rfl⟩ := windowFrom_limit o w c hc
  induction w generalizing o with
  | zero => simp [windowFrom] at hc
  | succ w ih =>
    simp only [windowFrom, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨o, hc⟩
    · exact ih _ hc

/-- An attempt that hears nothing, or hears that the receiver has the blob, leaves the sender
where it was: its chunks arrive as if late. -/
theorem attempt_quiet {s : PState} {o m k : Nat} (hq : k = 0 ∨ s.store ≠ none) :
    (attempt hash b limit s o m k).2.getD o = o := by
  simp only [attempt, next]
  rcases hq with rfl | hs
  · simp
  · obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hs
    have hnone := (deliver_stored (hash := hash) (b := b) hd (windowFrom b limit o m)).2.2
    generalize (deliver hash b s (windowFrom b limit o m)).2 = rs at hnone
    split
    · simp
    · rename_i hne
      obtain ⟨r, rs', hr⟩ : ∃ r rs', rs.take k = r :: rs' := by
        cases h : rs.take k with
        | nil => exact absurd h hne
        | cons r rs' => exact ⟨r, rs', rfl⟩
      have : r = none := hnone r (List.mem_of_mem_take (hr ▸ List.mem_cons_self))
      rw [hr, this]; rfl

/-- **Attempt progress**: an attempt from within the receiver's prefix, short of the blob's
end, that hears `k` replies takes the prefix at least `k` chunks on from where it started, or
to the end, and the sender goes on from there; or the receiver stores the blob. -/
theorem attempt_progress (hinj : ∀ x y, hash x = hash y → x = y) {s : PState}
    (hs : s.store = none) (hpre : s.pre <+: b) (hlen : s.pre.length < b.length) {o m k : Nat}
    (ho : o ≤ s.pre.length) (hk : 0 < k) (hkm : k ≤ m) :
    (attempt hash b limit s o m k).1.store = some b ∨
    ∃ n, (attempt hash b limit s o m k).2 = some n ∧ min (o + k * limit) b.length ≤ n ∧
      n ≤ (attempt hash b limit s o m k).1.pre.length := by
  rw [attempt_split s o hkm]
  simp only
  generalize hdk : deliver hash b s (windowFrom b limit o k) = dk
  have hdkh := deliver_honest (b := b) hinj _ s
    (windowFrom_honest (b := b) (limit := limit) o k) hs hlen
  have hreach := window_reaches (b := b) (limit := limit) hinj k s o hs hlen ho
  rw [hdk] at hdkh hreach
  rcases hdkh with h1 | ⟨_, h2, _⟩ | ⟨h1, _, h3, h4, _, h6⟩
  · exact Or.inl (deliver_stored (hash := hash) (b := b) h1 _).1
  · exact absurd hpre h2
  · rcases hreach with r1 | ⟨r1, _⟩ | r1
    · rw [h1] at r1; cases r1
    · exact absurd hpre r1
    · have hne : dk.2 ≠ [] := by
        intro h; have := congrArg List.length h
        rw [← hdk, deliver_length, windowFrom_length] at this; simp at this; omega
      have hk' : windowFrom b limit o k ≠ [] := by
        intro h; have := congrArg List.length h
        rw [windowFrom_length] at this; simp at this; omega
      have hdmh := deliver_honest (b := b) hinj
        (windowFrom b limit (o + k * limit) (m - k)) dk.1
        (windowFrom_honest (b := b) (limit := limit) _ _) h1 h3
      rcases hdmh with g1 | ⟨_, g2, _⟩ | ⟨_, g2, _, _, _, _⟩
      · exact Or.inl g1
      · exact absurd (h4 hpre) g2
      · refine Or.inr ⟨dk.1.pre.length, ?_, r1, g2.length_le⟩
        unfold next; simp only [hne, ↓reduceIte, h6 hk']

/-- **A restarting sender stalls**: a sender that starts every attempt from the beginning, as
musubi's did, takes the prefix nowhere once it holds the chunks the attempt delivers, however
many replies it hears. -/
theorem restart_stalls {s : PState} (hs : s.store = none) (hlen : s.pre.length < b.length)
    {m k : Nat} (hm : m * limit ≤ s.pre.length) :
    (attempt hash b limit s 0 m k).1.pre = s.pre ∧
      (attempt hash b limit s 0 m k).1.store = none := by
  suffices h : ∀ (m : Nat) (s : PState) (o : Nat), s.store = none → s.pre.length < b.length →
      o + m * limit ≤ s.pre.length →
      (deliver hash b s (windowFrom b limit o m)).1.pre = s.pre ∧
        (deliver hash b s (windowFrom b limit o m)).1.store = none by
    exact h m s 0 hs hlen (by omega)
  intro m
  induction m with
  | zero => intro s o hs _ _; exact ⟨rfl, hs⟩
  | succ m ih =>
    intro s o hs hlen hm
    simp only [windowFrom, deliver]
    have hw : (honest b o limit).off + (honest b o limit).data.length ≤ s.pre.length := by
      simp only [honest, List.length_take, List.length_drop]
      rw [Nat.succ_mul] at hm; omega
    have hx : extend s.pre (honest b o limit) = s.pre := extend_within hw
    have hr : (receive hash b (sent s (honest b o limit)) (honest b o limit) b.length).1 =
        sent s (honest b o limit) := by
      simp only [receive, sent, hs, hx, hlen, ↓reduceIte]
    rw [hr]
    exact ih _ (o + limit) hs hlen (by rw [Nat.succ_mul] at hm; simp only [sent]; omega)

end attemptProofs

/-! ### Sweeps of what has gone untouched

musubi's stores sweep blobs by age. In `TStep`, time passes (`wait`), and a sweep takes the
sender's blob (`sweepSource`: the hub's, for a download), or what the receiver has of it,
partial or stored, only once it has gone untouched for `life`. A chunk renews what it touches,
at most every `renew` (`refresh`), whether it moves anything or not: an attempt delivering one
renews the blob at both ends; a chunk that moves nothing (`touch`), as a sender sends to keep a
blob of a request or a reply while another moves, does too; a chunk arriving late, at the
receiver. musubi's touches renew only the hub's end; a node sweeps what it holds only as a call
begins, a day old, so that its end of a call's transfers needs no renewal while the call
lasts. The hub also forgets a prepared blob a minute after serving its last chunk, which the
model doesn't count: a call needs no blob again once it has downloaded it.

A fair run (`FairRun`) is one of these steps but the sweeps, in which no more than `gap` passes
without an attempt that delivers a chunk, or a touch. Every state a fair run reaches from a state
renewed within `renew`, with `renew + gap ≤ life`, has gone untouched for less than `life`, so
that no sweep can take place there (`fair_unswept`): a blob kept by touches alone, once stored,
among them. Its attempts are a run of `ARun`'s (`fair_arun`), so that, from a state the receiver
reaches, one of `ameasure` attempts that hear a reply ends with the receiver storing the blob
(`fair_finishes`). Once a sweep has taken the sender's blob, nothing stores it at the receiver
(`swept_source_stalls`): the liveness rests on the renewal.

That attempts which hear a reply keep coming, `ameasure` of them, is the network's part. On a
real link it depends also on how much of the sender's own earlier windows, timed out, still
takes the link's time ahead of it, which narrowing the window after a timeout bounds, and which
the model doesn't count. -/

/-- A transfer in time: the receiver, where the sender goes on from, whether the sender still
has the blob, and how long since a chunk last touched the sender's blob, and what the receiver
has of it. -/
structure TState where
  s : PState
  o : Nat
  source : Bool
  srcAge : Nat
  tgtAge : Nat

/-- A blob a chunk touches is renewed if `renew` has passed since it last was. -/
def refresh (renew age : Nat) : Nat := if renew ≤ age then 0 else age

section timedDefs

variable (hash : List Nat → Nat) (b : List Nat) (limit renew : Nat)

/-- `t` after an attempt from `t.o` that delivers `m` chunks and hears of `k`. -/
def TState.attempted (t : TState) (m k : Nat) : TState :=
  { t with s := (attempt hash b limit t.s t.o m k).1,
           o := (attempt hash b limit t.s t.o m k).2.getD t.o,
           srcAge := refresh renew t.srcAge, tgtAge := refresh renew t.tgtAge }

/-- `t` after a chunk that moves nothing. -/
def TState.touched (t : TState) : TState :=
  { t with srcAge := refresh renew t.srcAge, tgtAge := refresh renew t.tgtAge }

/-- `t` after the honest chunk at `off`, of an earlier window, reaches the receiver late. -/
def TState.late (t : TState) (off : Nat) : TState :=
  { t with s := (deliver hash b t.s [honest b off limit]).1,
           tgtAge := refresh renew t.tgtAge }

/-- `t` after `d` passes. -/
def TState.waited (t : TState) (d : Nat) : TState :=
  { t with srcAge := t.srcAge + d, tgtAge := t.tgtAge + d }

variable (life : Nat)

/-- Steps of a transfer in time. -/
inductive TStep : TState → TState → Prop
  | attempt (t : TState) (m k : Nat) (hkm : k ≤ m) (hm : 0 < m) (hsrc : t.source = true) :
      TStep t (t.attempted hash b limit renew m k)
  | touch (t : TState) (hsrc : t.source = true) : TStep t (t.touched renew)
  | late (t : TState) (off : Nat) (hsrc : t.source = true) :
      TStep t (t.late hash b limit renew off)
  | reread (t : TState) : TStep t { t with o := t.s.pre.length }
  | wait (t : TState) (d : Nat) : TStep t (t.waited d)
  | sweepSource (t : TState) (h : life ≤ t.srcAge) : TStep t { t with source := false }
  | sweepPartial (t : TState) (h : life ≤ t.tgtAge) :
      TStep t { t with s := { t.s with pre := [] } }
  | sweepStored (t : TState) (h : life ≤ t.tgtAge) :
      TStep t { t with s := { t.s with store := none } }

inductive TSteps : TState → TState → Prop
  | refl (t : TState) : TSteps t t
  | head {t u v : TState} : TStep hash b limit renew life t u → TSteps u v → TSteps t v

/-- A fair run: `TStep`s but sweeps, `n` of its attempts hearing a reply, in which no more
than `gap` passes without an attempt or a touch; `idle` is how long it has been. -/
inductive FairRun (gap : Nat) : Nat → Nat → TState → TState → Prop
  | refl (idle : Nat) (t : TState) : FairRun gap 0 idle t t
  | heard {n idle : Nat} {t u : TState} (m k : Nat) (hk : 0 < k) (hkm : k ≤ m)
      (hs : t.s.store = none) (hsrc : t.source = true) :
      FairRun gap n 0 (t.attempted hash b limit renew m k) u → FairRun gap (n + 1) idle t u
  | quiet {n idle : Nat} {t u : TState} (m k : Nat) (hkm : k ≤ m) (hm : 0 < m)
      (hq : k = 0 ∨ t.s.store ≠ none) (hsrc : t.source = true) :
      FairRun gap n 0 (t.attempted hash b limit renew m k) u → FairRun gap n idle t u
  | touch {n idle : Nat} {t u : TState} (hsrc : t.source = true) :
      FairRun gap n 0 (t.touched renew) u → FairRun gap n idle t u
  | late {n idle : Nat} {t u : TState} (off : Nat) (hsrc : t.source = true) :
      FairRun gap n idle (t.late hash b limit renew off) u → FairRun gap n idle t u
  | reread {n idle : Nat} {t u : TState} :
      FairRun gap n idle { t with o := t.s.pre.length } u → FairRun gap n idle t u
  | wait {n idle : Nat} {t u : TState} (d : Nat) (hd : idle + d ≤ gap) :
      FairRun gap n (idle + d) (t.waited d) u → FairRun gap n idle t u

end timedDefs

section timedProofs

variable {hash : List Nat → Nat} {b : List Nat} {limit renew life : Nat}

theorem refresh_lt (hr : 0 < renew) (age : Nat) : refresh renew age < renew := by
  unfold refresh; split <;> omega

theorem refresh_le (age : Nat) : refresh renew age ≤ age := by
  unfold refresh; split <;> omega

/-- A fair run is a run of `TStep`s. -/
theorem fair_tsteps {gap n idle : Nat} {t u : TState}
    (h : FairRun hash b limit renew gap n idle t u) : TSteps hash b limit renew life t u := by
  induction h with
  | refl => exact TSteps.refl _
  | heard m k hk hkm _ hsrc _ ih => exact TSteps.head (TStep.attempt _ m k hkm (by omega) hsrc) ih
  | quiet m k hkm hm _ hsrc _ ih => exact TSteps.head (TStep.attempt _ m k hkm hm hsrc) ih
  | touch hsrc _ ih => exact TSteps.head (TStep.touch _ hsrc) ih
  | late off hsrc _ ih => exact TSteps.head (TStep.late _ off hsrc) ih
  | reread _ ih => exact TSteps.head (TStep.reread _) ih
  | wait d _ _ ih => exact TSteps.head (TStep.wait _ d) ih

/-- **Never swept**: every state a fair run reaches, from one renewed within `renew` of the
run's idle time, with `renew + gap ≤ life`, has gone untouched for less than `life`, at both
ends, so that no sweep can take place there. -/
theorem fair_unswept (hr : 0 < renew) {gap n idle : Nat} {t u : TState}
    (h : FairRun hash b limit renew gap n idle t u) (hlife : renew + gap ≤ life)
    (hsrc : t.srcAge < renew + idle) (htgt : t.tgtAge < renew + idle) (hidle : idle ≤ gap) :
    ¬ life ≤ u.srcAge ∧ ¬ life ≤ u.tgtAge := by
  induction h with
  | refl => omega
  | @heard _ _ t _ _ _ _ _ _ _ _ ih =>
    exact ih (by have := refresh_lt hr t.srcAge; simp only [TState.attempted]; omega)
      (by have := refresh_lt hr t.tgtAge; simp only [TState.attempted]; omega)
      (Nat.zero_le _)
  | @quiet _ _ t _ _ _ _ _ _ _ _ ih =>
    exact ih (by have := refresh_lt hr t.srcAge; simp only [TState.attempted]; omega)
      (by have := refresh_lt hr t.tgtAge; simp only [TState.attempted]; omega)
      (Nat.zero_le _)
  | @touch _ _ t _ _ _ ih =>
    exact ih (by have := refresh_lt hr t.srcAge; simp only [TState.touched]; omega)
      (by have := refresh_lt hr t.tgtAge; simp only [TState.touched]; omega)
      (Nat.zero_le _)
  | @late _ _ t _ off _ _ ih =>
    exact ih (by simp only [TState.late]; omega)
      (by have := refresh_le (renew := renew) t.tgtAge; simp only [TState.late]; omega) hidle
  | reread _ ih => exact ih hsrc htgt hidle
  | wait d hd _ ih =>
    exact ih (by simp only [TState.waited]; omega) (by simp only [TState.waited]; omega) hd

/-- A fair run's attempts that hear a reply are a run of `ARun`'s. -/
theorem fair_arun {gap n idle : Nat} {t u : TState}
    (h : FairRun hash b limit renew gap n idle t u) :
    ARun hash b limit n (t.s, t.o) (u.s, u.o) := by
  induction h with
  | refl => exact ARun.refl _
  | heard m k hk hkm hs _ _ ih => exact ARun.attempt hk hkm hs ih
  | @quiet _ _ t _ m k _ _ hq _ _ ih =>
    simp only [TState.attempted, attempt_quiet (hash := hash) (b := b) (limit := limit)
      (o := t.o) (m := m) hq] at ih
    exact arun_late_all _ t.s (windowFrom_honest_limit _ _) ih
  | touch _ _ ih => exact ih
  | late off _ _ ih => exact ARun.late ih
  | reread _ ih => exact ARun.reread ih
  | wait _ _ _ ih => exact ih

/-- **Fair runs finish**: from any state the prefix receiver reaches, a fair run with as many
attempts hearing a reply as the state's measure ends with the receiver storing exactly `b`. -/
theorem fair_finishes (hinj : ∀ x y, hash x = hash y → x = y) (hlim : 0 < limit)
    {gap n idle : Nat} {t u : TState} (hx : PReach hash b limit t.s)
    (h : FairRun hash b limit renew gap n idle t u) (hn : ameasure b (t.s, t.o) ≤ n) :
    u.s.store = some b :=
  attempts_finish (x := (t.s, t.o)) (y := (u.s, u.o)) hinj hlim hx (fair_arun h) hn

/-- **A swept source stalls the transfer**: once a sweep has taken the sender's blob, no step
stores it at the receiver. -/
theorem swept_source_stalls {t u : TState} (hsrc : t.source = false) (hs : t.s.store = none)
    (h : TStep hash b limit renew life t u) : u.source = false ∧ u.s.store = none := by
  cases h with
  | attempt _ _ _ _ h => rw [hsrc] at h; cases h
  | touch h => rw [hsrc] at h; cases h
  | late _ h => rw [hsrc] at h; cases h
  | reread => exact ⟨hsrc, hs⟩
  | wait => exact ⟨hsrc, hs⟩
  | sweepSource => exact ⟨rfl, hs⟩
  | sweepPartial => exact ⟨hsrc, hs⟩
  | sweepStored => exact ⟨hsrc, rfl⟩

end timedProofs

end Musubi.Chunks

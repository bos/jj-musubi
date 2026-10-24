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

end Musubi.Chunks

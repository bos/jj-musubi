/-
Once records are fixed, the raw names of a node's pending drops settle (`pending_names_settle`),
which records being adopted no longer gives: a node renames a pending drop to the hub's version
of its original (`name_pending_as`), and may do so after the record-adoption cut.

Within the window the hub's history is a chain: the closure of each head contains the closure
of each earlier one, and holds one version of each original at most. So two vertices of the
history from the window on with one original are one raw vertex (`raw_alias_unique`): no record
renames them any more. The node's identity normalizer renames a pending name to the version
below the head it knows, if that has one and its body is here, and otherwise keeps it. It may
normalize only some originals while other bodies are still arriving. Renaming an original
normalizes all its remaining names together; every other event leaves the pending drops alone,
or lets acknowledged ones leave. With no fresh pending originals, each original is renamed at
most once, to that one vertex, and never back.
The pending originals not yet named by a vertex of the history are finitely many, and each
renaming spends one, so the renamings stop. Neither the known head nor how often a name changes
is assumed to settle.
-/
import Musubi.AsyncLiveness

namespace Musubi.PendingEpoch

open Musubi

/-! ## Lists -/

theorem filter_len_mono {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x ∈ L, q x = true → p x = true) : (L.filter q).length ≤ (L.filter p).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.filter_cons]
    cases hq : q a <;> cases hp : p a <;> simp
    all_goals first
      | omega
      | exact absurd (h a List.mem_cons_self hq) (by rw [hp]; decide)

theorem filter_len_lt {α : Type} (L : List α) (p q : α → Bool)
    (h : ∀ x ∈ L, q x = true → p x = true) (hx : ∃ x ∈ L, p x = true ∧ q x = false) :
    (L.filter q).length < (L.filter p).length := by
  induction L with
  | nil => obtain ⟨x, hx, -⟩ := hx; exact absurd hx List.not_mem_nil
  | cons a L ih =>
    have hL : ∀ x ∈ L, q x = true → p x = true := fun x hx => h x (List.mem_cons_of_mem a hx)
    have hmono := filter_len_mono L p q hL
    simp only [List.filter_cons]
    obtain ⟨x, hxm, hpx, hqx⟩ := hx
    rcases List.mem_cons.1 hxm with rfl | hxm
    · simp [hpx, hqx]
      omega
    · have ih := ih hL ⟨x, hxm, hpx, hqx⟩
      cases hq : q a <;> cases hp : p a <;> simp
      all_goals first
        | omega
        | exact absurd (h a List.mem_cons_self hq) (by rw [hp]; decide)

/-! ## The window -/

section Window

variable (par : Nat → List Nat) (hist : Nat → Nat) (w : Nat) (orig : Nat → Nat)

/-- The hub's history from the window on, raw vertices with their originals: each head is
above the earlier ones, and its closure holds one version of each original at most (the hub
refuses a push that repeats an original, and with the records fixed nothing renames). `hist`
may be indexed by sequence number or by the time the hub had the head, and `par` may be the
whole raw graph ever made, whose parents never change. -/
structure History : Prop where
  chain : ∀ i j, w ≤ i → i ≤ j → Anc par (hist i) (hist j)
  unique : ∀ j, w ≤ j → ∀ x y, Anc par x (hist j) → Anc par y (hist j) → orig x = orig y →
    x = y

/-- A raw vertex of the hub's history from the window on. -/
def InWindow (x : Nat) : Prop := ∃ i, w ≤ i ∧ Anc par x (hist i)

variable {par hist w orig}

/-- Two vertices of the history from the window on with one original are one raw vertex. -/
theorem raw_alias_unique (H : History par hist w orig) {x y : Nat} (hx : InWindow par hist w x)
    (hy : InWindow par hist w y) (ho : orig x = orig y) : x = y := by
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hyj⟩ := hy
  rcases Nat.le_total i j with h | h
  · exact H.unique j hj x y (hxi.trans (H.chain i j hi h)) hyj ho
  · exact H.unique i hi x y hxi (hyj.trans (H.chain j i hj h)) ho

end Window

/-! ## Pending names -/

section Pending

variable {par : Nat → List Nat} {hist : Nat → Nat} {w : Nat} {orig : Nat → Nat}

variable (par hist orig) in
/-- The identity normalizer with the hub's head at sequence `k` known: a pending name `p`
becomes `p'`, the version of its original below that head, if it has one, and otherwise stays
as it was. -/
def NormTo (k p p' : Nat) : Prop :=
  (Anc par p' (hist k) ∧ orig p' = orig p) ∨
    (p' = p ∧ ¬ ∃ x, Anc par x (hist k) ∧ orig x = orig p)

variable (par hist orig) in
/-- A normalizing step, the hub's head at sequence `k` known: each name after is the
normalizer's of a name before, so no original is new, and any may leave, as an acknowledged
drop does. -/
def NormStep (k : Nat) (P P' : List Nat) : Prop :=
  ∀ p' ∈ P', ∃ p ∈ P, NormTo par hist orig k p p'

variable (par hist orig) in
/-- A step may normalize some originals and keep others, as when only part of the known
history has arrived. A new name is a normalized old one, and all names for its original
afterward agree. Deletion needs neither normalization nor complete metadata. -/
structure PStep (k : Nat) (P P' : List Nat) : Prop where
  names : ∀ p' ∈ P', p' ∈ P ∨ ∃ p ∈ P, NormTo par hist orig k p p'
  coherent : ∀ p' ∈ P', p' ∉ P → ∀ q ∈ P', orig q = orig p' → q = p'

/-- Frames and acknowledgements only remove names. -/
theorem subset_step {k : Nat} {P P' : List Nat} (hs : ∀ p' ∈ P', p' ∈ P) :
    PStep par hist orig k P P' :=
  ⟨fun p hp => Or.inl (hs p hp), fun p hp hn => False.elim (hn (hs p hp))⟩

/-- A step that brings a name normalizes. -/
theorem norm_of_new {k : Nat} {P P' : List Nat} (hs : PStep par hist orig k P P') {p' : Nat}
    (hp' : p' ∈ P') (hnew : p' ∉ P) : ∃ p ∈ P, NormTo par hist orig k p p' := by
  exact (hs.names p' hp').resolve_left hnew

/-- No step brings an original: each name after it has the original of one before. -/
theorem orig_before {k : Nat} {P P' : List Nat} (hs : PStep par hist orig k P P') {p' : Nat}
    (hp' : p' ∈ P') : ∃ p ∈ P, orig p = orig p' := by
  rcases hs.names p' hp' with hp | hn
  · exact ⟨p', hp, rfl⟩
  · obtain ⟨p, hp, hn⟩ := hn
    rcases hn with ⟨-, ho⟩ | ⟨rfl, -⟩
    · exact ⟨p, hp, ho.symm⟩
    · exact ⟨p', hp, rfl⟩

/-- A name a step brings is a vertex of the history from the window on, below the head it
knows, for an original whose name before was not. -/
theorem new_name (H : History par hist w orig) {k : Nat} (hk : w ≤ k) {P P' : List Nat}
    (hs : PStep par hist orig k P P') {p' : Nat} (hp' : p' ∈ P') (hnew : p' ∉ P) :
    Anc par p' (hist k) ∧ ∃ p ∈ P, orig p = orig p' ∧ ¬ InWindow par hist w p := by
  obtain ⟨p, hp, hn⟩ := norm_of_new hs hp' hnew
  rcases hn with ⟨hbelow, ho⟩ | ⟨rfl, -⟩
  · refine ⟨hbelow, p, hp, ho.symm, fun hpw => hnew ?_⟩
    rw [raw_alias_unique H ⟨k, hk, hbelow⟩ hpw ho]
    exact hp
  · exact absurd hp hnew

/-- A whole-list normalization satisfies the partial relation as well. -/
theorem norm_step (H : History par hist w orig) {k : Nat} (hk : w ≤ k) {P P' : List Nat}
    (hs : NormStep par hist orig k P P') : PStep par hist orig k P P' := by
  refine ⟨fun p hp => Or.inr (hs p hp), ?_⟩
  intro p' hp' hnew q hq ho
  obtain ⟨p, hp, hn⟩ := hs p' hp'
  have hbelow : Anc par p' (hist k) := by
    rcases hn with ⟨hb, -⟩ | ⟨rfl, -⟩
    · exact hb
    · exact absurd hp hnew
  obtain ⟨r, -, hn⟩ := hs q hq
  rcases hn with ⟨hqk, -⟩ | ⟨rfl, hnone⟩
  · exact H.unique k hk q p' hqk hbelow ho
  · exact absurd ⟨p', hbelow, ho.symm⟩ hnone

/-- With the records fixed and the hub's history a window, a node's pending drops take no new
raw name from some step on, whatever head it knows, so long as it is one of the window's: each
original is renamed at most once, to the one vertex of the history that is it, and drops may
leave. Several names for one original, as a lost record and an applied alias may give for a
while, are allowed. -/
theorem pending_names_settle (H : History par hist w orig) (P : Nat → List Nat)
    (known : Nat → Nat) (hk : ∀ t, w ≤ known t)
    (hstep : ∀ t, PStep par hist orig (known t) (P t) (P (t + 1))) :
    ∃ T, ∀ t, T ≤ t → ∀ p ∈ P (t + 1), p ∈ P t := by
  classical
  -- No original is new: each is one of those at the start.
  have horig : ∀ t, ∀ p ∈ P t, orig p ∈ (P 0).map orig := by
    intro t
    induction t with
    | zero => intro p hp; exact List.mem_map_of_mem hp
    | succ t ih =>
      intro p hp
      obtain ⟨q, hq, ho⟩ := orig_before (hstep t) hp
      rw [← ho]
      exact ih q hq
  -- The originals some pending drop names by a vertex outside the history.
  let bad : Nat → Nat → Bool := fun t o =>
    decide (∃ p ∈ P t, orig p = o ∧ ¬ InWindow par hist w p)
  let credit : Nat → Nat := fun t => (((P 0).map orig).filter (bad t)).length
  have hmono : ∀ t, ∀ o, bad (t + 1) o = true → bad t o = true := by
    intro t o h
    simp only [bad, decide_eq_true_eq] at h ⊢
    obtain ⟨p, hp, ho, hw⟩ := h
    by_cases hin : p ∈ P t
    · exact ⟨p, hin, ho, hw⟩
    · exact absurd ⟨known t, hk t, (new_name H (hk t) (hstep t) hp hin).1⟩ hw
  have hle : ∀ t, credit (t + 1) ≤ credit t :=
    fun t => filter_len_mono _ _ _ (fun o _ => hmono t o)
  obtain ⟨T, hT⟩ := nat_trace_stabilizes credit hle
  refine ⟨T, fun t ht p' hp' => Classical.byContradiction fun hnew => ?_⟩
  obtain ⟨hbelow, p, hp, ho, hw⟩ := new_name H (hk t) (hstep t) hp' hnew
  have hlt : credit (t + 1) < credit t := by
    refine filter_len_lt _ _ _ (fun o _ => hmono t o) ⟨orig p, horig t p hp, ?_, ?_⟩
    · simp only [bad, decide_eq_true_eq]
      exact ⟨p, hp, rfl, hw⟩
    · simp only [bad, decide_eq_false_iff_not]
      rintro ⟨q, hq, hqo, hqw⟩
      rw [(hstep t).coherent p' hp' hnew q hq (hqo.trans ho)] at hqw
      exact hqw ⟨known t, hk t, hbelow⟩
  have e1 := hT t ht
  have e2 := hT (t + 1) (by omega)
  omega

/-- From some step on, every pending name is one it had then: the pending drops' raw names
are fixed, and only leave. -/
theorem pending_names_fixed (H : History par hist w orig) (P : Nat → List Nat)
    (known : Nat → Nat) (hk : ∀ t, w ≤ known t)
    (hstep : ∀ t, PStep par hist orig (known t) (P t) (P (t + 1))) :
    ∃ T, ∀ t, T ≤ t → ∀ p ∈ P t, p ∈ P T := by
  obtain ⟨T, hT⟩ := pending_names_settle H P known hk hstep
  refine ⟨T, fun t ht => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction d with
  | zero => exact fun p hp => hp
  | succ d ih =>
    intro p hp
    exact ih (by omega) p (hT (T + d) (by omega) p hp)

/-- Normalization depends on the actual known head, not on how its history is indexed. -/
theorem PStep.head_eq {hist' : Nat → Nat} {k k' : Nat} {P P' : List Nat}
    (he : hist k = hist' k') (hs : PStep par hist orig k P P') :
    PStep par hist' orig k' P P' := by
  refine ⟨?_, hs.coherent⟩
  intro p hp
  rcases hs.names p hp with h | ⟨q, hq, hnorm⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, hq, by simpa only [NormTo, he] using hnorm⟩

/-- After old observations and reopens stop, knowledge either stays at its initial pair
or enters the current raw history window and stays there. Both possibilities have finite
alias credit. No fair observation or eventual knowledge entry is assumed, avoiding a cycle
with the later finite-local-work argument. The obsolete head needs only its own unique
originals, not ancestry comparability with the new window. -/
theorem pending_names_settle_with_old_known (H : History par hist w orig)
    (P : Nat → List Nat) (known : Nat → Nat)
    (hsource : ∀ t, known (t + 1) = known t ∨ w ≤ known (t + 1))
    (hold : ∀ x y, Anc par x (hist (known 0)) → Anc par y (hist (known 0)) →
      orig x = orig y → x = y)
    (hstep : ∀ t, PStep par hist orig (known t) (P t) (P (t + 1))) :
    ∃ T, ∀ t, T ≤ t → ∀ p ∈ P (t + 1), p ∈ P t := by
  classical
  by_cases enters : ∃ t, w ≤ known t
  · obtain ⟨k, hk⟩ := enters
    have window : ∀ t, k ≤ t → w ≤ known t := by
      intro t ht
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
      induction d with
      | zero => exact hk
      | succ d ih =>
        rcases hsource (k + d) with he | hw
        · rw [show k + (d + 1) = k + d + 1 by omega, he]
          exact ih (by omega)
        · exact hw
    obtain ⟨T, hT⟩ := pending_names_settle H (fun t => P (k + t))
      (fun t => known (k + t)) (fun t => window _ (Nat.le_add_right _ _))
      (fun t => by simpa only [Nat.add_assoc] using hstep (k + t))
    refine ⟨k + T, fun t ht p hp => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ t by omega)
    exact hT d (by omega) p hp
  · have fixed : ∀ t, known t = known 0 := by
      intro t
      induction t with
      | zero => rfl
      | succ t ih =>
        rcases hsource t with he | hw
        · exact he.trans ih
        · exact False.elim (enters ⟨t + 1, hw⟩)
    let oldHist := fun _ : Nat => hist (known 0)
    have oldWindow : History par oldHist 0 orig :=
      ⟨fun _ _ _ _ => Anc.refl, fun _ _ => hold⟩
    exact pending_names_settle oldWindow P (fun _ => 0) (fun _ => Nat.zero_le _)
      (fun t => (hstep t).head_eq (by simp only [oldHist, fixed t]))

/-- Reserve index zero for an obsolete head. Positive indices name the current raw history
by observation time; they are not native sequence numbers, which rollback can reuse. -/
def withOldHead (old : Nat) (heads : Nat → Nat) : Nat → Nat
  | 0 => old
  | i + 1 => heads i

def sourceIndex : Option Nat → Nat
  | none => 0
  | some i => i + 1

def sourceHead (old : Nat) (heads : Nat → Nat) : Option Nat → Nat
  | none => old
  | some i => heads i

/-- A direct source-indexed form for the actual-time history from GlobalRaw: `none` is the
unchanged old pair, and `some i` records a head observed at time `i` in the current window.
No numerical comparison of the old native sequence with the current one is made. -/
theorem pending_names_settle_from_sources (H : History par hist 0 orig)
    (old : Nat) (P : Nat → List Nat) (source : Nat → Option Nat)
    (hsource : ∀ t, source (t + 1) = source t ∨ ∃ i, source (t + 1) = some i)
    (hold : ∀ x y, Anc par x old → Anc par y old → orig x = orig y → x = y)
    (hstep : ∀ t, PStep par (fun _ => sourceHead old hist (source t)) orig 0
      (P t) (P (t + 1))) :
    ∃ T, ∀ t, T ≤ t → ∀ p ∈ P (t + 1), p ∈ P t := by
  have window : History par (withOldHead old hist) 1 orig := by
    constructor
    · intro i j hi hij
      cases i with
      | zero => omega
      | succ i =>
        cases j with
        | zero => omega
        | succ j => exact H.chain i j (Nat.zero_le _) (by omega)
    · intro j hj
      cases j with
      | zero => omega
      | succ j => exact H.unique j (Nat.zero_le _)
  apply pending_names_settle_with_old_known window P (fun t => sourceIndex (source t))
  · intro t
    rcases hsource t with he | ⟨i, he⟩
    · exact Or.inl (congrArg sourceIndex he)
    · exact Or.inr (by simp [he, sourceIndex])
  · cases h : source 0 with
    | none => exact hold
    | some i => exact H.unique i (Nat.zero_le _)
  · intro t
    apply (hstep t).head_eq
    cases source t <;> rfl

end Pending

section Metadata

/-- Immutable metadata for a finite relevant closure eventually stops arriving. Nothing
requires every missing body to arrive: after the cut, some inputs may remain absent. -/
theorem finite_metadata_stabilizes {α : Type} (L : List Nat) (facts : Nat → Nat → Option α)
    (hkeep : ∀ t x a, facts t x = some a → facts (t + 1) x = some a) :
    ∃ T, ∀ t, T ≤ t → ∀ x ∈ L, facts t x = facts T x := by
  let missing := fun t => (L.filter fun x => (facts t x).isNone).length
  have mono : ∀ t x, (facts (t + 1) x).isNone = true → (facts t x).isNone = true := by
    intro t x h
    cases before : facts t x with
    | none => rfl
    | some a => simp [hkeep t x a before] at h
  have le : ∀ t, missing (t + 1) ≤ missing t :=
    fun t => filter_len_mono L _ _ (fun x _ => mono t x)
  obtain ⟨T, hT⟩ := nat_trace_stabilizes missing le
  have step : ∀ t, T ≤ t → ∀ x ∈ L, facts (t + 1) x = facts t x := by
    intro t ht x hx
    cases before : facts t x with
    | some a => exact hkeep t x a before
    | none =>
      cases after : facts (t + 1) x with
      | none => rfl
      | some a =>
        have strict : missing (t + 1) < missing t :=
          filter_len_lt L _ _ (fun y _ => mono t y)
            ⟨x, hx, by simp [before], by simp [after]⟩
        rw [hT t ht, hT (t + 1) (by omega)] at strict
        exact False.elim (Nat.lt_irrefl _ strict)
  refine ⟨T, fun t ht x hx => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  induction d with
  | zero => rfl
  | succ d ih => exact (step (T + d) (by omega) x hx).trans (ih (by omega))

/-- A deterministic computation with finite metadata support stabilizes with those inputs.
For native normalization the support is the fixed raw ancestry and retained drop bodies;
the support law is a separate code correspondence, not an assumed output cutoff. -/
theorem finite_metadata_output_stabilizes {α β : Type} (L : List Nat)
    (facts : Nat → Nat → Option α) (compute : (Nat → Option α) → β)
    (hkeep : ∀ t x a, facts t x = some a → facts (t + 1) x = some a)
    (hsupport : ∀ f g, (∀ x ∈ L, f x = g x) → compute f = compute g) :
    ∃ T, ∀ t, T ≤ t → compute (facts t) = compute (facts T) := by
  obtain ⟨T, hT⟩ := finite_metadata_stabilizes L facts hkeep
  exact ⟨T, fun t ht => hsupport _ _ (hT t ht)⟩

end Metadata

end Musubi.PendingEpoch

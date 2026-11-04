/-
Raw closure and frontier ranks for a frozen-known local burst. These contracts describe field
changes; the rank decrease is proved from them, never assumed of the native core.
-/
import Musubi.NodeSettle
import Musubi.PendingEpoch

namespace Musubi.EarlyEntry.Burst

open Musubi NodeSettle

/-- A no-RPC burst keeps one raw known closure. Locality reads those hub names; frontier
ancestry reads the node-space images and heads. The known head and its images are never
identified. Native conformance places both among distinct vertices of one raw DAG. -/
structure State where
  loc : Nat → Bool
  heads : List Nat
  plan : List Nat

def covered (anc : Nat → Nat → Bool) (heads : List Nat) (i : Nat) : Bool :=
  heads.any (anc i)

def rank (rawClosure images : List Nat) (anc : Nat → Nat → Bool) (s : State) : List Nat :=
  [(rawClosure.filter fun x => !s.loc x).length,
    (images.filter fun i => !(covered anc s.heads i)).length, s.heads.length, s.plan.length]

def LocalGrows (L : List Nat) (s t : State) : Prop :=
  ∀ x ∈ L, s.loc x = true → t.loc x = true

/-- The native locality question: there is at least one node-space image, and every
image has a local realization. Raw known names are not replaced by their originals. -/
def localFromImages (images : List Nat) (mapped : Nat → Bool) : Bool :=
  !images.isEmpty && images.all mapped

theorem localFromImages_mono (images : List Nat) {mapped mapped' : Nat → Bool}
    (hm : ∀ x, mapped x = true → mapped' x = true)
    (h : localFromImages images mapped = true) : localFromImages images mapped' = true := by
  simp only [localFromImages, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun x hx => hm x (h.2 x hx)⟩

/-- Partial naming may change when another ancestor body arrives. Finite immutable input
support derives a naming cutoff, without assuming complete metadata or a naming cutoff.
Thereafter append-only local realizations imply the burst's locality-monotonicity law.
`normalize` returns images only for the fixed relevant names; other names may map to []. -/
theorem local_grows_after_inputs {α : Type} (inputs : List Nat)
    (facts : Nat → Nat → Option α)
    (normalize : (Nat → Option α) → Nat → List Nat) (mapped : Nat → Nat → Bool)
    (hkeep : ∀ t x a, facts t x = some a → facts (t + 1) x = some a)
    (hsupport : ∀ f g, (∀ x ∈ inputs, f x = g x) → normalize f = normalize g)
    (hmapped : ∀ t x, mapped t x = true → mapped (t + 1) x = true) :
    ∃ T, ∀ t, T ≤ t → ∀ x,
      localFromImages (normalize (facts t) x) (mapped t) = true →
      localFromImages (normalize (facts (t + 1)) x) (mapped (t + 1)) = true := by
  obtain ⟨T, hT⟩ := PendingEpoch.finite_metadata_output_stabilizes inputs facts normalize
    hkeep hsupport
  refine ⟨T, fun t ht x h => ?_⟩
  have same := (hT (t + 1) (by omega)).trans (hT t ht).symm
  rw [same]
  exact localFromImages_mono _ (hmapped t) h

/-- Native core branches before the next request or idle. A queued entry can already be
local because the adapter realizes batches; dequeuing it still spends plan length. A NEW
survey's first entry was nonlocal when surveyed and becomes local after successful realize.
Merge and advance describe frontier effects, not a promised rank decrease. -/
inductive Step (rawClosure images : List Nat) (anc : Nat → Nat → Bool) :
    State → State → Prop
  | plan {s t : State} (x : Nat) (rest : List Nat) (hp : s.plan = x :: rest)
      (ht : t.plan = rest) (hh : t.heads = s.heads) (hl : LocalGrows rawClosure s t) :
      Step rawClosure images anc s t
  | survey {s t : State} (x : Nat) (hp : s.plan = []) (hx : x ∈ rawClosure)
      (hbefore : s.loc x = false) (hafter : t.loc x = true)
      (hh : t.heads = s.heads) (hl : LocalGrows rawClosure s t) : Step rawClosure images anc s t
  | merge {s t : State} (h : Nat) (h2 : 2 ≤ s.heads.length) (hh : t.heads = [h])
      (ha : ∀ p ∈ s.heads, anc p h = true) (hl : LocalGrows rawClosure s t) :
      Step rawClosure images anc s t
  | advance {s t : State} (h : Nat) (hh : s.heads = [h])
      (hmiss : ∃ i ∈ images, anc i h = false)
      (hcovers : ∀ i ∈ images, covered anc t.heads i = true) (hl : LocalGrows rawClosure s t) :
      Step rawClosure images anc s t

theorem missing_mono {s t : State} (L : List Nat) (hl : LocalGrows L s t) :
    (L.filter fun x => !t.loc x).length ≤ (L.filter fun x => !s.loc x).length := by
  apply PendingEpoch.filter_len_mono
  intro x hxm hx
  cases hs : s.loc x
  · rfl
  · simp [hl x hxm hs] at hx

theorem covered_merge {anc : Nat → Nat → Bool}
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    {s t : State} {h : Nat} (hh : t.heads = [h]) (ha : ∀ p ∈ s.heads, anc p h = true)
    (i : Nat) (hi : covered anc s.heads i = true) : covered anc t.heads i = true := by
  obtain ⟨p, hp, hip⟩ := List.any_eq_true.1 hi
  simpa [covered, hh] using trans i p h hip (ha p hp)

theorem step_rank {rawClosure images : List Nat} {anc : Nat → Nat → Bool}
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    {s t : State} (hs : Step rawClosure images anc s t) :
    LexLt (rank rawClosure images anc t) (rank rawClosure images anc s) := by
  cases hs with
  | plan x rest hp ht hh hl =>
    apply lt_cons (missing_mono rawClosure hl)
    intro _
    apply lt_cons (by simp [hh])
    intro _
    apply lt_cons (by simp [hh])
    intro _
    apply lt_hd
    simp [hp, ht]
  | survey x hp hx hb ha hh hl =>
    apply lt_hd
    apply PendingEpoch.filter_len_lt
    · intro y hym hy
      cases hs : s.loc y
      · rfl
      · simp [hl y hym hs] at hy
    · exact ⟨x, hx, by simp [hb], by simp [ha]⟩
  | merge h h2 hh ha hl =>
    apply lt_cons (missing_mono rawClosure hl)
    intro _
    apply lt_cons
      (PendingEpoch.filter_len_mono images _ _ (fun i _ hi => by
        cases hb : covered anc s.heads i
        · rfl
        · simp [covered_merge trans hh ha i hb] at hi))
    intro _
    apply lt_hd
    simp only [hh, List.length_singleton]
    omega
  | advance h hh hmiss hc hl =>
    apply lt_cons (missing_mono rawClosure hl)
    intro _
    apply lt_hd
    have empty : (images.filter fun i => !(covered anc t.heads i)) = [] := by
      apply List.filter_eq_nil_iff.2
      intro i hi
      simp [hc i hi]
    rw [empty]
    obtain ⟨i, hi, hm⟩ := hmiss
    have present : i ∈ images.filter (fun i => !(covered anc s.heads i)) :=
      List.mem_filter.2 ⟨hi, by simp [covered, hh, hm]⟩
    exact List.length_pos_iff.2 (fun hnil => by rw [hnil] at present; cases present)

/-- Frozen knowledge and finite raw closure cannot support infinitely many own core
branches without another RPC or idle. This prefix argument does not need complete metadata,
an original-label realization trace, or a fair round-completion premise. -/
theorem no_infinite_burst (rawClosure images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run : Nat → State)
    (hs : ∀ i, Step rawClosure images anc (run i) (run (i + 1))) : False := by
  have less := fun i => step_rank trans (hs i)
  obtain ⟨k, hk⟩ := lex_stabilizes 4 (fun i => rank rawClosure images anc (run i))
    (fun _ => rfl) (fun i => (less i).le)
  have bad := less k
  rw [hk (k + 1) (by omega)] at bad
  exact lexLt_irrefl _ bad

inductive Kind
  | realize (op : Nat)
  | merge
  | advance

def growsB (L : List Nat) (s t : State) : Bool :=
  L.all fun x => !s.loc x || t.loc x

/-- Executable per-branch contracts, checked against the core's actual before/after
snapshots. These check field effects; `step_rank` derives their decreasing rank. -/
def stepB (rawClosure images : List Nat) (anc : Nat → Nat → Bool)
    (kind : Kind) (s t : State) : Bool :=
  growsB rawClosure s t && match kind with
    | .realize x => decide (t.heads = s.heads) && match s.plan with
      | [] => rawClosure.contains x && !s.loc x && t.loc x
      | y :: rest => decide (x = y) && decide (t.plan = rest)
    | .merge => match t.heads with
      | [h] => decide (2 ≤ s.heads.length) && s.heads.all (fun p => anc p h)
      | _ => false
    | .advance => match s.heads with
      | [h] => images.any (fun i => !anc i h) && images.all (covered anc t.heads)
      | _ => false

theorem growsB_sound {L : List Nat} {s t : State} (h : growsB L s t = true) :
    LocalGrows L s t := by
  intro x hx hl
  have := List.all_eq_true.1 h x hx
  simpa [hl] using this

theorem stepB_sound {rawClosure images : List Nat} {anc : Nat → Nat → Bool}
    {kind : Kind} {s t : State} (h : stepB rawClosure images anc kind s t = true) :
    Step rawClosure images anc s t := by
  simp only [stepB, Bool.and_eq_true] at h
  obtain ⟨hg, hs⟩ := h
  have hl := growsB_sound hg
  cases kind with
  | realize x =>
    simp only [Bool.and_eq_true] at hs
    obtain ⟨hh, hs⟩ := hs
    have hh := of_decide_eq_true hh
    cases hp : s.plan with
    | nil =>
      simp only [hp, Bool.and_eq_true] at hs
      obtain ⟨⟨hx, hb⟩, ha⟩ := hs
      exact .survey x hp (List.contains_iff_mem.1 hx) (by simpa using hb) ha hh hl
    | cons y rest =>
      simp only [hp, Bool.and_eq_true, decide_eq_true_eq] at hs
      obtain ⟨rfl, ht⟩ := hs
      exact .plan x rest hp ht hh hl
  | merge =>
    cases hh : t.heads with
    | nil => simp [hh] at hs
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [hh, Bool.and_eq_true, decide_eq_true_eq] at hs
        exact .merge x hs.1 hh (List.all_eq_true.1 hs.2) hl
      | cons y rest => simp [hh] at hs
  | advance =>
    cases hh : s.heads with
    | nil => simp [hh] at hs
    | cons x rest =>
      cases rest with
      | nil =>
        simp only [hh, Bool.and_eq_true] at hs
        obtain ⟨i, hi, hm⟩ := List.any_eq_true.1 hs.1
        exact .advance x hh ⟨i, hi, by simpa using hm⟩ (List.all_eq_true.1 hs.2) hl
      | cons y rest => simp [hh] at hs

end Musubi.EarlyEntry.Burst

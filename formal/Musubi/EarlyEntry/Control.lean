import Musubi.EarlyEntry.Burst
import Musubi.ExecSound

/-! ## A pending node's raw control after the cuts

After the record and receipt cuts, with the hub's raw head `H` stable, its records current and
the known closure and images fixed, a node with pending drops reaches its pending push
(`pending_push_reached`). Each core step is chosen as `NodeCore::step` chooses it (`choose`),
from what it reads; with nothing announced, records current, drops pending and no concurrent
change of the op head, it never adopts, idles or polls (`choose_guarded`), the one idle a
survey could give being ruled out by NodeSettle's survey completeness, read on the raw survey
graph (`raw_survey_guard`). Every other step lowers one rank: a burst step Burst's, and a call,
with the reply the core waits for, the count of raw operations it lacks or lacks the objects
of (`call_rank`). Raw ids throughout: no original is identified with a raw id. -/

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-- What a node's control reads after the cuts, raw: the burst's state; which raw operations
it has a body for to realize from (`stg`: staged, or its canonical body; realizing one does not
take it away); and which have their objects here. -/
structure State where
  burst : Burst.State
  stg : Nat → Bool
  obj : Nat → Bool

/-- Nothing in the raw known closure that is local, has a body or has its objects stops being
so. -/
def Grows (raw : List Nat) (s t : State) : Prop :=
  Burst.LocalGrows raw s.burst t.burst ∧ (∀ x ∈ raw, s.stg x = true → t.stg x = true) ∧
    (∀ x ∈ raw, s.obj x = true → t.obj x = true)

/-- The raw operations of the known closure neither local nor with a body. -/
def missOps (raw : List Nat) (s : State) : Nat :=
  (raw.filter fun x => !s.burst.loc x && !s.stg x).length

/-- The raw operations of the known closure not local whose objects are not all here. -/
def missObjs (raw : List Nat) (s : State) : Nat :=
  (raw.filter fun x => !s.burst.loc x && !s.obj x).length

def rank (raw images : List Nat) (anc : Nat → Nat → Bool) (s : State) : List Nat :=
  missOps raw s :: missObjs raw s :: Burst.rank raw images anc s.burst

/-- A core step after the cuts other than the pending push, with the replies to what it
sends: a burst step; a `Fetch` the survey sends for an operation it lacks, whose reply stages
it, or makes it local, as metadata of an alias the node had not seen can; or a `GetObjects`
for an operation whose objects it lacks, whose reply brings them, or makes it local. A call
changes neither the op heads nor the plan; what is local may grow. -/
inductive Call (raw images : List Nat) (anc : Nat → Nat → Bool) : State → State → Prop
  | burst {s t : State} (h : Burst.Step raw images anc s.burst t.burst) (hg : Grows raw s t) :
      Call raw images anc s t
  | fetch {s t : State} (x : Nat) (hx : x ∈ raw) (hl : s.burst.loc x = false)
      (hs : s.stg x = false) (ht : t.stg x = true ∨ t.burst.loc x = true)
      (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
      (hg : Grows raw s t) : Call raw images anc s t
  | objects {s t : State} (x : Nat) (hx : x ∈ raw) (hl : s.burst.loc x = false)
      (ho : s.obj x = false) (ht : t.obj x = true ∨ t.burst.loc x = true)
      (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
      (hg : Grows raw s t) : Call raw images anc s t

theorem false_of_grows {a b : Bool} (h : a = true → b = true) (hb : b = false) : a = false := by
  cases a
  · rfl
  · rw [h rfl] at hb; cases hb

theorem missOps_mono {raw : List Nat} {s t : State} (hg : Grows raw s t) :
    missOps raw t ≤ missOps raw s := by
  apply PendingEpoch.filter_len_mono
  intro x hx h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
  exact ⟨false_of_grows (hg.1 x hx) h.1, false_of_grows (hg.2.1 x hx) h.2⟩

theorem missObjs_mono {raw : List Nat} {s t : State} (hg : Grows raw s t) :
    missObjs raw t ≤ missObjs raw s := by
  apply PendingEpoch.filter_len_mono
  intro x hx h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
  exact ⟨false_of_grows (hg.1 x hx) h.1, false_of_grows (hg.2.2 x hx) h.2⟩

theorem call_rank {raw images : List Nat} {anc : Nat → Nat → Bool}
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    {s t : State} (h : Call raw images anc s t) :
    LexLt (rank raw images anc t) (rank raw images anc s) := by
  cases h with
  | burst h hg =>
    exact lt_cons (missOps_mono hg) fun _ =>
      lt_cons (missObjs_mono hg) fun _ => Burst.step_rank trans h
  | fetch x hx hl hs ht hh hp hg =>
    apply lt_hd
    apply PendingEpoch.filter_len_lt
    · intro y hy h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
      exact ⟨false_of_grows (hg.1 y hy) h.1, false_of_grows (hg.2.1 y hy) h.2⟩
    · refine ⟨x, hx, by simp [hl, hs], ?_⟩
      rcases ht with ht | ht <;> simp [ht]
  | objects x hx hl ho ht hh hp hg =>
    apply lt_cons (missOps_mono hg)
    intro _
    apply lt_hd
    apply PendingEpoch.filter_len_lt
    · intro y hy h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h ⊢
      exact ⟨false_of_grows (hg.1 y hy) h.1, false_of_grows (hg.2.2 y hy) h.2⟩
    · refine ⟨x, hx, by simp [hl, ho], ?_⟩
      rcases ht with ht | ht <;> simp [ht]

/-- No run of such calls goes on forever. -/
theorem no_infinite_calls (raw images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run : Nat → State) (hs : ∀ i, Call raw images anc (run i) (run (i + 1))) : False := by
  have less := fun i => call_rank trans (hs i)
  obtain ⟨k, hk⟩ := lex_stabilizes 6 (fun i => rank raw images anc (run i))
    (fun _ => rfl) (fun i => (less i).le)
  have bad := less k
  rw [hk (k + 1) (by omega)] at bad
  exact lexLt_irrefl _ bad

theorem lexLt_trans : ∀ {x y z : List Nat}, LexLt x y → LexLt y z → LexLt x z
  | a :: as, b :: bs, c :: cs, h1, h2 => by
    rcases h1 with h1 | ⟨rfl, h1⟩ <;> rcases h2 with h2 | ⟨rfl, h2⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, lexLt_trans h1 h2⟩
  | [], _, _, h1, _ => by simp [LexLt] at h1
  | _ :: _, [], _, h1, _ => by simp [LexLt] at h1
  | _ :: _, _ :: _, [], _, h2 => by simp [LexLt] at h2

theorem lexLt_of_le_lt {x y z : List Nat} (h1 : LexLe x y) (h2 : LexLt y z) : LexLt x z := by
  rcases h1 with h | rfl
  · exact lexLt_trans h h2
  · exact h2

/-- What may happen to a node's control state between its step's calls completing and its next
step's reading, after that step's prelude, in the same round, with no automatic write of the node
(the prelude's own writers, `before_sync`'s `reconcile_settings` and `show_other_workspaces`, a
`jj op abandon` passed on, are such, and the frame is asked only past their cut, `QuietAt`):
nothing in the raw closure stops being local, having a body or its objects (the prelude's
`prepare_records` writes rewrites beside what is there; nothing is removed), and the CANONICAL op
heads and the plan the core reads are the same. The prelude may move the physical heads
(`canonical_heads`, `check_abandon` and `realign_heads`, `reparent_late`), but their canonical
readings, under naming that does not change and once any recovery's own prelude has completed
before the readings, are unchanged (that completion, not entry: `fresh_head_reached` uses frames
before entry is derived, so entry is no premise of a frame); notices are handled between rounds
and user work is past. Locality is read through naming, which may change, so a frame is asked only
across steps naming does not change across (`Naming.Still`). -/
def Frame (raw : List Nat) (s t : State) : Prop :=
  Grows raw s t ∧ t.burst.heads = s.burst.heads ∧ t.burst.plan = s.burst.plan

/-- A frame never raises the control rank. -/
theorem frame_rank {raw images : List Nat} {anc : Nat → Nat → Bool} {s t : State}
    (h : Frame raw s t) : LexLe (rank raw images anc t) (rank raw images anc s) := by
  obtain ⟨hg, hh, hp⟩ := h
  refine le_cons (missOps_mono hg) fun _ => le_cons (missObjs_mono hg) fun _ =>
    le_cons (Burst.missing_mono raw hg.1) fun _ => ?_
  right
  simp only [hh, hp]

/-- No run of such calls, each followed by a frame, goes on forever. -/
theorem no_infinite_framed (raw images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run after : Nat → State) (hs : ∀ i, Call raw images anc (run i) (after i))
    (hf : ∀ i, Frame raw (after i) (run (i + 1))) : False := by
  have less : ∀ i, LexLt (rank raw images anc (run (i + 1))) (rank raw images anc (run i)) :=
    fun i => lexLt_of_le_lt (frame_rank (hf i)) (call_rank trans (hs i))
  obtain ⟨k, hk⟩ := lex_stabilizes 6 (fun i => rank raw images anc (run i))
    (fun _ => rfl) (fun i => (less i).le)
  have bad := less k
  rw [hk (k + 1) (by omega)] at bad
  exact lexLt_irrefl _ bad

/-! ### The core's choice -/

/-- What `NodeCore::step` reads to choose: records announced and not taken; whether taking
them drops an op head (`prepare_records`); two op heads or more; whether the known head is
local; a plan left; the survey's plan, missing operations and missing objects; whether an op
head descends from the known one; whether its records differ from the hub's as heard; pending
drops; the op head the known one; and the fix-up's new head the known one. -/
structure Reads where
  announced : Bool
  dropHead : Bool
  heads2 : Bool
  knownLocal : Bool
  planNe : Bool
  ready : Bool
  missOps : Bool
  missObjs : Bool
  descends : Bool
  differ : Bool
  pending : Bool
  headIsKnown : Bool
  newIsKnown : Bool

inductive Choice
  | adopt
  | merge
  | realize
  | fetch
  | objects
  | idle
  | advance
  | poll
  | push
  deriving DecidableEq

/-- `NodeCore::step`'s choice, in its order. A survey that finds an operation missing fetches,
with a `GetObjects` beside if objects are missing too; one finding only objects missing asks
for them. -/
def choose (r : Reads) : Choice :=
  if r.announced && !r.dropHead then .adopt
  else if r.heads2 then .merge
  else if !r.knownLocal then
    if r.planNe || r.ready then .realize
    else if r.missOps then .fetch
    else if r.missObjs then .objects
    else .idle
  else if r.dropHead || !r.descends then .advance
  else if r.differ then (if r.announced then .idle else .poll)
  else if !r.pending then (if r.headIsKnown then .idle else .push)
  else if r.newIsKnown then .poll
  else .push

/-- With nothing announced, records current, drops pending and the fix-up's head another
than the known one, and a survey that, finding nothing ready, finds something missing, the
core never adopts, idles or polls. -/
theorem choose_guarded {r : Reads} (ha : r.announced = false) (hdh : r.dropHead = false)
    (hd : r.differ = false) (hp : r.pending = true) (hn : r.newIsKnown = false)
    (hs : r.knownLocal = false → r.ready = false → r.missOps = true ∨ r.missObjs = true) :
    choose r = .merge ∨ choose r = .realize ∨ choose r = .fetch ∨ choose r = .objects ∨
      choose r = .advance ∨ choose r = .push := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk, nk⟩ := r
  simp only at ha hdh hd hp hn hs
  subst ha hdh hd hp hn
  cases h2 <;> cases kl <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;> cases de <;>
    simp_all [choose]


/-- The core pushes only with one op head, the known head local and an op head descending
from it. -/
theorem choose_push {r : Reads} (h : choose r = .push) :
    r.descends = true ∧ r.knownLocal = true ∧ r.heads2 = false := by
  unfold choose at h
  repeat' first | contradiction | split at h
  all_goals simp_all

/-- The core pushes only when its records do not differ from those it last heard. -/
theorem choose_push_differ {r : Reads} (h : choose r = .push) : r.differ = false := by
  unfold choose at h
  repeat' first | contradiction | split at h
  all_goals simp_all

theorem choose_objects_missObjs {r : Reads} (h : choose r = .objects) : r.missObjs = true := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · assumption
    · cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h <;> cases h


theorem choose_adopt_of {r : Reads} (ha : r.announced = true) (hd : r.dropHead = false) :
    choose r = .adopt := by
  simp [choose, ha, hd]

/-- With an announcement that drops an op head, the core never gets as far as polling or
pushing: it advances, taking it, first. -/
theorem choose_late_dropHead {r : Reads} (hd : r.dropHead = true)
    (h : choose r = .poll ∨ choose r = .push) : False := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk, nk⟩ := r
  simp only at hd
  subst hd
  cases a <;> cases h2 <;> cases kl <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;>
    simp_all [choose]


/-- With an announcement that drops an op head, the core idles only in its survey, with the
known head not local and nothing ready. -/
theorem choose_idle_dropHead {r : Reads} (hd : r.dropHead = true) (h : choose r = .idle) :
    r.knownLocal = false ∧ r.ready = false := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk, nk⟩ := r
  simp only at hd ⊢
  subst hd
  cases a <;> cases h2 <;> cases kl <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;>
    simp_all [choose]


theorem choose_fetch_missOps {r : Reads} (h : choose r = .fetch) : r.missOps = true := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · assumption
    split at h <;> cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h <;> cases h


/-- The core idles in its survey only finding nothing missing. -/
theorem choose_idle_survey {r : Reads} (h : choose r = .idle) (hk : r.knownLocal = false) :
    r.missOps = false ∧ r.missObjs = false := by
  obtain ⟨a, dh, h2, kl, pln, rd, mo, mb, de, di, pe, hk', nk⟩ := r
  simp only at hk ⊢
  subst hk
  cases a <;> cases dh <;> cases h2 <;> cases pln <;> cases rd <;> cases mo <;> cases mb <;>
    simp_all [choose]


/-- The core pushes only with nothing announced. -/
theorem choose_push_announced {r : Reads} (h : choose r = .push) : r.announced = false := by
  unfold choose at h
  repeat' first | contradiction | split at h
  all_goals simp_all

/-- The survey's guard, from NodeSettle's survey completeness read on the raw survey graph:
the raw parents, and native locality, staging and objects of raw ids, from the known raw head.
Given that the native survey finds exactly what NodeSettle's walk does there, a known head that
is not local has something ready or something missing. -/
def rawSurvey (base : NS) (par : Nat → List Nat) (loc stg obj : Nat → Bool) (H : Nat) : NS :=
  { base with
    par := par
    loc := fun x => loc x = true
    stg := fun x => stg x = true
    obj := fun x => obj x = true
    known := (base.known.1, H) }

theorem raw_survey_guard {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool}
    {H : Nat} {r : Reads} (hlt : ParLt par) (hloc : r.knownLocal = loc H)
    (hready : r.ready = true ↔ ∃ x, Ready (rawSurvey base par loc stg obj H) x)
    (hops : r.missOps = true ↔ MissOps (rawSurvey base par loc stg obj H))
    (hobjs : r.missObjs = true ↔ MissObjs (rawSurvey base par loc stg obj H)) :
    r.knownLocal = false → r.ready = false → r.missOps = true ∨ r.missObjs = true := by
  intro hk hr
  have hl : ¬ (rawSurvey base par loc stg obj H).loc (rawSurvey base par loc stg obj H).known.2 :=
    by
      change ¬ loc H = true
      rw [← hloc, hk]
      exact Bool.false_ne_true
  rcases survey_complete hlt hl with h | h | h
  · rw [← hready, hr] at h; cases h
  · exact Or.inl (hops.2 h)
  · exact Or.inr (hobjs.2 h)

/-- A `Fetch` sent for a missing operation is such a call: the walk stays in the raw known
closure, and the reply about the stable head stages every operation of it not local, or makes
it local. -/
theorem fetch_call {raw images : List Nat} {anc : Nat → Nat → Bool} {base : NS}
    {par : Nat → List Nat} {H : Nat} {s t : State}
    (hm : MissOps (rawSurvey base par s.burst.loc s.stg s.obj H))
    (hwalk : ∀ x, Walk (rawSurvey base par s.burst.loc s.stg s.obj H) x → x ∈ raw)
    (hstage : ∀ x ∈ raw, s.burst.loc x = false → t.stg x = true ∨ t.burst.loc x = true)
    (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
    (hg : Grows raw s t) : Call raw images anc s t := by
  obtain ⟨x, hw, hl, hs⟩ := hm
  have hx := hwalk x hw
  exact .fetch x hx (by simpa [rawSurvey] using hl) (by simpa [rawSurvey] using hs)
    (hstage x hx (by simpa [rawSurvey] using hl)) hh hp hg

/-- A `GetObjects` for the operations whose objects are missing is such a call: its reply
brings them, or makes the operation local. -/
theorem objects_call {raw images : List Nat} {anc : Nat → Nat → Bool} {base : NS}
    {par : Nat → List Nat} {H : Nat} {s t : State}
    (hm : MissObjs (rawSurvey base par s.burst.loc s.stg s.obj H))
    (hwalk : ∀ x, Walk (rawSurvey base par s.burst.loc s.stg s.obj H) x → x ∈ raw)
    (hbring : ∀ x, Walk (rawSurvey base par s.burst.loc s.stg s.obj H) x →
      s.burst.loc x = false → s.stg x = true → s.obj x = false →
        t.obj x = true ∨ t.burst.loc x = true)
    (hh : t.burst.heads = s.burst.heads) (hp : t.burst.plan = s.burst.plan)
    (hg : Grows raw s t) : Call raw images anc s t := by
  obtain ⟨x, hw, hl, hs, ho⟩ := hm
  have hl' : s.burst.loc x = false := by simpa [rawSurvey] using hl
  have ho' : s.obj x = false := by simpa [rawSurvey] using ho
  exact .objects x (hwalk x hw) hl' ho'
    (hbring x hw hl' (by simpa [rawSurvey] using hs) ho') hh hp hg

/-- A node with pending drops, after the cuts, reaches its pending push: given at each core
step the guards `choose_guarded` takes, and the effect of the step it chooses (a burst step,
or a call with its reply), it pushes at some step. No step is assumed to push. -/
theorem pending_push_reached (raw images : List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run after : Nat → State) (reads : Nat → Reads)
    (hframe : ∀ i, Frame raw (after i) (run (i + 1)))
    (hguard : ∀ i, (reads i).announced = false ∧ (reads i).dropHead = false ∧
      (reads i).differ = false ∧ (reads i).pending = true ∧ (reads i).newIsKnown = false)
    (hsurvey : ∀ i, (reads i).knownLocal = false → (reads i).ready = false →
      (reads i).missOps = true ∨ (reads i).missObjs = true)
    (hburst : ∀ i, (choose (reads i) = .merge ∨ choose (reads i) = .realize ∨
      choose (reads i) = .advance) →
      Burst.Step raw images anc (run i).burst (after i).burst ∧ Grows raw (run i) (after i))
    (hcall : ∀ i, (choose (reads i) = .fetch ∨ choose (reads i) = .objects) →
      Call raw images anc (run i) (after i)) :
    ∃ i, choose (reads i) = .push := by
  apply Classical.byContradiction
  intro hno
  apply no_infinite_framed raw images anc trans run after _ hframe
  intro i
  obtain ⟨ha, hdh, hd, hp, hn⟩ := hguard i
  rcases choose_guarded ha hdh hd hp hn (hsurvey i) with h | h | h | h | h | h
  · obtain ⟨hs, hg⟩ := hburst i (Or.inl h); exact .burst hs hg
  · obtain ⟨hs, hg⟩ := hburst i (Or.inr (Or.inl h)); exact .burst hs hg
  · exact hcall i (Or.inl h)
  · exact hcall i (Or.inr h)
  · obtain ⟨hs, hg⟩ := hburst i (Or.inr (Or.inr h)); exact .burst hs hg
  · exact absurd ⟨i, h⟩ hno

/-! ### The survey and the choice, computed on the raw graph

What the survey finds is computed from the raw graph and the native bits alone, over the raw
known closure: the walk is ancestry through the parents of operations neither local nor
without a body (`walk_iff`), so `Exec.ancB` decides it, and readiness and what is missing are
found among the closure's operations (`readyB_iff`, `missOpsB_iff`, `missObjsB_iff`). So the
survey's guard is derived (`rawReads_survey`), not assumed, and `rawControl` computes the core's
choice from a state before a step and the primitive bits the native core reports, never from
the choice it made. `callB` checks a call's effect, soundly (`callB_sound`). -/

/-- The parents the survey walks through: an operation's own, if it is neither local nor
without a body; none otherwise. -/
def walkParents (par : Nat → List Nat) (loc stg : Nat → Bool) (x : Nat) : List Nat :=
  if (!loc x && stg x) = true then par x else []

theorem parLt_walkParents {par : Nat → List Nat} {loc stg : Nat → Bool} (hlt : ParLt par) :
    ParLt (walkParents par loc stg) := by
  intro y p hp
  unfold walkParents at hp
  split at hp
  · exact hlt y p hp
  · cases hp

theorem mem_walkParents {par : Nat → List Nat} {loc stg : Nat → Bool} {x p : Nat} :
    p ∈ walkParents par loc stg x ↔ loc x = false ∧ stg x = true ∧ p ∈ par x := by
  unfold walkParents
  split <;> rename_i h <;> simp_all

/-- NodeSettle's walk on the raw survey graph is ancestry through the walked parents. -/
theorem walk_iff {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool} {H x : Nat} :
    Walk (rawSurvey base par loc stg obj H) x ↔ Anc (walkParents par loc stg) x H := by
  constructor
  · intro h
    induction h with
    | top => exact Anc.refl
    | up _ hl hs hp ih =>
      refine (Anc.parent (mem_walkParents.2 ⟨?_, hs, hp⟩)).trans ih
      simpa [rawSurvey] using hl
  · intro h
    have key : ∀ y, Anc (walkParents par loc stg) x y →
        Walk (rawSurvey base par loc stg obj H) y →
          Walk (rawSurvey base par loc stg obj H) x := by
      intro y hxy
      induction hxy with
      | refl => exact id
      | step hp _ ih =>
        intro hy
        obtain ⟨hl, hs, hp⟩ := mem_walkParents.1 hp
        exact ih (Walk.up hy (by simp [rawSurvey, hl]) hs hp)
    exact key H h Walk.top

/-- The walk, decided. -/
def walkB (par : Nat → List Nat) (loc stg : Nat → Bool) (H x : Nat) : Bool :=
  Exec.ancB (walkParents par loc stg) x H

theorem walkB_iff {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool} {H x : Nat}
    (hlt : ParLt par) :
    walkB par loc stg H x = true ↔ Walk (rawSurvey base par loc stg obj H) x := by
  rw [walkB, Exec.ancB_iff (parLt_walkParents hlt), walk_iff]

/-- Something the survey can realize now, among the raw known closure `raw`. -/
def readyB (raw : List Nat) (par : Nat → List Nat) (loc stg obj : Nat → Bool) (H : Nat) :
    Bool :=
  raw.any fun x => walkB par loc stg H x && !loc x && stg x && obj x && (par x).all loc

/-- Something the survey reaches that has no body. -/
def missOpsB (raw : List Nat) (par : Nat → List Nat) (loc stg : Nat → Bool) (H : Nat) : Bool :=
  raw.any fun x => walkB par loc stg H x && !loc x && !stg x

/-- Something the survey reaches with a body whose objects are not all here. -/
def missObjsB (raw : List Nat) (par : Nat → List Nat) (loc stg obj : Nat → Bool) (H : Nat) :
    Bool :=
  raw.any fun x => walkB par loc stg H x && !loc x && stg x && !obj x

theorem walk_mem {base : NS} {par : Nat → List Nat} {loc stg obj : Nat → Bool} {H x : Nat}
    {raw : List Nat} (hraw : ∀ x, Anc par x H → x ∈ raw)
    (hw : Walk (rawSurvey base par loc stg obj H) x) : x ∈ raw :=
  hraw x hw.anc

theorem readyB_iff {base : NS} {raw : List Nat} {par : Nat → List Nat}
    {loc stg obj : Nat → Bool} {H : Nat} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    readyB raw par loc stg obj H = true ↔ ∃ x, Ready (rawSurvey base par loc stg obj H) x := by
  unfold readyB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, h⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hw, hl⟩, hs⟩, ho⟩, hp⟩ := h
    exact ⟨x, (walkB_iff hlt).1 hw, by simp [rawSurvey, hl], hs, ho, hp⟩
  · rintro ⟨x, hw, hl, hs, ho, hp⟩
    refine ⟨x, walk_mem hraw hw, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_true]
    exact ⟨⟨⟨⟨(walkB_iff hlt).2 hw, by simpa [rawSurvey] using hl⟩, hs⟩, ho⟩, hp⟩

theorem missOpsB_iff {base : NS} {raw : List Nat} {par : Nat → List Nat}
    {loc stg obj : Nat → Bool} {H : Nat} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    missOpsB raw par loc stg H = true ↔ MissOps (rawSurvey base par loc stg obj H) := by
  unfold missOpsB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, h⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨hw, hl⟩, hs⟩ := h
    exact ⟨x, (walkB_iff hlt).1 hw, by simp [rawSurvey, hl], by simp [rawSurvey, hs]⟩
  · rintro ⟨x, hw, hl, hs⟩
    refine ⟨x, walk_mem hraw hw, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨⟨(walkB_iff hlt).2 hw, by simpa [rawSurvey] using hl⟩,
      by simpa [rawSurvey] using hs⟩

theorem missObjsB_iff {base : NS} {raw : List Nat} {par : Nat → List Nat}
    {loc stg obj : Nat → Bool} {H : Nat} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    missObjsB raw par loc stg obj H = true ↔ MissObjs (rawSurvey base par loc stg obj H) := by
  unfold missObjsB
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, -, h⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨⟨⟨hw, hl⟩, hs⟩, ho⟩ := h
    exact ⟨x, (walkB_iff hlt).1 hw, by simp [rawSurvey, hl], hs, by simp [rawSurvey, ho]⟩
  · rintro ⟨x, hw, hl, hs, ho⟩
    refine ⟨x, walk_mem hraw hw, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨⟨⟨(walkB_iff hlt).2 hw, by simpa [rawSurvey] using hl⟩, hs⟩,
      by simpa [rawSurvey] using ho⟩

/-- The primitive bits the native core reports at a step: records announced and not taken,
whether taking them drops an op head, whether its records differ from the hub's as heard,
pending drops, the op head the known one, and the fix-up's new head the known one. -/
structure Prims where
  announced : Bool
  dropHead : Bool
  differ : Bool
  pending : Bool
  headIsKnown : Bool
  newIsKnown : Bool

/-- What the core reads at a step, computed from the state before it: the survey on the raw
graph `par` from the known raw head `H`, over the raw known closure `raw`; whether an op head
descends from the known head (it has node-space images, and every one is below the head, in
`anc`: no images, none descends); and the primitive bits. -/
def rawReads (raw images : List Nat) (par : Nat → List Nat) (anc : Nat → Nat → Bool)
    (H : Nat) (s : State) (q : Prims) : Reads where
  announced := q.announced
  dropHead := q.dropHead
  heads2 := decide (2 ≤ s.burst.heads.length)
  knownLocal := s.burst.loc H
  planNe := !s.burst.plan.isEmpty
  ready := readyB raw par s.burst.loc s.stg s.obj H
  missOps := missOpsB raw par s.burst.loc s.stg H
  missObjs := missObjsB raw par s.burst.loc s.stg s.obj H
  descends := !images.isEmpty && s.burst.heads.any fun h => images.all fun i => anc i h
  differ := q.differ
  pending := q.pending
  headIsKnown := q.headIsKnown
  newIsKnown := q.newIsKnown

/-- The core's choice at a step, computed. -/
def rawControl (raw images : List Nat) (par : Nat → List Nat) (anc : Nat → Nat → Bool)
    (H : Nat) (s : State) (q : Prims) : Choice :=
  choose (rawReads raw images par anc H s q)

/-- A core state to read the raw survey graph into: `rawSurvey` replaces all that the survey
reads. -/
def surveyBase : NS :=
  ⟨(0, 0), [], none, none, 0, [], false, [], [], fun _ => [], 0, fun _ => False,
    fun _ => False, fun _ => False, false⟩

/-- The survey's guard, derived: on the raw graph, with the closure holding the known head's
ancestry, a known head that is not local has something ready or something missing. -/
theorem rawReads_survey {raw images : List Nat} {par : Nat → List Nat}
    {anc : Nat → Nat → Bool} {H : Nat} {s : State} {q : Prims} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) :
    (rawReads raw images par anc H s q).knownLocal = false →
      (rawReads raw images par anc H s q).ready = false →
      (rawReads raw images par anc H s q).missOps = true ∨
        (rawReads raw images par anc H s q).missObjs = true :=
  raw_survey_guard (base := surveyBase) (par := par) (loc := s.burst.loc) (stg := s.stg)
    (obj := s.obj) (H := H) hlt rfl
    (readyB_iff hlt hraw) (missOpsB_iff hlt hraw) (missObjsB_iff hlt hraw)

/-- With the primitive guards, the computed choice is a burst step, a call or the push. -/
theorem rawControl_guarded {raw images : List Nat} {par : Nat → List Nat}
    {anc : Nat → Nat → Bool} {H : Nat} {s : State} {q : Prims} (hlt : ParLt par)
    (hraw : ∀ x, Anc par x H → x ∈ raw) (ha : q.announced = false) (hdh : q.dropHead = false)
    (hd : q.differ = false) (hp : q.pending = true) (hn : q.newIsKnown = false) :
    let c := rawControl raw images par anc H s q
    c = .merge ∨ c = .realize ∨ c = .fetch ∨ c = .objects ∨ c = .advance ∨ c = .push :=
  choose_guarded ha hdh hd hp hn (rawReads_survey hlt hraw)

/-! ### A call's effect, checked -/

/-- What a step was, as the native core reports it. -/
inductive CallKind
  | burst (k : Burst.Kind)
  | fetch
  | objects

def growsB (raw : List Nat) (s t : State) : Bool :=
  Burst.growsB raw s.burst t.burst && raw.all (fun x => !s.stg x || t.stg x) &&
    raw.all (fun x => !s.obj x || t.obj x)

/-- A step's effect, checked against its states before and after: a burst step Burst's; a
`Fetch` that brings a body, or locality, to an operation of the closure that had neither; a
`GetObjects` that brings the objects, or locality, of one that lacked them; neither call
moving the op heads or the plan, and nothing lost. -/
def callB (raw images : List Nat) (anc : Nat → Nat → Bool) (kind : CallKind) (s t : State) :
    Bool :=
  growsB raw s t && match kind with
    | .burst k => Burst.stepB raw images anc k s.burst t.burst
    | .fetch => decide (t.burst.heads = s.burst.heads) && decide (t.burst.plan = s.burst.plan) &&
        raw.any fun x => !s.burst.loc x && !s.stg x && (t.stg x || t.burst.loc x)
    | .objects => decide (t.burst.heads = s.burst.heads) &&
        decide (t.burst.plan = s.burst.plan) &&
        raw.any fun x => !s.burst.loc x && !s.obj x && (t.obj x || t.burst.loc x)

theorem growsB_sound {raw : List Nat} {s t : State} (h : growsB raw s t = true) :
    Grows raw s t := by
  simp only [growsB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨hl, hs⟩, ho⟩ := h
  refine ⟨Burst.growsB_sound hl, fun x hx h => ?_, fun x hx h => ?_⟩
  · simpa [h] using hs x hx
  · simpa [h] using ho x hx

theorem callB_sound {raw images : List Nat} {anc : Nat → Nat → Bool} {kind : CallKind}
    {s t : State} (h : callB raw images anc kind s t = true) : Call raw images anc s t := by
  simp only [callB, Bool.and_eq_true] at h
  obtain ⟨hg, hk⟩ := h
  have hg := growsB_sound hg
  cases kind with
  | burst k => exact .burst (Burst.stepB_sound hk) hg
  | fetch =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hk
    obtain ⟨⟨hh, hp⟩, x, hx, hb⟩ := hk
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at hb
    obtain ⟨⟨hl, hs⟩, ht⟩ := hb
    exact .fetch x hx hl hs ht hh hp hg
  | objects =>
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hk
    obtain ⟨⟨hh, hp⟩, x, hx, hb⟩ := hk
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true] at hb
    obtain ⟨⟨hl, ho⟩, ht⟩ := hb
    exact .objects x hx hl ho ht hh hp hg

/-- Before a first fresh observation, even an eligible node can know an old raw head whose
node-space images differ. Its raw local burst still reaches an RPC or idle, without a
single embedding, current records, or a stable hub. `run` samples its successive scheduled
core steps during one frozen-known round. The finite record-disturbance cut excludes adoption
and prepared record-taking advances; local steps supply their checked raw field effects.
Idle ends the round, whose next start fetches; fairness of that start and of its call is a
separate driver obligation, not an assumed completed round here. -/
theorem raw_round_yields (raw images : List Nat) (par : Nat → List Nat)
    (anc : Nat → Nat → Bool) (H : Nat)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (run : Nat → State) (prims : Nat → Prims)
    (hrecord : ∀ i, rawControl raw images par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw images par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hburst : ∀ i, (rawControl raw images par anc H (run i) (prims i) = .merge ∨
        rawControl raw images par anc H (run i) (prims i) = .realize ∨
        (rawControl raw images par anc H (run i) (prims i) = .advance ∧
          (prims i).dropHead = false)) →
      ∃ k, Burst.stepB raw images anc k (run i).burst (run (i + 1)).burst = true) :
    ∃ i, let c := rawControl raw images par anc H (run i) (prims i)
      c = .fetch ∨ c = .objects ∨ c = .idle ∨ c = .poll ∨ c = .push := by
  apply Classical.byContradiction
  intro hno
  apply Burst.no_infinite_burst raw images anc trans (fun i => (run i).burst)
  intro i
  have hb : rawControl raw images par anc H (run i) (prims i) = .merge ∨
      rawControl raw images par anc H (run i) (prims i) = .realize ∨
      (rawControl raw images par anc H (run i) (prims i) = .advance ∧
        (prims i).dropHead = false) := by
    cases hc : rawControl raw images par anc H (run i) (prims i) with
    | adopt => exact False.elim ((hrecord i).1 hc)
    | merge => exact Or.inl rfl
    | realize => exact Or.inr (Or.inl rfl)
    | advance => exact Or.inr (Or.inr ⟨rfl, (hrecord i).2 hc⟩)
    | fetch | objects | idle | poll | push =>
      exact False.elim (hno ⟨i, by simp [hc]⟩)
  obtain ⟨k, hk⟩ := hburst i hb
  exact Burst.stepB_sound hk

end Musubi.EarlyEntry.Control

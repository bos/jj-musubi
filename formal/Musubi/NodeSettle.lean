/-
A node settles once the hub does (`node_settles`). The hub's head `H`, sequence `S` and records
`R` stay fixed (HubSuffix and the record cut): every reply says so. One node's control follows
`NodeCore::step` branch by branch, each step with the replies to the requests it sends, as
`driver.sync` handles them before the next step. Nothing assumes a round of steps completes,
nor that fix-ups, neutral tips or merges are finitely many: an eleven-part lexicographic rank
falls at every step that neither idles nor sends a push the stable hub would accept, so a round
that starts runs to `Idle`, and an `Idle` at the stable hub is the goal.

Ids are raw hub-space ones, as the core compares them; nothing projects versions to originals.
What the adapter and the replies do is stated as algebraic contracts, scoped to the head the
node knows and the records the hub announces: `FetchedRep`, `HeadRep`, `ObjRep`, `Take`, `Ext`
(with `Adv` and `FreshOn`), and `WriteRes`, which follows RetryControl's `Publication.write`.
The last section lists them, and what each must be tied to. The core is the repaired one:
once the known head is local, it advances when `prepare_records` said the records drop an op
head, as well as when no head descends from the known one, so no invariant of the hub's
dropped operations is needed.
-/
import Musubi.RetryControl

namespace Musubi.NodeSettle

open Musubi

/-! ## Lexicographic ranks -/

/-- Strictly below, first difference first, for lists of one length. -/
def LexLt : List Nat → List Nat → Prop
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLt as bs)
  | _, _ => False

def LexLe (x y : List Nat) : Prop := LexLt x y ∨ x = y

theorem lexLt_irrefl : ∀ x : List Nat, ¬ LexLt x x
  | [] => fun h => False.elim h
  | _ :: as => fun h => by
    rcases h with h | ⟨_, h⟩
    · exact Nat.lt_irrefl _ h
    · exact lexLt_irrefl as h

theorem lt_hd {a b : Nat} {as bs : List Nat} (h : a < b) : LexLt (a :: as) (b :: bs) :=
  Or.inl h

theorem lt_cons {a b : Nat} {as bs : List Nat} (h : a ≤ b) (t : a = b → LexLt as bs) :
    LexLt (a :: as) (b :: bs) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, t h⟩

theorem le_cons {a b : Nat} {as bs : List Nat} (h : a ≤ b) (t : a = b → LexLe as bs) :
    LexLe (a :: as) (b :: bs) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inl (Or.inl h)
  · rcases t h with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · subst h; subst h'; exact Or.inr rfl

theorem LexLt.le {x y : List Nat} (h : LexLt x y) : LexLe x y := Or.inl h

theorem lexLe_head {a b : Nat} {as bs : List Nat} (h : LexLe (a :: as) (b :: bs)) : a ≤ b := by
  rcases h with h | h
  · rcases h with h | ⟨h, -⟩
    · exact Nat.le_of_lt h
    · exact Nat.le_of_eq h
  · injection h with h1; exact Nat.le_of_eq h1

theorem lexLe_tail {a : Nat} {as bs : List Nat} (h : LexLe (a :: as) (a :: bs)) :
    LexLe as bs := by
  rcases h with h | h
  · rcases h with h | ⟨-, h⟩
    · exact absurd h (Nat.lt_irrefl _)
    · exact Or.inl h
  · injection h with _ h2; exact Or.inr h2

/-- A run of ranks of one length that never rises stops changing. -/
theorem lex_stabilizes : ∀ (L : Nat) (f : Nat → List Nat), (∀ i, (f i).length = L) →
    (∀ i, LexLe (f (i + 1)) (f i)) → ∃ k, ∀ i, k ≤ i → f i = f k := by
  intro L
  induction L with
  | zero =>
    intro f hl _
    exact ⟨0, fun i _ => by
      rw [List.eq_nil_of_length_eq_zero (hl i), List.eq_nil_of_length_eq_zero (hl 0)]⟩
  | succ L ih =>
    intro f hl hf
    have hcons : ∀ i, f i = (f i).headD 0 :: (f i).tail := by
      intro i
      have := hl i
      revert this
      cases f i with
      | nil => intro h; simp at h
      | cons a as => intro _; rfl
    have hhd : ∀ i, (f (i + 1)).headD 0 ≤ (f i).headD 0 := by
      intro i
      have := hf i
      rw [hcons (i + 1), hcons i] at this
      exact lexLe_head this
    obtain ⟨k1, hk1⟩ := nat_trace_stabilizes (fun i => (f i).headD 0) hhd
    have hh : ∀ i, k1 ≤ i → (f i).headD 0 = (f k1).headD 0 := fun i hi => hk1 i hi
    have htl : ∀ j, LexLe (f (k1 + j + 1)).tail (f (k1 + j)).tail := by
      intro j
      have := hf (k1 + j)
      rw [hcons (k1 + j + 1), hcons (k1 + j), hh (k1 + j + 1) (by omega),
        hh (k1 + j) (by omega)] at this
      exact lexLe_tail this
    obtain ⟨k2, hk2⟩ := ih (fun j => (f (k1 + j)).tail)
      (fun j => by simp [hl]) htl
    refine ⟨k1 + k2, fun i hi => ?_⟩
    rw [hcons i, hcons (k1 + k2), hh i (by omega), hh (k1 + k2) (by omega)]
    have e : (f (k1 + (i - k1))).tail = (f (k1 + k2)).tail := hk2 (i - k1) (by omega)
    rw [show k1 + (i - k1) = i by omega] at e
    rw [e]

/-! ## Indicators -/

noncomputable def ind (P : Prop) : Nat := @ite _ P (Classical.propDecidable P) 1 0

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by
  unfold ind; split
  · rfl
  · contradiction

theorem ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by
  unfold ind; split
  · contradiction
  · rfl

theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases hp : P
  · rw [ind_pos hp, ind_pos (h hp)]; exact Nat.le_refl _
  · rw [ind_neg hp]; exact Nat.zero_le _

theorem ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by
  rw [propext h]

/-! ## Counting -/

theorem cnt_pt_of_eq {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x)
    (he : cnt B Q = cnt B P) : ∀ x, x < B → P x → Q x := by
  intro x hx hp
  apply Classical.byContradiction
  intro hq
  have := cnt_lt h ⟨x, hx, hp, hq⟩
  omega

/-! ## The node -/

/-- The stable hub: its sequence, head and records, and which node operations the records
of each state drop (`prepare_records`' `taking.dropped`, read through canonical names). -/
structure Ctx where
  S : Nat
  H : Nat
  R : Nat
  drops : Nat → Nat → Prop

/-- What `NodeCore` holds (`known`, `plan`, `hub_records`, `announced`) and what it reads
through `LocalRepo`: the applied records' state, pending drops, op heads, what stands for the
known head (`to_node`), the operation graph, and which operations are local, staged, and have
their objects; and whether the cached fix-up is written (`fixup_written`). `act` is whether a
`sync` round is running. -/
structure NS where
  known : Nat × Nat
  plan : List Nat
  hubRecs : Option Nat
  annc : Option Nat
  ap : Nat
  pending : List Nat
  written : Bool
  heads : List Nat
  img : List Nat
  par : Nat → List Nat
  next : Nat
  loc : Nat → Prop
  stg : Nat → Prop
  obj : Nat → Prop
  act : Bool

/-- The first test of `step`: announced records equal to the applied ones are dropped. -/
def normA : Option Nat → Nat → Option Nat
  | some A, ap => if A = ap then none else some A
  | none, _ => none

def norm (σ : NS) : NS := { σ with annc := normA σ.annc σ.ap }

/-- A fresh operation on top of `L`, the only op head after: a merge, or a fix-up or neutral
tip on the single head. -/
def fresh (σ : NS) (L : List Nat) : NS :=
  { σ with par := upd σ.par σ.next L, next := σ.next + 1,
           loc := fun y => σ.loc y ∨ y = σ.next, heads := [σ.next] }

def realize (σ : NS) (x : Nat) (rest : List Nat) : NS :=
  { σ with loc := fun y => σ.loc y ∨ y = x, plan := rest }

/-- The op heads merged into an operation the node already has, labelled `m` (the same canonical
content, written by another copy or before), now local here and the only op head after. No new
operation is written. -/
def mergeTo (σ : NS) (m : Nat) : NS :=
  { σ with heads := [m], loc := fun y => σ.loc y ∨ y = m }

/-- Every op head but `x` is an ancestor of `x`, and leaves: jj's merge of the op heads drops
those below another (as an interrupted publish can leave them) and, with one left, writes
nothing. -/
def pruneTo (σ : NS) (x : Nat) : NS := { σ with heads := [x] }

/-- The op heads that jj's merge of them (`load_at_head`) keeps, `M`, as far as the model asks:
some of the op heads, every op head an ancestor of one of them. jj keeps those below no other,
which are such. -/
structure Keeps (σ : NS) (M : List Nat) : Prop where
  sub : ∀ y ∈ M, y ∈ σ.heads
  cover : ∀ y ∈ σ.heads, ∃ z ∈ M, Anc σ.par y z

theorem Keeps.norm {σ : NS} {M : List Nat} (h : Keeps σ M) : Keeps (norm σ) M :=
  ⟨h.sub, h.cover⟩

/-- `is_ancestor(known, y)`: every operation standing for the known head is below `y`. -/
def Desc (σ : NS) (y : Nat) : Prop := ∀ i ∈ σ.img, Anc σ.par i y

/-- `prepare_records` says the records drop an op head. -/
def Blocked (c : Ctx) (σ : NS) (A : Nat) : Prop := ∃ y ∈ σ.heads, c.drops A y

/-- `step` got past its first test without adopting. -/
def Go (c : Ctx) (σ : NS) : Prop := ∀ A, σ.annc = some A → A ≠ σ.ap → Blocked c σ A

/-- `differ` in `step`. -/
def Differ (σ : NS) : Prop :=
  match σ.hubRecs with
  | some X => X ≠ σ.ap
  | none => σ.pending ≠ []

/-- What `survey` walks: down from the known head through staged operations that are not
local. -/
inductive Walk (σ : NS) : Nat → Prop
  | top : Walk σ σ.known.2
  | up {x p : Nat} : Walk σ x → ¬ σ.loc x → σ.stg x → p ∈ σ.par x → Walk σ p

/-- The front of `survey`'s plan: staged, objects here, parents local. -/
def Ready (σ : NS) (x : Nat) : Prop :=
  Walk σ x ∧ ¬ σ.loc x ∧ σ.stg x ∧ σ.obj x ∧ ∀ p ∈ σ.par x, σ.loc p

def MissOps (σ : NS) : Prop := ∃ x, Walk σ x ∧ ¬ σ.loc x ∧ ¬ σ.stg x

def MissObjs (σ : NS) : Prop := ∃ x, Walk σ x ∧ ¬ σ.loc x ∧ σ.stg x ∧ ¬ σ.obj x

theorem Walk.anc {σ : NS} {x : Nat} (h : Walk σ x) : Anc σ.par x σ.known.2 := by
  induction h with
  | top => exact Anc.refl
  | up _ _ _ hp ih => exact (Anc.parent hp).trans ih

/-- Survey completeness: a known head that is not local has a ready operation, or lacks an
operation or some objects, which a request fetches. -/
theorem survey_complete {σ : NS} (hlt : ParLt σ.par) (hl : ¬ σ.loc σ.known.2) :
    (∃ x, Ready σ x) ∨ MissOps σ ∨ MissObjs σ := by
  apply Classical.byContradiction
  intro hn
  have hr : ¬ ∃ x, Ready σ x := fun h => hn (Or.inl h)
  have ho : ¬ MissOps σ := fun h => hn (Or.inr (Or.inl h))
  have hb : ¬ MissObjs σ := fun h => hn (Or.inr (Or.inr h))
  have key : ∀ n x, x < n → Walk σ x → σ.loc x := by
    intro n
    induction n with
    | zero => intro x hx; omega
    | succ n ih =>
      intro x hx hw
      apply Classical.byContradiction
      intro hlx
      have hs : σ.stg x := Classical.byContradiction fun h => ho ⟨x, hw, hlx, h⟩
      have hob : σ.obj x := Classical.byContradiction fun h => hb ⟨x, hw, hlx, hs, h⟩
      exact hr ⟨x, hw, hlx, hs, hob, fun p hp =>
        ih p (by have := hlt x p hp; omega) (Walk.up hw hlx hs hp)⟩
  exact hl (key _ _ (Nat.lt_succ_self _) Walk.top)

/-! ## What holds of every state -/

structure SInv (c : Ctx) (σ : NS) : Prop where
  parLt : ParLt σ.par
  knownLt : σ.known.2 < σ.next
  hLt : c.H < σ.next
  headsNe : σ.heads ≠ []
  headsLt : ∀ y ∈ σ.heads, y < σ.next
  imgNe : σ.img ≠ []
  imgLt : ∀ i ∈ σ.img, i < σ.next
  /-- Learning the hub's head is always followed by noting its records. -/
  recs : σ.known = (c.S, c.H) → σ.hubRecs = some c.R

/-! ## Contracts: replies and adapter calls -/

/-- A `Fetched` reply from the stable hub to a `Fetch`: the node knows `(S, H)` after,
learning it if it didn't, and has noted the records (`note_announced`, the announcement
contract: the announced records are `R`, or none when they are the applied ones). It has staged
every operation below `H` that is neither local nor staged (the transfer contract for this
`H`), and changed nothing else. -/
structure FetchedRep (c : Ctx) (σ σ' : NS) : Prop where
  known : σ'.known = (c.S, c.H)
  hubRecs : σ'.hubRecs = some c.R
  annc : σ'.annc = some c.R ∨ (σ'.annc = none ∧ c.R = σ.ap)
  same : σ.known = (c.S, c.H) → σ'.plan = σ.plan ∧ σ'.img = σ.img
  imgNe : σ'.img ≠ []
  imgLt : ∀ i ∈ σ'.img, i < σ.next
  stg : ∀ x, σ.stg x → σ'.stg x
  obj : ∀ x, σ.obj x → σ'.obj x
  stages : ∀ x, Anc σ.par x c.H → ¬ σ.loc x → σ'.stg x
  ap : σ'.ap = σ.ap
  pending : σ'.pending = σ.pending
  written : σ'.written = σ.written
  heads : σ'.heads = σ.heads
  par : σ'.par = σ.par
  next : σ'.next = σ.next
  loc : σ'.loc = σ.loc
  act : σ'.act = σ.act

/-- A `Head` reply, a notification or a push's rejection: the node knows `(S, H)` and has
noted the records, and nothing else changed. -/
structure HeadRep (c : Ctx) (σ σ' : NS) : Prop where
  known : σ'.known = (c.S, c.H)
  hubRecs : σ'.hubRecs = some c.R
  annc : σ'.annc = σ.annc
  same : σ.known = (c.S, c.H) → σ'.plan = σ.plan ∧ σ'.img = σ.img
  imgNe : σ'.img ≠ []
  imgLt : ∀ i ∈ σ'.img, i < σ.next
  stg : σ'.stg = σ.stg
  obj : σ'.obj = σ.obj
  ap : σ'.ap = σ.ap
  pending : σ'.pending = σ.pending
  written : σ'.written = σ.written
  heads : σ'.heads = σ.heads
  par : σ'.par = σ.par
  next : σ'.next = σ.next
  loc : σ'.loc = σ.loc
  act : σ'.act = σ.act

/-- An `Objects` reply: the objects asked for are here. -/
structure ObjRep (σ σ' : NS) (M : Nat → Prop) : Prop where
  obj : ∀ x, σ.obj x ∨ M x → σ'.obj x
  rest : σ' = { σ with obj := σ'.obj }

/-- Taking records `A`, by `adopt` or by advancing while they are prepared: they are applied
after, and the node may have renamed anything else, but the core keeps its plan. -/
structure Take (c : Ctx) (σ σ' : NS) (A : Nat) : Prop where
  ap : σ'.ap = A
  plan : σ'.plan = σ.plan
  known : σ'.known = σ.known
  hubRecs : σ'.hubRecs = σ.hubRecs
  annc : σ'.annc = none ∨ σ'.annc = σ.annc
  act : σ'.act = σ.act
  inv : SInv c σ'

/-- Local operations written on top of what was there: what `advance_to` publishes (the
realization, or its merge with concurrent heads), or a fix-up's chain. They are new labels, or
operations the node holds already (identical canonical content, written before or by another
copy, held as structure or detached), which the write makes local: locality only grows. Nothing
else moves. -/
structure Ext (σ σ' : NS) : Prop where
  parLt : ParLt σ'.par
  grows : σ.next ≤ σ'.next
  parOld : ∀ y, y < σ.next → σ'.par y = σ.par y
  locOld : ∀ y, y < σ.next → σ.loc y → σ'.loc y
  headsNe : σ'.heads ≠ []
  headsLt : ∀ y ∈ σ'.heads, y < σ'.next
  known : σ'.known = σ.known
  annc : σ'.annc = σ.annc
  ap : σ'.ap = σ.ap
  hubRecs : σ'.hubRecs = σ.hubRecs
  img : σ'.img = σ.img
  stg : σ'.stg = σ.stg
  obj : σ'.obj = σ.obj
  pending : σ'.pending = σ.pending
  act : σ'.act = σ.act

/-- `advance(known)`: the op heads move to cover what stands for the known head. -/
structure Adv (σ σ' : NS) : Prop where
  ext : Ext σ σ'
  plan : σ'.plan = []
  written : σ'.written = σ.written
  covers : ∀ i ∈ σ.img, ∃ y ∈ σ'.heads, Anc σ'.par i y

/-- The node's fix-up cache as RetryControl's `Publication`: its pending drops, whether its
restoring fix-up is written, and whether its single op head is the known head, as the core
compares them (`publish_from`). -/
def pubOf (σ : NS) : Retry.Publication :=
  ⟨⟨σ.pending, σ.written, true⟩, decide (σ.heads = [σ.known.2])⟩

/-- A write that publishes: a chain on the single head `y`, whose last operation `new` is the
only op head after, with the cache as `Publication.write` leaves it. The chain is new, or the
node holds it already: identical canonical content (no nonce), written before or by another
copy, so it takes no new label, its parents labelled too, and the write makes it local (`Ext`'s
locality only grows). Either way `new` is above `y`, the chain having at least one operation. -/
structure FreshOn (σ σ1 : NS) (y new : Nat) : Prop where
  ext : Ext σ σ1
  heads : σ1.heads = [new]
  fresh : σ.next ≤ new ∨ (new < σ.next ∧ σ1.next = σ.next)
  proper : new ≠ y
  covers : Anc σ1.par y new
  plan : σ1.plan = σ.plan
  written : σ1.written = (pubOf σ).write.1.cache.written

/-- `write_fixup(publish_from)` from the single head `y`, as `Publication.write` says: the
restoring fix-up if it isn't written yet, else a neutral tip if the head is the known head,
else nothing (`write_drop_tip` writes when the head is the known one, the same exact id, there
being no concurrent command). The new head is what it writes, or else the head. With no pending
drops it writes nothing, as a plain push. -/
def WriteRes (σ σ1 : NS) (new : Nat) : Prop :=
  ∃ y, σ.heads = [y] ∧
    ((((pubOf σ).write.2.1 || (pubOf σ).write.2.2) = true ∧ FreshOn σ σ1 y new) ∨
      (((pubOf σ).write.2.1 || (pubOf σ).write.2.2) = false ∧ σ1 = σ ∧ new = y))

/-- A write that leaves the known head as the new one reuses it, restoring: nothing written is
excluded, `Publication.write` writing whenever there are pending drops and the head is the known
head; a new chain has new labels above the known head's; and a neutral tip is written only on
the known head, above which its new head is. So the cache was not written, and the write sets
it. -/
theorem write_known {σ σ1 : NS} {new : Nat} (hk : σ.known.2 < σ.next) (hp : σ.pending ≠ [])
    (W : WriteRes σ σ1 new) (he : new = σ.known.2) :
    σ.written = false ∧ σ1.written = true ∧ σ1.pending = σ.pending := by
  obtain ⟨y, hy, (⟨hwr, F⟩ | ⟨hno, -, rfl⟩)⟩ := W
  · rcases F.fresh with hf | ⟨-, -⟩
    · omega
    have hpendNotEmpty : σ.pending.isEmpty = false := by
      cases h : σ.pending with
      | nil => exact absurd h hp
      | cons _ _ => rfl
    have hw1 := F.written
    have hpend : σ1.pending = σ.pending := F.ext.pending
    cases hwr' : σ.written with
    | false =>
      refine ⟨rfl, ?_, hpend⟩
      rw [hw1]
      simp [pubOf, Retry.Publication.write, Retry.Fixup.write, hpendNotEmpty, hwr']
    | true =>
      exfalso
      have hhk : (pubOf σ).headKnown = true := by
        revert hwr
        simp [pubOf, Retry.Publication.write, Retry.Fixup.write, hpendNotEmpty, hwr']
      have hyk : y = σ.known.2 := by
        have h' : σ.heads = [σ.known.2] := by simpa [pubOf] using hhk
        rw [hy] at h'
        exact List.cons.inj h' |>.1
      exact F.proper (he.trans hyk.symm)
  · exfalso
    have hprog := Retry.publication_progress (pubOf σ) hp (by simp [pubOf, hy, he])
    revert hno hprog
    cases (pubOf σ).write.2.1 <;> cases (pubOf σ).write.2.2 <;> simp

/-! ## The core's steps, in `NodeCore::step`'s order -/

/-- A step that neither idles nor sends a push the stable hub would accept, with the replies to
what it sends. -/
inductive Busy (c : Ctx) : NS → NS → Prop
  | adopt {σ σ' : NS} (A : Nat) (ha : σ.annc = some A) (hne : A ≠ σ.ap)
      (hb : ¬ Blocked c σ A) (ht : Take c σ σ' A) : Busy c σ σ'
  /-- jj merges the op heads it keeps, `M`, writing an operation on them that the node has no
  label for. -/
  | merge {σ σ' : NS} (M : List Nat) (hg : Go c σ) (h2 : 2 ≤ σ.heads.length)
      (hM : Keeps σ M) (he : σ' = fresh (norm σ) M) : Busy c σ σ'
  /-- The merge of `M` is an operation the node already holds a label for, `m`: the same
  canonical content, written by another copy or before. -/
  | mergeExisting {σ σ' : NS} (M : List Nat) (m : Nat) (hg : Go c σ)
      (h2 : 2 ≤ σ.heads.length) (hM : Keeps σ M) (hm : m < σ.next)
      (hpar : ∀ y, y ∈ σ.par m ↔ y ∈ M) (he : σ' = mergeTo (norm σ) m) : Busy c σ σ'
  /-- jj keeps one op head, `x`, the others its ancestors: nothing is written. -/
  | prune {σ σ' : NS} (x : Nat) (hg : Go c σ) (h2 : 2 ≤ σ.heads.length) (hM : Keeps σ [x])
      (he : σ' = pruneTo (norm σ) x) : Busy c σ σ'
  | realizePlan {σ σ' : NS} (x : Nat) (rest : List Nat) (hg : Go c σ)
      (h1 : σ.heads.length < 2) (hl : ¬ σ.loc σ.known.2) (hp : σ.plan = x :: rest)
      (he : σ' = realize (norm σ) x rest) : Busy c σ σ'
  | realizeSurvey {σ σ' : NS} (x : Nat) (L : List Nat) (hg : Go c σ)
      (h1 : σ.heads.length < 2) (hl : ¬ σ.loc σ.known.2) (hp : σ.plan = [])
      (hr : Ready σ x) (he : σ' = realize (norm σ) x L) : Busy c σ σ'
  | fetch {σ σ' : NS} (σ1 : NS) (hg : Go c σ) (h1 : σ.heads.length < 2)
      (hl : ¬ σ.loc σ.known.2) (hp : σ.plan = []) (hr : ¬ ∃ x, Ready σ x)
      (hm : MissOps σ ∨ MissObjs σ)
      (hf : (MissOps σ ∧ FetchedRep c (norm σ) σ1) ∨ (¬ MissOps σ ∧ σ1 = norm σ))
      (ho : (MissObjs σ ∧
          ObjRep σ1 σ' (fun x => Walk σ x ∧ ¬ σ.loc x ∧ σ.stg x ∧ ¬ σ.obj x)) ∨
        (¬ MissObjs σ ∧ σ' = σ1)) : Busy c σ σ'
  /-- Records announced and prepared that drop an op head (`records_drop_head`), the known
  head local: advancing takes them, whether or not a head descends from the known one. -/
  | advanceTake {σ σ' : NS} (A : Nat) (hg : Go c σ) (h1 : σ.heads.length < 2)
      (hl : σ.loc σ.known.2) (ha : (norm σ).annc = some A)
      (ht : Take c { norm σ with plan := [] } σ' A) : Busy c σ σ'
  | advance {σ σ' : NS} (hg : Go c σ) (h1 : σ.heads.length < 2) (hl : σ.loc σ.known.2)
      (hd : ¬ ∃ y ∈ σ.heads, Desc σ y) (ha : (norm σ).annc = none) (hv : Adv (norm σ) σ') :
      Busy c σ σ'
  | differPoll {σ σ' : NS} (hg : Go c σ) (h1 : σ.heads.length < 2) (hl : σ.loc σ.known.2)
      (hd : ∃ y ∈ σ.heads, Desc σ y) (hf : Differ σ) (ha : (norm σ).annc = none)
      (hr : FetchedRep c { norm σ with plan := [] } σ') : Busy c σ σ'
  /-- A push before the node knows the hub's head: the stable hub refuses it, its records
  not being the hub's, or rejects it with its head, which the node learns. -/
  | pushStale {σ σ' : NS} (σ1 : NS) (new : Nat) (hg : Go c σ) (h1 : σ.heads.length < 2)
      (hl : σ.loc σ.known.2) (hd : ∃ y ∈ σ.heads, Desc σ y) (hnr : (norm σ).annc = none)
      (hf : ¬ Differ σ) (hw : σ.pending ≠ [] ∨ σ.heads ≠ [σ.known.2])
      (hk : σ.known ≠ (c.S, c.H)) (hw' : WriteRes { norm σ with plan := [] } σ1 new)
      (hnew : new ≠ σ.known.2)
      (hr : (σ.ap ≠ c.R ∧ σ' = { σ1 with hubRecs := some c.R }) ∨
        (σ.ap = c.R ∧ HeadRep c σ1 σ')) : Busy c σ σ'
  /-- The branch that polls when the write leaves the known head as the new one: the write then
  reuses the known head, the restoring fix-up identical to it, and writes the cache
  (`write_known`), which the rank counts (`cw`). -/
  | writePoll {σ σ' : NS} (σ1 : NS) (new : Nat) (hg : Go c σ) (h1 : σ.heads.length < 2)
      (hl : σ.loc σ.known.2) (hd : ∃ y ∈ σ.heads, Desc σ y) (hnr : (norm σ).annc = none)
      (hf : ¬ Differ σ) (hw : σ.pending ≠ [])
      (hw' : WriteRes { norm σ with plan := [] } σ1 new) (hnew : new = σ.known.2)
      (hr : FetchedRep c σ1 σ') : Busy c σ σ'

/-- A step that returns `Idle`, ending the round. -/
inductive Idle (c : Ctx) : NS → NS → Prop
  | fetchIdle {σ σ' : NS} (hg : Go c σ) (h1 : σ.heads.length < 2) (hl : ¬ σ.loc σ.known.2)
      (hp : σ.plan = []) (hr : ¬ ∃ x, Ready σ x) (ho : ¬ MissOps σ) (hb : ¬ MissObjs σ)
      (he : σ' = { norm σ with act := false }) : Idle c σ σ'
  | differIdle {σ σ' : NS} (hg : Go c σ) (h1 : σ.heads.length < 2) (hl : σ.loc σ.known.2)
      (hd : ∃ y ∈ σ.heads, Desc σ y) (hf : Differ σ) (hnr : (norm σ).annc = none)
      (ha : (norm σ).annc ≠ none)
      (he : σ' = { norm σ with plan := [], act := false }) : Idle c σ σ'
  | goal {σ σ' : NS} (hg : Go c σ) (h1 : σ.heads.length < 2) (hl : σ.loc σ.known.2)
      (hd : ∃ y ∈ σ.heads, Desc σ y) (hnr : (norm σ).annc = none) (hf : ¬ Differ σ)
      (hp : σ.pending = [])
      (hh : σ.heads = [σ.known.2]) (he : σ' = { norm σ with plan := [], act := false }) :
      Idle c σ σ'

/-- A step that sends a push once the node knows the hub's head: from it, with the hub's records,
its pending drops, and the new head `write_fixup` leaves (`WriteRes`), which is not `H`
(`emit_packet`). The stable hub would accept such a push. -/
def Emit (c : Ctx) (σ σ1 : NS) (new : Nat) : Prop :=
  σ.act = true ∧ Go c σ ∧ σ.heads.length < 2 ∧ σ.loc σ.known.2 ∧
    (∃ y ∈ σ.heads, Desc σ y) ∧ (norm σ).annc = none ∧ ¬ Differ σ ∧
    (σ.pending ≠ [] ∨ σ.heads ≠ [σ.known.2]) ∧ σ.known = (c.S, c.H) ∧
    WriteRes { norm σ with plan := [] } σ1 new ∧ new ≠ σ.known.2

inductive Lab
  | busy
  | idle
  | maint
  | emit
  | start
  | notify
  | frame

/-- What can happen to the node: a step in a round; the start of a round, a `Fetch` and its
reply; a notification; or something elsewhere. -/
inductive Ev (c : Ctx) : Lab → NS → NS → Prop
  | busy {σ σ' : NS} (ha : σ.act = true) (h : Busy c σ σ') : Ev c .busy σ σ'
  | idle {σ σ' : NS} (ha : σ.act = true) (h : Idle c σ σ') : Ev c .idle σ σ'
  /-- The core idled, but the daemon's housekeeping (`when_idle`) wrote something, so the
  round goes on: fresh operations on top, nothing else changed. -/
  | maint {σ σ' σ1 : NS} (ha : σ.act = true) (h : Idle c σ σ1)
      (hw : Ext { σ1 with act := true } σ') : Ev c .maint σ σ'
  | emit {σ σ' : NS} (σ1 : NS) (new : Nat) (h : Emit c σ σ1 new) : Ev c .emit σ σ'
  | start {σ σ' σ1 : NS} (ha : σ.act = false) (h : FetchedRep c σ σ1)
      (he : σ' = { σ1 with act := true }) : Ev c .start σ σ'
  | notify {σ σ' : NS} (h : HeadRep c σ σ') : Ev c .notify σ σ'
  | frame {σ : NS} : Ev c .frame σ σ

/-- The goal: the node knows the hub's head, has its records and no other drops, and its only op
head is the hub's head. -/
def Settled (c : Ctx) (σ : NS) : Prop :=
  σ.known = (c.S, c.H) ∧ σ.ap = c.R ∧ σ.hubRecs = some c.R ∧ σ.pending = [] ∧
    σ.heads = [c.H] ∧ σ.loc c.H ∧ Desc σ c.H ∧ (σ.annc = none ∨ σ.annc = some c.R)

/-! ## The rank -/

/-- The node doesn't know the hub's head yet. -/
noncomputable def ck (c : Ctx) (σ : NS) : Nat := ind (σ.known ≠ (c.S, c.H))

/-- An announcement of older records, still to take. -/
noncomputable def cz (c : Ctx) (σ : NS) : Nat := ind (∃ A, σ.annc = some A ∧ A ≠ c.R ∧ A ≠ σ.ap)

/-- The hub's records are not applied. -/
noncomputable def cr (c : Ctx) (σ : NS) : Nat := ind (σ.ap ≠ c.R)

/-- Operations below the known head not yet local. -/
noncomputable def cm (σ : NS) : Nat :=
  cnt (σ.known.2 + 1) (fun x => Anc σ.par x σ.known.2 ∧ ¬ σ.loc x)

/-- ... of which not staged. -/
noncomputable def cs1 (σ : NS) : Nat :=
  cnt (σ.known.2 + 1) (fun x => Anc σ.par x σ.known.2 ∧ ¬ σ.loc x ∧ ¬ σ.stg x)

/-- ... of which staged without their objects. -/
noncomputable def cs2 (σ : NS) : Nat :=
  cnt (σ.known.2 + 1) (fun x => Anc σ.par x σ.known.2 ∧ ¬ σ.loc x ∧ σ.stg x ∧ ¬ σ.obj x)

/-- Some operation standing for the known head is below no op head. -/
noncomputable def ca (σ : NS) : Nat := ind (¬ ∀ i ∈ σ.img, ∃ y ∈ σ.heads, Anc σ.par i y)

/-- Op heads beyond one. -/
def ch (σ : NS) : Nat := σ.heads.length - 1

/-- The hub's records are not noted, or not applied nor announced. -/
noncomputable def cd (c : Ctx) (σ : NS) : Nat :=
  ind (σ.hubRecs ≠ some c.R) + ind (σ.ap ≠ c.R ∧ σ.annc ≠ some c.R)

/-- Pending drops whose restoring fix-up is not written (`Fixup.credit`). Natively,
`repair_received_work` can clear the cache before a write; the model takes no such step (the
obligation under `WriteRes` in the last section). -/
noncomputable def cw (σ : NS) : Nat := ind (σ.written = false ∧ σ.pending ≠ [])

noncomputable def rank (c : Ctx) (σ : NS) : List Nat :=
  [ck c σ, cz c σ, cr c σ, cm σ, σ.plan.length, cs1 σ, cs2 σ, ca σ, ch σ, cd c σ, cw σ]

theorem rank_length (c : Ctx) (σ : NS) : (rank c σ).length = 11 := rfl

theorem cw_congr {σ σ' : NS} (hw : σ'.written = σ.written) (hp : σ'.pending = σ.pending) :
    cw σ' = cw σ := by
  unfold cw; rw [hw, hp]

theorem lt_cons_eq {a b : Nat} {as bs : List Nat} (h : a = b) (t : LexLt as bs) :
    LexLt (a :: as) (b :: bs) := Or.inr ⟨h, t⟩

theorem le_cons_eq {a b : Nat} {as bs : List Nat} (h : a = b) (t : LexLe as bs) :
    LexLe (a :: as) (b :: bs) := le_cons (Nat.le_of_eq h) fun _ => t

theorem normA_ne {A ap : Nat} (h : A ≠ ap) : normA (some A) ap = some A := by
  simp [normA, h]

theorem normA_some {o : Option Nat} {ap A : Nat} (h : normA o ap = some A) :
    o = some A ∧ A ≠ ap := by
  cases o with
  | none => simp [normA] at h
  | some B =>
    by_cases hb : B = ap
    · simp [normA, hb] at h
    · rw [normA_ne hb] at h
      cases h; exact ⟨rfl, hb⟩

theorem normA_none {o : Option Nat} {ap : Nat} (h : normA o ap = none) :
    o = none ∨ o = some ap := by
  cases o with
  | none => exact Or.inl rfl
  | some B =>
    by_cases hb : B = ap
    · subst hb; exact Or.inr rfl
    · rw [normA_ne hb] at h; cases h

theorem cz_norm (c : Ctx) (σ : NS) : cz c (norm σ) = cz c σ := by
  show ind (∃ A, normA σ.annc σ.ap = some A ∧ A ≠ c.R ∧ A ≠ σ.ap) =
    ind (∃ A, σ.annc = some A ∧ A ≠ c.R ∧ A ≠ σ.ap)
  apply ind_congr
  constructor
  · rintro ⟨A, hA, h1, h2⟩
    exact ⟨A, (normA_some hA).1, h1, h2⟩
  · rintro ⟨A, hA, h1, h2⟩
    exact ⟨A, by rw [hA]; exact normA_ne h2, h1, h2⟩

theorem cd_norm (c : Ctx) (σ : NS) : cd c (norm σ) = cd c σ := by
  show ind (σ.hubRecs ≠ some c.R) + ind (σ.ap ≠ c.R ∧ normA σ.annc σ.ap ≠ some c.R) =
    ind (σ.hubRecs ≠ some c.R) + ind (σ.ap ≠ c.R ∧ σ.annc ≠ some c.R)
  congr 1
  apply ind_congr
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => h2 ?_⟩
    rw [h]; exact normA_ne fun e => h1 e.symm
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h => h2 (normA_some h).1⟩

theorem rank_norm (c : Ctx) (σ : NS) : rank c (norm σ) = rank c σ := by
  unfold rank; rw [cz_norm, cd_norm]; rfl

theorem single_of {l : List Nat} (h1 : l.length < 2) (hne : l ≠ []) : ∃ y, l = [y] := by
  match l, h1, hne with
  | [y], _, _ => exact ⟨y, rfl⟩
  | [], _, hne => exact absurd rfl hne
  | _ :: _ :: _, h1, _ => exact absurd h1 (by simp only [List.length_cons]; omega)

theorem ch_zero {σ : NS} (h1 : σ.heads.length < 2) (hne : σ.heads ≠ []) : ch σ = 0 := by
  obtain ⟨y, hy⟩ := single_of h1 hne
  unfold ch; rw [hy]; rfl

/-- Ancestry below `n` is unchanged by operations added at or above it. -/
theorem anc_agree {par par' : Nat → List Nat} {n : Nat} (hlt : ParLt par) (hlt' : ParLt par')
    (h : ∀ y, y < n → par' y = par y) {a x : Nat} (hx : x < n) :
    Anc par' a x ↔ Anc par a x := by
  constructor
  · intro ha
    induction ha with
    | refl => exact Anc.refl
    | @step p y hp _ ih =>
      exact Anc.step (by rw [← h y hx]; exact hp) (ih (Nat.lt_trans (hlt' y p hp) hx))
  · intro ha
    induction ha with
    | refl => exact Anc.refl
    | @step p y hp _ ih =>
      exact Anc.step (by rw [h y hx]; exact hp) (ih (Nat.lt_trans (hlt y p hp) hx))

/-! ## The invariant is kept -/

section Inv

variable {c : Ctx}

theorem SInv.norm {σ : NS} (I : SInv c σ) : SInv c (norm σ) :=
  ⟨I.parLt, I.knownLt, I.hLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt, I.recs⟩

theorem SInv.plan {σ : NS} (I : SInv c σ) (L : List Nat) : SInv c { σ with plan := L } :=
  ⟨I.parLt, I.knownLt, I.hLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt, I.recs⟩

theorem SInv.act {σ : NS} (I : SInv c σ) (b : Bool) : SInv c { σ with act := b } :=
  ⟨I.parLt, I.knownLt, I.hLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt, I.recs⟩

theorem SInv.fresh {σ : NS} (I : SInv c σ) {M : List Nat} (hM : ∀ y ∈ M, y ∈ σ.heads) :
    SInv c (fresh σ M) where
  parLt := parLt_upd I.parLt fun y hy => I.headsLt y (hM y hy)
  knownLt := Nat.lt_succ_of_lt I.knownLt
  hLt := Nat.lt_succ_of_lt I.hLt
  headsNe := List.cons_ne_nil _ _
  headsLt := by
    intro y hy
    have hy' : y = σ.next := List.mem_singleton.1 hy
    subst hy'; exact Nat.lt_succ_self _
  imgNe := I.imgNe
  imgLt := fun i hi => Nat.lt_succ_of_lt (I.imgLt i hi)
  recs := I.recs

theorem SInv.realize {σ : NS} (I : SInv c σ) (x : Nat) (L : List Nat) :
    SInv c (realize σ x L) :=
  ⟨I.parLt, I.knownLt, I.hLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt, I.recs⟩

theorem SInv.mergeTo {σ : NS} {m : Nat} (I : SInv c σ) (hm : m < σ.next) :
    SInv c (mergeTo σ m) :=
  ⟨I.parLt, I.knownLt, I.hLt, List.cons_ne_nil m [],
    fun y hy => by rw [List.mem_singleton.1 hy]; exact hm,
    I.imgNe, I.imgLt, I.recs⟩

theorem SInv.pruneTo {σ : NS} {x : Nat} (I : SInv c σ) (hx : x ∈ σ.heads) :
    SInv c (pruneTo σ x) :=
  ⟨I.parLt, I.knownLt, I.hLt, List.cons_ne_nil x [],
    fun y hy => by rw [List.mem_singleton.1 hy]; exact I.headsLt x hx, I.imgNe, I.imgLt, I.recs⟩

theorem SInv.fetched {σ σ' : NS} (I : SInv c σ) (F : FetchedRep c σ σ') : SInv c σ' where
  parLt := by rw [F.par]; exact I.parLt
  knownLt := by rw [F.known, F.next]; exact I.hLt
  hLt := by rw [F.next]; exact I.hLt
  headsNe := by rw [F.heads]; exact I.headsNe
  headsLt := by rw [F.heads, F.next]; exact I.headsLt
  imgNe := F.imgNe
  imgLt := by rw [F.next]; exact F.imgLt
  recs := fun _ => F.hubRecs

theorem SInv.head {σ σ' : NS} (I : SInv c σ) (F : HeadRep c σ σ') : SInv c σ' where
  parLt := by rw [F.par]; exact I.parLt
  knownLt := by rw [F.known, F.next]; exact I.hLt
  hLt := by rw [F.next]; exact I.hLt
  headsNe := by rw [F.heads]; exact I.headsNe
  headsLt := by rw [F.heads, F.next]; exact I.headsLt
  imgNe := F.imgNe
  imgLt := by rw [F.next]; exact F.imgLt
  recs := fun _ => F.hubRecs

theorem SInv.obj {σ σ' : NS} {M : Nat → Prop} (I : SInv c σ) (O : ObjRep σ σ' M) :
    SInv c σ' := by
  rw [O.rest]
  exact ⟨I.parLt, I.knownLt, I.hLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt, I.recs⟩

theorem Ext.fields {σ σ' : NS} (E : Ext σ σ') :
    σ'.known = σ.known ∧ σ'.annc = σ.annc ∧ σ'.ap = σ.ap ∧ σ'.hubRecs = σ.hubRecs ∧
      σ'.img = σ.img ∧ σ'.stg = σ.stg ∧ σ'.obj = σ.obj ∧ σ'.pending = σ.pending ∧
      σ'.act = σ.act :=
  ⟨E.known, E.annc, E.ap, E.hubRecs, E.img, E.stg, E.obj, E.pending, E.act⟩

theorem SInv.ext {σ σ' : NS} (I : SInv c σ) (E : Ext σ σ') : SInv c σ' := by
  obtain ⟨fk, -, -, fh, fi, -, -, -, -⟩ := E.fields
  refine ⟨E.parLt, ?_, Nat.lt_of_lt_of_le I.hLt E.grows, E.headsNe, E.headsLt, ?_, ?_, ?_⟩
  · rw [fk]; exact Nat.lt_of_lt_of_le I.knownLt E.grows
  · rw [fi]; exact I.imgNe
  · rw [fi]; exact fun i hi => Nat.lt_of_lt_of_le (I.imgLt i hi) E.grows
  · rw [fk, fh]; exact I.recs

theorem SInv.adv {σ σ' : NS} (I : SInv c σ) (A : Adv σ σ') : SInv c σ' := I.ext A.ext

theorem SInv.writeRes {σ σ1 : NS} {new : Nat} (I : SInv c σ) (W : WriteRes σ σ1 new) :
    SInv c σ1 := by
  obtain ⟨y, -, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
  · exact I.ext F.ext
  · subst he; exact I

theorem SInv.refused {σ : NS} (I : SInv c σ) : SInv c { σ with hubRecs := some c.R } :=
  ⟨I.parLt, I.knownLt, I.hLt, I.headsNe, I.headsLt, I.imgNe, I.imgLt, fun _ => rfl⟩

theorem inv_busy {σ σ' : NS} (I : SInv c σ) (h : Busy c σ σ') : SInv c σ' := by
  cases h with
  | adopt _ _ _ _ ht => exact ht.inv
  | merge _ _ _ hM he => subst he; exact I.norm.fresh hM.sub
  | mergeExisting _ _ _ _ _ hm _ he => subst he; exact I.norm.mergeTo hm
  | prune x _ _ hM he => subst he; exact I.norm.pruneTo (hM.sub x (List.mem_singleton.2 rfl))
  | realizePlan x rest _ _ _ _ he => subst he; exact I.norm.realize x rest
  | realizeSurvey x L _ _ _ _ _ he => subst he; exact I.norm.realize x L
  | fetch σ1 _ _ _ _ _ _ hf ho =>
    have I1 : SInv c σ1 := by
      rcases hf with ⟨-, F⟩ | ⟨-, he⟩
      · exact I.norm.fetched F
      · rw [he]; exact I.norm
    rcases ho with ⟨-, O⟩ | ⟨-, he⟩
    · exact I1.obj O
    · rw [he]; exact I1
  | advanceTake _ _ _ _ _ ht => exact ht.inv
  | advance _ _ _ _ _ hv => exact I.norm.adv hv
  | differPoll _ _ _ _ _ _ hr => exact (I.norm.plan []).fetched hr
  | writePoll σ1 _ _ _ _ _ _ _ _ hw' _ hr => exact ((I.norm.plan []).writeRes hw').fetched hr
  | pushStale σ1 _ _ _ _ _ _ _ _ _ hw' _ hr =>
    have I1 := (I.norm.plan []).writeRes hw'
    rcases hr with ⟨-, he⟩ | ⟨-, F⟩
    · rw [he]; exact I1.refused
    · exact I1.head F

theorem inv_idle {σ σ' : NS} (I : SInv c σ) (h : Idle c σ σ') : SInv c σ' := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; exact I.norm.act false
  | differIdle _ _ _ _ _ _ _ he => subst he; exact (I.norm.plan []).act false
  | goal _ _ _ _ _ _ _ _ he => subst he; exact (I.norm.plan []).act false

end Inv

/-! ## How each change moves the rank -/

section Rank

variable {c : Ctx}

theorem counts_fresh {σ : NS} (I : SInv c σ) {M : List Nat} (hM : ∀ y ∈ M, y ∈ σ.heads) :
    cm (fresh σ M) = cm σ ∧ cs1 (fresh σ M) = cs1 σ ∧ cs2 (fresh σ M) = cs2 σ := by
  have key : ∀ x, x < σ.known.2 + 1 →
      (Anc (upd σ.par σ.next M) x σ.known.2 ↔ Anc σ.par x σ.known.2) :=
    fun _ _ => anc_upd_iff I.parLt (fun y hy => I.headsLt y (hM y hy)) I.knownLt
  have hl : ∀ x, x < σ.known.2 + 1 → ((σ.loc x ∨ x = σ.next) ↔ σ.loc x) := by
    intro x hx
    have := I.knownLt
    constructor
    · rintro (h | h)
      · exact h
      · omega
    · exact Or.inl
  refine ⟨cnt_congr fun x hx => ?_, cnt_congr fun x hx => ?_, cnt_congr fun x hx => ?_⟩ <;>
    simp only [fresh, key x hx, hl x hx]

theorem ca_fresh {σ : NS} (I : SInv c σ) {M : List Nat} (hM : Keeps σ M) :
    ca (fresh σ M) ≤ ca σ := by
  unfold ca
  apply ind_mono
  intro hn hall
  apply hn
  intro i hi
  obtain ⟨y, hy, ha⟩ := hall i hi
  obtain ⟨z, hz, hyz⟩ := hM.cover y hy
  refine ⟨σ.next, List.mem_singleton.2 rfl, ?_⟩
  have hMlt : ∀ p ∈ M, p < σ.next := fun p hp => I.headsLt p (hM.sub p hp)
  have h1 : Anc (upd σ.par σ.next M) i z :=
    (anc_upd_iff I.parLt hMlt (hMlt z hz)).2 (ha.trans hyz)
  exact h1.trans (Anc.parent (by rw [upd_same]; exact hz))

/-- A write leaves no more operations below the known head missing: locality only grows. -/
theorem counts_ext {σ σ' : NS} (I : SInv c σ) (E : Ext σ σ') :
    cm σ' ≤ cm σ ∧ cs1 σ' ≤ cs1 σ ∧ cs2 σ' ≤ cs2 σ := by
  obtain ⟨fk, -, -, -, -, fs, fobj, -, -⟩ := E.fields
  have key : ∀ x, x < σ.known.2 + 1 → (Anc σ'.par x σ.known.2 ↔ Anc σ.par x σ.known.2) :=
    fun _ _ => anc_agree I.parLt E.parLt E.parOld I.knownLt
  have hl : ∀ x, x < σ.known.2 + 1 → ¬ σ'.loc x → ¬ σ.loc x :=
    fun x hx h h' => h (E.locOld x (by have := I.knownLt; omega) h')
  unfold cm cs1 cs2
  rw [fk, fs, fobj]
  refine ⟨cnt_le fun x hx ⟨ha, hn⟩ => ⟨(key x hx).1 ha, hl x hx hn⟩,
    cnt_le fun x hx ⟨ha, hn, hs⟩ => ⟨(key x hx).1 ha, hl x hx hn, hs⟩,
    cnt_le fun x hx ⟨ha, hn, hs, ho⟩ => ⟨(key x hx).1 ha, hl x hx hn, hs, ho⟩⟩

theorem ca_ext_le {σ σ' : NS} (I : SInv c σ) (E : Ext σ σ')
    (hc : ∀ y ∈ σ.heads, ∃ y' ∈ σ'.heads, Anc σ'.par y y') : ca σ' ≤ ca σ := by
  obtain ⟨-, -, -, -, fi, -, -, -, -⟩ := E.fields
  unfold ca
  apply ind_mono
  intro hn hall
  apply hn
  intro i hi
  rw [fi] at hi
  obtain ⟨y, hy, ha⟩ := hall i hi
  obtain ⟨y', hy', ha'⟩ := hc y hy
  exact ⟨y', hy', ((anc_agree I.parLt E.parLt E.parOld (I.headsLt y hy)).2 ha).trans ha'⟩

theorem ck_congr {σ σ' : NS} (h : σ'.known = σ.known) : ck c σ' = ck c σ := by
  unfold ck; rw [h]

theorem cz_congr {σ σ' : NS} (ha : σ'.annc = σ.annc) (hap : σ'.ap = σ.ap) :
    cz c σ' = cz c σ := by
  unfold cz; rw [ha, hap]

theorem cr_congr {σ σ' : NS} (hap : σ'.ap = σ.ap) : cr c σ' = cr c σ := by
  unfold cr; rw [hap]

theorem ca_one {σ : NS} (h1 : σ.heads.length < 2) (hne : σ.heads ≠ [])
    (hd : ¬ ∃ y ∈ σ.heads, Desc σ y) : ca σ = 1 := by
  obtain ⟨y, hy⟩ := single_of h1 hne
  unfold ca
  apply ind_pos
  intro hall
  apply hd
  refine ⟨y, by rw [hy]; exact List.mem_singleton.2 rfl, fun i hi => ?_⟩
  obtain ⟨y', hy', ha⟩ := hall i hi
  rw [hy, List.mem_singleton] at hy'
  rw [← hy']; exact ha

theorem cm_realize_le (σ : NS) (x : Nat) (L : List Nat) : cm (realize σ x L) ≤ cm σ := by
  unfold cm
  exact cnt_le fun _ _ ⟨ha, hl⟩ => ⟨ha, fun h => hl (Or.inl h)⟩

theorem cm_realize_lt {σ : NS} {x : Nat} (L : List Nat) (hlt : ParLt σ.par)
    (ha : Anc σ.par x σ.known.2) (hl : ¬ σ.loc x) : cm (realize σ x L) < cm σ := by
  unfold cm
  exact cnt_lt (fun _ _ ⟨h1, h2⟩ => ⟨h1, fun h => h2 (Or.inl h)⟩)
    ⟨x, Nat.lt_succ_of_le (ha.le hlt), ⟨ha, hl⟩, fun ⟨_, h⟩ => h (Or.inr rfl)⟩

theorem ck_drop {σ σ' : NS} (hk : σ.known ≠ (c.S, c.H)) (hk' : σ'.known = (c.S, c.H)) :
    ck c σ' < ck c σ := by
  unfold ck
  rw [ind_pos hk, ind_neg (fun h => h hk')]
  exact Nat.zero_lt_one

/-- What a `Fetched` reply does to the rank once the node knows the hub's head. -/
theorem fetched_cmp {σ σ' : NS} (F : FetchedRep c σ σ') (hk : σ.known = (c.S, c.H)) :
    ck c σ' = ck c σ ∧ cz c σ' = 0 ∧ cr c σ' = cr c σ ∧ cm σ' = cm σ ∧ σ'.plan = σ.plan ∧
      cs1 σ' ≤ cs1 σ ∧ (cs1 σ' = cs1 σ → cs2 σ' ≤ cs2 σ) ∧ ca σ' = ca σ ∧ ch σ' = ch σ ∧
      cd c σ' = 0 := by
  have hK : σ'.known = σ.known := F.known.trans hk.symm
  refine ⟨?_, ?_, ?_, ?_, (F.same hk).1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ck; rw [hK]
  · unfold cz
    apply ind_neg
    rintro ⟨A, hA, hR, -⟩
    rcases F.annc with h | ⟨h, -⟩
    · rw [h] at hA; cases hA; exact hR rfl
    · rw [h] at hA; cases hA
  · unfold cr; rw [F.ap]
  · unfold cm; rw [hK, F.par, F.loc]
  · unfold cs1; rw [hK, F.par, F.loc]
    exact cnt_le fun x _ ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h => h3 (F.stg x h)⟩
  · intro he
    unfold cs1 at he
    unfold cs2
    rw [hK, F.par, F.loc] at he ⊢
    have pt := cnt_pt_of_eq (fun x _ ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h => h3 (F.stg x h)⟩) he
    refine cnt_le fun x hx ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, ?_, fun h => h4 (F.obj x h)⟩
    apply Classical.byContradiction
    intro hs
    exact (pt x hx ⟨h1, h2, hs⟩).2.2 h3
  · unfold ca; rw [(F.same hk).2, F.heads, F.par]
  · unfold ch; rw [F.heads]
  · unfold cd
    rw [ind_neg (fun h => h F.hubRecs)]
    have : ¬ (σ'.ap ≠ c.R ∧ σ'.annc ≠ some c.R) := by
      rintro ⟨hap, hne⟩
      rcases F.annc with h | ⟨-, hR⟩
      · exact hne h
      · rw [F.ap] at hap; exact hap hR.symm
    rw [ind_neg this]

theorem fetched_lt {σ σ' : NS} {x : Nat} (I : SInv c σ) (F : FetchedRep c σ σ')
    (hk : σ.known = (c.S, c.H)) (hw : Anc σ.par x σ.known.2) (hl : ¬ σ.loc x)
    (hs : ¬ σ.stg x) : cs1 σ' < cs1 σ := by
  have hK : σ'.known = σ.known := F.known.trans hk.symm
  have hst : σ'.stg x := F.stages x (by rw [hk] at hw; exact hw) hl
  unfold cs1
  rw [hK, F.par, F.loc]
  exact cnt_lt (fun y _ ⟨h1, h2, h3⟩ => ⟨h1, h2, fun h => h3 (F.stg y h)⟩)
    ⟨x, Nat.lt_succ_of_le (hw.le I.parLt), ⟨hw, hl, hs⟩, fun ⟨_, _, h⟩ => h hst⟩

/-- An `Objects` reply leaves every part of the rank but the missing objects. -/
theorem obj_cmp {σ σ' : NS} {M : Nat → Prop} (O : ObjRep σ σ' M) :
    ck c σ' = ck c σ ∧ cz c σ' = cz c σ ∧ cr c σ' = cr c σ ∧ cm σ' = cm σ ∧
      σ'.plan = σ.plan ∧ cs1 σ' = cs1 σ ∧ cs2 σ' ≤ cs2 σ ∧ ca σ' = ca σ ∧ ch σ' = ch σ ∧
      cd c σ' = cd c σ := by
  have ho := O.obj
  rw [O.rest] at ho ⊢
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
  unfold cs2
  exact cnt_le fun x _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun h => h4 (ho x (Or.inl h))⟩

theorem obj_lt {σ σ' : NS} {M : Nat → Prop} {x : Nat} (O : ObjRep σ σ' M) (hlt : ParLt σ.par)
    (hw : Anc σ.par x σ.known.2) (hl : ¬ σ.loc x) (hs : σ.stg x) (hb : ¬ σ.obj x) (hM : M x) :
    cs2 σ' < cs2 σ := by
  have ho := O.obj
  rw [O.rest] at ho ⊢
  unfold cs2
  exact cnt_lt (fun y _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, fun h => h4 (ho y (Or.inl h))⟩)
    ⟨x, Nat.lt_succ_of_le (hw.le hlt), ⟨hw, hl, hs, hb⟩,
      fun ⟨_, _, _, h⟩ => h (ho x (Or.inr hM))⟩

/-- Taking records drops the rank: a stale announcement goes, or the hub's records are taken. -/
theorem rank_take {σ σ' : NS} {A : Nat} (ha : σ.annc = some A) (hne : A ≠ σ.ap)
    (tk : σ'.known = σ.known) (tap : σ'.ap = A) (tann : σ'.annc = none ∨ σ'.annc = σ.annc) :
    LexLt (rank c σ') (rank c σ) := by
  have hz' : cz c σ' = 0 := by
    unfold cz
    apply ind_neg
    rintro ⟨B, hB, -, hB'⟩
    rw [tap] at hB'
    rcases tann with h | h
    · rw [h] at hB; cases hB
    · rw [h, ha] at hB; cases hB; exact hB' rfl
  have hk : ck c σ' = ck c σ := by unfold ck; rw [tk]
  unfold rank
  refine lt_cons (Nat.le_of_eq hk) fun _ => ?_
  by_cases hA : A = c.R
  · refine lt_cons (by rw [hz']; exact Nat.zero_le _) fun _ => lt_hd ?_
    have h1 : cr c σ = 1 := ind_pos fun h => hne (hA.trans h.symm)
    have h2 : cr c σ' = 0 := ind_neg fun h => h (tap.trans hA)
    rw [h1, h2]; exact Nat.zero_lt_one
  · apply lt_hd
    have h1 : cz c σ = 1 := ind_pos ⟨A, ha, hA, hne⟩
    rw [h1, hz']; exact Nat.zero_lt_one

/-- A supersede's local write leaves the rank but for fewer heads to cover. -/
theorem write_cmp {σ σ1 : NS} {new : Nat} (I : SInv c σ) (hp : σ.plan = [])
    (h1 : σ.heads.length < 2) (W : WriteRes σ σ1 new) :
    σ1.known = σ.known ∧ σ1.annc = σ.annc ∧ σ1.ap = σ.ap ∧ σ1.hubRecs = σ.hubRecs ∧
      cm σ1 ≤ cm σ ∧ σ1.plan = [] ∧ cs1 σ1 ≤ cs1 σ ∧ cs2 σ1 ≤ cs2 σ ∧ ca σ1 ≤ ca σ ∧
      ch σ1 = 0 := by
  obtain ⟨y, hy, (⟨-, F⟩ | ⟨-, he, -⟩)⟩ := W
  · obtain ⟨fk, fa, fap, fh, -, -, -, -, -⟩ := F.ext.fields
    obtain ⟨e1, e2, e3⟩ := counts_ext I F.ext
    refine ⟨fk, fa, fap, fh, e1, F.plan.trans hp, e2, e3, ca_ext_le I F.ext ?_, ?_⟩
    · intro y' hy'
      rw [hy, List.mem_singleton] at hy'
      subst hy'
      exact ⟨new, by rw [F.heads]; exact List.mem_singleton.2 rfl, F.covers⟩
    · unfold ch; rw [F.heads]; rfl
  · subst he
    exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _, hp, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      ch_zero h1 I.headsNe⟩

end Rank

/-! ## Every step that neither idles nor emits lowers the rank -/

section Steps

variable {c : Ctx}

theorem normA_sub (o : Option Nat) (ap : Nat) : normA o ap = none ∨ normA o ap = o := by
  cases o with
  | none => exact Or.inl rfl
  | some B =>
    by_cases hb : B = ap
    · left; simp [normA, hb]
    · right; exact normA_ne hb

theorem rank_busy {σ σ' : NS} (I : SInv c σ) (h : Busy c σ σ') :
    LexLt (rank c σ') (rank c σ) := by
  cases h with
  | adopt A ha hne _ ht => exact rank_take ha hne ht.known ht.ap ht.annc
  | merge M _ h2 hM he =>
    subst he
    rw [← rank_norm c σ]
    obtain ⟨e1, e2, e3⟩ := counts_fresh I.norm hM.sub
    have hca := ca_fresh I.norm hM.norm
    have hch : ch (fresh (norm σ) M) < ch (norm σ) := by
      show 0 < σ.heads.length - 1; omega
    unfold rank
    exact lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq e1 (lt_cons_eq rfl
      (lt_cons_eq e2 (lt_cons_eq e3 (lt_cons hca fun _ => lt_hd hch)))))))
  | mergeExisting M m _ h2 hM _ hpar he =>
    subst he
    rw [← rank_norm c σ]
    have hcm : cm (mergeTo (norm σ) m) ≤ cm (norm σ) :=
      cnt_le fun _ _ ⟨ha, hl⟩ => ⟨ha, fun h => hl (Or.inl h)⟩
    have hcs1 : cs1 (mergeTo (norm σ) m) ≤ cs1 (norm σ) :=
      cnt_le fun _ _ ⟨ha, hl, hs⟩ => ⟨ha, fun h => hl (Or.inl h), hs⟩
    have hcs2 : cs2 (mergeTo (norm σ) m) ≤ cs2 (norm σ) :=
      cnt_le fun _ _ ⟨ha, hl, hs, ho⟩ => ⟨ha, fun h => hl (Or.inl h), hs, ho⟩
    have hca : ca (mergeTo (norm σ) m) ≤ ca (norm σ) := by
      unfold ca
      apply ind_mono
      intro hn hall
      apply hn
      intro i hi
      obtain ⟨y, hy, ha⟩ := hall i hi
      obtain ⟨z, hz, hyz⟩ := hM.cover y hy
      exact ⟨m, List.mem_singleton.2 rfl, Anc.step ((hpar z).2 hz) (ha.trans hyz)⟩
    have hch : ch (mergeTo (norm σ) m) < ch (norm σ) := by
      show [m].length - 1 < σ.heads.length - 1
      simp only [List.length_singleton]
      omega
    unfold rank
    exact lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl (lt_cons hcm fun _ => lt_cons_eq rfl
      (lt_cons hcs1 fun _ => lt_cons hcs2 fun _ => lt_cons hca fun _ => lt_hd hch))))
  | prune x _ h2 hM he =>
    subst he
    rw [← rank_norm c σ]
    have hca : ca (pruneTo (norm σ) x) ≤ ca (norm σ) := by
      unfold ca
      apply ind_mono
      intro hn hall
      apply hn
      intro i hi
      obtain ⟨y, hy, hiy⟩ := hall i hi
      obtain ⟨z, hz, hyz⟩ := hM.cover y hy
      exact ⟨z, hz, hiy.trans hyz⟩
    have hch : ch (pruneTo (norm σ) x) < ch (norm σ) := by
      show [x].length - 1 < σ.heads.length - 1
      simp only [List.length_singleton]
      omega
    unfold rank
    exact lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl
      (lt_cons_eq rfl (lt_cons_eq rfl (lt_cons hca fun _ => lt_hd hch)))))))
  | realizePlan x rest _ _ _ hp he =>
    subst he
    rw [← rank_norm c σ]
    unfold rank
    refine lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl
      (lt_cons (cm_realize_le _ _ _) fun _ => lt_hd ?_)))
    show rest.length < σ.plan.length
    rw [hp]; exact Nat.lt_succ_self _
  | realizeSurvey x L _ _ _ _ hr he =>
    subst he
    rw [← rank_norm c σ]
    unfold rank
    have ha : Anc σ.par x σ.known.2 := Walk.anc hr.1
    exact lt_cons_eq rfl (lt_cons_eq rfl (lt_cons_eq rfl
      (lt_hd (cm_realize_lt (σ := norm σ) L I.parLt ha hr.2.1))))
  | fetch σ1 _ _ _ _ _ hm hf ho =>
    rw [← rank_norm c σ]
    have hO : ck c σ' = ck c σ1 ∧ cz c σ' = cz c σ1 ∧ cr c σ' = cr c σ1 ∧ cm σ' = cm σ1 ∧
        σ'.plan = σ1.plan ∧ cs1 σ' = cs1 σ1 ∧ cs2 σ' ≤ cs2 σ1 ∧ ca σ' = ca σ1 ∧
        ch σ' = ch σ1 ∧ cd c σ' = cd c σ1 := by
      rcases ho with ⟨-, O⟩ | ⟨-, he⟩
      · exact obj_cmp O
      · subst he; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _, rfl, rfl, rfl⟩
    obtain ⟨k2, z2, r2, m2, p2, s2, -, -, -, -⟩ := hO
    by_cases hmo : MissOps σ
    · obtain ⟨-, F⟩ := hf.resolve_right fun h => h.1 hmo
      by_cases hk : σ.known = (c.S, c.H)
      · obtain ⟨k1, z1, r1, m1, p1, -, -, -, -, -⟩ := fetched_cmp F hk
        obtain ⟨x, hw, hlx, hsx⟩ := hmo
        have ha : Anc σ.par x σ.known.2 := Walk.anc hw
        have hlt1 : cs1 σ1 < cs1 (norm σ) := fetched_lt I.norm F hk ha hlx hsx
        unfold rank
        exact lt_cons_eq (k2.trans k1) (lt_cons (by rw [z2, z1]; exact Nat.zero_le _)
          fun _ => lt_cons_eq (r2.trans r1) (lt_cons_eq (m2.trans m1)
            (lt_cons_eq (by rw [p2, p1]) (lt_hd (by rw [s2]; exact hlt1)))))
      · unfold rank
        exact lt_hd (by rw [k2]; exact ck_drop hk F.known)
    · have he1 : σ1 = norm σ := (hf.resolve_left fun h => hmo h.1).2
      subst he1
      have hmb : MissObjs σ := hm.resolve_left hmo
      obtain ⟨-, O⟩ := ho.resolve_right fun h => h.1 hmb
      obtain ⟨x, hw, hlx, hs, hb⟩ := hmb
      have ha : Anc σ.par x σ.known.2 := Walk.anc hw
      have hlt2 : cs2 σ' < cs2 (norm σ) :=
        obj_lt O I.parLt ha hlx hs hb ⟨hw, hlx, hs, hb⟩
      unfold rank
      exact lt_cons_eq k2 (lt_cons_eq z2 (lt_cons_eq r2 (lt_cons_eq m2
        (lt_cons_eq (by rw [p2]) (lt_cons_eq s2 (lt_hd hlt2))))))
  | advanceTake A _ _ _ ha ht =>
    rw [← rank_norm c σ]
    exact rank_take (σ := norm σ) ha (normA_some ha).2 ht.known ht.ap ht.annc
  | writePoll σ1 _ _ h1 _ _ _ hf hw hw' hnew hr =>
    -- the write reuses the known head: restoring, the cache written
    rw [← rank_norm c σ]
    obtain ⟨hw0, hw1, hp1⟩ := write_known (σ := { norm σ with plan := [] }) I.knownLt hw hw' hnew
    obtain ⟨wk, wa, wap, wh, wm, wp, ws1, ws2, wca, wch⟩ :=
      write_cmp (I.norm.plan []) rfl h1 hw'
    by_cases hk : σ.known = (c.S, c.H)
    · have hk1 : σ1.known = (c.S, c.H) := wk.trans hk
      obtain ⟨k1, z1, r1, m1, p1, s1, s2, a1, h1', d1⟩ := fetched_cmp hr hk1
      have hch0 : ch (norm σ) = 0 := ch_zero h1 I.headsNe
      have hcw : cw σ' < cw (norm σ) := by
        show ind (σ'.written = false ∧ σ'.pending ≠ []) < ind (σ.written = false ∧ σ.pending ≠ [])
        rw [hr.written, hw1, ind_neg (fun h => by cases h.1), ind_pos ⟨hw0, hw⟩]
        exact Nat.zero_lt_one
      unfold rank
      exact lt_cons_eq (k1.trans (by show ind (σ1.known ≠ _) = ind (σ.known ≠ _); rw [wk]; rfl))
        (lt_cons (by rw [z1]; exact Nat.zero_le _) fun _ =>
        lt_cons_eq (r1.trans (by show ind (σ1.ap ≠ c.R) = ind (σ.ap ≠ c.R); rw [wap]; rfl))
        (lt_cons (by rw [m1]; exact wm) fun _ => lt_cons (by rw [p1, wp]; exact Nat.zero_le _)
        fun _ => lt_cons (Nat.le_trans s1 ws1) fun he =>
        lt_cons (Nat.le_trans (s2 (by
          have h2 : cs1 σ1 ≤ cs1 (norm σ) := ws1
          have := s1; omega)) ws2) fun _ =>
        lt_cons (by rw [a1]; exact wca) fun _ =>
        lt_cons_eq (h1'.trans (by rw [wch, hch0])) (lt_cons (by rw [d1]; exact Nat.zero_le _)
          fun _ => lt_hd hcw)))
    · unfold rank
      exact lt_hd (ck_drop hk hr.known)
  | advance _ h1 _ hd _ hv =>
    rw [← rank_norm c σ]
    obtain ⟨fk, fa, fap, -, fi, -, -, -, -⟩ := hv.ext.fields
    obtain ⟨e1, e2, e3⟩ := counts_ext I.norm hv.ext
    have hz : ca σ' = 0 := by
      unfold ca
      apply ind_neg
      intro hn
      apply hn
      rw [fi]
      exact hv.covers
    have hone : ca (norm σ) = 1 := ca_one h1 I.headsNe hd
    unfold rank
    exact lt_cons_eq (ck_congr fk) (lt_cons_eq (cz_congr fa fap) (lt_cons_eq (cr_congr fap)
      (lt_cons e1 fun _ => lt_cons (by rw [hv.plan]; exact Nat.zero_le _) fun _ =>
        lt_cons e2 fun _ => lt_cons e3 fun _ =>
          lt_hd (by rw [hz, hone]; exact Nat.zero_lt_one))))
  | differPoll _ _ _ _ hf ha hr =>
    rw [← rank_norm c σ]
    by_cases hk : σ.known = (c.S, c.H)
    · obtain ⟨k1, z1, r1, m1, p1, s1, s2, a1, h1', d1⟩ := fetched_cmp hr hk
      have hrec := I.recs hk
      have hne : c.R ≠ σ.ap := by simp only [Differ, hrec] at hf; exact hf
      have e1 : ind (σ.hubRecs ≠ some c.R) = 0 := ind_neg fun h => h hrec
      have e2 : ind (σ.ap ≠ c.R ∧ (norm σ).annc ≠ some c.R) = 1 :=
        ind_pos ⟨fun e => hne e.symm, by rw [ha]; intro h; cases h⟩
      have hd0 : cd c (norm σ) = 1 := by
        show ind (σ.hubRecs ≠ some c.R) + ind (σ.ap ≠ c.R ∧ (norm σ).annc ≠ some c.R) = 1
        rw [e1, e2]
      unfold rank
      exact lt_cons_eq k1 (lt_cons (by rw [z1]; exact Nat.zero_le _) fun _ =>
        lt_cons_eq r1 (lt_cons_eq m1 (lt_cons (by rw [p1]; exact Nat.zero_le _) fun _ =>
          lt_cons s1 fun he => lt_cons (s2 he) fun _ => lt_cons_eq a1 (lt_cons_eq h1'
            (lt_hd (by rw [d1, hd0]; exact Nat.zero_lt_one))))))
    · unfold rank
      exact lt_hd (ck_drop hk hr.known)
  | pushStale σ1 _ _ h1 _ _ _ hf _ hk hw' _ hr =>
    rw [← rank_norm c σ]
    rcases hr with ⟨hap, he⟩ | ⟨-, F⟩
    · subst he
      obtain ⟨wk, wa, wap, wh, wm, wp, ws1, ws2, wca, wch⟩ :=
        write_cmp (I.norm.plan []) rfl h1 hw'
      have hub0 : σ.hubRecs ≠ some c.R := by
        intro h
        apply hf
        simp only [Differ, h]
        exact fun e => hap e.symm
      have k' : ck c { σ1 with hubRecs := some c.R } = ck c (norm σ) := by
        show ind (σ1.known ≠ _) = ind (σ.known ≠ _); rw [wk]; rfl
      have z' : cz c { σ1 with hubRecs := some c.R } = cz c (norm σ) := by
        show ind (∃ A, σ1.annc = some A ∧ A ≠ c.R ∧ A ≠ σ1.ap) =
          ind (∃ A, (norm σ).annc = some A ∧ A ≠ c.R ∧ A ≠ σ.ap)
        rw [wa, wap]; rfl
      have r' : cr c { σ1 with hubRecs := some c.R } = cr c (norm σ) := by
        show ind (σ1.ap ≠ c.R) = ind (σ.ap ≠ c.R); rw [wap]; rfl
      have hch0 : ch (norm σ) = 0 := ch_zero h1 I.headsNe
      have d' : cd c { σ1 with hubRecs := some c.R } < cd c (norm σ) := by
        show ind (some c.R ≠ some c.R) + ind (σ1.ap ≠ c.R ∧ σ1.annc ≠ some c.R) <
          ind (σ.hubRecs ≠ some c.R) + ind (σ.ap ≠ c.R ∧ (norm σ).annc ≠ some c.R)
        rw [wa, wap, ind_neg (fun h => h rfl), ind_pos hub0]
        show 0 + ind (σ.ap ≠ c.R ∧ (norm σ).annc ≠ some c.R) <
          1 + ind (σ.ap ≠ c.R ∧ (norm σ).annc ≠ some c.R)
        omega
      unfold rank
      exact lt_cons_eq k' (lt_cons_eq z' (lt_cons_eq r' (lt_cons wm fun _ =>
        lt_cons (by show σ1.plan.length ≤ _; rw [wp]; exact Nat.zero_le _) fun _ =>
          lt_cons ws1 fun _ => lt_cons ws2 fun _ => lt_cons wca fun _ =>
            lt_cons_eq (by show ch σ1 = ch (norm σ); rw [wch, hch0]) (lt_hd d'))))
    · unfold rank
      exact lt_hd (ck_drop hk F.known)

theorem rank_idle {σ σ' : NS} (h : Idle c σ σ') : LexLe (rank c σ') (rank c σ) := by
  rw [← rank_norm c σ]
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; exact Or.inr rfl
  | differIdle _ _ _ _ _ _ _ he =>
    subst he
    unfold rank
    exact le_cons_eq rfl (le_cons_eq rfl (le_cons_eq rfl (le_cons_eq rfl
      (le_cons (Nat.zero_le _) fun _ => Or.inr rfl))))
  | goal _ _ _ _ _ _ _ _ he =>
    subst he
    unfold rank
    exact le_cons_eq rfl (le_cons_eq rfl (le_cons_eq rfl (le_cons_eq rfl
      (le_cons (Nat.zero_le _) fun _ => Or.inr rfl))))

theorem rank_start {σ σ1 : NS} (F : FetchedRep c σ σ1) :
    LexLe (rank c { σ1 with act := true }) (rank c σ) := by
  rw [show rank c { σ1 with act := true } = rank c σ1 from rfl]
  by_cases hk : σ.known = (c.S, c.H)
  · obtain ⟨k1, z1, r1, m1, p1, s1, s2, a1, h1, d1⟩ := fetched_cmp F hk
    unfold rank
    exact le_cons_eq k1 (le_cons (by rw [z1]; exact Nat.zero_le _) fun _ =>
      le_cons_eq r1 (le_cons_eq m1 (le_cons_eq (by rw [p1])
        (le_cons s1 fun he => le_cons (s2 he) fun _ => le_cons_eq a1 (le_cons_eq h1
          (le_cons (by rw [d1]; exact Nat.zero_le _) fun _ =>
            Or.inr (by rw [cw_congr F.written F.pending])))))))
  · unfold rank
    exact LexLt.le (lt_hd (ck_drop hk F.known))

theorem rank_notify {σ σ' : NS} (I : SInv c σ) (F : HeadRep c σ σ') :
    LexLe (rank c σ') (rank c σ) := by
  by_cases hk : σ.known = (c.S, c.H)
  · have hK : σ'.known = σ.known := F.known.trans hk.symm
    obtain ⟨hp, hi⟩ := F.same hk
    refine Or.inr ?_
    unfold rank ck cz cr cm cs1 cs2 ca ch cd cw
    rw [hK, F.annc, F.ap, F.par, F.loc, F.stg, F.obj, hp, hi, F.heads, F.hubRecs, I.recs hk,
      F.written, F.pending]
  · unfold rank
    exact LexLt.le (lt_hd (ck_drop hk F.known))

theorem idle_act {σ σ' : NS} (h : Idle c σ σ') : σ'.act = false := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; rfl
  | differIdle _ _ _ _ _ _ _ he => subst he; rfl
  | goal _ _ _ _ _ _ _ _ he => subst he; rfl

/-- Every event but an emitted push keeps the invariant and never raises the rank; a busy
step lowers it. -/
theorem ev_ok {σ σ' : NS} {l : Lab} (I : SInv c σ) (h : Ev c l σ σ') (hl : l ≠ .emit)
    (hm : l ≠ .maint) :
    SInv c σ' ∧ LexLe (rank c σ') (rank c σ) ∧
      (l = .busy → LexLt (rank c σ') (rank c σ)) := by
  cases h with
  | maint _ _ _ => exact absurd rfl hm
  | busy _ h => exact ⟨inv_busy I h, (rank_busy I h).le, fun _ => rank_busy I h⟩
  | idle _ h => exact ⟨inv_idle I h, rank_idle h, fun h' => Lab.noConfusion h'⟩
  | emit _ _ _ => exact absurd rfl hl
  | start _ F he =>
    subst he
    exact ⟨(I.fetched F).act true, rank_start F, fun h' => Lab.noConfusion h'⟩
  | notify F => exact ⟨I.head F, rank_notify I F, fun h' => Lab.noConfusion h'⟩
  | frame => exact ⟨I, Or.inr rfl, fun h' => Lab.noConfusion h'⟩

/-- Every event but an emitted push keeps the invariant, housekeeping included. -/
theorem inv_ev {σ σ' : NS} {l : Lab} (I : SInv c σ) (h : Ev c l σ σ') (hl : l ≠ .emit) :
    SInv c σ' := by
  cases h with
  | maint _ h hw => exact ((inv_idle I h).act true).ext hw
  | emit _ _ _ => exact absurd rfl hl
  | busy _ h => exact inv_busy I h
  | idle _ h => exact inv_idle I h
  | start _ F he => subst he; exact (I.fetched F).act true
  | notify F => exact I.head F
  | frame => exact I

end Steps

/-! ## Idle at the stable hub is the goal, and the goal is kept -/

section Goal

variable {c : Ctx}

/-- The node knows the hub's head and holds no older announcement: true after any round's
first reply. -/
def Good (c : Ctx) (σ : NS) : Prop :=
  σ.known = (c.S, c.H) ∧ (σ.annc = none ∨ σ.annc = some c.R)

theorem good_norm {σ : NS} (hg : Good c σ) (L : List Nat) (b : Bool) :
    Good c { norm σ with plan := L, act := b } := by
  refine ⟨hg.1, ?_⟩
  show normA σ.annc σ.ap = none ∨ normA σ.annc σ.ap = some c.R
  rcases normA_sub σ.annc σ.ap with h | h
  · exact Or.inl h
  · rw [h]; exact hg.2

theorem good_idle {σ σ' : NS} (hg : Good c σ) (h : Idle c σ σ') : Good c σ' := by
  cases h with
  | fetchIdle _ _ _ _ _ _ _ he => subst he; exact good_norm hg σ.plan false
  | differIdle _ _ _ _ _ _ _ he => subst he; exact good_norm hg [] false
  | goal _ _ _ _ _ _ _ _ he => subst he; exact good_norm hg [] false

theorem good_ev {σ σ' : NS} {l : Lab} (hg : Good c σ) (h : Ev c l σ σ') (hb : l ≠ .busy)
    (hn : l ≠ .emit) : Good c σ' := by
  cases h with
  | busy _ _ => exact absurd rfl hb
  | emit _ _ _ => exact absurd rfl hn
  | idle _ h => exact good_idle hg h
  | maint _ h hw =>
    have g1 := good_idle hg h
    obtain ⟨fk, fa, -, -, -, -, -, -, -⟩ := hw.fields
    exact ⟨fk.trans g1.1, by rw [fa]; exact g1.2⟩
  | start _ F he =>
    subst he
    refine ⟨F.known, ?_⟩
    rcases F.annc with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  | notify F => exact ⟨F.known, by rw [F.annc]; exact hg.2⟩
  | frame => exact hg

/-- An `Idle` once the node knows the hub's head, with no older announcement, is the goal:
survey completeness rules out idling with the known head not local, and the repaired advance
idling while a prepared adoption is blocked. -/
theorem idle_settled {σ σ' : NS} (I : SInv c σ) (hg : Good c σ) (h : Idle c σ σ') :
    Settled c σ' := by
  obtain ⟨hk, hann⟩ := hg
  cases h with
  | fetchIdle _ _ hl _ hr ho hb _ =>
    rcases survey_complete I.parLt hl with h | h | h
    · exact absurd h hr
    · exact absurd h ho
    · exact absurd h hb
  | differIdle _ _ _ _ _ hnr ha _ => exact absurd hnr ha
  | goal _ _ hl hd _ hf hp hh he =>
    subst he
    have hrec := I.recs hk
    have hap : σ.ap = c.R := by
      apply Classical.byContradiction
      intro hne
      apply hf
      simp only [Differ, hrec]
      exact fun e => hne e.symm
    obtain ⟨y, hy, hdes⟩ := hd
    rw [hh, List.mem_singleton] at hy
    subst hy
    refine ⟨hk, hap, hrec, hp, by show σ.heads = [c.H]; rw [hh, hk], by rw [hk] at hl; exact hl,
      by rw [hk] at hdes; exact hdes, ?_⟩
    left
    show normA σ.annc σ.ap = none
    rcases hann with h | h <;> rw [h]
    · rfl
    · rw [hap]; simp [normA]

/-- The goal is kept: at it the core idles, and replies and notifications change nothing it
says. -/
theorem settled_ev {σ σ' : NS} {l : Lab} (hs : Settled c σ) (h : Ev c l σ σ')
    (hm : l ≠ .maint) : Settled c σ' := by
  obtain ⟨hk, hap, hrec, hp, hh, hl, hd, hann⟩ := hs
  have hK : σ.known.2 = c.H := by rw [hk]
  have notDiffer : ¬ Differ σ := by
    simp only [Differ, hrec]
    exact fun h => h hap.symm
  have hdesc : ∃ y ∈ σ.heads, Desc σ y :=
    ⟨c.H, by rw [hh]; exact List.mem_singleton.2 rfl, hd⟩
  have hloc : σ.loc σ.known.2 := by rw [hK]; exact hl
  have hnoadopt : ∀ A, σ.annc = some A → A ≠ σ.ap → False := by
    intro A hA hne
    rcases hann with h | h <;> rw [h] at hA <;> cases hA
    exact hne hap.symm
  cases h with
  | busy _ h =>
    exfalso
    cases h with
    | adopt A ha hne _ _ => exact hnoadopt A ha hne
    | merge _ _ h2 _ _ => rw [hh] at h2; simp at h2
    | mergeExisting _ _ _ h2 _ _ _ _ => rw [hh] at h2; simp at h2
    | prune _ _ h2 _ _ => rw [hh] at h2; simp at h2
    | realizePlan _ _ _ _ hl' _ _ => exact hl' hloc
    | realizeSurvey _ _ _ _ hl' _ _ _ => exact hl' hloc
    | fetch _ _ _ hl' _ _ _ _ _ => exact hl' hloc
    | advanceTake A _ _ _ ha _ =>
      obtain ⟨h1, h2⟩ := normA_some ha
      exact hnoadopt A h1 h2
    | advance _ _ _ hd' _ _ => exact hd' hdesc
    | differPoll _ _ _ _ hf _ _ => exact notDiffer hf
    | pushStale _ _ _ _ _ _ _ _ _ hk' _ _ _ => exact hk' hk
    | writePoll _ _ _ _ _ _ _ _ hw _ _ _ => exact hw hp
  | idle _ h =>
    cases h with
    | fetchIdle _ _ hl' _ _ _ _ _ => exact absurd hloc hl'
    | differIdle _ _ _ _ hf _ _ _ => exact absurd hf notDiffer
    | goal _ _ _ _ _ _ _ _ he =>
      subst he
      refine ⟨hk, hap, hrec, hp, hh, hl, hd, ?_⟩
      left
      show normA σ.annc σ.ap = none
      rcases hann with h | h <;> rw [h]
      · rfl
      · rw [hap]; simp [normA]
  | emit _ _ h =>
    exfalso
    obtain ⟨-, -, -, -, -, -, -, hw, -, -, -⟩ := h
    rcases hw with hw | hw
    · exact hw hp
    · exact hw (by rw [hh, hK])
  | start _ F he =>
    subst he
    obtain ⟨-, hi⟩ := F.same hk
    refine ⟨F.known, F.ap.trans hap, F.hubRecs, F.pending.trans hp, F.heads.trans hh,
      Eq.mpr (congrFun F.loc c.H) hl, ?_, ?_⟩
    · show ∀ i ∈ _, Anc _ i c.H
      rw [hi, F.par]; exact hd
    · rcases F.annc with h | ⟨h, -⟩
      · exact Or.inr h
      · exact Or.inl h
  | notify F =>
    obtain ⟨-, hi⟩ := F.same hk
    refine ⟨F.known, F.ap.trans hap, F.hubRecs, F.pending.trans hp, F.heads.trans hh,
      Eq.mpr (congrFun F.loc c.H) hl, ?_, by rw [F.annc]; exact hann⟩
    show ∀ i ∈ _, Anc _ i c.H
    rw [hi, F.par]; exact hd
  | maint _ _ _ => exact absurd rfl hm
  | frame => exact ⟨hk, hap, hrec, hp, hh, hl, hd, hann⟩

/-- What an emitted push is: from the hub's head, with the hub's records and the node's pending
drops, and a new head that is not the hub's, which `write_fixup` left. -/
theorem emit_packet {σ σ1 : NS} {new : Nat} (I : SInv c σ) (h : Emit c σ σ1 new) :
    σ.known = (c.S, c.H) ∧ σ.ap = c.R ∧ σ.hubRecs = some c.R ∧ new ≠ c.H ∧
      WriteRes { norm σ with plan := [] } σ1 new := by
  obtain ⟨-, -, -, -, -, -, hf, -, hk, hw', hnew⟩ := h
  have hrec := I.recs hk
  have hap : σ.ap = c.R := by
    apply Classical.byContradiction
    intro hne
    apply hf
    simp only [Differ, hrec]
    exact fun e => hne e.symm
  refine ⟨hk, hap, hrec, ?_, hw'⟩
  rw [hk] at hnew
  exact hnew

end Goal

/-! ## The node settles -/

/-- The core of `node_settles`: from `k0` on there is no emitted push and no housekeeping. -/
theorem settles_from (c : Ctx) (run : Nat → NS) (lab : Nat → Lab) (k0 : Nat)
    (hev : ∀ i, k0 ≤ i → Ev c (lab i) (run i) (run (i + 1)))
    (h0 : SInv c (run k0))
    (noemit : ∀ i, k0 ≤ i → lab i ≠ .emit)
    (nomaint : ∀ i, k0 ≤ i → lab i ≠ .maint)
    (hstart : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k0 ≤ i → (run i).act = true →
      ∃ j, i ≤ j ∧ (lab j = .busy ∨ lab j = .idle ∨ lab j = .emit)) :
    ∃ k, ∀ i, k ≤ i → Settled c (run i) := by
  have hinv : ∀ d, SInv c (run (k0 + d)) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih =>
      exact (ev_ok ih (hev _ (by omega)) (noemit _ (by omega)) (nomaint _ (by omega))).1
  have hinv' : ∀ i, k0 ≤ i → SInv c (run i) := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact hinv d
  have step : ∀ i, k0 ≤ i → LexLe (rank c (run (i + 1))) (rank c (run i)) ∧
      (lab i = .busy → LexLt (rank c (run (i + 1))) (rank c (run i))) :=
    fun i hi => (ev_ok (hinv' i hi) (hev i hi) (noemit i hi) (nomaint i hi)).2
  obtain ⟨k1, hk1⟩ := lex_stabilizes 11 (fun j => rank c (run (k0 + j)))
    (fun _ => rank_length c _) (fun j => (step (k0 + j) (by omega)).1)
  have nobusy : ∀ i, k0 + k1 ≤ i → lab i ≠ .busy := by
    intro i hi hb
    have hlt := (step i (by omega)).2 hb
    have e1 : rank c (run (k0 + (i - k0))) = rank c (run (k0 + k1)) := hk1 (i - k0) (by omega)
    have e2 : rank c (run (k0 + (i + 1 - k0))) = rank c (run (k0 + k1)) :=
      hk1 (i + 1 - k0) (by omega)
    rw [show k0 + (i - k0) = i by omega] at e1
    rw [show k0 + (i + 1 - k0) = i + 1 by omega] at e2
    rw [e1, e2] at hlt
    exact lexLt_irrefl _ hlt
  have idleAt : ∀ j, k0 + k1 ≤ j →
      (lab j = .busy ∨ lab j = .idle ∨ lab j = .emit) → lab j = .idle := by
    intro j hj hl
    rcases hl with h | h | h
    · exact absurd h (nobusy j hj)
    · exact h
    · exact absurd h (noemit j (by omega))
  have hst : ∃ j, k0 + k1 ≤ j ∧ lab j = .start := by
    cases ha : (run (k0 + k1)).act with
    | false => exact hstart _ (by omega) ha
    | true =>
      obtain ⟨j0, hj0, hl0⟩ := hcore _ (by omega) ha
      have hidle := idleAt j0 hj0 hl0
      have h := hev j0 (by omega)
      rw [hidle] at h
      have hact : (run (j0 + 1)).act = false := by
        cases h with
        | idle _ h => exact idle_act h
      obtain ⟨j, hj, hl⟩ := hstart (j0 + 1) (by omega) hact
      exact ⟨j, by omega, hl⟩
  obtain ⟨j, hj, hlj⟩ := hst
  have hgood1 : Good c (run (j + 1)) ∧ (run (j + 1)).act = true := by
    have h := hev j (by omega)
    rw [hlj] at h
    cases h with
    | start _ F he =>
      rw [he]
      refine ⟨⟨F.known, ?_⟩, rfl⟩
      rcases F.annc with h | ⟨h, -⟩
      · exact Or.inr h
      · exact Or.inl h
  have hgood : ∀ d, Good c (run (j + 1 + d)) := by
    intro d
    induction d with
    | zero => exact hgood1.1
    | succ d ih =>
      exact good_ev ih (hev _ (by omega)) (nobusy _ (by omega)) (noemit _ (by omega))
  obtain ⟨j', hj', hl'⟩ := hcore (j + 1) (by omega) hgood1.2
  have hidle := idleAt j' (by omega) hl'
  have hset : Settled c (run (j' + 1)) := by
    have h := hev j' (by omega)
    rw [hidle] at h
    cases h with
    | idle _ h =>
      have hg : Good c (run j') := by
        have := hgood (j' - (j + 1))
        rwa [show j + 1 + (j' - (j + 1)) = j' by omega] at this
      exact idle_settled (hinv' j' (by omega)) hg h
  refine ⟨j' + 1, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => exact hset
  | succ d ih => exact settled_ev (ih (by omega)) (hev _ (by omega)) (nomaint _ (by omega))

/-- Once the hub is stable, a node settles at its head, or sends a push from the hub's head with
the hub's records (`emit_packet`), which the stable hub would accept and so cannot have been
sent. Premises: the run's events from `k0` on, with no failed call (a failure reopens the node,
which root's RecordEpoch shows eventually stops); the invariant at `k0`; housekeeping that writes
(`when_idle`) eventually stops; a round starts whenever none is running; and a running round's
next step happens, its calls completing. A round is never assumed to finish. -/
theorem node_settles (c : Ctx) (run : Nat → NS) (lab : Nat → Lab) (k0 : Nat)
    (hev : ∀ i, k0 ≤ i → Ev c (lab i) (run i) (run (i + 1)))
    (h0 : SInv c (run k0))
    (hmaint : ∃ kb, ∀ i, kb ≤ i → lab i ≠ .maint)
    (hstart : ∀ i, k0 ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k0 ≤ i → (run i).act = true →
      ∃ j, i ≤ j ∧ (lab j = .busy ∨ lab j = .idle ∨ lab j = .emit ∨ lab j = .maint)) :
    (∃ i, k0 ≤ i ∧ lab i = .emit ∧ ∃ σ1 new, Emit c (run i) σ1 new) ∨
      ∃ k, ∀ i, k ≤ i → Settled c (run i) := by
  by_cases hem : ∃ i, k0 ≤ i ∧ lab i = .emit
  · left
    obtain ⟨i, hi, hl⟩ := hem
    have h := hev i hi
    rw [hl] at h
    cases h with
    | emit σ1 new h => exact ⟨i, hi, hl, σ1, new, h⟩
  · right
    have noemit : ∀ i, k0 ≤ i → lab i ≠ .emit := fun i hi he => hem ⟨i, hi, he⟩
    obtain ⟨kb, hkb⟩ := hmaint
    have hinv : ∀ d, SInv c (run (k0 + d)) := by
      intro d
      induction d with
      | zero => exact h0
      | succ d ih => exact inv_ev ih (hev _ (by omega)) (noemit _ (by omega))
    refine settles_from c run lab (k0 + kb) (fun i hi => hev i (by omega)) (hinv kb)
      (fun i hi => noemit i (by omega)) (fun i hi => hkb i (by omega))
      (fun i hi ha => hstart i (by omega) ha) (fun i hi ha => ?_)
    obtain ⟨j, hj, hl⟩ := hcore i (by omega) ha
    refine ⟨j, hj, ?_⟩
    rcases hl with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd h (hkb j (by omega))

/-! ## What this rests on

`node_settles` assumes, from `k0` on:
- `hev`: every event is one of `Ev`'s. This is where the hub's stability enters: every reply
  carries `(S, H, R)` (HubSuffix and the record cut), the node's knowledge is truthful
  (`hub_went_back` never fires), and there are no user operations, abandonments, crashes or
  maintenance writes.
- `h0`: `SInv` at `k0`.
- `hstart`, `hcore`: a round starts whenever none is running, and a running round's next step
  happens, its calls completing. Nothing says a round ends; that is derived.

The contracts, each to be tied to the native code or a primitive model for this `H` and these
records, not to a projection of versions onto originals:
- `FetchedRep`: a `Fetched` reply stages every operation below `H` that is neither local nor
  staged (transfer), and `note_announced` notes `R` and announces it unless applied
  (announcement completion: its `held` mismatch and `lacks_pruned` paths are not taken).
- `HeadRep`: `note_records` from a notification or a rejection notes `R`.
- `ObjRep`: an `Objects` reply brings the objects asked for.
- `Take`: `adopt`, or `advance` while records are prepared, applies them.
- `Take` also keeps the core's plan, as `adopt` does; it may forget staging and rename the rest.
- `Ext`, `Adv`: `advance_to` makes the op heads cover what stands for the known head, adding
  only fresh operations (a realization's merge with concurrent heads).
- `WriteRes`, `FreshOn`: `write_fixup(publish_from)` publishes what `Publication.write` says,
  as a chain on the single head: the restoring fix-up while it isn't written, else a neutral tip
  when the head is the known head (`write_drop_tip`, the same exact id, with no concurrent
  command), else nothing. The chain is new, or identical to operations the node holds already
  (no nonce), taking no new label. The new head is the known one only when the restoring fix-up
  is identical to it (`write_known`, from `publication_progress`): the branch that polls instead
  (`writePoll`), whose write sets the cache, lowering the rank's last component (`cw`). A write
  only makes operations local (`Ext.locOld`), a reused chain included. OBLIGATION: before it
  decides, `write_fixup_until` runs `repair_received_work` (supersede.rs), which, for received
  work whose operations the pending records removed, may rewrite the fix-up and clear
  `fixup_written`, a new restoring obligation. `WriteRes` reads the cache as it was, taking no
  such repair: a correspondence obligation past the input cut (received work being finite
  input), vacuous with no pending drops (it returns at once), as in the fine tail. Before that,
  a repair would raise `cw` with no other component falling.
- `realize` makes a freshly surveyed ready operation local, and the front of a plan kept from
  before an adoption too, once failed calls have stopped. A failed call, a stale plan entry the
  records taken since rename or drop, ends `driver.sync` in an error, which reopens the node and
  restarts its core: not an event here. Root's RecordEpoch proves such failures stop, adoptions
  being finite; `k0` is after that.
- `when_idle`: housekeeping that writes keeps the round going (`maint`); that it eventually stops
  writing is the premise `hmaint`, the idle-maintenance assumption HubSuffix makes too.

Not given here: that the stable hub accepts what `Emit` sends, which root's packet coupling
and the hub's guards give, and which contradicts its stability; so the composition takes the
right disjunct. Nor that every node is eligible: the composition argues that a node not
aligned with `R` must adopt it (`Take` drops `cr` or `cz`), which the common node cut forbids.
-/

end Musubi.NodeSettle

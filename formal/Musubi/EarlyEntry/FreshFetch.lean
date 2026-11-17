/-
The round after a fresh Fetch and its record-taking laws. The convergence proof uses this file.
-/
import Musubi.EarlyEntry.FreshHead

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-! ### Taking the hub's records after a fresh `Fetch`

Right after an eligible node handles a fresh `Fetch`:
* it has the hub's current records announced, unless it has applied them already and holds no
  receipts;
* every operation below the hub's head that it does not have locally has its body and objects
  there: the reply brought them, the node's drops being the hub's, so that the head's images
  are the head.

Nothing is then missing in its round. So long as the announcement stands, the core adopts it or,
if it drops an op head, merges, realizes and finally advances, taking it (`fresh_fetch_takes`).
Past the cut after which the node takes no more records, the announcement cannot stand, so the
node has the hub's records applied and no receipts (`fresh_fetch_current`). The hub may change
meanwhile; the node's own round keeps its known head. -/

/-- Every raw operation below the known head `H` has a body here (`stg`: staged, or its
canonical body in the node's store), local or not: what a fresh `Fetch` leaves, its objects
aside. Naming does not enter it, so it lasts while bodies are kept, even as naming changes. -/
def RawBodies (par : Nat → List Nat) (H : Nat) (s : State) : Prop :=
  ∀ x, Anc par x H → s.stg x = true

theorem anc_of_walk {par : Nat → List Nat} {loc stg : Nat → Bool} {x y : Nat}
    (h : Anc (walkParents par loc stg) x y) : Anc par x y := by
  induction h with
  | refl => exact Anc.refl
  | step hp _ ih => exact Anc.step (mem_walkParents.1 hp).2.2 ih

/-- With every body here, the survey finds no operation missing. -/
theorem missOpsB_bodies {raw : List Nat} {par : Nat → List Nat} {H : Nat} {s : State}
    (hlt : ParLt par) (h : RawBodies par H s) : missOpsB raw par s.burst.loc s.stg H = false := by
  unfold missOpsB
  apply List.any_eq_false.2
  intro x _
  cases hw : walkB par s.burst.loc s.stg H x
  · simp
  · simp [h x (anc_of_walk ((Exec.ancB_iff (parLt_walkParents hlt)).1 hw))]

/-- What the round right after a fresh `Fetched` reply reads, sampled from the node's actual
events. Data only: its laws are `FetchLaws`. -/
structure FetchData (α : Type) extends RunData α where
  /-- Whether the step is the round's own. -/
  active : Nat → Bool
  /-- Whether the step's `GetObjects` reply lacked what it was asked for. -/
  failed : Nat → Prop
  /-- Whether the node holds receipts at the round's first reading (`prims 0`). That includes
  at least the receipts held right after the reply; the prelude may add some. -/
  receiptsAtStart : Bool

/-- The native laws of that round, as `fresh_fetch_takes` takes them. They are asked of the
round's own steps only, so a round that ends at once has them. `hserve` (no `GetObjects` of the
round fails) is not among them: `fresh_fetch_takes` takes it as a separate argument. -/
structure FetchLaws {α : Type} (d : FetchData α) : Prop extends RunLaws d.toRunData where
  /-- The round's first step is its own. -/
  active_first : d.active 0 = true
  /-- Naming's laws hold. -/
  naming_laws : d.naming.Laws d.par d.H fun i => d.active i = true
  /-- A step that merges, realizes or asks for objects without failing is followed by another. -/
  round_continues : ∀ i, d.active i = true →
    (d.ctl i = .merge ∨ d.ctl i = .realize ∨ (d.ctl i = .objects ∧ ¬ d.failed i)) →
    d.active (i + 1) = true
  /-- The record-credit cut: no adoption, no prepared taking advance. -/
  record_cut : ∀ i, d.active i = true →
    d.ctl i ≠ .adopt ∧ (d.ctl i = .advance → (d.prims i).dropHead = false)
  /-- Every operation below the known head has a body at the round's first step. -/
  bodies_first : RawBodies d.par d.H (d.run 0)
  /-- Bodies staged in the closure stay staged through the round. -/
  bodies_kept : ∀ i, d.active i = true → ∀ x ∈ d.raw, (d.run i).stg x = true →
    (d.run (i + 1)).stg x = true
  /-- An announcement stands past a step that neither adopts nor takes by advancing. -/
  announced_stands : ∀ i, d.active i = true → (d.prims i).announced = true →
    d.ctl i ≠ .adopt → ¬ (d.ctl i = .advance ∧ (d.prims i).dropHead = true) →
    (d.prims (i + 1)).announced = true
  /-- A merge or realize is a checked burst, across a step naming does not change. -/
  burst_step : ∀ i, d.active i = true → d.naming.Still i → (d.ctl i = .merge ∨ d.ctl i = .realize) →
    ∃ k, callB d.raw (d.naming.images i) d.anc (.burst k) (d.run i) (d.after i) = true
  /-- An objects call brings what it was asked for, or its reply lacks it and fails. -/
  objects_step : ∀ i, d.active i = true → d.naming.Still i → d.ctl i = .objects →
    d.failed i ∨
    ((∀ x, walkB d.par (d.run i).burst.loc (d.run i).stg d.H x = true →
      (d.run i).burst.loc x = false → (d.run i).stg x = true → (d.run i).obj x = false →
      (d.after i).obj x = true ∨ (d.after i).burst.loc x = true) ∧
    (d.after i).burst.heads = (d.run i).burst.heads ∧
    (d.after i).burst.plan = (d.run i).burst.plan ∧
    growsB d.raw (d.run i) (d.after i) = true)
  /-- What a step leaves frames the next step's reading, across a step naming does not change. -/
  frame_step : ∀ i, d.active i = true → d.active (i + 1) = true → d.naming.Still i →
    Frame d.raw (d.after i) (d.run (i + 1))

/-- `FetchLaws`, and that the round's first reading announces the hub's records `R` unless the
node, which had applied `ap` when it handled the reply, has applied them and holds no
receipts. -/
structure FetchCurrent {ρ α : Type} (ap R : ρ) (d : FetchData α) : Prop extends FetchLaws d where
  /-- The first reading announces exactly when the node lacks the records or holds receipts. -/
  announced_iff : (d.prims 0).announced = true ↔ (ap ≠ R ∨ d.receiptsAtStart = true)

/-- After a fresh `Fetch` that brought the bodies of the known head's raw closure, an
announcement does not stand through the node's round: with no adoption and no taking advance,
the core would merge, realize and ask for objects forever. `FetchLaws` gives:
* `anc_trans`, `par_lt`, `raw_closure`: the raw graph's laws, from `RunLaws`.
* `active_first`, `round_continues`: `active` marks the round's own core steps from the reply on,
  the known head frozen. The first step is the round's, and a step of it that merges, realizes or
  asks for objects, sending no `Fetch`, is followed by another (the `GetObjects` reply comes, and
  the next core step, fairly). Every other law is asked of those steps only; the run past the
  round's end is arbitrary.
* `record_cut`: no step of the round adopts, nor takes by advancing with a prepared drop, so
  an announcement is not discharged by the core's choice.
* `bodies_first`, `bodies_kept`, `announced_stands`: bodies are kept through the round. Objects
  may not have come with the `Fetch`: a `GetObjects` brings what the survey finds missing, or its
  reply lacks them (`failed`) and the round fails.
* `naming_laws`, `burst_step`, `objects_step`, `frame_step`: naming may change in the round; it
  settles there (`Naming.settles`), and the checked burst and objects laws are asked only of
  steps it does not change across.
* `hserve` is separate: no `GetObjects` of the round fails. This is not a law of the round; it is
  to be derived from the hub keeping what it can serve (the `SerialReply` credit). -/
theorem fresh_fetch_takes {α : Type} {d : FetchData α} (L : FetchLaws d)
    (hserve : ∀ i, d.active i = true → ¬ d.failed i) :
    (d.prims 0).announced = false := by
  cases ha0 : (d.prims 0).announced with
  | false => rfl
  | true =>
    exfalso
    -- standing, the announcement drops an op head, and the round's step merges, realizes or
    -- asks for objects
    have step : ∀ i, d.active i = true → (d.prims i).announced = true →
        RawBodies d.par d.H (d.run i) →
        (d.ctl i = .merge ∨ d.ctl i = .realize ∨ d.ctl i = .objects) ∧
        (d.prims (i + 1)).announced = true ∧ d.active (i + 1) = true ∧
          RawBodies d.par d.H (d.run (i + 1)) := by
      intro i hact ha hb
      have hmo : missOpsB d.raw d.par (d.run i).burst.loc (d.run i).stg d.H = false :=
        missOpsB_bodies L.par_lt hb
      have hrec := L.record_cut i hact
      have hdh : (d.prims i).dropHead = true := by
        cases hd : (d.prims i).dropHead
        · exact absurd (choose_adopt_of (r := d.reads i) ha hd) hrec.1
        · rfl
      have hmr : d.ctl i = .merge ∨ d.ctl i = .realize ∨ d.ctl i = .objects := by
        cases hc' : d.ctl i with
        | adopt => exact absurd hc' hrec.1
        | merge => exact Or.inl rfl
        | realize => exact Or.inr (Or.inl rfl)
        | objects => exact Or.inr (Or.inr rfl)
        | fetch =>
          have h := choose_fetch_missOps hc'
          change missOpsB d.raw d.par (d.run i).burst.loc (d.run i).stg d.H = true at h
          rw [hmo] at h; cases h
        | idle =>
          obtain ⟨hk, hr⟩ := choose_idle_dropHead hdh hc'
          obtain ⟨hmo', hmb'⟩ := choose_idle_survey hc' hk
          rcases rawReads_survey (images := d.naming.images i) (anc := d.anc) (s := d.run i)
              (q := d.prims i) L.par_lt L.raw_closure hk hr with h | h
          · rw [hmo'] at h; cases h
          · rw [hmb'] at h; cases h
        | advance =>
          have h := hrec.2 hc'
          rw [hdh] at h; cases h
        | poll => exact (choose_late_dropHead hdh (Or.inl hc')).elim
        | push => exact (choose_late_dropHead hdh (Or.inr hc')).elim
      have hgo : d.ctl i = .merge ∨ d.ctl i = .realize ∨ (d.ctl i = .objects ∧ ¬ d.failed i) := by
        rcases hmr with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h, hserve i hact⟩)
      refine ⟨hmr, L.announced_stands i hact ha hrec.1 ?_, L.round_continues i hact hgo,
        fun x hx => L.bodies_kept i hact x (L.raw_closure x hx) (hb x hx)⟩
      rintro ⟨hadv, -⟩
      rcases hmr with h | h | h <;> rw [h] at hadv <;> cases hadv
    have hall : ∀ i, d.active i = true ∧ (d.prims i).announced = true ∧
        RawBodies d.par d.H (d.run i) := by
      intro i
      induction i with
      | zero => exact ⟨L.active_first, ha0, L.bodies_first⟩
      | succ i ih =>
        obtain ⟨-, ha', hact', hb'⟩ := step i ih.1 ih.2.1 ih.2.2
        exact ⟨hact', ha', hb'⟩
    -- the round goes on forever with its known head, so naming settles
    obtain ⟨T, hT⟩ := d.naming.settles L.naming_laws fun i => (hall i).1
    apply no_infinite_framed d.raw (d.naming.images T) d.anc L.anc_trans (fun j => d.run (T + j))
      (fun j => d.after (T + j)) _
      (fun j => L.frame_step (T + j) (hall _).1 (hall _).1 (hT (T + j) (by omega)).1)
    intro j
    have hact := (hall (T + j)).1
    obtain ⟨hs, himg⟩ := hT (T + j) (by omega)
    rcases (step (T + j) hact (hall _).2.1 (hall _).2.2).1 with h | h | h
    · obtain ⟨k, hk⟩ := L.burst_step _ hact hs (Or.inl h)
      rw [himg] at hk
      exact callB_sound hk
    · obtain ⟨k, hk⟩ := L.burst_step _ hact hs (Or.inr h)
      rw [himg] at hk
      exact callB_sound hk
    · rcases L.objects_step _ hact hs h with hf | ⟨hbr, hh, hp', hg⟩
      · exact absurd hf (hserve _ hact)
      · exact objects_call (base := surveyBase)
          ((missObjsB_iff L.par_lt L.raw_closure).1 (choose_objects_missObjs h))
          (fun x hw => walk_mem L.raw_closure hw)
          (fun x hw => hbr x ((walkB_iff L.par_lt).2 hw)) hh hp' (growsB_sound hg)

/-- So, past the cut after which the node takes no more records, the node has the hub's records
`R` applied and holds no receipts when it has handled a fresh `Fetch`: the core announces them
otherwise (`FetchCurrent.announced_iff`). Assumes `FetchCurrent`, and, as `fresh_fetch_takes`
does, `hserve`. -/
theorem fresh_fetch_current {ρ α : Type} {ap R : ρ} {d : FetchData α} (L : FetchCurrent ap R d)
    (hserve : ∀ i, d.active i = true → ¬ d.failed i) :
    ap = R ∧ d.receiptsAtStart = false := by
  have h := fresh_fetch_takes L.toFetchLaws hserve
  refine ⟨Classical.byContradiction fun hne => ?_, ?_⟩
  · rw [L.announced_iff.2 (Or.inl hne)] at h; cases h
  · cases hr : d.receiptsAtStart
    · rfl
    · rw [L.announced_iff.2 (Or.inr hr)] at h; cases h

end Musubi.EarlyEntry.Control

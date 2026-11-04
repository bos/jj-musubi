import Musubi.EarlyEntry.FreshHead

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-! ### Taking the hub's records after a fresh `Fetch`

Right after an eligible node handles a fresh `Fetch` it has the hub's current records announced
unless it has applied them already and holds no receipts, and every operation below the hub's
head that it does not have locally has its body and objects there: the reply brought them, the
node's drops being the hub's, so that the head's images are the head. Then, in its round, nothing
is missing: so long as the announcement stands, the core adopts it, or (if it drops an op head)
merges, realizes and finally advances taking it (`fresh_fetch_takes`). Past the cut after which
the node takes no more records, the announcement cannot stand, so the node has the hub's
records applied and no receipts (`fresh_fetch_current`). The hub need not be stable; the node's
own round keeps its known head. -/

/-- Every raw operation below the known head `H` has a body here (`stg`: staged, or its
canonical body in the node's store), local or not: what a fresh `Fetch` leaves, its objects
aside. Naming does not enter it, so it lasts while bodies are kept, as naming changes. -/
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

/-- After a fresh `Fetch` that brought the bodies of the known head's raw closure, an
announcement does not stand through the node's round: with no adoption and no taking advance,
it would have the core merge, realize and ask for objects forever. `active` marks the round's
own core steps from the reply on, the known head frozen: the first step is the round's, and a
step of it that merges, realizes or asks for objects, sending no `Fetch`, is followed by
another (the `GetObjects` reply comes, and the next core step, fairly); every law is asked of
those steps only, and the run past the round's end is arbitrary. Bodies are kept through the
round, but objects need not have come with the `Fetch`: a `GetObjects` brings what the survey
finds missing, or its reply lacks them (`failed`), and the round fails. That no `GetObjects` of
the round fails is no law of the round: `hserve` is to be derived from the hub keeping what it
can serve (the `SerialReply` credit), not assumed as an ordinary failure cutoff. Naming may
change in the round; it settles there (`Naming.settles`), and the checked burst and objects
laws are asked only of steps it does not change across. A round already settled ends at once;
none is assumed to go on. -/
theorem fresh_fetch_takes {α : Type} (raw : List Nat) (nm : Naming α) (par : Nat → List Nat)
    (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (H : Nat) (hraw : ∀ x, Anc par x H → x ∈ raw)
    (run after : Nat → State) (prims : Nat → Prims) (active : Nat → Bool)
    (failed : Nat → Prop)
    (h0 : active 0 = true)
    (hnaming : nm.Laws par H fun i => active i = true)
    (hnext : ∀ i, active i = true →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
        (rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects ∧ ¬ failed i)) →
      active (i + 1) = true)
    (hrecord : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hbodies : RawBodies par H (run 0))
    (hstg : ∀ i, active i = true → ∀ x ∈ raw, (run i).stg x = true → (run (i + 1)).stg x = true)
    (hann : ∀ i, active i = true → (prims i).announced = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt →
      ¬ (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance ∧
        (prims i).dropHead = true) → (prims (i + 1)).announced = true)
    (hburst : ∀ i, active i = true → nm.Still i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hobjects : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects →
      failed i ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg H x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, active i = true → active (i + 1) = true → nm.Still i →
      Frame raw (after i) (run (i + 1)))
    (hserve : ∀ i, active i = true → ¬ failed i) :
    (prims 0).announced = false := by
  cases ha0 : (prims 0).announced with
  | false => rfl
  | true =>
    exfalso
    -- standing, the announcement drops an op head, and the round's step merges, realizes or
    -- asks for objects
    have step : ∀ i, active i = true → (prims i).announced = true → RawBodies par H (run i) →
        (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects) ∧
        (prims (i + 1)).announced = true ∧ active (i + 1) = true ∧
          RawBodies par H (run (i + 1)) := by
      intro i hact ha hb
      have hmo : missOpsB raw par (run i).burst.loc (run i).stg H = false := missOpsB_bodies hlt hb
      have hrec := hrecord i hact
      have hdh : (prims i).dropHead = true := by
        cases hd : (prims i).dropHead
        · exact absurd (choose_adopt_of
            (r := rawReads raw (nm.images i) par anc H (run i) (prims i)) ha hd) hrec.1
        · rfl
      have hmr : rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects := by
        cases hc' : rawControl raw (nm.images i) par anc H (run i) (prims i) with
        | adopt => exact absurd hc' hrec.1
        | merge => exact Or.inl rfl
        | realize => exact Or.inr (Or.inl rfl)
        | objects => exact Or.inr (Or.inr rfl)
        | fetch =>
          have h := choose_fetch_missOps hc'
          change missOpsB raw par (run i).burst.loc (run i).stg H = true at h
          rw [hmo] at h; cases h
        | idle =>
          obtain ⟨hk, hr⟩ := choose_idle_dropHead hdh hc'
          obtain ⟨hmo', hmb'⟩ := choose_idle_survey hc' hk
          rcases rawReads_survey (images := nm.images i) (anc := anc) (s := run i) (q := prims i)
              hlt hraw hk hr with h | h
          · rw [hmo'] at h; cases h
          · rw [hmb'] at h; cases h
        | advance =>
          have h := hrec.2 hc'
          rw [hdh] at h; cases h
        | poll => exact (choose_late_dropHead hdh (Or.inl hc')).elim
        | push => exact (choose_late_dropHead hdh (Or.inr hc')).elim
      have hgo : rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
          rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
          (rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects ∧
            ¬ failed i) := by
        rcases hmr with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨h, hserve i hact⟩)
      refine ⟨hmr, hann i hact ha hrec.1 ?_, hnext i hact hgo,
        fun x hx => hstg i hact x (hraw x hx) (hb x hx)⟩
      rintro ⟨hadv, -⟩
      rcases hmr with h | h | h <;> rw [h] at hadv <;> cases hadv
    have hall : ∀ i, active i = true ∧ (prims i).announced = true ∧
        RawBodies par H (run i) := by
      intro i
      induction i with
      | zero => exact ⟨h0, ha0, hbodies⟩
      | succ i ih =>
        obtain ⟨-, ha', hact', hb'⟩ := step i ih.1 ih.2.1 ih.2.2
        exact ⟨hact', ha', hb'⟩
    -- the round goes on forever with its known head, so naming settles, at a step derived here
    obtain ⟨T, hT⟩ := nm.settles hnaming fun i => (hall i).1
    apply no_infinite_framed raw (nm.images T) anc trans (fun j => run (T + j))
      (fun j => after (T + j)) _
      (fun j => hframe (T + j) (hall _).1 (hall _).1 (hT (T + j) (by omega)).1)
    intro j
    have hact := (hall (T + j)).1
    obtain ⟨hs, himg⟩ := hT (T + j) (by omega)
    rcases (step (T + j) hact (hall _).2.1 (hall _).2.2).1 with h | h | h
    · obtain ⟨k, hk⟩ := hburst _ hact hs (Or.inl h)
      rw [himg] at hk
      exact callB_sound hk
    · obtain ⟨k, hk⟩ := hburst _ hact hs (Or.inr h)
      rw [himg] at hk
      exact callB_sound hk
    · rcases hobjects _ hact hs h with hf | ⟨hbr, hh, hp', hg⟩
      · exact absurd hf (hserve _ hact)
      · exact objects_call (base := surveyBase)
          ((missObjsB_iff hlt hraw).1 (choose_objects_missObjs h))
          (fun x hw => walk_mem hraw hw) (fun x hw => hbr x ((walkB_iff hlt).2 hw)) hh hp'
          (growsB_sound hg)

/-- So, past the cut after which the node takes no more records, the node has the hub's records
`R` applied and holds no receipts when it has handled a fresh `Fetch`: the core announces them
otherwise (`note_announced`). -/
theorem fresh_fetch_current {ρ α : Type} (raw : List Nat) (nm : Naming α) (par : Nat → List Nat)
    (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (H : Nat) (hraw : ∀ x, Anc par x H → x ∈ raw)
    (run after : Nat → State) (prims : Nat → Prims) (active : Nat → Bool)
    (failed : Nat → Prop) (ap R : ρ)
    (receipts : Bool)
    (hnote : (prims 0).announced = true ↔ (ap ≠ R ∨ receipts = true))
    (h0 : active 0 = true)
    (hnaming : nm.Laws par H fun i => active i = true)
    (hnext : ∀ i, active i = true →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
        (rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects ∧ ¬ failed i)) →
      active (i + 1) = true)
    (hrecord : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hbodies : RawBodies par H (run 0))
    (hstg : ∀ i, active i = true → ∀ x ∈ raw, (run i).stg x = true → (run (i + 1)).stg x = true)
    (hann : ∀ i, active i = true → (prims i).announced = true →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt →
      ¬ (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance ∧
        (prims i).dropHead = true) → (prims (i + 1)).announced = true)
    (hburst : ∀ i, active i = true → nm.Still i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hobjects : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects →
      failed i ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg H x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, active i = true → active (i + 1) = true → nm.Still i →
      Frame raw (after i) (run (i + 1)))
    (hserve : ∀ i, active i = true → ¬ failed i) :
    ap = R ∧ receipts = false := by
  have h := fresh_fetch_takes raw nm par anc trans hlt H hraw run after prims active failed h0
    hnaming hnext hrecord hbodies hstg hann hburst hobjects hframe hserve
  refine ⟨Classical.byContradiction fun hne => ?_, ?_⟩
  · rw [hnote.2 (Or.inl hne)] at h; cases h
  · cases hr : receipts
    · rfl
    · rw [hnote.2 (Or.inr hr)] at h; cases h

/-- What the round right after a fresh `Fetched` reply reads, sampled from the node's actual
events: its raw closure, naming (whose images of the known head may change), raw graph and known
head (the fresh one), its core states and reads at its successive steps, which of those are the
round's own (`active`), its core states right after each step's calls complete (`after`), which of
its `GetObjects` replies lacked what they were asked for (`failed`), and the node's receipts after
the reply. Data only: its laws are `FetchLaws`. -/
structure FetchData (α : Type) where
  raw : List Nat
  naming : Naming α
  par : Nat → List Nat
  anc : Nat → Nat → Bool
  H : Nat
  run : Nat → State
  after : Nat → State
  prims : Nat → Prims
  active : Nat → Bool
  failed : Nat → Prop
  receipts : Bool

/-- The native laws of that round, as `fresh_fetch_current` takes them, `ap` being the records the
node had applied when it handled the reply. They are asked of the round's own steps only, so a
round that ends at once has them. That no `GetObjects` of the round fails is not one of them:
`FetchLaws.current` takes it apart. -/
structure FetchLaws {ρ α : Type} (ap R : ρ) (d : FetchData α) : Prop where
  trans : ∀ a b c, d.anc a b = true → d.anc b c = true → d.anc a c = true
  hlt : ParLt d.par
  hraw : ∀ x, Anc d.par x d.H → x ∈ d.raw
  note : (d.prims 0).announced = true ↔ (ap ≠ R ∨ d.receipts = true)
  active0 : d.active 0 = true
  naming : d.naming.Laws d.par d.H fun i => d.active i = true
  next : ∀ i, d.active i = true → (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i)
    (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims
    i) = .realize ∨ (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims i) =
    .objects ∧ ¬ d.failed i)) → d.active (i + 1) = true
  record : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i)
    (d.prims i) ≠ .adopt ∧ (rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims
    i) = .advance → (d.prims i).dropHead = false)
  bodies : RawBodies d.par d.H (d.run 0)
  stg : ∀ i, d.active i = true → ∀ x ∈ d.raw, (d.run i).stg x = true → (d.run (i + 1)).stg x = true
  ann : ∀ i, d.active i = true → (d.prims i).announced = true → rawControl d.raw (d.naming.images i)
    d.par d.anc d.H (d.run i) (d.prims i) ≠ .adopt → ¬ (rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .advance ∧ (d.prims i).dropHead = true) → (d.prims (i +
    1)).announced = true
  burst : ∀ i, d.active i = true → d.naming.Still i → (rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par d.anc d.H
    (d.run i) (d.prims i) = .realize) → ∃ k, callB d.raw (d.naming.images i) d.anc (.burst k) (d.run
    i) (d.after i) = true
  objects : ∀ i, d.active i = true → d.naming.Still i → rawControl d.raw (d.naming.images i) d.par
    d.anc d.H (d.run i) (d.prims i) = .objects → d.failed i ∨ ((∀ x, walkB d.par (d.run i).burst.loc
    (d.run i).stg d.H x = true → (d.run i).burst.loc x = false → (d.run i).stg x = true → (d.run
    i).obj x = false → (d.after i).obj x = true ∨ (d.after i).burst.loc x = true) ∧ (d.after
    i).burst.heads = (d.run i).burst.heads ∧ (d.after i).burst.plan = (d.run i).burst.plan ∧ growsB
    d.raw (d.run i) (d.after i) = true)
  frame : ∀ i, d.active i = true → d.active (i + 1) = true → d.naming.Still i → Frame d.raw (d.after
    i) (d.run (i + 1))

theorem FetchLaws.current {ρ α : Type} {ap R : ρ} {d : FetchData α} (L : FetchLaws ap R d)
    (hserve : ∀ i, d.active i = true → ¬ d.failed i) :
    ap = R ∧ d.receipts = false :=
  fresh_fetch_current
    d.raw d.naming d.par d.anc L.trans L.hlt d.H L.hraw d.run d.after d.prims d.active d.failed
    ap R d.receipts L.note L.active0 L.naming L.next L.record L.bodies L.stg L.ann L.burst
    L.objects L.frame hserve


end Musubi.EarlyEntry.Control

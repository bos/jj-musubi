import Musubi.EarlyEntry.Control

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-! ### Naming, settling inside a frozen round

The core reads its known head's node-space images, and which raw operations are local, through
its naming (`to_node`), which changes as metadata arrives and as pending names normalize, past
the record cut too: no images are fixed for good. But with the known head fixed, naming reads
the metadata of finitely many raw operations only, the head's raw closure and the pending
names (with what a preparation of the announced records may make pending), which only
arrives, and which names are pending, which, past the one preparation from scratch, are renamed
against that one head at most once per original. So inside any round that goes on forever with
its known head fixed, naming settles (`Naming.settles`), at a step derived there, not
assumed. -/

/-- What the core's naming reads at its successive steps, each read after the step's prelude:
the metadata it holds of each raw operation (`facts`), and the raw names its naming takes as
pending drops (`names`: the operands `to_node` reads, a preparation's `Taking.pending`
included), with every raw operation's original (`orig`); the known head's node-space images then
(`images`, the native `to_node` of the known head); the finite raw operations whose metadata
the naming reads (`inputs`); whether, between a step's reading and the next step's, the
announced records are prepared again from scratch (`prep`: `prepare_again_if_moved` does so
whenever the op heads moved, as the core's own merge moves them); and whether the step's reading
has two op heads or more (`multi`). -/
structure Naming (α : Type) where
  inputs : List Nat
  facts : Nat → Nat → Option α
  names : Nat → List Nat
  orig : Nat → Nat
  images : Nat → List Nat
  prep : Nat → Prop
  multi : Nat → Bool

namespace Naming

variable {α : Type} (N : Naming α)

/-- Nothing naming reads changes across step `i`. -/
def Still (i : Nat) : Prop :=
  (∀ x ∈ N.inputs, N.facts (i + 1) x = N.facts i x) ∧ ∀ x, x ∈ N.names (i + 1) ↔ x ∈ N.names i

/-- Naming's native laws over the steps `P` holds of, the known raw head `H` fixed: metadata only
arrives; at two of those steps that agree on the metadata of `inputs` and on which names are
pending, the images agree (the naming's actual dependence, on the actual metadata); the known
head's raw closure holds one version of each original (the hub refuses a push that repeats one);
from a step to the next, both of them `P`'s, with no preparation from scratch between, the
pending names are renamed only to the version of their original below the known head, if it has
one, or leave (`PendingEpoch.PStep`, `name_pending_as`): the announcement being the same
throughout, its first preparation is in the first reading already; a step from one op head or
none leaves one or none (realizing is detached, calls do not move the op heads, an ordinary
advance leaves one, a taking advance and user work are excluded); and a preparation from scratch
comes only where the op heads moved, which, the announcement standing, only the core's merge of
two op heads or more does, leaving one. So such preparations come once at most
(`Naming.settles`), not assumed. -/
structure Laws (N : Naming α) (par : Nat → List Nat) (H : Nat) (P : Nat → Prop) : Prop where
  keep : ∀ i, P i → ∀ x a, N.facts i x = some a → N.facts (i + 1) x = some a
  support : ∀ i j, P i → P j → (∀ x ∈ N.inputs, N.facts i x = N.facts j x) →
    (∀ x, x ∈ N.names i ↔ x ∈ N.names j) → N.images i = N.images j
  unique : ∀ x y, Anc par x H → Anc par y H → N.orig x = N.orig y → x = y
  rename : ∀ i, P i → P (i + 1) → ¬ N.prep i →
    PendingEpoch.PStep par (fun _ => H) N.orig 0 (N.names i) (N.names (i + 1))
  single : ∀ i, P i → P (i + 1) → N.multi i = false → N.multi (i + 1) = false
  prepMerge : ∀ i, P i → P (i + 1) → N.prep i → N.multi i = true ∧ N.multi (i + 1) = false

variable {N}

theorem names_below {T : Nat} (hleave : ∀ i, T ≤ i → ∀ x ∈ N.names (i + 1), x ∈ N.names i) :
    ∀ d, ∀ x ∈ N.names (T + d), x ∈ N.names T
  | 0 => fun _ h => h
  | d + 1 => fun x h => names_below hleave d x (hleave (T + d) (by omega) x h)

/-- Inside a round that goes on forever, its known head fixed, naming settles: past some step,
nothing it reads changes, so neither do the images. Derived from the pointwise laws: past the
one preparation from scratch, if any, renaming against the one known head stops
(`PendingEpoch.pending_names_settle`), then the names only leave, and metadata stops arriving for
the finite inputs (`PendingEpoch.finite_metadata_stabilizes`). No cutoff is assumed. -/
theorem settles {par : Nat → List Nat} {H : Nat} {P : Nat → Prop} (L : N.Laws par H P)
    (hP : ∀ i, P i) :
    ∃ T, ∀ i, T ≤ i → N.Still i ∧ N.images i = N.images T := by
  -- past the preparation from scratch, if any, one op head or none stays so, and none comes
  have hS : ∃ S0, ∀ i, S0 ≤ i → ¬ N.prep i := by
    by_cases h : ∃ i, N.prep i
    · obtain ⟨i0, h0⟩ := h
      have hone : ∀ d, N.multi (i0 + 1 + d) = false := by
        intro d
        induction d with
        | zero => exact (L.prepMerge i0 (hP _) (hP _) h0).2
        | succ d ih => exact L.single _ (hP _) (hP _) ih
      refine ⟨i0 + 1, fun i hi hp => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
      have := (L.prepMerge _ (hP _) (hP _) hp).1
      rw [hone d] at this
      cases this
    · exact ⟨0, fun i _ hp => h ⟨i, hp⟩⟩
  obtain ⟨S0, hS0⟩ := hS
  obtain ⟨T0', hleave'⟩ := PendingEpoch.pending_names_settle
    (hist := fun _ => H) (w := 0) ⟨fun _ _ _ _ => Anc.refl, fun _ _ => L.unique⟩
    (fun t => N.names (S0 + t)) (fun _ => 0) (fun _ => Nat.le_refl 0)
    (fun t => L.rename (S0 + t) (hP _) (hP _) (hS0 _ (by omega)))
  let T0 := S0 + T0'
  have hleave : ∀ i, T0 ≤ i → ∀ x ∈ N.names (i + 1), x ∈ N.names i := by
    intro i hi x hx
    obtain ⟨d, rfl⟩ : ∃ d, i = S0 + d := ⟨i - S0, by omega⟩
    exact hleave' d (by omega) x hx
  obtain ⟨T1, h1⟩ := PendingEpoch.finite_metadata_stabilizes N.inputs N.facts
    (fun t => L.keep t (hP t))
  let m := fun d => ((N.names T0).filter fun x => decide (x ∈ N.names (T0 + d))).length
  have hm : ∀ d, m (d + 1) ≤ m d := fun d =>
    PendingEpoch.filter_len_mono _ _ _ fun x _ h => by
      simp only [decide_eq_true_eq] at h ⊢
      exact hleave (T0 + d) (by omega) x (by simpa [Nat.add_assoc] using h)
  obtain ⟨D, h2⟩ := nat_trace_stabilizes m hm
  have same : ∀ t, T0 + D ≤ t → ∀ x, x ∈ N.names (t + 1) ↔ x ∈ N.names t := by
    intro t ht x
    obtain ⟨d, rfl⟩ : ∃ d, t = T0 + d := ⟨t - T0, by omega⟩
    refine ⟨hleave (T0 + d) (by omega) x, fun hx => Classical.byContradiction fun hn => ?_⟩
    have lt : m (d + 1) < m d :=
      PendingEpoch.filter_len_lt _ _ _
        (fun y _ h => by
          simp only [decide_eq_true_eq] at h ⊢
          exact hleave (T0 + d) (by omega) y (by simpa [Nat.add_assoc] using h))
        ⟨x, names_below hleave d x hx, by simpa using hx,
          by simpa [Nat.add_assoc] using hn⟩
    rw [h2 d (by omega), h2 (d + 1) (by omega)] at lt
    exact Nat.lt_irrefl _ lt
  have stay : ∀ t, T0 + D ≤ t → ∀ x, x ∈ N.names t ↔ x ∈ N.names (T0 + D) := by
    intro t ht x
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    induction d with
    | zero => exact Iff.rfl
    | succ d ih => exact (same (T0 + D + d) (by omega) x).trans (ih (by omega))
  refine ⟨max T1 (T0 + D), fun i hi => ⟨⟨fun x hx => ?_, same i (by omega)⟩, ?_⟩⟩
  · exact (h1 (i + 1) (by omega) x hx).trans (h1 i (by omega) x hx).symm
  · exact L.support i _ (hP i) (hP _)
      (fun x hx => (h1 i (by omega) x hx).trans (h1 (max T1 (T0 + D)) (by omega) x hx).symm)
      (fun x => (stay i (by omega) x).trans (stay (max T1 (T0 + D)) (by omega) x).symm)

end Naming

/-! ### A first fresh head

Before the node first observes a fresh head (a reply from after the record cut naming the hub's
current head, `Head` or `Fetched`; an `Incomplete` answer to a push counts, since the driver
hands it to the core before failing the round, though nothing here says what follows that
failure), its known head, raw closure and offered records stay as they are; its images of that
head may change, as naming does, until naming settles inside the hypothetical frozen round
(`Naming.settles`). Each of its core steps is then chosen as computed (`rawControl`), from the
images then. A step that fetches or polls sends a
`Fetch`, and one that idles is followed by a round that starts with one (fair start); a `Fetch`
completes, naming the hub's head (fair individual call), so either brings a fresh head
(`idle_brings_fresh`). A push gets a `Head` reply, which names it too, when its records are the
hub's and the hub does not drop its new head (`is_dropped`, which is `is_superseded` of that
head as the hub's records name it, rewrites included: a primitive of an honest push, not a
consequence of matching records); one with other records is refused, and the node then hears
the hub's records, which differ from those it offers, so it never pushes again. So, with no
fresh head, the node pushes at most once, and every other step is a burst step or an objects
call, which lower the control rank (`no_infinite_calls`) from where naming settles on: a fresh
head comes (`fresh_head_reached`). No completed round, no eventual fresh head and no naming
cutoff is assumed. -/

/-- What a step's calls bring back, as far as a fresh head goes. -/
inductive Reply
  | none
  | objects
  | fresh
  | refused
  deriving DecidableEq

/-- No fresh head before step `i`. -/
def Before (reply : Nat → Reply) (i : Nat) : Prop := ∀ j, j < i → reply j ≠ .fresh

/-- An idle is followed by a fresh head: the next round starts (fair start), with a `Fetch`, and
the `Fetch` completes naming the hub's head (fair individual call). -/
theorem idle_brings_fresh {reply : Nat → Reply} {starts fetchCall : Nat → Prop} {i : Nat}
    (hstart : ∃ j, i < j ∧ starts j) (hstartFetch : ∀ j, starts j → fetchCall j)
    (hfetchCall : ∀ j, fetchCall j → reply j = .fresh) : ∃ j, i < j ∧ reply j = .fresh := by
  obtain ⟨j, hj, hs⟩ := hstart
  exact ⟨j, hj, hfetchCall j (hstartFetch j hs)⟩

/-- A node observes a fresh head. Its events are core steps (`core`) and round starts (`starts`);
before a fresh head: the record-credit cut (no adoption, no prepared taking advance); `differ` as
the core computes it against the records last heard, which, across a core step that does not idle,
change only by a refusal's (between rounds a notification may change them, but an idle is followed
by a fresh `Fetch` reply anyway); a core step's law by its computed choice (a burst step as
checked; an objects call bringing the objects, or locality, of the walked operations with a body
but not their objects, the op heads and plan as they were and nothing lost, or else, its reply
lacking them, failing the round, so that a round starts after it (the adapter's `stage_objects`
checks they are here, and the driver reopens and starts a round with an initial `Fetch`); a fetch
or poll sending a `Fetch`; an idle followed by a round start); a round starting with a `Fetch`; a
`Fetch` completing fresh; and a push whose reply is refused unless it has the hub's records `R`,
and is fresh when it has them and the hub does not drop it (`pushDropped`, its `is_dropped`). Each
step's law relates its reading to its state right after its calls complete (`after`), and that
state to the next step's reading by a frame (`Frame`: nothing lost, the canonical op heads and the
plan as they were), not one reading to the next directly. That primitive is asked only of a push
with the hub's records: one with other records is refused first, even if its head is newly
superseded at the hub. Naming's laws hold of the steps (metadata only arrives, and the images read
only that of finitely many raw operations) and pending names only leave; the checked burst and
objects laws are asked only of steps naming does not change across. -/
theorem fresh_head_reached {ρ α : Type} [DecidableEq ρ] (raw : List Nat) (nm : Naming α)
    (par : Nat → List Nat) (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (H : Nat) (hraw : ∀ x, Anc par x H → x ∈ raw)
    (run after : Nat → State) (prims : Nat → Prims) (reply : Nat → Reply)
    (core starts fetchCall : Nat → Prop) (pushDropped : Nat → Bool)
    (offered R : ρ) (heard : Nat → Option ρ)
    (hnaming : nm.Laws par H (Before reply))
    (hkind : ∀ i, Before reply i → core i ∨ starts i)
    (hrecord : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .adopt ∧
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance →
        (prims i).dropHead = false))
    (hdiffer : ∀ i, Before reply i → core i → (prims i).differ = match heard i with
      | some h => !decide (h = offered)
      | none => (prims i).pending)
    (hheard : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .idle → reply i ≠ .fresh →
      heard (i + 1) = if reply i = .refused then some R else heard i)
    (hburst : ∀ i, Before reply i → core i → nm.Still i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .realize ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .advance) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hobjects : ∀ i, Before reply i → core i → nm.Still i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .objects →
      (∃ j, i < j ∧ starts j) ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg H x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, Before reply (i + 1) → core i → nm.Still i → Frame raw (after i) (run (i + 1)))
    (hpoll : ∀ i, Before reply i → core i →
      (rawControl raw (nm.images i) par anc H (run i) (prims i) = .fetch ∨
        rawControl raw (nm.images i) par anc H (run i) (prims i) = .poll) → fetchCall i)
    (hstart : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .idle → ∃ j, i < j ∧ starts j)
    (hstartFetch : ∀ j, Before reply j → starts j → fetchCall j)
    (hfetchCall : ∀ j, Before reply j → fetchCall j → reply j = .fresh)
    (hnd : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .push → offered = R →
      pushDropped i = false)
    (hpush : ∀ i, Before reply i → core i →
      rawControl raw (nm.images i) par anc H (run i) (prims i) = .push →
      (offered = R → pushDropped i = false → reply i = .fresh) ∧
      (offered ≠ R → reply i = .refused)) :
    ∃ i, reply i = .fresh := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ i, Before reply i := fun _ j _ h => hno ⟨j, h⟩
  have hcore : ∀ i, core i := by
    intro i
    rcases hkind i (hall i) with h | h
    · exact h
    · exact absurd ⟨i, hfetchCall i (hall i) (hstartFetch i (hall i) h)⟩ hno
  -- the known head stays, so naming settles, at a step derived here
  obtain ⟨T, hT⟩ := nm.settles hnaming hall
  have hcall : ∀ i, T ≤ i → rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .push →
      Call raw (nm.images T) anc (run i) (after i) := by
    intro i hi hp
    have hb := hall i
    have hc' := hcore i
    obtain ⟨hs, himg⟩ := hT i hi
    cases hc : rawControl raw (nm.images i) par anc H (run i) (prims i) with
    | adopt => exact absurd hc (hrecord i hb hc').1
    | merge =>
      obtain ⟨k, hk⟩ := hburst i hb hc' hs (Or.inl hc)
      rw [himg] at hk
      exact callB_sound hk
    | realize =>
      obtain ⟨k, hk⟩ := hburst i hb hc' hs (Or.inr (Or.inl hc))
      rw [himg] at hk
      exact callB_sound hk
    | advance =>
      obtain ⟨k, hk⟩ := hburst i hb hc' hs (Or.inr (Or.inr hc))
      rw [himg] at hk
      exact callB_sound hk
    | fetch => exact absurd ⟨i, hfetchCall i hb (hpoll i hb hc' (Or.inl hc))⟩ hno
    | poll => exact absurd ⟨i, hfetchCall i hb (hpoll i hb hc' (Or.inr hc))⟩ hno
    | idle =>
      obtain ⟨j, -, hj⟩ := idle_brings_fresh (hstart i hb hc' hc)
        (fun j h => hstartFetch j (hall j) h) (fun j h => hfetchCall j (hall j) h)
      exact absurd ⟨j, hj⟩ hno
    | objects =>
      rcases hobjects i hb hc' hs hc with hfail | ⟨hbr, hh, hp', hg⟩
      · -- the reply lacked them: the round fails, and the next one starts with a `Fetch`
        obtain ⟨j, -, hj⟩ := idle_brings_fresh hfail
          (fun j h => hstartFetch j (hall j) h) (fun j h => hfetchCall j (hall j) h)
        exact absurd ⟨j, hj⟩ hno
      · exact objects_call (base := surveyBase)
          ((missObjsB_iff hlt hraw).1 (choose_objects_missObjs hc))
          (fun x hw => walk_mem hraw hw) (fun x hw => hbr x ((walkB_iff hlt).2 hw)) hh hp'
          (growsB_sound hg)
    | push => exact absurd hc hp
  have hnoidle : ∀ i, rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .idle := by
    intro i hc
    obtain ⟨j, -, hj⟩ := idle_brings_fresh (hstart i (hall i) (hcore i) hc)
      (fun j h => hstartFetch j (hall j) h) (fun j h => hfetchCall j (hall j) h)
    exact hno ⟨j, hj⟩
  -- with no push from `S` on, the calls from there go on forever
  have tail : ∀ S, T ≤ S →
      (∀ i, S ≤ i → rawControl raw (nm.images i) par anc H (run i) (prims i) ≠ .push) →
      False := fun S hS hnp =>
    no_infinite_framed raw (nm.images T) anc trans (fun j => run (S + j)) (fun j => after (S + j))
      (fun j => hcall (S + j) (by omega) (hnp (S + j) (by omega)))
      (fun j => hframe (S + j) (hall _) (hcore _) (hT (S + j) (by omega)).1)
  by_cases hp : ∃ i0, rawControl raw (nm.images i0) par anc H (run i0) (prims i0) = .push
  · obtain ⟨i0, hi0⟩ := hp
    have hl := hpush i0 (hall i0) (hcore i0) hi0
    have hoR : offered ≠ R := fun ho =>
      hno ⟨i0, hl.1 ho (hnd i0 (hall i0) (hcore i0) hi0 ho)⟩
    have href : reply i0 = .refused := hl.2 hoR
    have hR : ∀ j, heard (i0 + 1 + j) = some R := by
      intro j
      induction j with
      | zero =>
        have h := hheard i0 (hall i0) (hcore i0) (hnoidle i0) (fun h => hno ⟨i0, h⟩)
        rw [href] at h
        simpa using h
      | succ j ih =>
        have h := hheard (i0 + 1 + j) (hall _) (hcore _) (hnoidle _) (fun h => hno ⟨_, h⟩)
        rw [show i0 + 1 + (j + 1) = i0 + 1 + j + 1 by omega, h]
        split
        · rfl
        · exact ih
    apply tail (max T (i0 + 1)) (Nat.le_max_left _ _)
    intro i hi hc
    obtain ⟨j, rfl⟩ : ∃ j, i = i0 + 1 + j := ⟨i - (i0 + 1), by omega⟩
    have hd := choose_push_differ hc
    have h := hdiffer (i0 + 1 + j) (hall _) (hcore _)
    rw [hR j] at h
    change (prims (i0 + 1 + j)).differ = false at hd
    rw [hd] at h
    simp only at h
    have : R = offered := by
      cases hdec : decide (R = offered)
      · rw [hdec] at h; cases h
      · exact of_decide_eq_true hdec
    exact hoR this.symm
  · exact tail T (Nat.le_refl _) (fun i _ h => hp ⟨i, h⟩)


end Musubi.EarlyEntry.Control

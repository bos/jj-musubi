/-
Naming stabilization inside a frozen round and the first fresh head-bearing reply. The
convergence proof uses this file.
-/
import Musubi.EarlyEntry.Control

namespace Musubi.EarlyEntry.Control

open Musubi NodeSettle

/-! ### Naming, settling inside a frozen round

The core reads its known head's node-space images, and which raw operations are local, through
its naming (`to_node`). Naming changes as metadata arrives and as pending names normalize, even
past the record cut, so no image is fixed for good. With the known head fixed, though, naming
reads the metadata of finitely many raw operations only: the head's raw closure and the pending
names, including whatever a preparation of the announced records makes pending. Metadata only
arrives, and, past the one preparation from scratch, pending names are renamed against that one
head at most once per original. So in any round that goes on forever with its known head fixed,
naming settles (`Naming.settles`) at some step. -/

/-- What the core's naming reads at its successive steps, each read after the step's prelude. -/
structure Naming (α : Type) where
  /-- The finite set of raw operations whose metadata the naming reads. -/
  inputs : List Nat
  /-- `facts i x`: the metadata the core holds of raw operation `x` at step `i`. -/
  facts : Nat → Nat → Option α
  /-- `names i`: the raw names naming takes as pending drops at step `i`: the operands `to_node`
  reads, a preparation's `Taking.pending` included. -/
  names : Nat → List Nat
  /-- Every raw operation's original. -/
  orig : Nat → Nat
  /-- `images i`: the known head's node-space images at step `i` (the native `to_node` of the
  known head). -/
  images : Nat → List Nat
  /-- `prep i`: between the readings of steps `i` and `i + 1`, the announced records are
  prepared again from scratch (`prepare_again_if_moved` does so whenever the op heads moved, as
  the core's own merge moves them). -/
  prep : Nat → Prop
  /-- `multi i`: the reading of step `i` has two op heads or more. -/
  multi : Nat → Bool

namespace Naming

variable {α : Type} (N : Naming α)

/-- Nothing naming reads changes across step `i`. -/
def Still (i : Nat) : Prop :=
  (∀ x ∈ N.inputs, N.facts (i + 1) x = N.facts i x) ∧ ∀ x, x ∈ N.names (i + 1) ↔ x ∈ N.names i

/-- Naming's laws over the steps `P` holds of, with the known raw head `H` fixed:
* `keep`: metadata only arrives.
* `support`: two steps that agree on the metadata of `inputs` and on which names are pending have
  the same images.
* `unique`: the known head's raw closure holds one version of each original (the hub refuses a
  push that repeats one).
* `rename`: from one step to the next, both in `P`, with no preparation from scratch between,
  pending names are renamed only to the version of their original below the known head, if it
  has one, or leave (`PendingEpoch.PStep`, `name_pending_as`). The announcement is the same
  throughout, so its first preparation is already in the first reading.
* `single`: a step from one op head or none leaves one or none (realizing is detached, calls
  do not move the op heads, an ordinary advance leaves one; a taking advance and user work are
  excluded).
* `prepMerge`: a preparation from scratch comes only where the op heads moved, which, the
  announcement standing, only the core's merge of two op heads or more does, leaving one.

So such preparations come once at most (`Naming.settles`). -/
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
nothing it reads changes, so neither do the images. Proof: past the one preparation from scratch,
if any, renaming against the one known head stops (`PendingEpoch.pending_names_settle`), then the
names only leave, and metadata stops arriving for the finite inputs
(`PendingEpoch.finite_metadata_stabilizes`). -/
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

/-! ### One node's round, bundled

Every theorem about a node's entry reads the same run: the raw closure, the naming, the raw graph
and the core's states, each a function of the step. `RunData` holds them once, `RunLaws` the laws
of the raw graph, and the bundles for the rounds that follow extend them: `HeadData` and
`HeadLaws` for the run up to a first fresh head (below), `FetchData` and `FetchLaws` for the round
after a fresh `Fetch` reply (`FreshFetch`), `EntryData` and `EntryLaws` for a node's whole
pre-entry run (`RawEntry`). A step's choice is `RunData.ctl`, so no theorem writes out the
seven arguments of `rawControl`.

The layers are not a chain. `FetchLaws` extends `RunLaws`, not `HeadLaws`, because a fetch round
has its own frozen known head and none of the `reply`, `core`, `starts` or `fetchCall` data that
`HeadLaws` speaks of; `FetchCurrent` adds a third layer, the first reading's announcement. -/

/-- What a node's raw run reads at its successive steps, sampled from its actual events: the part
every round shares. Data only: its laws are `RunLaws`. -/
structure RunData (α : Type) where
  /-- The raw closure of the known head. -/
  raw : List Nat
  /-- The core's naming; its images of the known head may change. -/
  naming : Naming α
  /-- The raw graph: each operation's parents. -/
  par : Nat → List Nat
  /-- The raw ancestry test. -/
  anc : Nat → Nat → Bool
  /-- The known raw head. -/
  H : Nat
  /-- The core state at each sampled step. -/
  run : Nat → State
  /-- The core state right after the step's calls complete. -/
  after : Nat → State
  /-- What the core reads at the step. -/
  prims : Nat → Prims

/-- What the core reads at step `i`, computed raw from the images at that step. -/
abbrev RunData.reads {α : Type} (d : RunData α) (i : Nat) : Reads :=
  rawReads d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims i)

/-- The core's choice at step `i`, computed. -/
abbrev RunData.ctl {α : Type} (d : RunData α) (i : Nat) : Choice :=
  rawControl d.raw (d.naming.images i) d.par d.anc d.H (d.run i) (d.prims i)

/-- The laws of a run's raw graph, asked of every round. -/
structure RunLaws {α : Type} (d : RunData α) : Prop where
  /-- The raw ancestry test is transitive. -/
  anc_trans : ∀ a b c, d.anc a b = true → d.anc b c = true → d.anc a c = true
  /-- Every raw operation's parents have smaller ids. -/
  par_lt : ParLt d.par
  /-- The raw closure holds every ancestor of the known head. -/
  raw_closure : ∀ x, Anc d.par x d.H → x ∈ d.raw

/-! ### A first fresh head

A fresh head is a reply from after the record cut naming the hub's current head: `Head` or
`Fetched`. An `Incomplete` answer to a push counts, since the driver hands it to the core before
failing the round; what follows that failure is not modelled here.

Until the node first observes a fresh head, its known head, raw closure and offered records stay
as they are. Its images of that head may change, as naming does, until naming settles inside the
hypothetical frozen round (`Naming.settles`). Each core step is chosen as computed
(`rawControl`) from the images at that step:

* A step that fetches or polls sends a `Fetch`. One that idles is followed by a round that
  starts with one (fair start). A `Fetch` completes, naming the hub's head (fair individual
  call). So either brings a fresh head (`idle_brings_fresh`).
* A push whose records are the hub's gets a `Head` reply, which names the head too, provided the
  hub does not drop its new head (`is_dropped`, which is `is_superseded` of that head as the
  hub's records name it, rewrites included: a primitive of an honest push, not a consequence of
  matching records).
* A push with other records is refused. The node then hears the hub's records, which differ from
  those it offers, so it never pushes again.

So with no fresh head the node pushes at most once, and every other step is a burst step or an
objects call, which lower the control rank (`no_infinite_calls`) once naming settles. Hence a
fresh head comes (`fresh_head_reached`). -/

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

/-- What a node's run reads until its first fresh reply, sampled from its actual events. Data
only: its laws are `HeadLaws`. -/
structure HeadData (ρ α : Type) extends RunData α where
  /-- What the step's calls bring back. -/
  reply : Nat → Reply
  /-- The step is a core step. -/
  core : Nat → Prop
  /-- The step is a round start. -/
  starts : Nat → Prop
  /-- The step's call is a `Fetch`. -/
  fetchCall : Nat → Prop
  /-- `is_dropped` of a push's new head. -/
  pushDropped : Nat → Bool
  /-- The records the node offers. -/
  offered : ρ
  /-- The records last heard, at each step. -/
  heard : Nat → Option ρ

/-- The laws of that run, as `fresh_head_reached` takes them, `R` being the hub's records: those
of the raw graph (`RunLaws`), which hold throughout, and the others, each asked of the steps
before the first fresh reply only. -/
structure HeadLaws {ρ α : Type} [DecidableEq ρ] (R : ρ) (d : HeadData ρ α) : Prop
    extends RunLaws d.toRunData where
  /-- Naming's laws hold. -/
  naming_laws : d.naming.Laws d.par d.H (Before d.reply)
  /-- A step is a core step or a round start. -/
  step_kind : ∀ i, Before d.reply i → d.core i ∨ d.starts i
  /-- The record-credit cut: a core step does not adopt, nor take by advancing. -/
  record_cut : ∀ i, Before d.reply i → d.core i →
    d.ctl i ≠ .adopt ∧ (d.ctl i = .advance → (d.prims i).dropHead = false)
  /-- A core step's `differ` is as the core computes it against the records last heard. -/
  differ_heard : ∀ i, Before d.reply i → d.core i → (d.prims i).differ = match d.heard i with
    | some h => !decide (h = d.offered)
    | none => (d.prims i).pending
  /-- Across a core step that does not idle, the records heard change only by a refusal. -/
  heard_step : ∀ i, Before d.reply i → d.core i → d.ctl i ≠ .idle → d.reply i ≠ .fresh →
    d.heard (i + 1) = if d.reply i = .refused then some R else d.heard i
  /-- A merge, realize or advance is a checked burst, across a step naming does not change. -/
  burst_step : ∀ i, Before d.reply i → d.core i → d.naming.Still i →
    (d.ctl i = .merge ∨ d.ctl i = .realize ∨ d.ctl i = .advance) →
    ∃ k, callB d.raw (d.naming.images i) d.anc (.burst k) (d.run i) (d.after i) = true
  /-- An objects call brings what it was asked for, or the round fails and another starts. -/
  objects_step : ∀ i, Before d.reply i → d.core i → d.naming.Still i → d.ctl i = .objects →
    (∃ j, i < j ∧ d.starts j) ∨
    ((∀ x, walkB d.par (d.run i).burst.loc (d.run i).stg d.H x = true →
      (d.run i).burst.loc x = false → (d.run i).stg x = true → (d.run i).obj x = false →
      (d.after i).obj x = true ∨ (d.after i).burst.loc x = true) ∧
    (d.after i).burst.heads = (d.run i).burst.heads ∧
    (d.after i).burst.plan = (d.run i).burst.plan ∧
    growsB d.raw (d.run i) (d.after i) = true)
  /-- What a step leaves frames the next step's reading: nothing lost, op heads and plan kept. -/
  frame_step : ∀ i, Before d.reply (i + 1) → d.core i → d.naming.Still i →
    Frame d.raw (d.after i) (d.run (i + 1))
  /-- A step that fetches or polls sends a `Fetch`. -/
  poll_fetches : ∀ i, Before d.reply i → d.core i → (d.ctl i = .fetch ∨ d.ctl i = .poll) →
    d.fetchCall i
  /-- A step that idles is followed by a round start. -/
  idle_restarts : ∀ i, Before d.reply i → d.core i → d.ctl i = .idle → ∃ j, i < j ∧ d.starts j
  /-- A round starts with a `Fetch`. -/
  start_fetches : ∀ j, Before d.reply j → d.starts j → d.fetchCall j
  /-- A `Fetch` completes with a fresh reply. -/
  fetch_fresh : ∀ j, Before d.reply j → d.fetchCall j → d.reply j = .fresh
  /-- The hub does not drop the new head of a push that offers its records. -/
  push_undropped : ∀ i, Before d.reply i → d.core i → d.ctl i = .push → d.offered = R →
    d.pushDropped i = false
  /-- A push with the hub's records, not dropped, is answered fresh; any other is refused. -/
  push_reply : ∀ i, Before d.reply i → d.core i → d.ctl i = .push →
    (d.offered = R → d.pushDropped i = false → d.reply i = .fresh) ∧
    (d.offered ≠ R → d.reply i = .refused)

/-- A node observes a fresh head: some step's reply is fresh. Its events are core steps (`core`)
and round starts (`starts`). `HeadLaws` gives, of every step before a fresh head:
* `naming_laws`: metadata only arrives, the images read only that of finitely many raw
  operations, pending names only leave.
* `record_cut`: the record-credit cut: no adoption, no prepared taking advance.
* `differ_heard`, `heard_step`: `differ` is as the core computes it against the records last
  heard. Across a core step that does not idle, those records change only by a refusal. (Between
  rounds a notification may change them, but an idle is followed by a fresh `Fetch` reply anyway.)
* `burst_step`, `objects_step`: a core step's law follows from its computed choice, asked only of
  steps across which naming does not change. A burst step is as checked. An objects call brings
  the objects, or locality, of the walked operations with a body but not their objects, with the
  op heads and plan as they were and nothing lost; or its reply lacks them and fails the round,
  so that a round starts after it (the adapter's `stage_objects` checks they are here, and the
  driver reopens and starts a round with an initial `Fetch`).
* `frame_step`: each step's law relates its reading to its state right after its calls complete
  (`after`), and that state to the next step's reading by a frame (`Frame`: nothing lost, the
  canonical op heads and the plan as they were).
* `poll_fetches`, `idle_restarts`, `start_fetches`, `fetch_fresh`: a fetch or poll sends a
  `Fetch`; an idle is followed by a round start; a round starts with a `Fetch`; a `Fetch`
  completes fresh.
* `push_undropped`, `push_reply`: a push is refused unless it has the hub's records `R`, and is
  fresh when it has them and the hub does not drop it (`pushDropped`, its `is_dropped`). That
  primitive is asked only of a push with the hub's records: one with other records is refused
  first, even if its head is newly superseded at the hub. -/
theorem fresh_head_reached {ρ α : Type} [DecidableEq ρ] {R : ρ} {d : HeadData ρ α}
    (L : HeadLaws R d) : ∃ i, d.reply i = .fresh := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ i, Before d.reply i := fun _ j _ h => hno ⟨j, h⟩
  have hcore : ∀ i, d.core i := by
    intro i
    rcases L.step_kind i (hall i) with h | h
    · exact h
    · exact absurd ⟨i, L.fetch_fresh i (hall i) (L.start_fetches i (hall i) h)⟩ hno
  -- the known head stays, so naming settles
  obtain ⟨T, hT⟩ := d.naming.settles L.naming_laws hall
  have hcall : ∀ i, T ≤ i → d.ctl i ≠ .push →
      Call d.raw (d.naming.images T) d.anc (d.run i) (d.after i) := by
    intro i hi hp
    have hb := hall i
    have hc' := hcore i
    obtain ⟨hs, himg⟩ := hT i hi
    cases hc : d.ctl i with
    | adopt => exact absurd hc (L.record_cut i hb hc').1
    | merge =>
      obtain ⟨k, hk⟩ := L.burst_step i hb hc' hs (Or.inl hc)
      rw [himg] at hk
      exact callB_sound hk
    | realize =>
      obtain ⟨k, hk⟩ := L.burst_step i hb hc' hs (Or.inr (Or.inl hc))
      rw [himg] at hk
      exact callB_sound hk
    | advance =>
      obtain ⟨k, hk⟩ := L.burst_step i hb hc' hs (Or.inr (Or.inr hc))
      rw [himg] at hk
      exact callB_sound hk
    | fetch => exact absurd ⟨i, L.fetch_fresh i hb (L.poll_fetches i hb hc' (Or.inl hc))⟩ hno
    | poll => exact absurd ⟨i, L.fetch_fresh i hb (L.poll_fetches i hb hc' (Or.inr hc))⟩ hno
    | idle =>
      obtain ⟨j, -, hj⟩ := idle_brings_fresh (L.idle_restarts i hb hc' hc)
        (fun j h => L.start_fetches j (hall j) h) (fun j h => L.fetch_fresh j (hall j) h)
      exact absurd ⟨j, hj⟩ hno
    | objects =>
      rcases L.objects_step i hb hc' hs hc with hfail | ⟨hbr, hh, hp', hg⟩
      · -- the reply lacked them: the round fails, and the next one starts with a `Fetch`
        obtain ⟨j, -, hj⟩ := idle_brings_fresh hfail
          (fun j h => L.start_fetches j (hall j) h) (fun j h => L.fetch_fresh j (hall j) h)
        exact absurd ⟨j, hj⟩ hno
      · exact objects_call (base := surveyBase)
          ((missObjsB_iff L.par_lt L.raw_closure).1 (choose_objects_missObjs hc))
          (fun x hw => walk_mem L.raw_closure hw)
          (fun x hw => hbr x ((walkB_iff L.par_lt).2 hw)) hh hp' (growsB_sound hg)
    | push => exact absurd hc hp
  have hnoidle : ∀ i, d.ctl i ≠ .idle := by
    intro i hc
    obtain ⟨j, -, hj⟩ := idle_brings_fresh (L.idle_restarts i (hall i) (hcore i) hc)
      (fun j h => L.start_fetches j (hall j) h) (fun j h => L.fetch_fresh j (hall j) h)
    exact hno ⟨j, hj⟩
  -- with no push from `S` on, the calls from there go on forever
  have tail : ∀ S, T ≤ S → (∀ i, S ≤ i → d.ctl i ≠ .push) → False := fun S hS hnp =>
    no_infinite_framed d.raw (d.naming.images T) d.anc L.anc_trans (fun j => d.run (S + j))
      (fun j => d.after (S + j)) (fun j => hcall (S + j) (by omega) (hnp (S + j) (by omega)))
      (fun j => L.frame_step (S + j) (hall _) (hcore _) (hT (S + j) (by omega)).1)
  by_cases hp : ∃ i0, d.ctl i0 = .push
  · obtain ⟨i0, hi0⟩ := hp
    have hl := L.push_reply i0 (hall i0) (hcore i0) hi0
    have hoR : d.offered ≠ R := fun ho =>
      hno ⟨i0, hl.1 ho (L.push_undropped i0 (hall i0) (hcore i0) hi0 ho)⟩
    have href : d.reply i0 = .refused := hl.2 hoR
    have hR : ∀ j, d.heard (i0 + 1 + j) = some R := by
      intro j
      induction j with
      | zero =>
        have h := L.heard_step i0 (hall i0) (hcore i0) (hnoidle i0) (fun h => hno ⟨i0, h⟩)
        rw [href] at h
        simpa using h
      | succ j ih =>
        have h := L.heard_step (i0 + 1 + j) (hall _) (hcore _) (hnoidle _) (fun h => hno ⟨_, h⟩)
        rw [show i0 + 1 + (j + 1) = i0 + 1 + j + 1 by omega, h]
        split
        · rfl
        · exact ih
    apply tail (max T (i0 + 1)) (Nat.le_max_left _ _)
    intro i hi hc
    obtain ⟨j, rfl⟩ : ∃ j, i = i0 + 1 + j := ⟨i - (i0 + 1), by omega⟩
    have hd := choose_push_differ hc
    have h := L.differ_heard (i0 + 1 + j) (hall _) (hcore _)
    rw [hR j] at h
    change (d.prims (i0 + 1 + j)).differ = false at hd
    rw [hd] at h
    simp only at h
    have : R = d.offered := by
      cases hdec : decide (R = d.offered)
      · rw [hdec] at h; cases h
      · exact of_decide_eq_true hdec
    exact hoR this.symm
  · exact tail T (Nat.le_refl _) (fun i _ h => hp ⟨i, h⟩)


end Musubi.EarlyEntry.Control

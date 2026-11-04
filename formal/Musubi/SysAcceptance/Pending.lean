/-
Raw control cannot remain pending once the hub and its records have settled.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.
-/
import Musubi.SysAcceptance.Acceptance

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-! ## A pending node on a stable hub

The non-E counterpart of `node_settles_accepted`, on raw ids: a node whose drops stay pending
after the cuts, on a hub that stays as it is, is impossible. Its control is computed from its
states and the bits its native core reports (`Control.rawControl`), never from what it chose;
the survey's guard and the branches it can take are derived (`Control.rawControl_guarded`),
each step's effect is the native law of that step (a burst step checked by `Control.callB`; a
`Fetch` or `GetObjects` reply), so it pushes (`Control.pending_push_reached`). That push is
the core's pending push; the hub's checks of it, each a native law of its own, have the hub
accept it (`RawPublish.stable_no_pendingPush`), and the hub would move. No push is assumed, and
nothing is read in original ids. -/

open Musubi.EarlyEntry.Control in
theorem choose_fetch {r : Reads} (h : choose r = .fetch) : r.missOps = true := by
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

open Musubi.EarlyEntry.Control in
theorem choose_objects {r : Reads} (h : choose r = .objects) : r.missObjs = true := by
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

/-- The hub does not drop the head a push sends: it is no dropped name, no cached renaming key,
and not among the push's own drops. -/
theorem not_dropped_of {named cached : Nat → Bool} {x : Nat} {dropped : List Nat}
    (hnn : named x = false) (hnc : cached x = false) (hnot : x ∉ dropped) :
    ((named x || cached x) || decide (x ∈ dropped)) = false := by
  simpa [hnn, hnc] using hnot

open Musubi.EarlyEntry Musubi.EarlyEntry.Control in
/-- No node keeps drops pending forever on a stable hub, given at each core step of its round
(`active`: the run starts at one, and each of its steps that merges, realizes, advances, fetches
or gets its objects goes on with it): the cuts' bits (nothing announced, no op head dropped by
them, records not differing from those last heard, and the new head of a fix-up never the known
one), with drops pending throughout, the case refuted; the native law of the step it takes (a
burst step as checked; a `Fetch` reply about the stable head giving each operation of the closure
not local a body or locality; a `GetObjects` reply giving each walked operation with a body but
not its objects them, or locality; neither moving the op heads or the plan, nothing lost); and, at
a push, the fields the native core gives it (from the known raw head, the fix-up's head or the op
head, the pending drops), the records it offers, those it last heard and the hub's own, and the
hub's checks of it (its records compared; whether it is dropped, which is the hub's
`is_superseded` of the sent head, a dropped name or a key of its cached renamings, or its
membership in the push's drops: the sent head is a complete canonical body written under the
node's drops that survives them (`normal`), which include the hub's records when the node's
applied ones match; so it is no name those records drop (`hsurvive`), and no key of the hub's
cached renamings, a cached key having a body or ancestor those records drop (`hnoCache`); and it
is not among its own drops; so not dropped, `not_dropped_of`; whether its closure is stored, which
is the executable hub's closure check after it stores this packet together with the hub's other
validations of it (no operation missing or abandoned, no original repeated, `valid`), the sender's
cache covering all the hub lacks of it, so stored, `Exec.packet_upload_closes_split`; and
`descends` naming the known head by its images), the hub, stable, staying.

The states are read off the native ones as inputs: `stg x` when the node has `x`'s body, staged or
canonical; `obj x` only when it has that body and every object the body requires is here, never
when the body is unknown (an unknown body's objects are unknown, so an operation without one is
not ready, and a body arriving that requires objects keeps `Grows`).

`differ` compares the records the node offers with those it last heard (`NodeCore::step`); the hub
compares them with its own. They agree at a push because the hub's records when it handles the
packet are the ones the node last heard (`hheard`). Deriving this needs a current stored value or
a fresh post-cut Head, Fetched or Refused reply, as well as fixed records and no old reply still
to come: draining old replies alone does not update a stored old value. `differ` alone says
nothing of the hub's records.

The hub stays, so the known head does: naming settles inside the run (`Naming.settles`), and the
checked burst, `Fetch` and `GetObjects` laws are asked only of steps naming does not change
across. No naming cutoff is assumed. A `GetObjects` reply may lack what it was asked for
(`failed`), and the round then fails; that none does (`hserve`) is not a law of the run, but is to
be derived from the hub keeping what it can serve (the `SerialReply` credit). The round never ends
(derived): a push at one of its steps would have the hub accept it, and every other step the
guards allow goes on with it; so no notice or round start is read as a core step. -/
theorem no_forever_pending {ρ α : Type} [DecidableEq ρ] (raw : List Nat) (nm : Naming α)
    (par : Nat → List Nat)
    (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (hub : RawPublish.Hub) (hraw : ∀ x, Anc par x hub.head → x ∈ raw)
    (run after : Nat → Control.State) (prims : Nat → Prims)
    (pkt : Nat → RawPublish.Push) (checks : Nat → RawPublish.Checks) (failed : Nat → Prop)
    (active : Nat → Bool) (h0 : active 0 = true)
    (hnaming : nm.Laws par hub.head fun i => active i = true)
    (hnext : ∀ i, active i = true →
      (rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .realize ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .advance ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .fetch ∨
        (rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .objects ∧
          ¬ failed i)) →
      active (i + 1) = true)
    (hguard : ∀ i, active i = true → (prims i).announced = false ∧ (prims i).dropHead = false ∧
      (prims i).differ = false ∧ (prims i).pending = true ∧ (prims i).newIsKnown = false)
    (hburst : ∀ i, active i = true → nm.Still i →
      (rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .realize ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .advance) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hfetch : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .fetch →
      (∀ x ∈ raw, (run i).burst.loc x = false →
        (after i).stg x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true)
    (hobjects : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .objects →
      failed i ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg hub.head x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, active i = true → active (i + 1) = true → nm.Still i →
      Control.Frame raw (after i) (run (i + 1)))
    (hpkt : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (pkt i).expected = hub.head ∧
      (prims i).newIsKnown = decide ((pkt i).new = hub.head) ∧
      (prims i).pending = !(pkt i).dropped.isEmpty ∧
      ∀ h ∈ (run i).burst.heads, anc h (pkt i).new = true)
    (offered : Nat → ρ) (heard : Nat → Option ρ) (current : ρ)
    (hdiffer : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (prims i).differ = match heard i with
        | some h => !decide (h = offered i)
        | none => (prims i).pending)
    (hmatch : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).recordsMatch = decide (offered i = current))
    (hheard : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      heard i = some current)
    (hubNamed hubCached : Nat → Nat → Bool)
    (normal : Nat → Nat → Bool) (valid : Nat → Bool)
    (hdroppedB : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).dropped = ((hubNamed i (pkt i).new || hubCached i (pkt i).new) ||
        decide ((pkt i).new ∈ (pkt i).dropped)))
    (hwitness : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      normal i (pkt i).new = true)
    (hnoCache : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      offered i = current → ∀ y, normal i y = true → hubCached i y = false)
    (hsurvive : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      offered i = current → ∀ y, normal i y = true → hubNamed i y = false)
    (hassert : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (pkt i).new ∉ (pkt i).dropped)
    (es : Nat → Exec.EState) (xp : Nat → Exec.PushPacket) (opBases objectBases : Nat → List Nat)
    (hclosedB : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).closed = (((es i).hubStore (xp i).ops (xp i).objs).closedB (xp i).new && valid i))
    (hvalid : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push → valid i = true)
    (hparF : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      ParLt (es i).parF)
    (hbases : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      ∀ b ∈ opBases i, ClosedAt (Exec.abs (es i)) b)
    (hretained : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      ∀ b ∈ objectBases i, ∀ x, Anc (es i).parF x b → ∀ o ∈ (es i).objsF x, o ∈ (es i).hub.objs)
    (hcovers : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      Exec.UploadCoversSplit (es i) (xp i) (opBases i) (objectBases i))
    (hname : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).descends =
        (!(nm.images i).isEmpty && (nm.images i).all fun j => anc j (pkt i).new))
    (hstable : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      RawPublish.after hub (pkt i) (checks i) = hub)
    (hserve : ∀ i, active i = true → ¬ failed i) :
    False := by
  -- a push at a step of the round has the hub accept it, so the hub would move
  have nopush : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) ≠ .push := by
    intro i hact hpush
    have hi : choose (rawReads raw (nm.images i) par anc hub.head (run i) (prims i)) = .push :=
      hpush
    obtain ⟨hdesc, -, -⟩ := choose_push hi
    obtain ⟨-, -, hd, hp, hn⟩ := hguard i hact
    obtain ⟨he, hnk, hpend, habove⟩ := hpkt i hact hpush
    have b : RawPublish.PendingPush (hub.seq, hub.head) (pkt i) := by
      refine ⟨he, ?_, ?_⟩
      · intro h
        rw [hn] at hnk
        exact absurd (decide_eq_true h) (by rw [← hnk]; exact Bool.false_ne_true)
      · intro h
        rw [hp, h] at hpend
        cases hpend
    have heq : current = offered i := by
      have hdi := hdiffer i hact hpush
      rw [hheard i hact hpush, hd] at hdi
      simp only at hdi
      cases h : decide (current = offered i)
      · rw [h] at hdi; cases hdi
      · exact of_decide_eq_true h
    have hr : (checks i).recordsMatch = true := by
      rw [hmatch i hact hpush]
      exact decide_eq_true heq.symm
    -- the hub does not drop the sent head: no name, no cached key, not among its own drops
    have hnd : (checks i).dropped = false :=
      (hdroppedB i hact hpush).trans (not_dropped_of
        (hsurvive i hact hpush heq.symm _ (hwitness i hact hpush))
        (hnoCache i hact hpush heq.symm _ (hwitness i hact hpush)) (hassert i hact hpush))
    -- and stores its closure, once it stores the packet: the sender's cache covers the rest
    have hcl : (checks i).closed = true := by
      rw [hclosedB i hact hpush, Exec.packet_upload_closes_split (hparF i hact hpush)
        (hbases i hact hpush) (hretained i hact hpush) (hcovers i hact hpush),
        hvalid i hact hpush]
      rfl
    have hdescends : (checks i).descends = true := by
      rw [hname i hact hpush]
      change (!(nm.images i).isEmpty && (run i).burst.heads.any fun h =>
        (nm.images i).all fun j => anc j h) = true at hdesc
      simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hdesc ⊢
      obtain ⟨hne, h, hh, hall⟩ := hdesc
      exact ⟨hne, fun x hx => trans x h _ (hall x hx) (habove h hh)⟩
    exact RawPublish.stable_no_pendingPush b rfl hr hnd hcl hdescends (hstable i hact hpush)
  -- so the round never ends: each of its steps is a burst step or a call, which goes on with it
  have hall : ∀ i, active i = true := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih =>
      obtain ⟨ha, hdh, hd, hp, hn⟩ := hguard i ih
      apply hnext i ih
      rcases rawControl_guarded (images := nm.images i) (anc := anc) (s := run i) (q := prims i)
          hlt hraw ha hdh hd hp hn with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hserve i ih⟩)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact absurd h (nopush i ih)
  -- the hub stays, so does the known head: naming settles, at a step derived here
  obtain ⟨T, hT⟩ := nm.settles hnaming hall
  have hwalk : ∀ (s : Control.State) x,
      Walk (rawSurvey surveyBase par s.burst.loc s.stg s.obj hub.head) x → x ∈ raw :=
    fun _ _ hw => walk_mem hraw hw
  have himg : ∀ j, nm.images (T + j) = nm.images T := fun j => (hT (T + j) (by omega)).2
  have hst : ∀ j, nm.Still (T + j) := fun j => (hT (T + j) (by omega)).1
  obtain ⟨j, hj⟩ := pending_push_reached raw (nm.images T) anc trans (fun j => run (T + j))
    (fun j => after (T + j))
    (fun j => rawReads raw (nm.images T) par anc hub.head (run (T + j)) (prims (T + j)))
    (fun j => hframe (T + j) (hall _) (hall _) (hst j))
    (fun j => hguard (T + j) (hall _))
    (fun j => rawReads_survey hlt hraw)
    (fun j hc => by
      have hc' : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
          (prims (T + j)) = .merge ∨
          rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .realize ∨
          rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .advance := by
        rw [himg j]; exact hc
      obtain ⟨k, hk⟩ := hburst (T + j) (hall _) (hst j) hc'
      rw [himg j] at hk
      simp only [callB, Bool.and_eq_true] at hk
      exact ⟨Burst.stepB_sound hk.2, growsB_sound hk.1⟩)
    (fun j hc => by
      rcases hc with hc | hc
      · have hc' : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .fetch := by rw [himg j]; exact hc
        obtain ⟨hs, hh, hp, hg⟩ := hfetch (T + j) (hall _) (hst j) hc'
        exact fetch_call (base := surveyBase) ((missOpsB_iff hlt hraw).1 (choose_fetch hc))
          (hwalk (run (T + j))) hs hh hp (growsB_sound hg)
      · have hc' : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .objects := by rw [himg j]; exact hc
        obtain ⟨hb, hh, hp, hg⟩ :=
          (hobjects (T + j) (hall _) (hst j) hc').resolve_left (hserve _ (hall _))
        exact objects_call (base := surveyBase)
          ((missObjsB_iff hlt hraw).1 (choose_objects hc)) (hwalk (run (T + j)))
          (fun x hw => hb x ((walkB_iff hlt).2 hw)) hh hp (growsB_sound hg))
  have hpush : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
      (prims (T + j)) = .push := by
    show choose _ = _
    rw [himg j]; exact hj
  exact nopush (T + j) (hall _) hpush

/-! ## Earlier fixed-point argument

The assembled proof uses `not_dropped_of`; this independent lemma retains the stronger
fixed-point alternative for callers that have its premises. -/

/-- (Archived: the proof now goes through `not_dropped_of`, with the cache's cause.) The hub does
not drop the head a push sends. The hub's `is_superseded` is a dropped name (`named`) or a key of
its cached renamings (`cached`): a cached key is renamed (`current_R` of it is not itself,
identity renamings being filtered), and the sent head is fixed by the hub's naming, so it is no
cached key; the sent head is no dropped name; and the push's own drops do not hold it. So
`is_dropped` of it is false. No ancestry witness is used, and `current_R` is not asked of dropped
names outside the hub head's closure, which are named but have no image. -/
theorem not_dropped_fixed {cur : Nat → List Nat} {named cached : Nat → Bool} {x : Nat}
    {dropped : List Nat} (hren : ∀ y, cached y = true → cur y ≠ [y]) (hfix : cur x = [x])
    (hnn : named x = false) (hnot : x ∉ dropped) :
    ((named x || cached x) || decide (x ∈ dropped)) = false := by
  cases hc : cached x
  · simpa [hnn] using hnot
  · exact absurd hfix (hren x hc)

end Musubi.SysAcceptance

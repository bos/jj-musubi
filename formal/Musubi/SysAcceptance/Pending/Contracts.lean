/-
Named interfaces for the pending-node contradiction. The abstract round separates control,
publication checks and the two survival facts derived from native naming. The native view
constructs that round from one actual packet; source laws never assume hub stability or that
object replies succeed.
-/
import Musubi.SysAcceptance.Acceptance

namespace Musubi.SysAcceptance

open Musubi NodeSettle EarlyEntry NodeSys NodeSysEntry SysFreshCuts EarlyEntry.Control

/-- Readings shared by the abstract pending round and its native observation. Agreement
between the executable packet, graph and check readings is supplied by the publication laws. -/
structure PendingInputs (ρ α : Type) where
  raw : List Nat
  naming : Naming α
  par : Nat → List Nat
  anc : Nat → Nat → Bool
  run : Nat → Control.State
  after : Nat → Control.State
  prims : Nat → Prims
  checks : Nat → RawPublish.Checks
  failed : Nat → Prop
  active : Nat → Bool
  offered : Nat → ρ
  heard : Nat → Option ρ
  current : ρ
  hubNamed : Nat → Nat → Bool
  hubCached : Nat → Nat → Bool
  normal : Nat → Nat → Bool
  valid : Nat → Bool
  es : Nat → Exec.EState
  xp : Nat → Exec.PushPacket
  opBases : Nat → List Nat
  objectBases : Nat → List Nat

/-- The abstract round supplies its raw packet separately from the executable reading.
The native adapter below instead derives that packet from the executable one. -/
structure PendingRun (ρ α : Type) extends PendingInputs ρ α where
  pkt : Nat → RawPublish.Push

/-- The core's computed action at an event, under the stable hub's head. -/
abbrev PendingRun.choice (R : PendingRun ρ α) (hub : RawPublish.Hub) (i : Nat) :=
  rawControl R.raw (R.naming.images i) R.par R.anc hub.head (R.run i) (R.prims i)

/-- Local graph, scheduling and checked call effects. -/
structure PendingControl {ρ α : Type} (hub : RawPublish.Hub)
    (R : PendingRun ρ α) : Prop where
  trans : ∀ a b c, R.anc a b = true → R.anc b c = true → R.anc a c = true
  hlt : ParLt R.par
  hraw : ∀ x, Anc R.par x hub.head → x ∈ R.raw
  hnaming : R.naming.Laws R.par hub.head fun i => R.active i = true
  hnext : ∀ i, R.active i = true → (R.choice hub i = .merge ∨ R.choice hub i = .realize ∨
    R.choice hub i = .advance ∨ R.choice hub i = .fetch ∨
    (R.choice hub i = .objects ∧ ¬ R.failed i)) → R.active (i + 1) = true

  /-- The frozen round's guard bits. Natively, `newIsKnown = false` needs complete-body
  normalization and a stable drop mask with the known head local; it does not require a fresh
  id. `normalized_write_ne_known` derives the inequality under that source obligation. -/
  hguard : ∀ i, R.active i = true → (R.prims i).announced = false ∧ (R.prims i).dropHead = false ∧
    (R.prims i).differ = false ∧ (R.prims i).pending = true ∧ (R.prims i).newIsKnown = false
  hburst : ∀ i, R.active i = true → R.naming.Still i →
    (R.choice hub i = .merge ∨ R.choice hub i = .realize ∨ R.choice hub i = .advance) → ∃ k, callB
    R.raw (R.naming.images i) R.anc (.burst k) (R.run i) (R.after i) = true
  hfetch : ∀ i, R.active i = true → R.naming.Still i → R.choice hub i = .fetch → (∀ x ∈ R.raw,
    (R.run i).burst.loc x = false → (R.after i).stg x = true ∨ (R.after i).burst.loc x = true) ∧
    (R.after i).burst.heads = (R.run i).burst.heads ∧ (R.after i).burst.plan =
    (R.run i).burst.plan ∧ growsB R.raw (R.run i) (R.after i) = true
  hobjects : ∀ i, R.active i = true → R.naming.Still i → R.choice hub i = .objects → R.failed i ∨
    ((∀ x, walkB R.par (R.run i).burst.loc (R.run i).stg hub.head x = true → (R.run i).burst.loc x
    = false → (R.run i).stg x = true → (R.run i).obj x = false → (R.after i).obj x = true ∨
    (R.after i).burst.loc x = true) ∧ (R.after i).burst.heads = (R.run i).burst.heads ∧
    (R.after i).burst.plan = (R.run i).burst.plan ∧ growsB R.raw (R.run i) (R.after i) = true)
  hframe : ∀ i, R.active i = true → R.active (i + 1) = true → R.naming.Still i → Control.Frame
    R.raw (R.after i) (R.run (i + 1))

/-- Packet checks, record matching and upload coverage. -/
structure PendingPublication {ρ α : Type} [DecidableEq ρ] (hub : RawPublish.Hub)
    (R : PendingRun ρ α) : Prop where
  hpkt : ∀ i, R.active i = true → R.choice hub i = .push → (R.pkt i).expected = hub.head ∧
    (R.prims i).newIsKnown = decide ((R.pkt i).new = hub.head) ∧ (R.prims i).pending =
    !(R.pkt i).dropped.isEmpty ∧ ∀ h ∈ (R.run i).burst.heads, R.anc h (R.pkt i).new = true
  hdiffer : ∀ i, R.active i = true → R.choice hub i = .push → (R.prims i).differ =
    match R.heard i with
    | some h => !decide (h = R.offered i)
    | none => (R.prims i).pending
  hmatch : ∀ i, R.active i = true → R.choice hub i = .push → (R.checks i).recordsMatch = decide
    (R.offered i = R.current)
  hheard : ∀ i, R.active i = true → R.choice hub i = .push → R.heard i = some R.current
  hdroppedB : ∀ i, R.active i = true → R.choice hub i = .push → (R.checks i).dropped =
    ((R.hubNamed i (R.pkt i).new || R.hubCached i (R.pkt i).new) || decide ((R.pkt i).new ∈
    (R.pkt i).dropped))
  hwitness : ∀ i, R.active i = true → R.choice hub i = .push → R.normal i (R.pkt i).new = true
  hassert : ∀ i, R.active i = true → R.choice hub i = .push → (R.pkt i).new ∉ (R.pkt i).dropped
  hclosedB : ∀ i, R.active i = true → R.choice hub i = .push → (R.checks i).closed =
    (((R.es i).hubStore (R.xp i).ops (R.xp i).objs).closedB (R.xp i).new && R.valid i)
  hvalid : ∀ i, R.active i = true → R.choice hub i = .push → R.valid i = true
  hparF : ∀ i, R.active i = true → R.choice hub i = .push → ParLt (R.es i).parF
  hbases : ∀ i, R.active i = true → R.choice hub i = .push → ∀ b ∈ R.opBases i, ClosedAt (Exec.abs
    (R.es i)) b
  hretained : ∀ i, R.active i = true → R.choice hub i = .push → ∀ b ∈ R.objectBases i, ∀ x, Anc
    (R.es i).parF x b → ∀ o ∈ (R.es i).objsF x, o ∈ (R.es i).hub.objs
  hcovers : ∀ i, R.active i = true → R.choice hub i = .push → Exec.UploadCoversSplit (R.es i)
    (R.xp i) (R.opBases i) (R.objectBases i)
  hname : ∀ i, R.active i = true → R.choice hub i = .push → (R.checks i).descends =
    (!(R.naming.images i).isEmpty && (R.naming.images i).all fun j => R.anc j (R.pkt i).new)

/-- Survival facts derived from native naming. -/
structure PendingSurvival {ρ α : Type} (hub : RawPublish.Hub)
    (R : PendingRun ρ α) : Prop where
  hnoCache : ∀ i, R.active i = true → R.choice hub i = .push → R.offered i = R.current → ∀ y,
    R.normal i y = true → R.hubCached i y = false
  hsurvive : ∀ i, R.active i = true → R.choice hub i = .push → R.offered i = R.current → ∀ y,
    R.normal i y = true → R.hubNamed i y = false

/-- Native observations of one node's frozen round. Naming, raw graph, calls and completed
states come from its actual events. `xp` is the immutable executable packet; `pkt` below is
its raw projection. Original identities, node/hub drops and record encoding supply the native
naming facts from which the abstract survival interface is derived. -/
structure PendingData (ρ α : Type) extends PendingInputs ρ α where
  pushes : Nat → Prop
  orig : Nat → Nat
  nodeD : Nat → Nat → Bool
  hubD : Nat → Nat → Bool

/-- The push as `Push::answer` reads it, raw: a view of the one packet the node sends. -/
def PendingData.pkt {ρ α : Type} (d : PendingData ρ α) (i : Nat) : RawPublish.Push :=
  ⟨(d.xp i).expected, (d.xp i).new, (d.xp i).pending⟩

/-- Read the abstract pending round from this same native observation. -/
def PendingData.toRun (d : PendingData ρ α) : PendingRun ρ α where
  toPendingInputs := d.toPendingInputs
  pkt := d.pkt

/-- Native obligations beyond the shared control and publication laws. Survival of the sent
body and exclusion from cached renamings are derived below. `hsend` connects the computed push
to its actual call. Completion of that call and success of object replies remain separate
premises of `PendingLaws.absurd`. -/
structure PendingLaws {ρ α : Type} [DecidableEq ρ] (hub : RawPublish.Hub)
    (d : PendingData ρ α) : Prop
    extends PendingControl hub d.toRun, PendingPublication hub d.toRun where
  /-- A complete canonical body under the node's drops: its whole body closure is present, and
  its whole raw ancestry, root included and not only its parents, survives the node's drops (the
  closure's presence is not used here). -/
  hnormalDef : ∀ i, d.active i = true → d.toRun.choice hub i = .push → ∀ y, d.normal i y = true →
    ∀ z, Anc d.par z y → d.nodeD i (d.orig z) = false

  /-- A raw name the hub's records drop has its original dropped by them. One way only: names
  are raw, and other versions of the same original need not be named. -/
  hnamedDef : ∀ i, d.active i = true → d.toRun.choice hub i = .push → ∀ y, d.hubNamed i y = true →
    d.hubD i (d.orig y) = true

  /-- A cached renaming exists because the hub's records drop the key's body or an ancestor of
  it (the native contraction and its composed cache). -/
  hcachedCause : ∀ i, d.active i = true → d.toRun.choice hub i = .push → ∀ y, d.hubCached i y =
    true → ∃ z, Anc d.par z y ∧ d.hubD i (d.orig z) = true

  /-- With the records it offers the hub's, the node drops at least what they drop. -/
  hdropsSub : ∀ i, d.active i = true → d.toRun.choice hub i = .push → d.offered i = d.current → ∀
    o, d.hubD i o = true → d.nodeD i o = true
  hsend : ∀ i, d.active i = true → d.toRun.choice hub i = .push → d.pushes i

open Musubi.EarlyEntry.Control in
/-- A normal body is no raw name the hub's records drop when the node offers them: a named one
has its original dropped by them, so by the node, while the body itself survives the node's
drops (`NodeSys.Exec.unsuperseded_of_normal`). -/
theorem PendingLaws.hsurviveOf {ρ α : Type} [DecidableEq ρ] {hub : RawPublish.Hub}
    {d : PendingData ρ α} (L : PendingLaws hub d) : ∀ i, d.active i = true →
    rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run i) (d.prims i) = .push →
    d.offered i = d.current → ∀ y, d.normal i y = true → d.hubNamed i y = false := by
  intro i hact hpush heq y hy
  exact (Exec.unsuperseded_of_normal (L.hnormalDef i hact hpush y hy)
    (L.hdropsSub i hact hpush heq) (L.hnamedDef i hact hpush y)
    (L.hcachedCause i hact hpush y)).1

open Musubi.EarlyEntry.Control in
/-- A normal body is no key of the hub's cached renamings when the node offers the hub's
records: a cached key has a body or ancestor those records drop, so the node drops it too, while
the normal body's whole ancestry survives the node's drops
(`NodeSys.Exec.unsuperseded_of_normal`). -/
theorem PendingLaws.hnoCacheOf {ρ α : Type} [DecidableEq ρ] {hub : RawPublish.Hub}
    {d : PendingData ρ α} (L : PendingLaws hub d) : ∀ i, d.active i = true →
    rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run i) (d.prims i) = .push →
    d.offered i = d.current → ∀ y, d.normal i y = true → d.hubCached i y = false := by
  intro i hact hpush heq y hy
  exact (Exec.unsuperseded_of_normal (L.hnormalDef i hact hpush y hy)
    (L.hdropsSub i hact hpush heq) (L.hnamedDef i hact hpush y)
    (L.hcachedCause i hact hpush y)).2

end Musubi.SysAcceptance

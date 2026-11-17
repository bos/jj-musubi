/-
Observations of one actual hive run, grouped by responsibility. These structures contain data
only. `HiveContracts` supplies source, completion and fairness laws; the sampled views below
read this same data at each node's own events.

The convergence proof uses this file.
-/
import Musubi.SysAcceptance.Pending.Contracts

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

namespace Observation

/-! ## Sampling and batch completion -/

/-- `sched n p` is the hive time of node `n`'s `p`th sampled event. `doneAt n t` is the
completion time of the event starting at `t` (or `t` if it sends no calls). `latch n t`
names the last completed batch or post-prelude reading held by the system at `t`.
A batch's result and the next event's reading are separate observations. -/
structure Schedule where
  sched : (node event : Nat) → Nat
  doneAt : (node time : Nat) → Nat
  latch : (node time : Nat) → Nat
  roundId : (node time : Nat) → Nat

/-! ## Node control -/

/-- At a sampled event, `ctl` is the post-prelude reading; just after its batch completes,
it is the state the step left. `active` says which events belong to a running round. -/
structure Control where
  ctl : (node time : Nat) → EarlyEntry.Control.State
  prims : (node time : Nat) → EarlyEntry.Control.Prims
  reply : (node time : Nat) → EarlyEntry.Control.Reply
  core : (node time : Nat) → Prop
  starts : (node time : Nat) → Prop
  fetchCall : (node time : Nat) → Prop
  pushDropped : (node time : Nat) → Bool
  reopen : (node time : Nat) → Prop
  active : (node time : Nat) → Bool

/-! ## Records and entry -/

/-- Records heard, applied and announced are native identities of type `ρ`. The remaining
readings describe the node's raw entry and the result of its publication checks. -/
structure Records (ρ : Type) where
  heard : (node time : Nat) → Option ρ
  applied : (node time : Nat) → ρ
  annc : (node time : Nat) → Option ρ
  receipts : (node time : Nat) → Bool
  incomplete : (node time : Nat) → Bool
  expectedIsHead : (node time : Nat) → Bool
  closed : (node time : Nat) → Bool

/-! ## Naming and the raw graph -/

/-- Naming starts with the raw closure, pending names (including preparation's first
announcement) and retained work a preparation may make pending. `facts` is the metadata
held then; `orig` identifies each raw operation's original. `images` names the known head's
images. `prep` says the announced records are prepared again from scratch between events.
`par` and `anc` are that node's graph readings, not a separately chosen history. -/
structure Naming (α : Type) where
  raw : (node time : Nat) → List Nat
  facts : (node time op : Nat) → Option α
  names : (node time : Nat) → List Nat
  retained : (node time : Nat) → List Nat
  orig : Nat → Nat
  images : (node time : Nat) → List Nat
  prep : (node time : Nat) → Prop
  par : (node time op : Nat) → List Nat
  anc : (node time op : Nat) → Nat → Bool

/-! ## One immutable push and its handling -/

/-- `pushPacket` is the actual sent packet; `HiveObs.pkt` derives its raw view. The checks,
hub naming, cache and store are read when that packet is handled (`answerAt`). `normal`
means a complete canonical body under the sender's drops, including pending drops;
an identity fallback is insufficient. `nodeDrop` and `hubDrop` refer to originals.
`valid` covers the hub's other validations. The two base lists are the sender's omitted
operation and object bases, respectively. -/
structure Publication where
  checks : (node time : Nat) → RawPublish.Checks
  hubNamed : (node time op : Nat) → Bool
  hubCached : (node time op : Nat) → Bool
  normal : (node time op : Nat) → Bool
  nodeDrop : (node time op : Nat) → Bool
  hubDrop : (node time op : Nat) → Bool
  valid : (node time : Nat) → Bool
  pushStore : (node time : Nat) → Exec.EState
  pushPacket : (node time : Nat) → Exec.PushPacket
  opBases : (node time : Nat) → List Nat
  objectBases : (node time : Nat) → List Nat
  pushes : (node time : Nat) → Prop
  answerAt : (node time : Nat) → Nat

/-! ## Calls, replies and notifications -/

/-- `inbox` contains the shared request counter and live slots; a reopen retires slots without
resetting the counter. An `own` reply is head-bearing (`Head` or `Fetched`), identified by
its call id and the capture time of its hub state, not its wire time. A `note` names the
state just after its publishing accept. `callAt` gives each call's start time. For a cut
`c`, `oldNotes c` counts both in-flight and queued notices published before `c`. -/
structure Transport where
  inbox : (node time : Nat) → Retry.Inbox
  own : (node time : Nat) → Option (Nat × Nat)
  note : (node time : Nat) → Option Nat
  callAt : (node id : Nat) → Nat
  oldNotes : (cut node time : Nat) → Retry.Notifications.State

/-! ## Failures, object credit and semantic writes -/

/-- `objFail` means staging a `GetObjects` reply failed because it lacked requested objects;
the batch fails too. `objReady` is unspent object credit: targets are servable and claimed
haves (the implicit base included) are true, or recovery is under way and sends nothing
before reopening. `lost` invalidates that credit: a remade hub, lost hub objects, local gc
or a cached have becoming false. `ioFail` records ordinary I/O or transport failure. -/
structure Environment where
  objFail : (node time : Nat) → Prop
  objReady : (node time : Nat) → Bool
  lost : Nat → Prop
  ioFail : Nat → Prop
  /-- Node `n`'s own code makes, at hive time `t`, a semantic write no protocol step accounts
  for: idle housekeeping (`when_idle`: `show_other_workspaces`,
  `replace_abandoned_working_copies`, `record_forget_after`, `expire_idle`); the round's prelude
  (`before_sync`: `show_other_workspaces`); `advance_to`'s working-copy
  cleanup (`replace_abandoned_working_copies`, and `move_taken_workspaces` after a taking); the
  pass-on of a user's `jj op abandon` (`check_abandon`), which can come after the user's work;
  and the reparenting of late operations after a renaming (`reparent_late`). Not the git export
  copy (the same canonical form), the fix-up's write (`WriteRes`), a realization, a merge or
  the taking of records, which the model's steps account for. -/
  autoWrite : (node time : Nat) → Prop
  userWork : (node time : Nat) → Prop

/-! ## Knowledge and accepted history -/

/-- The node's known pair and the hub history it refers to. `known` is a raw head and `seq`
its sequence. `hist` indexes accepted heads in the hub's last generation. -/
structure Knowledge where
  known : (node time : Nat) → Nat
  seq : (node time : Nat) → Nat
  /-- The root operation. -/
  root : Nat
  hist : Nat → Nat

end Observation

/-- All views of one hive execution. Inheritance keeps each field directly accessible while
its declaration lives with the observations that explain it. No view carries its own run. -/
structure HiveObs (ρ α : Type) extends Observation.Schedule, Observation.Control,
    Observation.Records ρ, Observation.Naming α, Observation.Publication,
    Observation.Transport, Observation.Environment, Observation.Knowledge

namespace HiveObs

open Musubi.EarlyEntry.Control

variable {ρ α : Type} (O : HiveObs ρ α)

/-- The push node `n` sends at `t` as `Push::answer` reads it, raw: a view of the one packet. -/
def pkt (n t : Nat) : RawPublish.Push :=
  ⟨(O.pushPacket n t).expected, (O.pushPacket n t).new, (O.pushPacket n t).pending⟩

/-- A node's entry reading at hive time `t`. -/
def rawAt (n t : Nat) : RawNode ρ := ⟨O.applied n t, O.seq n t, O.annc n t, O.receipts n t⟩

/-- Node `n`'s naming from its `p`th scheduled event, its known head as it was then: the inputs
are that head's raw closure, the names pending then (its first preparation of the announcement
included) and what a preparation may make pending (a later name is one of those, or a renaming
of one to a version below that head), and its steps are `n`'s events. -/
def naming (n p : Nat) : Naming α where
  inputs := O.raw n (O.sched n p) ++ O.names n (O.sched n p) ++ O.retained n (O.sched n p)
  facts := fun m => O.facts n (O.sched n (p + m))
  names := fun m => O.names n (O.sched n (p + m))
  orig := O.orig
  images := fun m => O.images n (O.sched n (p + m))
  prep := fun m => O.prep n (O.sched n (p + m))
  multi := fun m => decide (2 ≤ (O.ctl n (O.sched n (p + m))).burst.heads.length)

/-- Whether node `n`'s events from its `p`th to its `(p + m)`th are all its round's own, in the
round of the first: once one is not, none later is, so no later round is read as this one. -/
def roundActive (n p m : Nat) : Bool :=
  (List.range (m + 1)).all fun m' =>
    O.active n (O.sched n (p + m')) && decide (O.roundId n (O.sched n (p + m')) =
      O.roundId n (O.sched n p))

/-- The round of node `n` from its `p`th scheduled event: its reading then, and its events. -/
def fetchData (n p : Nat) : FetchData α where
  raw := O.raw n (O.sched n p)
  naming := O.naming n p
  par := O.par n (O.sched n p)
  anc := O.anc n (O.sched n p)
  H := O.known n (O.sched n p)
  run := fun m => O.ctl n (O.sched n (p + m))
  after := fun m => O.ctl n (O.doneAt n (O.sched n (p + m)) + 1)
  prims := fun m => O.prims n (O.sched n (p + m))
  active := fun m => O.roundActive n p m
  failed := fun m => O.objFail n (O.sched n (p + m))
  receipts := O.receipts n (O.sched n p)

/-- Node `n`'s pre-entry run from its `p`th scheduled event: each sampled step is that event,
what it leaves is the node's reading right after its calls' batch completes, and the round after
a fresh reply is the node's run from its next scheduled event. -/
def entryData (n p : Nat) : EntryData ρ α where
  raw := O.raw n (O.sched n p)
  naming := O.naming n p
  par := O.par n (O.sched n p)
  anc := O.anc n (O.sched n p)
  H := O.known n (O.sched n p)
  run := fun j => O.ctl n (O.sched n (p + j))
  after := fun j => O.ctl n (O.doneAt n (O.sched n (p + j)) + 1)
  prims := fun j => O.prims n (O.sched n (p + j))
  reply := fun j => O.reply n (O.sched n (p + j))
  core := fun j => O.core n (O.sched n (p + j))
  starts := fun j => O.starts n (O.sched n (p + j))
  fetchCall := fun j => O.fetchCall n (O.sched n (p + j))
  pushDropped := fun j => O.pushDropped n (O.sched n (p + j))
  offered := O.applied n (O.sched n p)
  heard := fun j => O.heard n (O.sched n (p + j))
  ap := fun j => O.applied n (O.doneAt n (O.sched n (p + j)) + 1)
  seqAfter := fun j => O.seq n (O.doneAt n (O.sched n (p + j)) + 1)
  anncAfter := fun j => O.annc n (O.doneAt n (O.sched n (p + j)) + 1)
  receipts := fun j => O.receipts n (O.sched n (p + j))
  receiptsAfter := fun j => O.receipts n (O.doneAt n (O.sched n (p + j)) + 1)
  incomplete := fun j => O.incomplete n (O.sched n (p + j))
  expectedIsHead := fun j => O.expectedIsHead n (O.sched n (p + j))
  closed := fun j => O.closed n (O.sched n (p + j))
  round := fun j => O.fetchData n (p + j + 1)
  annc := fun j => O.annc n (O.sched n (p + j))

/-- Node `n`'s run from its `p`th scheduled event on a hub that stays, the hub's records being
`current`. -/
def pendingData (n p : Nat) (current : ρ) : PendingData ρ α where
  raw := O.raw n (O.sched n p)
  naming := O.naming n p
  par := O.par n (O.sched n p)
  anc := O.anc n (O.sched n p)
  run := fun j => O.ctl n (O.sched n (p + j))
  after := fun j => O.ctl n (O.doneAt n (O.sched n (p + j)) + 1)
  prims := fun j => O.prims n (O.sched n (p + j))
  checks := fun j => O.checks n (O.sched n (p + j))
  failed := fun j => O.objFail n (O.sched n (p + j))
  active := fun j => O.roundActive n p j
  offered := fun j => O.applied n (O.sched n (p + j))
  heard := fun j => O.heard n (O.sched n (p + j))
  current := current
  pushes := fun j => O.pushes n (O.sched n (p + j))
  hubNamed := fun j => O.hubNamed n (O.sched n (p + j))
  hubCached := fun j => O.hubCached n (O.sched n (p + j))
  normal := fun j => O.normal n (O.sched n (p + j))
  orig := O.orig
  nodeD := fun j => O.nodeDrop n (O.sched n (p + j))
  hubD := fun j => O.hubDrop n (O.sched n (p + j))
  valid := fun j => O.valid n (O.sched n (p + j))
  es := fun j => O.pushStore n (O.sched n (p + j))
  xp := fun j => O.pushPacket n (O.sched n (p + j))
  opBases := fun j => O.opBases n (O.sched n (p + j))
  objectBases := fun j => O.objectBases n (O.sched n (p + j))

theorem roundActive_zero {n p : Nat} (h : O.active n (O.sched n p) = true) :
    O.roundActive n p 0 = true := by
  simp [roundActive, h]

end HiveObs

end Musubi.SysAcceptance

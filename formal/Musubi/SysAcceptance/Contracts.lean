/-
Observations, record cuts, and the source and scheduling contracts of one actual hive run.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.
-/
import Musubi.SysAcceptance.Eligible
import Musubi.SysAcceptance.Events

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-! ## The hive converges

One actual run of the hive, read through what each part of the proof reads of it: the hub's
records and every node's dropped originals (`recs`); every node's record control (`epoch`, with
its adoptions and stale-plan failures); every node's actual events, sampled through its schedule
(`HiveObs`: its core state, reads, replies, pushes and the hub's checks of them, records heard,
applied and announced, receipts, its round readings); and the fine system's observation (`run`,
`acts`). Each run the proof reads of a node is its actual sampled events
(`HiveObs.entryData`, `HiveObs.pendingData`, `HiveObs.fetchData`), never one chosen apart from
them, and the native laws of each phase (`HiveContracts`) are laws of those events, each asked
only while its phase holds. From them the hub settles, and every node settles at its head
(`hive_converges`): records and drops stop changing (`Exec.record_and_drop_sets_stabilize`), then
adoptions and stale-plan failures (`Retry.Records.record_disturbances_stop`); every node enters
and stays entered (`EarlyEntry.Control.EntryLaws.enters`, `raw_entry_persists`); the eligible
nodes' system converges (`FineAt.converges`), so the hub is stable; and the laws of a node that is
not eligible, there, are contradictory (`PendingLaws.absurd`, the hub staying put through each
push it sends by `answer` and the stable hub), so every node is eligible. -/

open Musubi.EarlyEntry.Control in
/-- Every node's actual events, sampled through its schedule (`sched n p`, the hive time of its
`p`th scheduled core event or round start), and what it reads and does at each hive time (its
control state `ctl`: at a sampled event, its step's reading after the prelude; right after a batch
completes, what the step left): among them its naming's inputs (the metadata it holds, `facts`;
the names its naming takes as pending, `names`, a preparation's included; and what it applied
beyond the records it shares with those announced, which a preparation may make pending,
`retained`), every raw operation's original (`orig`), its images of the known head then
(`images`), whether the announced records are prepared again from scratch between its event then
and its next (`prep`), and the round its event belongs to (`roundId`); whether its core step sends
a push (`pushes`), and the hive time at which the hub handles that push (`answerAt`); for each
push, the hub's naming when it handles it (`hubNamed`, `hubCached`), which ids are complete
canonical bodies written under the node's drops that survive them (`normal`), the originals the
node's drops and the hub's records drop then (`nodeDrop`, `hubDrop`), whether the hub's other
validations pass (`valid`), the hub's store then (`pushStore`), THE packet, in the executable
model (`pushPacket`; `pkt` is its raw view, by definition), how records are encoded in a packet
(`recOf`), and the bases the sender's cache leaves out (`opBases`, `objectBases`); whether the
`GetObjects` reply it handles then lacked what it asked for (`objFail`: the adapter's
`stage_objects` then fails, and so does the round); whether its object credit is unspent
(`objReady`: every target left in its `Fetch` and `GetObjects` batch is one the hub can serve and
every have it claims, the implicit base one included, is true, or its recovery from a failed reply
is under way, sending nothing more before the reopen); and whether the environment invalidates
what its object credit counts on then (`lost`: the hub remade, the hub losing objects, the node's
own gc or a cached have no longer true); whether an ordinary I/O or transport failure happens then
(`ioFail`); whether its own code makes an automatic semantic write then, one no protocol step
accounts for (`autoWrite`, its field's doc lists them); whether its user works in the repository
then (`userWork`); the root
operation (`root`); its transport's call slots (`inbox`, `Retry.Inbox`: the shared counter of
request ids and the live slots, which a reopen disconnects and no reopen resets); the own
head-bearing reply (`Head` or `Fetched`, not `Objects` nor `Refused`) it handles then, if any, by
its call's id and the hive time whose hub state its head is (`own`: the hub's state right after it
answered, a capture time, not a wire time); the notice it handles then, if any, by the hive time
whose hub state it names (`note`: right after the accept it publishes); the hive time it starts
each call, by id (`callAt`); the hive time of the completed snapshot the `Sys` model holds of the
node, the end of its last completed batch or its last post-prelude reading (`latch`: the model
handles a batch at once, the driver each reply); the hub's head at each sequence number in its
last generation (`hist`); for each of its sampled events, the hive time its calls' batch
completes, the last of their replies handled (`doneAt`, the event's own time if it sends nothing);
and, for each cut `c`, the notices published before `c` it has in flight and queued (`oldNotes c`,
`Retry.Notifications`). -/
structure HiveObs (ρ α : Type) where
  sched : Nat → Nat → Nat
  ctl : Nat → Nat → EarlyEntry.Control.State
  prims : Nat → Nat → EarlyEntry.Control.Prims
  reply : Nat → Nat → EarlyEntry.Control.Reply
  core : Nat → Nat → Prop
  starts : Nat → Nat → Prop
  fetchCall : Nat → Nat → Prop
  pushDropped : Nat → Nat → Bool
  heard : Nat → Nat → Option ρ
  applied : Nat → Nat → ρ
  seq : Nat → Nat → Nat
  annc : Nat → Nat → Option ρ
  receipts : Nat → Nat → Bool
  incomplete : Nat → Nat → Bool
  expectedIsHead : Nat → Nat → Bool
  closed : Nat → Nat → Bool
  reopen : Nat → Nat → Prop
  raw : Nat → Nat → List Nat
  facts : Nat → Nat → Nat → Option α
  names : Nat → Nat → List Nat
  retained : Nat → Nat → List Nat
  orig : Nat → Nat
  images : Nat → Nat → List Nat
  prep : Nat → Nat → Prop
  roundId : Nat → Nat → Nat
  par : Nat → Nat → Nat → List Nat
  anc : Nat → Nat → Nat → Nat → Bool
  known : Nat → Nat → Nat
  active : Nat → Nat → Bool
  checks : Nat → Nat → RawPublish.Checks
  hubNamed : Nat → Nat → Nat → Bool
  hubCached : Nat → Nat → Nat → Bool
  normal : Nat → Nat → Nat → Bool
  nodeDrop : Nat → Nat → Nat → Bool
  hubDrop : Nat → Nat → Nat → Bool
  valid : Nat → Nat → Bool
  recOf : ρ → List Exec.Rec
  pushStore : Nat → Nat → Exec.EState
  pushPacket : Nat → Nat → Exec.PushPacket
  opBases : Nat → Nat → List Nat
  objectBases : Nat → Nat → List Nat
  pushes : Nat → Nat → Prop
  answerAt : Nat → Nat → Nat
  objFail : Nat → Nat → Prop
  objReady : Nat → Nat → Bool
  lost : Nat → Prop
  ioFail : Nat → Prop
  /-- Node `n`'s own code makes, at hive time `t`, a semantic write no protocol step accounts
  for: idle housekeeping (`when_idle`: `reconcile_settings`, `show_other_workspaces`,
  `replace_abandoned_working_copies`, `record_forget_after`, `expire_idle`); the round's prelude
  (`before_sync`: `reconcile_settings`, `show_other_workspaces`); `advance_to`'s working-copy
  cleanup (`replace_abandoned_working_copies`, and `move_taken_workspaces` after a taking); the
  pass-on of a user's `jj op abandon` (`check_abandon`), which can come after the user's work;
  and the reparenting of late operations after a renaming (`reparent_late`). Not the git export
  copy (the same canonical form), the fix-up's write (`WriteRes`), a realization, a merge or
  the taking of records, which the model's steps account for. -/
  autoWrite : Nat → Nat → Prop
  userWork : Nat → Nat → Prop
  root : Nat
  inbox : Nat → Nat → Retry.Inbox
  own : Nat → Nat → Option (Nat × Nat)
  note : Nat → Nat → Option Nat
  callAt : Nat → Nat → Nat
  latch : Nat → Nat → Nat
  hist : Nat → Nat
  doneAt : Nat → Nat → Nat
  oldNotes : Nat → Nat → Nat → Retry.Notifications.State

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
def naming (n p : Nat) : Naming α :=
  ⟨O.raw n (O.sched n p) ++ O.names n (O.sched n p) ++ O.retained n (O.sched n p),
    fun m => O.facts n (O.sched n (p + m)), fun m => O.names n (O.sched n (p + m)), O.orig,
    fun m => O.images n (O.sched n (p + m)), fun m => O.prep n (O.sched n (p + m)),
    fun m => decide (2 ≤ (O.ctl n (O.sched n (p + m))).burst.heads.length)⟩

/-- Whether node `n`'s events from its `p`th to its `(p + m)`th are all its round's own, in the
round of the first: once one is not, none later is, so no later round is read as this one. -/
def roundActive (n p m : Nat) : Bool :=
  (List.range (m + 1)).all fun m' =>
    O.active n (O.sched n (p + m')) && decide (O.roundId n (O.sched n (p + m')) =
      O.roundId n (O.sched n p))

/-- The round of node `n` from its `p`th scheduled event: its reading then, and its events. -/
def fetchData (n p : Nat) : FetchData α :=
  ⟨O.raw n (O.sched n p), O.naming n p, O.par n (O.sched n p),
    O.anc n (O.sched n p), O.known n (O.sched n p), fun m => O.ctl n (O.sched n (p + m)),
    fun m => O.ctl n (O.doneAt n (O.sched n (p + m)) + 1),
    fun m => O.prims n (O.sched n (p + m)), fun m => O.roundActive n p m,
    fun m => O.objFail n (O.sched n (p + m)), O.receipts n (O.sched n p)⟩

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
  recOf := O.recOf
  es := fun j => O.pushStore n (O.sched n (p + j))
  xp := fun j => O.pushPacket n (O.sched n (p + j))
  opBases := fun j => O.opBases n (O.sched n (p + j))
  objectBases := fun j => O.objectBases n (O.sched n (p + j))

theorem sched_ge {O : HiveObs ρ α} (hmono : ∀ n p, O.sched n p < O.sched n (p + 1)) (n : Nat) :
    ∀ p, p ≤ O.sched n p
  | 0 => Nat.zero_le _
  | p + 1 => Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (sched_ge hmono n p) (hmono n p))

theorem roundActive_zero {n p : Nat} (h : O.active n (O.sched n p) = true) :
    O.roundActive n p 0 = true := by
  simp [roundActive, h]

theorem sched_le {O : HiveObs ρ α} (hmono : ∀ n p, O.sched n p < O.sched n (p + 1)) (n : Nat)
    {p q : Nat} (h : p ≤ q) : O.sched n p ≤ O.sched n q := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ih (Nat.le_add_right _ _)) (hmono n (p + d)))

end HiveObs

/-- The records and every node's dropped originals stay as they are from `k`. -/
def RecordsFixedFrom (N : Nat) (recs : Nat → Exec.SEState) (k : Nat) : Prop :=
  ∀ i, k ≤ i → ((recs i).recs, (recs i).pruned) = ((recs k).recs, (recs k).pruned) ∧
    ∀ n, n < N → ∀ x, x ∈ (recs i).nodeDF n ↔ x ∈ (recs k).nodeDF n

/-- The cut: records and drops fixed, and no node adopts or fails for a stale plan, from `k`. -/
def CutAt (N : Nat) (recs : Nat → Exec.SEState) (adopts fails : Nat → Nat → Bool)
    (k : Nat) : Prop :=
  RecordsFixedFrom N recs k ∧
    ∀ n, n < N → ∀ i, k ≤ i → adopts n i = false ∧ fails n i = false

/-- A node is eligible at the cut `k`: it drops exactly what the hub's records drop. -/
def EligibleAt (N : Nat) (recs : Nat → Exec.SEState) (k : Nat) (n : Nat) : Prop :=
  n < N ∧ Exec.seteq ((recs k).nodeDF n) (recs k).hubDL = true

instance (N : Nat) (recs : Nat → Exec.SEState) (k : Nat) :
    DecidablePred (EligibleAt N recs k) := fun n => by
  unfold EligibleAt; infer_instance

/-- From `k` on, no ordinary I/O or transport failure, no node's own code makes an automatic
write (`autoWrite`: idle housekeeping, the prelude's, `advance_to`'s cleanup, a `jj op abandon`
passed on, a late reparenting), no user works in a node's repository, no `GetObjects` reply
lacks what it asked for (so no batch fails on one), and the environment loses nothing (`lost`:
no hub remade, no hub losing objects, no node's own gc, no cached have no longer true), so no
per-cut law has a hub regression to face. -/
def QuietAt {ρ α : Type} (N : Nat) (O : HiveObs ρ α) (k : Nat) : Prop :=
  (∀ t, k ≤ t → ¬ O.ioFail t) ∧ (∀ n, n < N → ∀ t, k ≤ t → ¬ O.autoWrite n t) ∧
    (∀ n, n < N → ∀ t, k ≤ t → ¬ O.userWork n t) ∧
    (∀ n, n < N → ∀ t, k ≤ t → ¬ O.objFail n t) ∧ ∀ t, k ≤ t → ¬ O.lost t

/-- From `k` on, no node handles an own head-bearing reply to a call it made before hive time
`c`, nor a notice published before `c`. -/
def OldGone {ρ α : Type} (N : Nat) (O : HiveObs ρ α) (c k : Nat) : Prop :=
  ∀ n, n < N → ∀ t, k ≤ t → (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
    ∀ a, O.note n t = some a → c ≤ a

/-- Node `n`'s known pair at `i` is one the hub had at a hive time from `k` on, by `i`. -/
def KnownTrue {ρ α : Type} (run : Nat → Sys) (O : HiveObs ρ α) (k n i : Nat) : Prop :=
  ∃ a, k ≤ a ∧ a ≤ i ∧ (O.seq n i, O.known n i) = ((run a).hub.seq, (run a).hub.head)

open Musubi.EarlyEntry.Control in
/-- The native laws of the hive's run, laws of its actual sampled events, each asked only in its
phase. The run observed is the record-safe suffix of the execution: it starts after the last
destructive fault that rewrites or loses records, drops or recent local writes (a hub rollback, a
lost local write), so `recStep`, `prune`, `dropsGrow` and the metadata's only arriving are laws of
that suffix, not of a faulty prefix; the convergence it proves carries back to the whole execution
by that offset.

The phases, in order, and their laws:
- From the start: the hub's record append and prune effects and every node's original-drop
  custody; every node's events keep being scheduled (`schedMono`, the driver's fairness); each
  node's transport call slots step as `Retry.InboxStep`, handling an own reply to a call issued
  before a given id being an old effect (`inboxStep`), the call of an own reply not yet issued at
  a time starting later (`callIds`, of the calls that have a reply only), and old notices being
  finitely many in flight and queued at any cut, each handled once (`notesOld`,
  `Retry.Notifications`: the subscription queue may outlive a reconnect).
- Once records and drops are fixed, from a time past which no node handles an own reply to a call
  made, or a notice published, before they were (`OldGone`): every node's record control
  (`epochStep`). An old `Fetched` can still announce old records before that.
- The environment: what invalidates a node's object credit (`lost`) happens only finitely often
  (`envFinal`); the hub and the node keep what can be served otherwise, and a node asks only
  within its credit (`readyKeep`); a `GetObjects` reply lacks what it asked for only with the
  credit spent, the recovery under way (`readyFail`, the reopen may come later). Ordinary I/O and
  transport failures (`failFinal`), a node's automatic writes (`autoWritesStop`: idle
  housekeeping, the prelude's, `advance_to`'s cleanup, a `jj op abandon` passed on, a late
  reparenting) and user work (`userFinal`) happen only finitely often: explicit premises, the
  automatic writes' end assumed, not proved. The laws of entry, its
  persistence, the pending run and the hub's handling of a push are asked only past them and past
  the end of failed `GetObjects` replies, which is derived (`QuietAt`): so a batch after a fresh
  `Fetch` never fails on an old `GetObjects`.
- Past the cut where all that holds: the laws of every node's pre-entry run from any of its
  scheduled events then on (`EntryLaws` of `HiveObs.entryData`, each step's law from its reading
  to its state right after its calls complete, then a frame, `Control.Frame`, to the next step's
  reading: nothing lost, the canonical op heads and the plan as they were, which is the frame
  obligation between the batch and the next prelude); the persistence of entry (a reopen follows
  `Incomplete`, or recovers from a failed `GetObjects` with no reopen since, `reopenWhy`;
  `Incomplete` only from the hub's head to a push it lacks the closure of; the conditional closure
  law for an entered node's push; what keeps entry otherwise); how the known pair moves (an own
  head-bearing reply names the hub's state at a hive time from the call's start to its handling,
  handled as `handle_reply` does, `ownHead`; a notice names the hub's state at a hive time up to
  its handling, `noteHead`; nothing else moves it, `quietKnown`; the hub's head at sequence zero
  is the root, `rootSeq`); a sampled event's calls complete before the node's next sampled event,
  whose prelude has hive times of its own, so the state the batch left and the next reading are
  distinct instants (`doneIn`); a fresh reply is an own reply to the call made then, handled
  within that event's batch (`freshOwn`).
- Past it too: an event that is not a core step of a running round is followed, fairly, by a round
  start (`idleStart`), whose next event is the round's first core step (`startCore`).
- Once every node has entered, has had a core step of a running round since, COMPLETED (its
  prelude completing any realignment its records' taking left unfinished, and its canonical op
  heads distinct after it: an alias forces a merge, which leaves one), and knows a pair the hub
  had past the cut (`KnownTrue`): what the eligible nodes' system takes (`FineAt`, from the
  refinement its doc lists). That is no field here but `hive_converges`'s premise `fine`, which
  `FineAssembly.hive_converges_observed` builds from the replay of observed native events.
- Once the hub is stable, and a node has entered and knows its head: the laws of the node's run
  from a core step of a running round, at its round's own steps (`PendingLaws` of
  `HiveObs.pendingData`), which cannot hold of a node that is not eligible: the round would never
  end, so no notice or round start is read as a core step; and the hub's handling of each push a
  node sends (`answer`: at a later hive time, the hub's `(seq, head)` after it is
  `RawPublish.after` of that very packet and those checks, the hub handling one request at a time
  per hive).

The local correspondence laws bind observations to native effects: `inboxStep`, `callIds`,
`notesOld`, `ownHead`, `noteHead`, `quietKnown`, `clock`, `maintBind`, `noteBind`, `replyBind`,
`freshOwn`, `rootSeq`, the latch laws, `hubSeqStep`, `histBind`, `readyKeep`, `readyFail`,
`reopenWhy`, record/drop effects, and the effect parts of `EntryLaws`, `FetchLaws` and
`PendingLaws`. Some fields combine effects with completion or fairness: `doneIn` requires
sampled batches to complete before the next event; `answer` supplies a later handling time as
well as that actual packet's effect; `EntryLaws.hobjects` and `hstart` require eventual round
restarts. These progress obligations remain assumptions. Scheduling also includes `schedMono`,
`idleStart`, `startCore`, and Fair and PushFair inside `FineAt`. Environment premises are
`envFinal`, `failFinal`, `autoWritesStop` and `userFinal`. `FineAt` documents its remaining
source obligations. The cuts and convergence obtained from these premises are derived below.

Nothing here is a conclusion of the proof: no old effects stopping, no entry, no truthful known
pair, no stable hub, no eligibility, no naming cutoff (each is derived inside the frozen round
that needs it), no hub staying put through a push (from `answer` and the stable hub), no end to
failed `GetObjects` replies (from the credit, `Retry.Serial.object_recoveries_stop`) nor to the
reopens that recover from them, and no node knowing the stable head (from a fresh own reply after
it). -/
structure HiveContracts {ρ α : Type} [DecidableEq ρ] (N : Nat) (D : Nat → Nat → Nat → Prop)
    (law : HubLaw) (run : Nat → Sys) (acts : Nat → Act) (recs : Nat → Exec.SEState) (B : Nat)
    (epoch : Nat → Nat → Retry.Records.State) (adopts fails : Nat → Nat → Bool)
    (recLabel : Nat → Nat) (Rof : Nat → ρ) (wOf : Nat → Nat) (O : HiveObs ρ α) : Prop where
  recStep : ∀ i, (recs (i + 1)).recs = (recs i).recs ∨
    ∃ D, (recs (i + 1)).recs = (recs i).takeRecs D
  prune : ∀ i, (recs i).pruned ≤ (recs (i + 1)).pruned
  pruneLe : ∀ i, (recs i).pruned ≤ (recs i).recs.length
  dropsGrow : ∀ i n, n < N → ∀ x, x ∈ (recs i).nodeDF n → x ∈ (recs (i + 1)).nodeDF n
  hubBound : ∀ i x, x ∈ (recs i).hubDL → x < B
  nodeBound : ∀ i n, n < N → ∀ x, x ∈ (recs i).nodeDF n → x < B
  epochStep : ∀ kR k, RecordsFixedFrom N recs kR → kR ≤ k → OldGone N O kR k → ∀ n, n < N →
    ∀ i, k ≤ i →
    Retry.Records.Step (recLabel kR) (epoch n i) (epoch n (i + 1)) (adopts n i) (fails n i)
  schedMono : ∀ n p, O.sched n p < O.sched n (p + 1)
  entry : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n, n < N → ∀ p,
    k ≤ O.sched n p → EntryLaws (Rof k) (wOf k) (O.entryData n p)
  reopenWhy : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    O.reopen n i → O.incomplete n i = true ∨
      ∃ t, t ≤ i ∧ O.objFail n t ∧ ∀ s, t < s → s < i → ¬ O.reopen n s
  incHead : ∀ k, CutAt N recs adopts fails k → ∀ n i, n < N → k ≤ i →
    O.incomplete n i = true → O.expectedIsHead n i = true ∧ O.closed n i = false
  closure : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    RawEntry (Rof k) (wOf k) (O.rawAt n i) → O.expectedIsHead n i = true →
    O.closed n i = true
  keep : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n i, n < N → k ≤ i →
    RawEntry (Rof k) (wOf k) (O.rawAt n i) → ¬ O.reopen n i →
    RawEntry (Rof k) (wOf k) (O.rawAt n (i + 1))
  pending : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n p, n < N →
    (∀ i, O.sched n p ≤ i → (run i).hub = (run (O.sched n p)).hub) →
    (∀ i, O.sched n p ≤ i → O.known n i = (run (O.sched n p)).hub.head) →
    (∀ i, O.sched n p ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
    ¬ EligibleAt N recs k n →
    PendingLaws ⟨(run (O.sched n p)).hub.seq, (run (O.sched n p)).hub.head⟩
      (O.pendingData n p (Rof k))
  envFinal : ∃ kE, ∀ t, kE ≤ t → ¬ O.lost t
  readyKeep : ∀ n t, n < N → ¬ O.lost t → O.objReady n t = true → O.objReady n (t + 1) = true
  readyFail : ∀ n t, n < N → ¬ O.lost t → O.objFail n t →
    O.objReady n t = false ∧ O.objReady n (t + 1) = true
  failFinal : ∃ kF, ∀ t, kF ≤ t → ¬ O.ioFail t
  /-- Each node's automatic writes (`HiveObs.autoWrite`) end: a premise, the protocol's
  boundary. That they end, from finite user and configuration input, is not proved here. -/
  autoWritesStop : ∀ n, n < N → ∃ kA, ∀ t, kA ≤ t → ¬ O.autoWrite n t
  userFinal : ∃ kU, ∀ t, kU ≤ t → ∀ n, n < N → ¬ O.userWork n t
  idleStart : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n p, n < N →
    k ≤ O.sched n p → O.active n (O.sched n p) = false → ∃ q, p ≤ q ∧ O.starts n (O.sched n q)
  startCore : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n q, n < N →
    k ≤ O.sched n q → O.starts n (O.sched n q) → O.active n (O.sched n (q + 1)) = true
  inboxStep : ∀ c n t, n < N →
    ∃ b, Retry.InboxStep c (O.inbox n t) (O.inbox n (t + 1)) b ∧
      ∀ id a, O.own n t = some (id, a) → id < c → b = true
  callIds : ∀ n t u id a, n < N → O.own n u = some (id, a) → (O.inbox n t).next ≤ id →
    t ≤ O.callAt n id
  ownHead : ∀ n t id a, n < N → ¬ O.reopen n t → O.own n t = some (id, a) →
    O.callAt n id ≤ a ∧ a ≤ t ∧
    (O.seq n (t + 1), O.known n (t + 1)) = Retry.Serial.handleHead O.root true false
      (O.seq n t, O.known n t) ((run a).hub.seq, (run a).hub.head)
  noteHead : ∀ n t a, n < N → ¬ O.reopen n t → O.note n t = some a →
    a ≤ t ∧ (O.seq n (t + 1), O.known n (t + 1)) = Retry.Serial.handleHead O.root false true
      (O.seq n t, O.known n t) ((run a).hub.seq, (run a).hub.head)
  notesOld : ∀ c n t, n < N → c ≤ t → ∃ h, Retry.Notifications.Step (O.oldNotes c n t)
    (O.oldNotes c n (t + 1)) h ∧ ∀ a, O.note n t = some a → a < c → h = true
  doneIn : ∀ n p, n < N → O.sched n p ≤ O.doneAt n (O.sched n p) ∧
    O.doneAt n (O.sched n p) + 1 < O.sched n (p + 1)
  quietKnown : ∀ n t, n < N → ¬ O.reopen n t → O.own n t = none → O.note n t = none →
    (O.seq n (t + 1), O.known n (t + 1)) = (O.seq n t, O.known n t)
  /-- The `Sys` model's clock is hive time. -/
  clock : ∀ i, (run i).time = i
  /-- A `Sys` housekeeping step is the node's `when_idle` writing then, an automatic write. -/
  maintBind : ∀ n i, n < N → acts i = .core n .maint → O.autoWrite n i
  /-- A notification a node takes in the `Sys` model is the one its driver handles then, naming
  the hub's state right after the accept that published it. -/
  noteBind : ∀ n i nt, n < N → acts i = .notice n nt → O.note n i = some (nt.time + 1)
  /-- Past a cut, a head-bearing reply the `Sys` model takes is taken when the node's batch
  completes, at the end of one of its sampled events (the model handling a batch at once), and
  the driver handled it at its own time in that event, for a call made by the time it was
  answered. -/
  replyBind : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ i r, k ≤ i →
    r ∈ (run i).reps → r ∉ (run (i + 1)).reps → r.node < N →
    (∃ s, r.ans = .fetched s ∨ r.ans = .head s) →
    ∃ p t id a, O.doneAt r.node (O.sched r.node p) = i ∧ O.sched r.node p ≤ t ∧
      O.own r.node t = some (id, a) ∧ O.callAt r.node id ≤ r.time
  freshOwn : ∀ n t, n < N → O.reply n t = .fresh → ∃ u id a, t ≤ u ∧ u ≤ O.doneAt n t ∧
    O.own n u = some (id, a) ∧ O.callAt n id = t
  rootSeq : ∀ a, (run a).hub.seq = 0 → (run a).hub.head = O.root
  latchKnown : ∀ n t, n < N →
    Recovery.HubSys.known (run t) n = (O.seq n (O.latch n t), O.known n (O.latch n t))
  latchLe : ∀ n t, n < N → O.latch n t ≤ t
  latchMono : ∀ n t t', n < N → t ≤ t' → O.latch n t ≤ O.latch n t'
  latchAtSample : ∀ n p, n < N → O.latch n (O.sched n p) = O.sched n p
  hubSeqStep : ∀ t, ¬ O.lost t → (run t).hub.seq ≤ (run (t + 1)).hub.seq
  histBind : ∀ a, (∀ s, a ≤ s → ¬ O.lost s) → O.hist ((run a).hub.seq) = (run a).hub.head
  answer : ∀ k, CutAt N recs adopts fails k → QuietAt N O k → ∀ n t, n < N → k ≤ t →
    O.pushes n t →
    t ≤ O.answerAt n t ∧
    (⟨(run (O.answerAt n t + 1)).hub.seq, (run (O.answerAt n t + 1)).hub.head⟩ :
        RawPublish.Hub) =
      RawPublish.after ⟨(run (O.answerAt n t)).hub.seq, (run (O.answerAt n t)).hub.head⟩
        (O.pkt n t) (O.checks n t)

/-- An own reply naming the pair the node knows leaves it. -/
theorem handleHead_same (r : Nat) (P : Retry.Serial.Head) :
    Retry.Serial.handleHead r true false P P = P := by
  simp [Retry.Serial.handleHead, Retry.Serial.wentBack, Retry.Serial.filteredLearn]

/-- A notice of a sequence no later than the one the node knows leaves it. -/
theorem handleHead_notice_le (r : Nat) (P q : Retry.Serial.Head) (h : q.1 ≤ P.1) :
    Retry.Serial.handleHead r false true P q = P := by
  simp [Retry.Serial.handleHead, Retry.Serial.filteredLearn, Nat.not_lt.2 h]

/-- A notice leaves the known pair, or makes it the notice's. -/
theorem handleHead_notice_or (r : Nat) (P q : Retry.Serial.Head) :
    Retry.Serial.handleHead r false true P q = P ∨
      Retry.Serial.handleHead r false true P q = q := by
  simp only [Retry.Serial.handleHead, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    Retry.Serial.filteredLearn]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- With nothing lost between, the hub's sequence does not go back. -/
theorem seq_chain {run : Nat → Sys} {lost : Nat → Prop}
    (hmono : ∀ t, ¬ lost t → (run t).hub.seq ≤ (run (t + 1)).hub.seq) {a t : Nat}
    (hat : a ≤ t) (hno : ∀ s, a ≤ s → s < t → ¬ lost s) :
    (run a).hub.seq ≤ (run t).hub.seq := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hat
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega) fun s h1 h2 => hno s h1 (by omega))
      (hmono _ (hno _ (by omega) (by omega)))

end Musubi.SysAcceptance

/-
Filter the actual hive to eligible nodes and assemble their stable-hub convergence.
See `Musubi.SysAcceptance` for the layers of the complete convergence argument.
-/
import Musubi.SysAcceptance.Pending

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-! ## The eligible nodes settle in the hive's actual run

`eligible_system_converges` read through the eligible nodes' system (`Recovery.HubSys.hiveSys`):
a node's fair scheduling reads only its own slot and the acts, its pushes' completion only its
own requests, which the system keeps, and the hub's decision on a push only the hub, so each
carries over from the actual run, and what the theorem concludes of the hub and of the eligible
nodes is of the actual run. -/

section Hive

open Musubi.Recovery.HubSys

variable {E : Nat → Prop} [DecidablePred E] {frozen : Nat → NodeC} {old : List Req}

theorem fair_filt {run : Nat → Sys} {acts : Nat → Act} {n kf : Nat} (hE : E n)
    (h : Fair run acts n kf) : Fair (fun j => filt E frozen old (run j)) acts n kf where
  start := fun i hi hw ha => h.start i hi (by rw [← filt_node_of hE]; exact hw)
    (by rw [← filt_node_of hE]; exact ha)
  core := fun i hi hw ha => h.core i hi (by rw [← filt_node_of hE]; exact hw)
    (by rw [← filt_node_of hE]; exact ha)
  reply := fun i hi hw => h.reply i hi (by rw [← filt_node_of hE]; exact hw)

theorem pushFair_filt {run : Nat → Sys} {acts : Nat → Act} {n k : Nat} (hE : E n)
    (h : PushFair run acts n k) : PushFair (fun j => filt E frozen old (run j)) acts n k := by
  intro i hi ha q hq hq' hn
  have keep : keepReq E old q = true := by simp [keepReq, hn, hE]
  obtain ⟨j, hj, h1, h2⟩ := h i hi ha q (List.mem_filter.1 hq).1
    (fun h' => hq' (List.mem_filter.2 ⟨h', keep⟩)) hn
  exact ⟨j, hj, List.mem_filter.2 ⟨h1, keep⟩, fun h' => h2 (List.mem_filter.1 h').1⟩

theorem lawful_filt {M : Nat} {decode : Nat → List Exec.Rec} {g g' : Sys} {P : Pkt}
    (h : Nonempty (LawfulDecision M decode g g' P)) :
    Nonempty (LawfulDecision M decode (filt E frozen old g) (filt E frozen old g') P) := by
  obtain ⟨d⟩ := h
  exact ⟨⟨⟨d.before, d.after, d.packet, d.handled, d.expected, d.new, d.records, d.head,
    d.recs, d.seqBefore, d.seqAfter⟩, d.primitives⟩⟩

end Hive

open Musubi.Recovery.HubSys in
/-- The eligible nodes settle in the hive's actual run. Observed from the entry cut `k` and read
as the eligible nodes' system, with what `Recovery.HubSys.hub_stabilizes_hive` takes, records
fixed from the cut, and for each eligible node fair scheduling of its own events, completion of
the pushes it sends and the hub's lawful decision on each of them, all of the actual run: the
actual hub settles, and every eligible node settles at its head, its heads that head. -/
theorem eligible_hive_converges {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {w : Nat} (run : Nat → Sys) (acts : Nat → Act)
    (initial : Nat → Nat) (k rawRoot M : Nat) (decode : Nat → List Exec.Rec)
    (hs : ∀ i, k ≤ i → HiveStep N D law E (run k).reqs (acts i) (run i) (run (i + 1)))
    (hE0 : ∀ n, E n → NodeSys.NodeOK D n (run k) ∧ ObjsOK n (run k))
    (hsys : SysOK law (run k)) (htime : TimeOK (run k))
    (hans : ∀ r ∈ (run k).reps, r.req = .objs → r.ans = .objects)
    (hroot : rawRoot < (run k).next) (hpar : (run k).par rawRoot = [])
    (hd : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x)
    (hb : RequestBounds (run k))
    (hi : Recovery.HistoryWindow w (state (run k) initial))
    (hknown : ∀ n, E n → Recovery.HubNodeSteps.HonestSnap w initial (run k)
      ⟨(known (run k) n).1, (known (run k) n).2, (run k).hub.recs⟩)
    (hl : ∀ i, NodeStepLaws E D w (histories (fun j => run (k + j)) initial i) (acts (k + i))
      (run (k + i)) (run (k + i + 1)))
    (hN : ∀ n, E n → n < N) (hm : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint)
    (hnodup : ∀ n, E n → Recovery.HubNodeSteps.HeadsNodup (run k) n)
    (hr : ∀ i, k ≤ i → (run i).hub.recs = (run k).hub.recs)
    (hf : ∀ n, E n → ∃ kf, Fair (fun j => run (k + j)) (fun j => acts (k + j)) n kf)
    (hq : ∀ n, E n → PushFair (fun j => run (k + j)) (fun j => acts (k + j)) n 0)
    (hdecide : ∀ n, E n → ∀ j q, q ∈ (run (k + j)).reqs → q ∉ (run (k + j + 1)).reqs →
      q.node = n → ∀ P, q.body = .push P →
        Nonempty (LawfulDecision M decode (run (k + j)) (run (k + j + 1)) P)) :
    ∃ K cut, k ≤ K ∧ K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, E n → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, heads (run i) n x ↔ x = (run K).hub.head := by
  obtain ⟨hρ, hk0, hb0, hi0, hkn0, hl0, -⟩ :=
    hive_filtered (N := N) (law := law) run acts initial k rawRoot hs hE0 hsys htime hans hroot
      hpar hb hi hknown hl hm hnodup
  have hdecide' : ∀ n, E n → ∀ j q, q ∈ (hiveSys E rawRoot run k j).reqs →
      q ∉ (hiveSys E rawRoot run k (j + 1)).reqs → q.node = n → ∀ P, q.body = .push P →
        Nonempty (LawfulDecision M decode (hiveSys E rawRoot run k j)
          (hiveSys E rawRoot run k (j + 1)) P) := by
    intro n hE j q hq hq' hn P hP
    have keep : keepReq E (run k).reqs q = true := by simp [keepReq, hn, hE]
    exact lawful_filt (hdecide n hE j q (List.mem_filter.1 hq).1
      (fun h' => hq' (List.mem_filter.2 ⟨h', keep⟩)) hn P hP)
  obtain ⟨K, cut, hKc, hhub, hnodes⟩ := eligible_system_converges (E := E) (w := w)
    (hiveSys E rawRoot run k) (fun j => acts (k + j)) initial M decode hρ hk0
    (fun i => hd (k + i)) hb0 hi0 hkn0 hl0 hN 0
    (fun i _ n hE => hm (k + i) (Nat.le_add_right k i) n hE)
    (fun i => (hr (k + i) (by omega)).trans (hr k (Nat.le_refl _)).symm)
    (fun n hE => by
      obtain ⟨kf, h⟩ := hf n hE
      exact ⟨kf, fair_filt hE h⟩)
    (fun n hE => pushFair_filt hE (hq n hE)) hdecide'
  refine ⟨k + K, k + cut, by omega, by omega, fun i hi => ?_, fun n hE => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    exact hhub j (by omega)
  · obtain ⟨H, hH⟩ := hnodes n hE
    refine ⟨H, fun i hi => ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    obtain ⟨h1, h2, h3⟩ := hH j (by omega)
    have hn : (hiveSys E rawRoot run k j).node n = (run (k + j)).node n := filt_node_of hE
    refine ⟨by rw [← hn]; exact h1, by rw [← hn]; exact h2, fun x => ?_⟩
    have := h3 x
    unfold heads at this ⊢
    rw [hn] at this
    exact this

open Musubi.EarlyEntry Musubi.EarlyEntry.Control in
/-- What a node's run on a hub that stays reads, sampled from its actual events: its round's raw
closure, naming and raw graph, and at each sampled step its core state, reads, the packet it
pushes and the hub's checks of that same call, its core states right after each step's calls
complete (`after`), whether its `GetObjects` reply lacked what it asked for (`failed`), which
steps are its round's own core steps (`active`), whether it sends a push (`pushes`), and the
records it offers and last heard, with the hub's; and, for each push, the hub's naming when it
handles it (`hubNamed` and `hubCached`, the dropped raw names and cached renaming keys whose union
is its `is_superseded`), which ids are complete canonical bodies written under the node's drops,
its applied records and pending drops, that survive them (`normal`: not a lookup's fallback to the
input id), each raw operation's original (`orig`), the originals the node's drops and the hub's
records drop at each push (`nodeD`, `hubD`), whether the hub's other validations of the packet
pass (`valid`: no operation missing or abandoned, no original repeated), the hub's store then
(`es`), THE packet, in the executable model (`xp`: its expected and new heads, drops, records, and
the ids its attachments carry; `pkt` is its raw view, by definition), how records are encoded in a
packet (`recOf`), and the bases the sender's cache leaves out for operations and for objects
(`opBases`, `objectBases`). Data only: its laws are `PendingLaws`. -/
structure PendingData (ρ α : Type) where
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
  pushes : Nat → Prop
  hubNamed : Nat → Nat → Bool
  hubCached : Nat → Nat → Bool
  normal : Nat → Nat → Bool
  orig : Nat → Nat
  nodeD : Nat → Nat → Bool
  hubD : Nat → Nat → Bool
  valid : Nat → Bool
  es : Nat → Exec.EState
  xp : Nat → Exec.PushPacket
  opBases : Nat → List Nat
  objectBases : Nat → List Nat
  recOf : ρ → List Exec.Rec

/-- The push as `Push::answer` reads it, raw: a view of the one packet the node sends. -/
def PendingData.pkt {ρ α : Type} (d : PendingData ρ α) (i : Nat) : RawPublish.Push :=
  ⟨(d.xp i).expected, (d.xp i).new, (d.xp i).pending⟩

open Musubi.EarlyEntry Musubi.EarlyEntry.Control in
/-- The native per-call laws of that run on the hub `hub`, as `no_forever_pending` takes them;
that a step whose computed choice is the push sends it (`NodeCore::step` returns it); and that
the store each push is checked against is the hub's (`hstore`) and the packet offers the records
the node has applied (`hrecs`); but not
the hub's staying put through its answers to the pushes, which is not a law of the run:
`PendingLaws.absurd` takes it apart, and the hive derives it from the hub's actual handling of
each push it sends; nor that no `GetObjects` reply lacks what it asked for, which `absurd` takes
apart too. -/
structure PendingLaws {ρ α : Type} [DecidableEq ρ] (hub : RawPublish.Hub)
    (d : PendingData ρ α) : Prop where
  trans : ∀ a b c, d.anc a b = true → d.anc b c = true → d.anc a c = true
  hlt : ParLt d.par
  hraw : ∀ x, Anc d.par x hub.head → x ∈ d.raw
  hnaming : d.naming.Laws d.par hub.head fun i => d.active i = true
  hnext : ∀ i, d.active i = true → (rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run i)
    (d.prims i) = .realize ∨ rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run i)
    (d.prims i) = .advance ∨ rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run i)
    (d.prims i) = .fetch ∨ (rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run i)
    (d.prims i) = .objects ∧ ¬ d.failed i)) → d.active (i + 1) = true
  /-- At the round's own steps: nothing announced, no head dropped, records not differing,
  pending drops, and the write's new head not the known one (`newIsKnown`). That last is no
  freshness (a write may reuse an operation the node holds) but `normalized_write_ne_known`'s
  cycle: the images are below the head (the push's guard), the write is properly above it, and
  a result equal to the known head would be its own singleton normal image. That normalization
  is the SOURCE OBLIGATION: the written result is a complete canonical body under the node's
  drops, with the mask stable, the known head local, and no concurrent user abandon or repair
  renaming it. -/
  hguard : ∀ i, d.active i = true → (d.prims i).announced = false ∧ (d.prims i).dropHead = false ∧
    (d.prims i).differ = false ∧ (d.prims i).pending = true ∧ (d.prims i).newIsKnown = false
  hburst : ∀ i, d.active i = true → d.naming.Still i → (rawControl d.raw (d.naming.images i) d.par
    d.anc hub.head (d.run i) (d.prims i) = .merge ∨ rawControl d.raw (d.naming.images i) d.par d.anc
    hub.head (d.run i) (d.prims i) = .realize ∨ rawControl d.raw (d.naming.images i) d.par d.anc
    hub.head (d.run i) (d.prims i) = .advance) → ∃ k, callB d.raw (d.naming.images i) d.anc (.burst
    k) (d.run i) (d.after i) = true
  hfetch : ∀ i, d.active i = true → d.naming.Still i → rawControl d.raw (d.naming.images i) d.par
    d.anc hub.head (d.run i) (d.prims i) = .fetch → (∀ x ∈ d.raw, (d.run i).burst.loc x = false →
    (d.after i).stg x = true ∨ (d.after i).burst.loc x = true) ∧ (d.after i).burst.heads = (d.run
    i).burst.heads ∧ (d.after i).burst.plan = (d.run i).burst.plan ∧ growsB d.raw (d.run i) (d.after
    i) = true
  hobjects : ∀ i, d.active i = true → d.naming.Still i → rawControl d.raw (d.naming.images i) d.par
    d.anc hub.head (d.run i) (d.prims i) = .objects → d.failed i ∨ ((∀ x, walkB d.par (d.run
    i).burst.loc (d.run i).stg hub.head x = true → (d.run i).burst.loc x = false → (d.run i).stg x =
    true → (d.run i).obj x = false → (d.after i).obj x = true ∨ (d.after i).burst.loc x = true) ∧
    (d.after i).burst.heads = (d.run i).burst.heads ∧ (d.after i).burst.plan = (d.run i).burst.plan
    ∧ growsB d.raw (d.run i) (d.after i) = true)
  hframe : ∀ i, d.active i = true → d.active (i + 1) = true → d.naming.Still i → Control.Frame d.raw
    (d.after i) (d.run (i + 1))
  hpkt : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → (d.pkt i).expected = hub.head ∧ (d.prims i).newIsKnown = decide ((d.pkt
    i).new = hub.head) ∧ (d.prims i).pending = !(d.pkt i).dropped.isEmpty ∧ ∀ h ∈ (d.run
    i).burst.heads, d.anc h (d.pkt i).new = true
  hdiffer : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → (d.prims i).differ = match d.heard i with
      | some h => !decide (h = d.offered i)
      | none => (d.prims i).pending
  hmatch : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → (d.checks i).recordsMatch = decide (d.offered i = d.current)
  hheard : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → d.heard i = some d.current
  hdroppedB : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → (d.checks i).dropped = ((d.hubNamed i (d.pkt i).new ||
    d.hubCached i (d.pkt i).new) || decide ((d.pkt i).new ∈ (d.pkt i).dropped))
  hwitness : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → d.normal i (d.pkt i).new = true
  /-- A complete canonical body under the node's drops: its whole body closure is present, and
  its whole raw ancestry, root included and not only its parents, survives the node's drops (the
  closure's presence is not used here). -/
  hnormalDef : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push →
    ∀ y, d.normal i y = true → ∀ z, Anc d.par z y → d.nodeD i (d.orig z) = false
  /-- A raw name the hub's records drop has its original dropped by them. One way only: names
  are raw, and other versions of the same original need not be named. -/
  hnamedDef : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push →
    ∀ y, d.hubNamed i y = true → d.hubD i (d.orig y) = true
  /-- A cached renaming exists because the hub's records drop the key's body or an ancestor of
  it (the native contraction and its composed cache). -/
  hcachedCause : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push →
    ∀ y, d.hubCached i y = true → ∃ z, Anc d.par z y ∧ d.hubD i (d.orig z) = true
  /-- With the records it offers the hub's, the node drops at least what they drop. -/
  hdropsSub : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push →
    d.offered i = d.current → ∀ o, d.hubD i o = true → d.nodeD i o = true
  hassert : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → (d.pkt i).new ∉ (d.pkt i).dropped
  hclosedB : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → (d.checks i).closed = (((d.es i).hubStore (d.xp i).ops (d.xp
    i).objs).closedB (d.xp i).new && d.valid i)
  hvalid : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → d.valid i = true
  hparF : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → ParLt (d.es i).parF
  hbases : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → ∀ b ∈ d.opBases i, ClosedAt (Exec.abs (d.es i)) b
  hretained : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → ∀ b ∈ d.objectBases i, ∀ x, Anc (d.es i).parF x b → ∀ o ∈ (d.es
    i).objsF x, o ∈ (d.es i).hub.objs
  hcovers : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head
    (d.run i) (d.prims i) = .push → Exec.UploadCoversSplit (d.es i) (d.xp i) (d.opBases i)
    (d.objectBases i)
  hname : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → (d.checks i).descends = (!(d.naming.images i).isEmpty &&
    (d.naming.images i).all fun j => d.anc j (d.pkt i).new)
  hsend : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → d.pushes i
  hstore : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → (d.es i).hub.head = hub.head
  hrecs : ∀ i, d.active i = true → rawControl d.raw (d.naming.images i) d.par d.anc hub.head (d.run
    i) (d.prims i) = .push → (d.xp i).applied = d.recOf (d.offered i)

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

open Musubi.EarlyEntry Musubi.EarlyEntry.Control in
/-- Such a run, on a hub that stays put through its answers to the pushes it sends, and
serving every `GetObjects` of it, is impossible. -/
theorem PendingLaws.absurd {ρ α : Type} [DecidableEq ρ] {hub : RawPublish.Hub}
    {d : PendingData ρ α} (L : PendingLaws hub d) (h0 : d.active 0 = true)
    (hstable : ∀ i, d.pushes i → RawPublish.after hub (d.pkt i) (d.checks i) = hub)
    (hserve : ∀ i, d.active i = true → ¬ d.failed i) :
    False :=
  no_forever_pending
    d.raw d.naming d.par d.anc L.trans L.hlt hub L.hraw d.run d.after d.prims d.pkt d.checks
    d.failed d.active h0 L.hnaming L.hnext L.hguard L.hburst L.hfetch L.hobjects L.hframe L.hpkt
    d.offered d.heard d.current L.hdiffer L.hmatch L.hheard d.hubNamed d.hubCached
    d.normal d.valid L.hdroppedB L.hwitness L.hnoCacheOf L.hsurviveOf L.hassert d.es d.xp
    d.opBases d.objectBases L.hclosedB L.hvalid L.hparF L.hbases L.hretained L.hcovers L.hname
    (fun i ha h => hstable i (L.hsend i ha h)) hserve

open Musubi.Recovery.HubSys in
/-- What the eligible nodes' system takes from the entry cut `k` on: exactly what
`eligible_hive_converges` takes, of the actual run. It is no primitive: each field is a law of the
hive's actual `Sys` observation (`run`, `acts`), and its source is the refinement of the eligible
nodes' native events to that system, field by field: the step relations (`hs`, `hl`, `hdecide`:
each actual event is a `HiveStep`, its node step lawful, each push decided as `Push::answer`
does), correspondence obligations of native code to the model, which existing tests cover in
parts, not checked as these relations nor proved here; the eligible nodes' state at `k` (`hE0`):
not from entry alone, since taking records writes them before the op heads move, but from each
node's core step since it entered, whose prelude completes any realignment left unfinished, the
record and failure cuts leaving none to begin after; that their op heads are distinct at `k`
(`hnodup`), from the same step, COMPLETED: an alias (two physical op heads with one canonical
form) comes only of an interrupted export, a failure. Canonical op heads with an alias are two or
more, so the step, past adoption, was a merge, and a completed merge leaves one op head (one of
aliases `[m, m]` writing a child of `m`); fewer than two were distinct already, and a step that
keeps the op heads (a realization) keeps that; after it `heads_nodup_step` keeps them distinct;
the invariants of the snapshot at `k` (`hsys`, `htime`, `hans`, `hroot`, `hpar`, `hd`, `hb`,
`hi`), explicit snapshot invariants of the actual observation, source obligations (no simulation
of the whole run as `SysStep`s is used); the cuts' facts (`hr` from the fixed records, `hm` from
automatic writes, housekeeping among them, having stopped by `k`, which makes the model's
`maintFresh` vacuous); and fairness
(`hf`, `hq`). The history window's start `w` and the history `initial` are given, not chosen; and
two facts are no fields at all but derived and passed to `FineAt.converges`: that each eligible
node's known pair in the `Sys` model is an honest snapshot of that history (from its latched
completed snapshot and `KnownTrue`), and that eligible nodes are nodes. -/
structure FineAt (N : Nat) (D : Nat → Nat → Nat → Prop) (law : HubLaw) (E : Nat → Prop)
    [DecidablePred E] (run : Nat → Sys) (acts : Nat → Act) (k w : Nat) (initial : Nat → Nat)
    where
  rawRoot : Nat
  M : Nat
  decode : Nat → List Exec.Rec
  hs : ∀ i, k ≤ i → HiveStep N D law E (run k).reqs (acts i) (run i) (run (i + 1))
  hE0 : ∀ n, E n → NodeSys.NodeOK D n (run k) ∧ ObjsOK n (run k)
  hsys : SysOK law (run k)
  htime : TimeOK (run k)
  hans : ∀ r ∈ (run k).reps, r.req = .objs → r.ans = .objects
  hroot : rawRoot < (run k).next
  hpar : (run k).par rawRoot = []
  hd : ∀ i x, x < (run i).next → ∀ p ∈ (run i).par x, p < x
  hb : RequestBounds (run k)
  hi : Recovery.HistoryWindow w (state (run k) initial)
  hl : ∀ i, NodeStepLaws E D w (histories (fun j => run (k + j)) initial i) (acts (k + i)) (run (k
    + i)) (run (k + i + 1))
  hm : ∀ i, k ≤ i → ∀ n, E n → acts i ≠ .core n .maint
  hnodup : ∀ n, E n → Recovery.HubNodeSteps.HeadsNodup (run k) n
  hr : ∀ i, k ≤ i → (run i).hub.recs = (run k).hub.recs
  hf : ∀ n, E n → ∃ kf, Fair (fun j => run (k + j)) (fun j => acts (k + j)) n kf
  hq : ∀ n, E n → PushFair (fun j => run (k + j)) (fun j => acts (k + j)) n 0
  hdecide : ∀ n, E n → ∀ j q, q ∈ (run (k + j)).reqs → q ∉ (run (k + j + 1)).reqs →
    q.node = n →
    ∀ P, q.body = .push P → Nonempty (LawfulDecision M decode (run (k + j)) (run (k + j + 1)) P)

open Musubi.Recovery.HubSys in
theorem FineAt.converges {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} [DecidablePred E] {run : Nat → Sys} {acts : Nat → Act} {k w : Nat}
    {initial : Nat → Nat} (F : FineAt N D law E run acts k w initial)
    (hknown : ∀ n, E n →
      Recovery.HubNodeSteps.HonestSnap w initial (run k) ⟨(known (run k) n).1,
        (known (run k) n).2, (run k).hub.recs⟩)
    (hN : ∀ n, E n → n < N) :
    ∃ K cut, k ≤ K ∧ K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, E n → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, heads (run i) n x ↔ x = (run K).hub.head :=
  eligible_hive_converges (w := w)
    run acts initial k F.rawRoot F.M F.decode F.hs F.hE0 F.hsys F.htime F.hans F.hroot F.hpar
    F.hd F.hb F.hi hknown F.hl hN F.hm F.hnodup F.hr F.hf F.hq F.hdecide

end Musubi.SysAcceptance

/-
The packet's acceptance boundary. Matching metadata is not enough: the packet must also upload
the complete closure and satisfy the adapter's scoped contracted comparison. Given these
primitive checks, acceptance and its exact head and sequence effect are theorems about the
executable hub.

The last section takes a node's pending drops on raw ids, as `Push::answer` sees them, with no
original identified with a raw id (`Musubi.RawPublish`).

The convergence proof uses this file except the executable-model upload and packet-check
theorems (`packet_checks_accept`, `packet_upload_closes` and their helpers), which are not used by
the assembly and stand alone.
-/
import Musubi.NodeSettle
import Musubi.RecordStability

namespace Musubi.Exec

open Musubi Contract

/-! ## One push -/

/-- One push: the sender, its writes, the expected and new heads, and the sender's applied
records and pending drops at send time. -/
structure PushPacket where
  node : Nat
  ops : List Nat
  objs : List Nat
  expected : Nat
  /-- Ghost send-time sequence; the wire carries the expected head, not this value. -/
  knownSeq : Nat
  new : Nat
  applied : List Rec
  pending : List Nat
  deriving Repr

/-- Every drop the packet carries: those of its applied records plus its pending ones. -/
def PushPacket.allDrops (p : PushPacket) : List Nat := union (flat p.applied) p.pending

/-- The hub's acceptance action built from the packet's own fields. -/
def PushPacket.accept (p : PushPacket) : SAction :=
  .hubSupAccept p.node p.ops p.objs p.expected p.new p.applied p.allDrops

/-- The packet's semantic fields all come from the send-time state `s`. Request and session
ids are transport control and are tied to slots separately. -/
def PushPacket.sourceMatchesB (N : Nat) (s : SEState) (p : PushPacket) : Bool :=
  decide (p.node < N) && recEq p.applied (s.appliedF p.node) &&
    seteq p.allDrops (s.nodeDF p.node) &&
    decide (p.expected = (s.es.nodeOf p.node).known.head) &&
    decide (p.knownSeq = (s.es.nodeOf p.node).known.seq) &&
    (s.es.nodeOf p.node).heads.contains p.new &&
    (s.es.nodeOf p.node).heads.all (· == p.new) &&
    p.pending.all (fun x => !(flat p.applied).contains x)

/-- Equal record lists drop the same ids. -/
theorem mem_flat_of_recEq {A B : List Rec} (h : recEq A B = true) (x : Nat) :
    x ∈ flat A ↔ x ∈ flat B := by
  have e := congrFun (recEq_flat h) x
  simp only [setP] at e
  exact Iff.of_eq e

/-- Set-equal lists have the same members. -/
theorem mem_of_seteq {a b : List Nat} (h : seteq a b = true) (x : Nat) : x ∈ a ↔ x ∈ b := by
  have e := congrFun (seteq_setP h) x
  simp only [setP] at e
  exact Iff.of_eq e

/-- Every drop of an applied record is carried by the packet. -/
theorem packet_custody (p : PushPacket) {x : Nat} (hx : x ∈ flat p.applied) :
    x ∈ p.allDrops := mem_union.2 (.inl hx)

/-- The packet's drops are the sender's drops in the source state. -/
theorem packet_source_drops {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) (x : Nat) :
    x ∈ p.allDrops ↔ x ∈ s.nodeDF p.node := by
  have he : seteq p.allDrops (s.nodeDF p.node) = true := by
    simp only [PushPacket.sourceMatchesB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.2
  exact mem_of_seteq he x

/-- The sender's known position in the source state is `⟨knownSeq, expected⟩`. -/
theorem packet_source_known {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) :
    (s.es.nodeOf p.node).known = ⟨p.knownSeq, p.expected⟩ := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Known.ext h.1.1.1.2.symm h.1.1.1.1.2.symm

/-- The sender's only head in the source state is the packet's new head. -/
theorem packet_source_heads {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) (x : Nat) :
    x ∈ (s.es.nodeOf p.node).heads ↔ x = p.new := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true] at h
  have hm := List.contains_iff_mem.1 h.1.1.2
  have hall := List.all_eq_true.1 h.1.2
  exact ⟨fun hx => by simpa using hall x hx, fun he => he ▸ hm⟩

/-- A packet matching its source names a node below `N`. -/
theorem packet_source_node {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) : p.node < N := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1

/-- If the hub accepts the packet, its applied records are the hub's, and the result's records
drop the packet's drops. Only packet fields are used, never current node state. -/
theorem packet_accept_fields {N : Nat} {s t : SEState} {p : PushPacket}
    (h : sexecStep N s p.accept = .ok t) :
    recEq p.applied s.recs = true ∧ t.recs = s.takeRecs p.allDrops := by
  unstep [PushPacket.accept, sexecStep, sexecCore] h with - hg
  simp only [acceptB, Bool.and_eq_true] at hg
  exact ⟨hg.1.1.1.1.1.1.1.2, rfl⟩

/-- If acceptance leaves the records unchanged, the packet's drops are exactly the hub's
dropped set. This uses the packet's send-time custody, not the sender's state at acceptance. -/
theorem packet_accept_fixed_drops {N : Nat} {s t : SEState} {p : PushPacket}
    (h : sexecStep N s p.accept = .ok t) (hfix : t.recs = s.recs) (x : Nat) :
    x ∈ p.allDrops ↔ x ∈ s.hubDL := by
  obtain ⟨hrec, heffect⟩ := packet_accept_fields h
  have hsub := (takeRecs_eq_iff s p.allDrops).1 (heffect.symm.trans hfix)
  constructor
  · exact hsub x
  · intro hx
    exact packet_custody p ((mem_flat_of_recEq hrec x).2 hx)

/-- A packet matching its source state, accepted with records unchanged, shows the source
sender's dropped set equals the hub's. The sender is identified by the packet, not by a ledger
entry naming the same head. -/
theorem packet_sender_aligned {N : Nat} {source s t : SEState} {p : PushPacket}
    (hsource : p.sourceMatchesB N source = true)
    (haccept : sexecStep N s p.accept = .ok t) (hfix : t.recs = s.recs) (x : Nat) :
    x ∈ source.nodeDF p.node ↔ x ∈ s.hubDL :=
  (packet_source_drops hsource x).symm.trans (packet_accept_fixed_drops haccept hfix x)

/-- If records and every node's drop set are fixed from step `k`, then a packet sent and
accepted after `k` shows its sender's dropped set equals the hub's at every step from `k`. The
sender is identified by the packet's own send-time snapshot. -/
theorem packet_sender_after_cut_aligned {N k sent accepted : Nat}
    {run : Nat → SEState} {p : PushPacket}
    (hrec : ∀ i, k ≤ i → (run i).recs = (run k).recs)
    (hdrop : ∀ i, k ≤ i → ∀ n, n < N → ∀ x,
      x ∈ (run i).nodeDF n ↔ x ∈ (run k).nodeDF n)
    (hsource : p.sourceMatchesB N (run sent) = true)
    (hsent : k ≤ sent) (haccepted : k ≤ accepted)
    (haccept : sexecStep N (run accepted) p.accept = .ok (run (accepted + 1))) :
    ∀ i, k ≤ i → ∀ x, x ∈ (run i).nodeDF p.node ↔ x ∈ (run i).hubDL := by
  have hn := packet_source_node hsource
  have hfix : (run (accepted + 1)).recs = (run accepted).recs :=
    (hrec _ (by omega)).trans (hrec _ haccepted).symm
  have halign := packet_sender_aligned hsource haccept hfix
  intro i hi x
  have hd := (hdrop i hi p.node hn x).trans (hdrop sent hsent p.node hn x).symm
  have hh : (run accepted).hubDL = (run i).hubDL := by
    simp only [SEState.hubDL, hrec accepted haccepted, hrec i hi]
  exact hd.trans ((halign x).trans (by rw [hh]))

/-! ## Upload coverage -/

/-- The packet uploads every op and object reachable from `new` but not from `expected`.
When pending drops rename the base, native `ops_between` instead excludes the union of the
`to_node(base)` images; that case is `UploadCoversBases`, once server-generated contraction
bodies are present. -/
structure UploadCovers (es : EState) (p : PushPacket) : Prop where
  ops : ∀ x, Anc es.parF x p.new → ¬ Anc es.parF x p.expected → x ∈ p.ops
  objs : ∀ o, (∃ x, Anc es.parF x p.new ∧ o ∈ es.objsF x) →
    (¬ ∃ x, Anc es.parF x p.expected ∧ o ∈ es.objsF x) → o ∈ p.objs

/-- The packet uploads every op and object reachable from `new` but not from `bases`, the base
frontier the sender's cache uses, in the graph after this packet's contraction. The scoped
native law must identify the same images at sender and hub and establish their generated
closure. It does not project arbitrary canonical versions. -/
structure UploadCoversBases (es : EState) (p : PushPacket) (bases : List Nat) : Prop where
  ops : ∀ x, Anc es.parF x p.new →
    (¬ ∃ b ∈ bases, Anc es.parF x b) → x ∈ p.ops
  objs : ∀ o, (∃ x, Anc es.parF x p.new ∧ o ∈ es.objsF x) →
    (¬ ∃ b ∈ bases, ∃ x, Anc es.parF x b ∧ o ∈ es.objsF x) → o ∈ p.objs

/-- `UploadCoversBases` with separate exclusions for bodies and objects. `ops_between` excludes
the current base images (`opBases`); `objects_attachment` also excludes objects reachable from
the raw expected head (`objectBases`). Those older objects stay stored even when contraction
drops their body, so they are already at the hub (`hobjects` in `packet_upload_closes_split`).
The generated image-base closure covers the rest. -/
structure UploadCoversSplit (es : EState) (p : PushPacket)
    (opBases objectBases : List Nat) : Prop where
  ops : ∀ x, Anc es.parF x p.new →
    (¬ ∃ b ∈ opBases, Anc es.parF x b) → x ∈ p.ops
  objs : ∀ o, (∃ x, Anc es.parF x p.new ∧ o ∈ es.objsF x) →
    (¬ ∃ b ∈ opBases, ∃ x, Anc es.parF x b ∧ o ∈ es.objsF x) →
    (¬ ∃ b ∈ objectBases, ∃ x, Anc es.parF x b ∧ o ∈ es.objsF x) → o ∈ p.objs

/-- The packet's upload closes `new` at the hub, given `UploadCoversSplit`. -/
theorem packet_upload_closes_split {es : EState} {p : PushPacket}
    {opBases objectBases : List Nat} (hpar : ParLt es.parF)
    (hclosed : ∀ b ∈ opBases, ClosedAt (abs es) b)
    (hobjects : ∀ b ∈ objectBases, ∀ x, Anc es.parF x b →
      ∀ o ∈ es.objsF x, o ∈ es.hub.objs)
    (hc : UploadCoversSplit es p opBases objectBases) :
    (es.hubStore p.ops p.objs).closedB p.new = true := by
  apply (closedB_iff (es := es.hubStore p.ops p.objs) hpar).2
  intro x hx
  have hx' : Anc es.parF x p.new := hx
  constructor
  · change x ∈ union es.hub.ops p.ops
    by_cases he : ∃ b ∈ opBases, Anc es.parF x b
    · obtain ⟨b, hb, he⟩ := he
      exact mem_union.2 (.inl (hclosed b hb x he).1)
    · exact mem_union.2 (.inr (hc.ops x hx' he))
  · intro o ho
    change o ∈ union es.hub.objs p.objs
    have ho' : o ∈ es.objsF x := ho
    by_cases he : ∃ b ∈ opBases, ∃ y, Anc es.parF y b ∧ o ∈ es.objsF y
    · obtain ⟨b, hb, y, hy, ho⟩ := he
      exact mem_union.2 (.inl ((hclosed b hb y hy).2 o ho))
    · by_cases old : ∃ b ∈ objectBases, ∃ y, Anc es.parF y b ∧ o ∈ es.objsF y
      · obtain ⟨b, hb, y, hy, ho⟩ := old
        exact mem_union.2 (.inl (hobjects b hb y hy o ho))
      · exact mem_union.2 (.inr (hc.objs o ⟨x, hx', ho'⟩ he old))

/-- The packet's upload closes `new` at the hub, given `UploadCoversBases`. -/
theorem packet_upload_closes_from_bases {es : EState} {p : PushPacket} {bases : List Nat}
    (hpar : ParLt es.parF) (hclosed : ∀ b ∈ bases, ClosedAt (abs es) b)
    (hc : UploadCoversBases es p bases) :
    (es.hubStore p.ops p.objs).closedB p.new = true := by
  apply (closedB_iff (es := es.hubStore p.ops p.objs) hpar).2
  intro x hx
  have hx' : Anc es.parF x p.new := hx
  constructor
  · change x ∈ union es.hub.ops p.ops
    by_cases he : ∃ b ∈ bases, Anc es.parF x b
    · obtain ⟨b, hb, he⟩ := he
      exact mem_union.2 (.inl (hclosed b hb x he).1)
    · exact mem_union.2 (.inr (hc.ops x hx' he))
  · intro o ho
    change o ∈ union es.hub.objs p.objs
    have ho' : o ∈ es.objsF x := ho
    by_cases he : ∃ b ∈ bases, ∃ y, Anc es.parF y b ∧ o ∈ es.objsF y
    · obtain ⟨b, hb, y, hy, ho⟩ := he
      exact mem_union.2 (.inl ((hclosed b hb y hy).2 o ho))
    · exact mem_union.2 (.inr (hc.objs o ⟨x, hx', ho'⟩ he))

/-- The packet's upload closes `new` at the hub, given `UploadCovers`. -/
theorem packet_upload_closes {es : EState} {p : PushPacket}
    (hpar : ParLt es.parF) (hclosed : ClosedAt (abs es) p.expected)
    (hc : UploadCovers es p) : (es.hubStore p.ops p.objs).closedB p.new = true := by
  apply (closedB_iff (es := es.hubStore p.ops p.objs) hpar).2
  intro x hx
  have hx' : Anc es.parF x p.new := hx
  constructor
  · change x ∈ union es.hub.ops p.ops
    by_cases he : Anc es.parF x p.expected
    · exact mem_union.2 (.inl (hclosed x he).1)
    · exact mem_union.2 (.inr (hc.ops x hx' he))
  · intro o ho
    change o ∈ union es.hub.objs p.objs
    have ho' : o ∈ es.objsF x := ho
    by_cases he : ∃ y, Anc es.parF y p.expected ∧ o ∈ es.objsF y
    · obtain ⟨y, hy, ho⟩ := he
      exact mem_union.2 (.inl ((hclosed y hy).2 o ho))
    · exact mem_union.2 (.inr (hc.objs o ⟨x, hx', ho'⟩ he))

/-- The native boundary laws for one immutable packet `p` sent from `s`. Record equality and
the expected head come from `Emit` and the stable hub; custody comes from the actual send. The
adapter supplies survival, comparison and closure. The fields are checks: neither a successful
outcome nor a rank decrease is one of them. -/
structure PacketPrimitives (s : SEState) (p : PushPacket) : Prop where
  par : s.es.parOK = true
  ledger : ledgerB s p.node p.new p.applied p.allDrops = true
  survives : !s.remDL.contains p.new = true
  pending : !(pendingOf p.applied p.allDrops).contains p.new = true
  sent : s.es.inNet (.push p.node p.ops p.objs p.expected p.new) = true
  descends : belowB s.es.parF (acceptDrops s p.allDrops).contains p.expected p.new = true
  closed : (s.es.hubStore p.ops p.objs).closedB p.new = true

/-- `PacketPrimitives`, plus: the packet's records are the hub's, its new head differs from the
hub's head, and its expected head is the hub's head. -/
structure PacketChecks (s : SEState) (p : PushPacket) : Prop extends PacketPrimitives s p where
  records : recEq p.applied s.recs = true
  different : s.es.hub.head ≠ p.new
  expected : s.es.hub.head = p.expected

/-- `PacketChecks` for a packet built from the sender's state `σ`. Source and hub use the same
ordered-record identity, and the packet is the actual post-write packet. `Emit` supplies the
matching records, the expected head and a new head distinct from the hub's; the remaining
primitive laws are the hypothesis `hnative`. -/
theorem packet_checks_of_emit {c : NodeSettle.Ctx} {σ σ1 : NodeSettle.NS} {new : Nat}
    {s : SEState} {p : PushPacket} (hi : NodeSettle.SInv c σ)
    (hem : NodeSettle.Emit c σ σ1 new) (hnative : PacketPrimitives s p)
    (hexpected : p.expected = σ.known.head) (hnew : p.new = new)
    (hhead : s.es.hub.head = c.H)
    (decode : Nat → List Rec)
    (hsource : p.applied = decode σ.ap) (hhub : s.recs = decode c.R) : PacketChecks s p := by
  obtain ⟨hk, hap, _, hne, _⟩ := NodeSettle.emit_packet hi hem
  refine ⟨hnative, ?_, ?_, ?_⟩
  · rw [hsource, hhub, hap]
    exact recEq_self _
  · rw [hhead, hnew]
    exact Ne.symm hne
  · rw [hhead, hexpected, hk]

/-- `PacketChecks` imply the executable acceptance guard `acceptB`. -/
theorem packet_checks_acceptB {s : SEState} {p : PushPacket} (h : PacketChecks s p) :
    acceptB s p.node p.ops p.objs p.expected p.new p.applied p.allDrops = true := by
  simp only [acceptB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h.ledger, h.records⟩, h.survives⟩, h.pending⟩, h.sent⟩, h.different⟩,
    h.expected⟩, h.descends⟩, h.closed⟩

/-- An accepted packet moves the hub to the packet's new head, with sequence plus one. -/
theorem packet_accept_effect {N : Nat} {s t : SEState} {p : PushPacket}
    (h : sexecStep N s p.accept = .ok t) :
    t.es.hub.head = p.new ∧ t.es.hub.seq = s.es.hub.seq + 1 := by
  unstep [PushPacket.accept, sexecStep, sexecCore] h with - -
  obtain ⟨hseq, hhead⟩ := acceptPush_hub s.es p.node p.ops p.objs p.new
  exact ⟨hhead, hseq⟩

/-- `PacketChecks` make `sexecStep` accept the packet, and the hub moves to the packet's new
head with sequence plus one. -/
theorem packet_checks_accept {N : Nat} {s : SEState} {p : PushPacket}
    (h : PacketChecks s p) :
    ∃ t, sexecStep N s p.accept = .ok t ∧
      t.es.hub.head = p.new ∧ t.es.hub.seq = s.es.hub.seq + 1 := by
  have hg := packet_checks_acceptB h
  have ht : sexecStep N s p.accept =
      .ok (s.supAccept (s.es.acceptPush p.node p.ops p.objs p.new) p.allDrops) := by
    simp [PushPacket.accept, sexecStep, sexecCore, req, h.par, hg]
  exact ⟨_, ht, packet_accept_effect ht⟩

/-- `PacketChecks` make the packet's rejection guard false. -/
theorem packet_checks_no_reject {s : SEState} {p : PushPacket} (h : PacketChecks s p) :
    rejectB s p.node p.ops p.objs p.expected p.new p.applied p.allDrops = false := by
  simp [rejectB, h.expected, h.descends]

/-- Every decision the hub can make on this packet: acceptance, refusal, idempotence, rejection
or incompleteness. The refusal guard is checked before idempotence, ancestry or closure, as in
`Push::answer`. `packet_checks_force_accept` shows that `PacketChecks` leave only acceptance. -/
inductive PacketHandled (N : Nat) (s : SEState) (p : PushPacket) : SEState → Prop
  | accept {t : SEState} (h : sexecStep N s p.accept = .ok t) : PacketHandled N s p t
  | refused (t : SEState) (h : (!recEq p.applied s.recs || s.remDL.contains p.new ||
      (pendingOf p.applied p.allDrops).contains p.new) = true) : PacketHandled N s p t
  | idempotent (t : SEState) (h : s.es.hub.head = p.new) : PacketHandled N s p t
  | rejected (t : SEState)
      (h : rejectB s p.node p.ops p.objs p.expected p.new p.applied p.allDrops = true) :
      PacketHandled N s p t
  | incomplete (t : SEState) (h : (s.es.hubStore p.ops p.objs).closedB p.new = false) :
      PacketHandled N s p t

/-- Under `PacketChecks`, any hub decision on the packet is acceptance, moving the hub to the
new head with sequence plus one. -/
theorem packet_checks_force_accept {N : Nat} {s t : SEState} {p : PushPacket}
    (hc : PacketChecks s p) (hh : PacketHandled N s p t) :
    sexecStep N s p.accept = .ok t ∧
      t.es.hub.head = p.new ∧ t.es.hub.seq = s.es.hub.seq + 1 := by
  cases hh with
  | accept h => exact ⟨h, packet_accept_effect h⟩
  | refused h =>
    have hs : s.remDL.contains p.new = false := by simpa using hc.survives
    have hp : (pendingOf p.applied p.allDrops).contains p.new = false :=
      by simpa using hc.pending
    simp only [hc.records, hs, hp, Bool.not_true, Bool.false_or, Bool.false_eq_true] at h
  | idempotent h => exact False.elim (hc.different h)
  | rejected h => rw [packet_checks_no_reject hc] at h; contradiction
  | incomplete h => rw [hc.closed] at h; contradiction

end Musubi.Exec

/-! ## A node's pending drops, pushed on raw ids

The core pushes its pending drops only from the hub's head it knows, with the hub's records,
to a raw head other than the one it knows (`NodeCore::step`). Given the hub's own checks for
that push (whether its records are the hub's, `is_dropped`, `is_closed` and `descends`, the last
three once the history drops what the push drops), `Push::answer` accepts it: the hub's
sequence and head move. So a tail where the hub stays as it is answers no such push.

The expected head and the new one are compared as the core and the hub compare them, raw ids
and not originals: a contracted rewrite `X'` of the known head `X` is another head, and the
hub's `descends`, not raw ancestry, judges `X` below it, naming it by the raw images the node
names it by (`descends_of_images`). `HubLaw`, whose guard is raw ancestry once records are
fixed, does not describe this accept, which may change the records.

Whether the push's records are the hub's is the hub's own comparison of them, count and digest
(`Checks.recordsMatch`). What an accept does to the records (`set_head` appends the push's
drops, less what the records drop already, if that leaves any) is not modelled here: the
ordered-record layer (`RecordCut`, `PacketCoupling`) owns it. -/

namespace Musubi.RawPublish

open Musubi

/-- The hub as `Push::answer` reads and moves it: its sequence and its head, a raw id. -/
structure Hub where
  seq : Nat
  head : Nat
  deriving DecidableEq, Repr

/-- A push as the hub reads it: the head it expects, the new head and what it drops, raw ids.
-/
structure Push where
  expected : Nat
  new : Nat
  dropped : List Nat
  deriving DecidableEq, Repr

/-- What `Push::answer` decides, in its order (`CasOutcome`). -/
inductive Outcome
  | refused
  | idempotent
  | incomplete
  | accepted
  | rejected
  deriving DecidableEq, Repr

/-- `CasOutcome`'s name for each outcome. -/
def Outcome.name : Outcome → String
  | .refused => "Refused"
  | .idempotent => "Idempotent"
  | .incomplete => "Incomplete"
  | .accepted => "Accepted"
  | .rejected => "Rejected"

/-- The hub's checks of one push at one state: whether the push's records are the hub's, as
`RecordState`s, count and digest; `is_dropped(new, dropped)`; and, once the push's operations
and objects are stored, `is_closed(new, dropped)` and `descends(expected, new, dropped)`. -/
structure Checks where
  recordsMatch : Bool
  dropped : Bool
  closed : Bool
  descends : Bool

/-- `Push::answer` on raw ids, from the hub at `h`. -/
def answer (h : Hub) (p : Push) (c : Checks) : Outcome :=
  if c.recordsMatch = false ∨ c.dropped = true then .refused
  else if p.new = h.head then .idempotent
  else if h.head = p.expected ∧ c.closed = false then .incomplete
  else if h.head = p.expected ∧ c.descends = true then .accepted
  else .rejected

/-- The hub's sequence and head after answering: an accept moves both (`set_head`). -/
def after (h : Hub) (p : Push) (c : Checks) : Hub :=
  if answer h p c = .accepted then ⟨h.seq + 1, p.new⟩ else h

/-- The oracle's answer to one push: the outcome, and the hub's sequence and head after. -/
def rawPush (h : Hub) (p : Push) (c : Checks) : Outcome × Hub :=
  (answer h p c, after h p c)

theorem answer_accepted {h : Hub} {p : Push} {c : Checks} (hr : c.recordsMatch = true)
    (hd : c.dropped = false) (hn : p.new ≠ h.head) (he : h.head = p.expected)
    (hc : c.closed = true) (hdesc : c.descends = true) : answer h p c = .accepted := by
  have he' : p.new ≠ p.expected := he ▸ hn
  simp [answer, hr, hd, he, he', hc, hdesc]

/-- An accept is never a frame of the hub. -/
theorem after_accepted_ne {h : Hub} {p : Push} {c : Checks} (ha : answer h p c = .accepted) :
    after h p c ≠ h := by
  intro he
  have hs := congrArg Hub.seq he
  simp only [after, ha, ite_true] at hs
  omega

/-- The core's pending branch (`NodeCore::step`), what it fixes of the push it sends: the
known head is local and below a head, there are pending drops, and the new head is not the
known one, raw ids compared (`new == known` polls instead). That its records are the hub's
is the hub's check, not a field of the push. -/
structure PendingPush (known : Known) (p : Push) : Prop where
  expected : p.expected = known.head
  moved : p.new ≠ known.head
  pending : p.dropped ≠ []

/-- The hub's `descends(expected, new, dropped)` from raw facts alone: the hub names the
expected head, once the history drops what the push drops, by `images`, the raw canonical ids
the node's `to_node` gives it (one law of the hub and the adapter), and judges them in the
global raw graph. The core's branch has each image below its head (`is_ancestor(known, head)`,
looping `canonical_is_ancestor` over them), and the new head is that head or the fix-up on it.
No original is identified with a raw id. -/
theorem descends_of_images {par : Nat → List Nat} {images : List Nat} {head new : Nat}
    {c : Checks} (hne : images ≠ [])
    (hhub : c.descends = true ↔ images ≠ [] ∧ ∀ i ∈ images, Anc par i new)
    (hguard : ∀ i ∈ images, Anc par i head) (hnew : Anc par head new) : c.descends = true :=
  hhub.2 ⟨hne, fun i hi => (hguard i hi).trans hnew⟩

/-- On a hub at `h` whose head the node knows, the pending push is accepted, given the hub's
checks of it: its records the hub's, as the hub compares them; not dropped, as the node
asserts it never pushes; closed once uploaded; and `descends`. -/
theorem pendingPush_accepted {known : Known} {p : Push} {c : Checks} {h : Hub}
    (b : PendingPush known p) (hk : known.head = h.head) (hr : c.recordsMatch = true)
    (hd : c.dropped = false) (hc : c.closed = true) (hdesc : c.descends = true) :
    answer h p c = .accepted := by
  refine answer_accepted hr hd ?_ ?_ hc hdesc
  · rw [← hk]; exact b.moved
  · rw [b.expected, hk]

/-- So a hub that stays as it is answers no such push. -/
theorem stable_no_pendingPush {known : Known} {p : Push} {c : Checks} {h : Hub}
    (b : PendingPush known p) (hk : known.head = h.head) (hr : c.recordsMatch = true)
    (hd : c.dropped = false) (hc : c.closed = true) (hdesc : c.descends = true)
    (hstable : after h p c = h) : False :=
  after_accepted_ne (pendingPush_accepted b hk hr hd hc hdesc) hstable

end Musubi.RawPublish

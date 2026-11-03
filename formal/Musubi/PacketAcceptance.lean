/-
The packet's acceptance boundary. Metadata identity is not enough: the actual packet must
also upload the complete closure and satisfy the adapter's scoped contracted comparison.
Given these primitive checks, acceptance and the exact head/sequence effect follow from
the executable hub, rather than being an assumed implementation progress event.

The last section takes a node's pending drops on raw ids, as `Push::answer` sees them, with no
original identified with a raw id (`Musubi.RawPublish`).
-/
import Musubi.PacketCoupling
import Musubi.CutHistory
import Musubi.NodeSettle

namespace Musubi.Exec

open Musubi Contract

/-- Sufficient upload coverage without renaming the base. Native ops_between instead
excludes the union of its actual to_node(base) images when pending drops rename that base;
that case uses UploadCoversBases after server-generated contraction bodies are present. -/
structure UploadCovers (es : EState) (p : PushPacket) : Prop where
  ops : ∀ x, Anc es.parF x p.new → ¬ Anc es.parF x p.expected → x ∈ p.ops
  objs : ∀ o, (∃ x, Anc es.parF x p.new ∧ o ∈ es.objsF x) →
    (¬ ∃ x, Anc es.parF x p.expected ∧ o ∈ es.objsF x) → o ∈ p.objs

/-- The exact base frontier used by the sender's cache, in the graph after this packet's
contraction. The scoped native law must identify the SAME images at sender and hub and
establish their generated closure. This does not project arbitrary canonical versions. -/
structure UploadCoversBases (es : EState) (p : PushPacket) (bases : List Nat) : Prop where
  ops : ∀ x, Anc es.parF x p.new →
    (¬ ∃ b ∈ bases, Anc es.parF x b) → x ∈ p.ops
  objs : ∀ o, (∃ x, Anc es.parF x p.new ∧ o ∈ es.objsF x) →
    (¬ ∃ b ∈ bases, ∃ x, Anc es.parF x b ∧ o ∈ es.objsF x) → o ∈ p.objs

/-- The native upload can use different exclusions for bodies and objects: ops_between
uses the current base images, while objects_attachment also uses objects reachable from
the raw expected head. Those old objects remain stored even when contraction drops its
body. Generated image-base closure and those separately retained objects cover the rest. -/
structure UploadCoversSplit (es : EState) (p : PushPacket)
    (opBases objectBases : List Nat) : Prop where
  ops : ∀ x, Anc es.parF x p.new →
    (¬ ∃ b ∈ opBases, Anc es.parF x b) → x ∈ p.ops
  objs : ∀ o, (∃ x, Anc es.parF x p.new ∧ o ∈ es.objsF x) →
    (¬ ∃ b ∈ opBases, ∃ x, Anc es.parF x b ∧ o ∈ es.objsF x) →
    (¬ ∃ b ∈ objectBases, ∃ x, Anc es.parF x b ∧ o ∈ es.objsF x) → o ∈ p.objs

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

/-- The native boundary laws for the SAME immutable packet. Record equality and expected
head come from Emit and the stable hub; custody comes from its actual send. The adapter
supplies survival, comparison and closure, not a successful outcome or rank decrease. -/
structure PacketPrimitives (s : SEState) (p : PushPacket) : Prop where
  par : s.es.parOK = true
  ledger : (s.sups.any fun q => q.1 == p.node && recEq q.2.1 p.applied &&
    seteq q.2.2.1 p.allDrops && q.2.2.2 == p.new) = true
  survives : !s.remDL.contains p.new = true
  pending : !(pendingOf p.applied p.allDrops).contains p.new = true
  sent : s.es.inNet (.push p.node p.ops p.objs p.expected p.new) = true
  descends : belowB s.es.parF (acceptDrops s p.applied p.allDrops).contains
    p.expected p.new = true
  closed : (s.es.hubStore p.ops p.objs).closedB p.new = true
  wellFormed : imageAcceptSafeB s p.ops p.new p.applied p.allDrops = true

structure PacketChecks (s : SEState) (p : PushPacket) : Prop extends PacketPrimitives s p where
  records : recEq p.applied s.recs = true
  different : s.es.hub.head ≠ p.new
  expected : s.es.hub.head = p.expected

/-- The source and hub use the same ordered-record identity, and the packet is the actual
post-write packet. Emit supplies matching metadata, expected head and a distinct new head;
the remaining primitive laws are deliberately not disguised as a liveness premise. -/
theorem packet_checks_of_emit {c : NodeSettle.Ctx} {σ σ1 : NodeSettle.NS} {new : Nat}
    {s : SEState} {p : PushPacket} (hi : NodeSettle.SInv c σ)
    (hem : NodeSettle.Emit c σ σ1 new) (hnative : PacketPrimitives s p)
    (hexpected : p.expected = σ.known.2) (hnew : p.new = new)
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

theorem packet_checks_acceptB {s : SEState} {p : PushPacket} (h : PacketChecks s p) :
    imageAcceptB s p.node p.ops p.objs p.expected p.new p.applied p.allDrops = true := by
  simp only [imageAcceptB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.par, h.ledger⟩, h.records⟩, h.survives⟩, h.pending⟩,
    h.sent⟩, h.different⟩, h.expected⟩, h.descends⟩, h.closed⟩, h.wellFormed⟩

theorem packet_accept_effect {N : Nat} {s t : SEState} {p : PushPacket}
    (h : cexecAction N s p.accept = .ok t) :
    t.es.hub.head = p.new ∧ t.es.hub.seq = s.es.hub.seq + 1 := by
  simp only [PushPacket.accept, cexecAction, cexecStep] at h
  cases hs : sexecStep N s
      (.hubSupAccept p.node p.ops p.objs p.expected p.new p.applied p.allDrops) with
  | ok result =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h
      obtain ⟨-, hs⟩ := sreq_ok hs
      simp only [sexecCore] at hs
      obtain ⟨-, hs⟩ := sreq_ok hs
      obtain ⟨-, hs⟩ := sreq_ok hs
      obtain ⟨-, hs⟩ := sreq_ok hs
      split at hs
      · cases hs
      · rename_i es' he
        obtain ⟨-, hs⟩ := sreq_ok hs
        cases hs
        obtain ⟨-, -, -, hh, hseq⟩ := execStep_hubPushAccept_guards he
        exact ⟨hh, hseq⟩
    · contradiction
  | error error =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h
      simp [SEState.imageAccept, SEState.supAccept, send_hub, EState.hubAccept,
        EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]
    · contradiction

/-- A proper packet enables the checked acceptance transition, in both the ordinary and
surviving-image paths. The resulting move is for this packet's new head, not some unrelated
sequence increase elsewhere in the run. -/
theorem packet_checks_accept {N : Nat} {s : SEState} {p : PushPacket}
    (h : PacketChecks s p) :
    ∃ t, cexecAction N s p.accept = .ok t ∧
      t.es.hub.head = p.new ∧ t.es.hub.seq = s.es.hub.seq + 1 := by
  have hg := packet_checks_acceptB h
  have hex : ∃ t, cexecAction N s p.accept = .ok t := by
    simp only [PushPacket.accept, cexecAction, cexecStep]
    cases hs : sexecStep N s
        (.hubSupAccept p.node p.ops p.objs p.expected p.new p.applied p.allDrops) with
    | ok result => exact ⟨result, by simp [legacyOutcomeB]⟩
    | error error =>
      exact ⟨s.imageAccept p.node p.ops p.objs p.new p.allDrops, by simp [hg]⟩
  obtain ⟨t, ht⟩ := hex
  exact ⟨t, ht, packet_accept_effect ht⟩

/-- The packet-specific rejection guard cannot reject those same primitive checks. -/
theorem packet_checks_no_reject {s : SEState} {p : PushPacket} (h : PacketChecks s p) :
    imageRejectB s p.node p.ops p.objs p.expected p.new p.applied p.allDrops = false := by
  simp [imageRejectB, h.expected, h.descends]

/-- An actual hub decision for this immutable packet. The refusal guard is checked before
idempotence, ancestry or closure, as in Push::answer. The relation permits every unsuccessful
outcome; the primitive checks below, rather than an assumed success, rule them out. -/
inductive PacketHandled (N : Nat) (s : SEState) (p : PushPacket) : SEState → Prop
  | accept {t : SEState} (h : cexecAction N s p.accept = .ok t) : PacketHandled N s p t
  | refused (t : SEState) (h : (!recEq p.applied s.recs || s.remDL.contains p.new ||
      (pendingOf p.applied p.allDrops).contains p.new) = true) : PacketHandled N s p t
  | idempotent (t : SEState) (h : s.es.hub.head = p.new) : PacketHandled N s p t
  | rejected (t : SEState)
      (h : imageRejectB s p.node p.ops p.objs p.expected p.new p.applied p.allDrops = true) :
      PacketHandled N s p t
  | incomplete (t : SEState) (h : (s.es.hubStore p.ops p.objs).closedB p.new = false) :
      PacketHandled N s p t

theorem packet_checks_force_accept {N : Nat} {s t : SEState} {p : PushPacket}
    (hc : PacketChecks s p) (hh : PacketHandled N s p t) :
    cexecAction N s p.accept = .ok t ∧
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
structure PendingPush (known : Nat × Nat) (p : Push) : Prop where
  expected : p.expected = known.2
  moved : p.new ≠ known.2
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
theorem pendingPush_accepted {known : Nat × Nat} {p : Push} {c : Checks} {h : Hub}
    (b : PendingPush known p) (hk : known.2 = h.head) (hr : c.recordsMatch = true)
    (hd : c.dropped = false) (hc : c.closed = true) (hdesc : c.descends = true) :
    answer h p c = .accepted := by
  refine answer_accepted hr hd ?_ ?_ hc hdesc
  · rw [← hk]; exact b.moved
  · rw [b.expected, hk]

/-- So a hub that stays as it is answers no such push. -/
theorem stable_no_pendingPush {known : Nat × Nat} {p : Push} {c : Checks} {h : Hub}
    (b : PendingPush known p) (hk : known.2 = h.head) (hr : c.recordsMatch = true)
    (hd : c.dropped = false) (hc : c.closed = true) (hdesc : c.descends = true)
    (hstable : after h p c = h) : False :=
  after_accepted_ne (pendingPush_accepted b hk hr hd hc hdesc) hstable

end Musubi.RawPublish

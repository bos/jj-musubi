/-
One complete push, coupled to the state from which it was sent. A supersede ledger entry holds
only a node and a new head, with no expected head, so it cannot identify a request. Here the
accepting action takes every field from one immutable packet.

The convergence proof uses `PushPacket` from this file. The packet-coupling theorems
(`packet_sender_aligned`, `packet_accept_fields` and the rest) are not used by the assembly;
they stand alone.
-/
import Musubi.PostCut

namespace Musubi.Exec

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
def PushPacket.accept (p : PushPacket) : CAction :=
  .old (.hubSupAccept p.node p.ops p.objs p.expected p.new p.applied p.allDrops)

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

/-- If `cexecAction` accepts the packet, whether `sexecStep` succeeds or the error is resolved
by the `imageAcceptB` guard, the packet's applied records equal the current records and the
result's records drop the packet's drop set. Only packet fields are used, never current node
state. -/
theorem packet_accept_fields {N : Nat} {s t : SEState} {p : PushPacket}
    (h : cexecAction N s p.accept = .ok t) :
    recEq p.applied s.recs = true ∧ t.recs = s.takeRecs p.allDrops := by
  simp only [PushPacket.accept, cexecAction, cexecStep] at h
  cases hs : sexecStep N s
      (.hubSupAccept p.node p.ops p.objs p.expected p.new p.applied p.allDrops) with
  | ok result =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h
      peel hs with _
      simp only [sexecCore] at hs
      peel hs with _ hrec _
      split at hs
      · cases hs
      · peel hs with _
        cases hs
        exact ⟨hrec, rfl⟩
    · contradiction
  | error error =>
    rw [hs] at h
    simp only at h
    split at h
    · rename_i hg
      cases h
      have hrec : recEq p.applied s.recs = true := by
        simp only [imageAcceptB, Bool.and_eq_true] at hg
        exact hg.1.1.1.1.1.1.1.1.2
      exact ⟨hrec, rfl⟩
    · contradiction

/-- If acceptance leaves the records unchanged, the packet's drops are exactly the hub's
dropped set. This uses the packet's send-time custody, not the sender's state at acceptance. -/
theorem packet_accept_fixed_drops {N : Nat} {s t : SEState} {p : PushPacket}
    (h : cexecAction N s p.accept = .ok t) (hfix : t.recs = s.recs) (x : Nat) :
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
    (haccept : cexecAction N s p.accept = .ok t) (hfix : t.recs = s.recs) (x : Nat) :
    x ∈ source.nodeDF p.node ↔ x ∈ s.hubDL :=
  (packet_source_drops hsource x).symm.trans (packet_accept_fixed_drops haccept hfix x)

/-- A packet matching its source names a node below `N`. -/
theorem packet_source_node {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) : p.node < N := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1

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
    (haccept : cexecAction N (run accepted) p.accept = .ok (run (accepted + 1))) :
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

end Musubi.Exec

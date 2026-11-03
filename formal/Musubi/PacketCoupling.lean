/-
One complete push, coupled to the state from which it was sent. The supersede ledger alone
does not provide request identity: its entries omit the expected head and are matched by
node and new head. Here the accepting action takes all fields from the same immutable packet.
-/
import Musubi.RecoveryEpoch

namespace Musubi.Exec

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

def PushPacket.allDrops (p : PushPacket) : List Nat := union (flat p.applied) p.pending

def PushPacket.accept (p : PushPacket) : CAction :=
  .old (.hubSupAccept p.node p.ops p.objs p.expected p.new p.applied p.allDrops)

/-- The checked send boundary. Request/session ids are transport control, separately tied
to slots; these are the semantic fields that must come from that same send-time snapshot. -/
def PushPacket.sourceMatchesB (N : Nat) (s : SEState) (p : PushPacket) : Bool :=
  decide (p.node < N) && recEq p.applied (s.appliedF p.node) &&
    seteq p.allDrops (s.nodeDF p.node) &&
    decide (p.expected = (s.es.nodeOf p.node).known.2) &&
    decide (p.knownSeq = (s.es.nodeOf p.node).known.1) &&
    (s.es.nodeOf p.node).heads.contains p.new &&
    (s.es.nodeOf p.node).heads.all (· == p.new) &&
    p.pending.all (fun x => !(flat p.applied).contains x)

theorem packet_custody (p : PushPacket) {x : Nat} (hx : x ∈ flat p.applied) :
    x ∈ p.allDrops := mem_union.2 (.inl hx)

theorem packet_source_drops {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) (x : Nat) :
    x ∈ p.allDrops ↔ x ∈ s.nodeDF p.node := by
  have he : seteq p.allDrops (s.nodeDF p.node) = true := by
    simp only [PushPacket.sourceMatchesB, Bool.and_eq_true] at h
    exact h.1.1.1.1.1.2
  exact mem_of_seteq he x

theorem packet_source_known {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) :
    (s.es.nodeOf p.node).known = (p.knownSeq, p.expected) := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Prod.ext h.1.1.1.2.symm h.1.1.1.1.2.symm

theorem packet_source_heads {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) (x : Nat) :
    x ∈ (s.es.nodeOf p.node).heads ↔ x = p.new := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true] at h
  have hm := List.contains_iff_mem.1 h.1.1.2
  have hall := List.all_eq_true.1 h.1.2
  exact ⟨fun hx => by simpa using hall x hx, fun he => he ▸ hm⟩

/-- The accepted action uses the packet's own records and drop set in both legacy and
survivor-acceptance branches. It cannot pair a request with unrelated current node state. -/
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
      obtain ⟨_, hs⟩ := sreq_ok hs
      simp only [sexecCore] at hs
      obtain ⟨_, hs⟩ := sreq_ok hs
      obtain ⟨hrec, hs⟩ := sreq_ok hs
      obtain ⟨_, hs⟩ := sreq_ok hs
      split at hs
      · cases hs
      · obtain ⟨_, hs⟩ := sreq_ok hs
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

/-- With fixed records, a successful packet carries exactly the hub's dropped set. This
uses send-time custody, not the sender's possibly changed state at the time of acceptance. -/
theorem packet_accept_fixed_drops {N : Nat} {s t : SEState} {p : PushPacket}
    (h : cexecAction N s p.accept = .ok t) (hfix : t.recs = s.recs) (x : Nat) :
    x ∈ p.allDrops ↔ x ∈ s.hubDL := by
  obtain ⟨hrec, heffect⟩ := packet_accept_fields h
  have hsub := (takeRecs_eq_iff s p.allDrops).1 (heffect.symm.trans hfix)
  constructor
  · exact hsub x
  · intro hx
    exact packet_custody p ((mem_flat_of_recEq hrec x).2 hx)

/-- Coupling the full packet to its source identifies that actual sender's dropped set,
instead of selecting some ledger entry that happens to name the same accepted head. -/
theorem packet_sender_aligned {N : Nat} {source s t : SEState} {p : PushPacket}
    (hsource : p.sourceMatchesB N source = true)
    (haccept : cexecAction N s p.accept = .ok t) (hfix : t.recs = s.recs) (x : Nat) :
    x ∈ source.nodeDF p.node ↔ x ∈ s.hubDL :=
  (packet_source_drops hsource x).symm.trans (packet_accept_fixed_drops haccept hfix x)

theorem packet_source_node {N : Nat} {s : SEState} {p : PushPacket}
    (h : p.sourceMatchesB N s = true) : p.node < N := by
  simp only [PushPacket.sourceMatchesB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1.1.1.1

/-- Once records and participant drop sets are fixed, a packet sent in that suffix and
accepted there identifies its actual sender as eligible for the entire suffix. No ledger
entry with merely the same target is substituted for the packet's own send snapshot. -/
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

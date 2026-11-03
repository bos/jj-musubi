/-
Composition at the actual acceptance boundary. A fair node does not get convergence by an
assumed decreasing implementation rank: NodeSettle derives the finite local work. Its other
outcome is a correctly formed push, whose successful handling moves the hub. Once HubSuffix
has proved the hub stable, that alternative is impossible. Finitely many nodes then admit a
common convergence cut. Suffix entry and the scoped adapter/transport refinement remain
separate obligations; this module states those boundary contracts explicitly.
-/
import Musubi.HubSuffix
import Musubi.NodeSettle
import Musubi.RecordReplies
import Musubi.RecordEpoch
import Musubi.CutHistory
import Musubi.PacketAcceptance

namespace Musubi.Recovery

open Musubi NodeSettle

/-- A correctly formed emitted push is eventually handled successfully. This is the
transport/adapter boundary: expected is the fixed hub head, records are its fixed ordered
list, the uploaded closure is complete and its dropped-head/ancestry checks pass. It does
not assume an entire round completes, or that the node itself has already converged. -/
def AcceptedEmits (_c : Ctx) (_run : Nat → NS) (lab : Nat → Lab)
    (hubSeq : Nat → Nat) (k : Nat) : Prop :=
  ∀ i, k ≤ i → lab i = .emit → ∃ j, i ≤ j ∧ hubSeq (j + 1) = hubSeq j + 1

/-- The real post-write packet and the real hub decision share one witness. Primitive
survival/comparison/upload laws are separate from the result of handling that packet. -/
structure EmittedPacketBoundary (N : Nat) (σ : NS) (new : Nat)
    (before after : Exec.SEState) (decode : Nat → List Exec.Rec) where
  packet : Exec.PushPacket
  primitives : Exec.PacketPrimitives before packet
  expected : packet.expected = σ.known.2
  target : packet.new = new
  sourceRecords : packet.applied = decode σ.ap
  handled : Exec.PacketHandled N before packet after

/-- Individually completed honest calls supply an actual packet decision. The executable
hub's checks then derive AcceptedEmits; successful acceptance is not a fairness premise. -/
theorem accepted_emits_of_packet_handling (N : Nat) (c : Ctx) (run : Nat → NS)
    (lab : Nat → Lab) (hub : Nat → Exec.SEState) (k : Nat)
    (decode : Nat → List Exec.Rec)
    (hhead : ∀ i, k ≤ i → (hub i).es.hub.head = c.H)
    (hrecords : ∀ i, k ≤ i → (hub i).recs = decode c.R)
    (hinv : ∀ i, k ≤ i → NodeSettle.SInv c (run i))
    (hdelivered : ∀ i, k ≤ i → lab i = .emit →
      ∃ σ1 new, Emit c (run i) σ1 new ∧ ∃ j, i ≤ j ∧ Nonempty
        (EmittedPacketBoundary N (run i) new (hub j) (hub (j + 1)) decode)) :
    AcceptedEmits c run lab (fun i => (hub i).es.hub.seq) k := by
  intro i hi hl
  obtain ⟨σ1, new, hem, j, hj, ⟨packet⟩⟩ := hdelivered i hi hl
  have checks := Exec.packet_checks_of_emit (hinv i hi) hem packet.primitives
    packet.expected packet.target (hhead j (by omega)) decode packet.sourceRecords
    (hrecords j (by omega))
  have accepted := Exec.packet_checks_force_accept checks packet.handled
  exact ⟨j, hj, accepted.2.2⟩

theorem stable_hub_excludes_emit {c : Ctx} {run : Nat → NS} {lab : Nat → Lab}
    {hubSeq : Nat → Nat}
    {k i : Nat} (hstable : ∀ j, k ≤ j → hubSeq j = hubSeq k)
    (haccepted : AcceptedEmits c run lab hubSeq k) (hi : k ≤ i) (hl : lab i = .emit) :
    False := by
  obtain ⟨j, hj, hm⟩ := haccepted i hi hl
  rw [hstable j (by omega), hstable (j + 1) (by omega)] at hm
  omega

/-- The reverse local bridge: individually completed calls and scheduled core steps give
convergence, because every nonsilent publication would contradict proved hub stability. -/
theorem node_converges_at_stable_hub (c : Ctx) (run : Nat → NS) (lab : Nat → Lab)
    (hubSeq : Nat → Nat) (k : Nat)
    (hstable : ∀ i, k ≤ i → hubSeq i = hubSeq k)
    (hev : ∀ i, k ≤ i → Ev c (lab i) (run i) (run (i + 1)))
    (h0 : NodeSettle.SInv c (run k))
    (hmaint : ∃ kb, ∀ i, kb ≤ i → lab i ≠ .maint)
    (hstart : ∀ i, k ≤ i → (run i).act = false → ∃ j, i ≤ j ∧ lab j = .start)
    (hcore : ∀ i, k ≤ i → (run i).act = true →
      ∃ j, i ≤ j ∧ (lab j = .busy ∨ lab j = .idle ∨ lab j = .emit ∨ lab j = .maint))
    (haccepted : AcceptedEmits c run lab hubSeq k) :
    ∃ cut, ∀ i, cut ≤ i → NodeSettle.Settled c (run i) := by
  rcases node_settles c run lab k hev h0 hmaint hstart hcore with hem | hdone
  · obtain ⟨i, hi, hl, _⟩ := hem
    exact False.elim (stable_hub_excludes_emit hstable haccepted hi hl)
  · exact hdone

theorem finite_common_cut (N : Nat) (P : Nat → Nat → Prop)
    (he : ∀ n, n < N → ∃ k, ∀ i, k ≤ i → P n i) :
    ∃ k, ∀ i, k ≤ i → ∀ n, n < N → P n i := by
  induction N with
  | zero => exact ⟨0, fun _ _ _ hn => by omega⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih (fun n hn => he n (by omega))
    obtain ⟨j, hj⟩ := he N (by omega)
    refine ⟨max k j, fun i hi n hn => ?_⟩
    by_cases heq : n = N
    · subst n; exact hj i (by omega)
    · exact hk i (by omega) n (by omega)

/-- Composition with the hub's own asynchronous stabilization proof. Local refinement
starts at a later cut: old calls/queued replies and adoption-related reopens may still occur
after the hub first becomes stable. It is not a premise that the hub stabilizes. Early
record/knowledge entry must supply the HubSuffix trace before applying this theorem. -/
theorem refined_suffix_converges {N : Nat} {E : Nat → Prop} {w : Nat}
    (hub : Nat → HubSuffix.GState)
    (h0 : HubSuffix.Inv E w (hub 0))
    (hs : ∀ i, HubSuffix.Step E w (hub i) (hub (i + 1)))
    (hN : ∀ n, E n → n < N) (kb : Nat)
    (hkb : ∀ i, kb ≤ i → (hub (i + 1)).bk = (hub i).bk)
    (nodes : Nat → Nat → NS) (labels : Nat → Nat → Lab)
    (records : Nat) (drops : Nat → Nat → Nat → Prop)
    (hlocal : ∀ k, (∀ i, k ≤ i →
        (hub i).s.hub.head = (hub k).s.hub.head ∧
        (hub i).s.hub.seq = (hub k).s.hub.seq) →
      ∀ n, n < N →
      ∃ later, k ≤ later ∧
      let c : Ctx := ⟨(hub k).s.hub.seq, (hub k).s.hub.head, records, drops n⟩
      (∀ i, later ≤ i → Ev c (labels n i) (nodes n i) (nodes n (i + 1))) ∧
      NodeSettle.SInv c (nodes n later) ∧
      (∃ kb, ∀ i, kb ≤ i → labels n i ≠ .maint) ∧
      (∀ i, later ≤ i → (nodes n i).act = false → ∃ j, i ≤ j ∧ labels n j = .start) ∧
      (∀ i, later ≤ i → (nodes n i).act = true → ∃ j, i ≤ j ∧
        (labels n j = .busy ∨ labels n j = .idle ∨ labels n j = .emit ∨
          labels n j = .maint)) ∧
      AcceptedEmits c (nodes n) (labels n) (fun i => (hub i).s.hub.seq) later) :
    ∃ k cut, ∀ i, cut ≤ i →
      (hub i).s.hub.head = (hub k).s.hub.head ∧
      (hub i).s.hub.seq = (hub k).s.hub.seq ∧
      ∀ n, n < N → NodeSettle.Settled
        ⟨(hub k).s.hub.seq, (hub k).s.hub.head, records, drops n⟩ (nodes n i) := by
  obtain ⟨k, hk⟩ := HubSuffix.hub_suffix_stabilizes hub h0 hs hN kb hkb
  have each : ∀ n, n < N → ∃ cut, ∀ i, cut ≤ i → NodeSettle.Settled
      ⟨(hub k).s.hub.seq, (hub k).s.hub.head, records, drops n⟩ (nodes n i) := by
    intro n hn
    obtain ⟨later, hlater, hev, hi, hmaint, hstart, hcore, ha⟩ := hlocal k hk n hn
    exact node_converges_at_stable_hub _ (nodes n) (labels n)
      (fun i => (hub i).s.hub.seq) later
      (fun i hi => (hk i (by omega)).2.trans (hk later hlater).2.symm)
      hev hi hmaint hstart hcore ha
  obtain ⟨cut, hc⟩ := finite_common_cut N _ each
  exact ⟨k, max k cut, fun i hi =>
    ⟨(hk i (by omega)).1, (hk i (by omega)).2, hc i (by omega)⟩⟩

end Musubi.Recovery

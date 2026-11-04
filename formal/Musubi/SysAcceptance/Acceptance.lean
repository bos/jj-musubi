/-
The push a fair node sends from the settled hub's head is accepted, so the hub could not have
settled: `node_settles_fresh`'s alternative is impossible, and the node settles
(`node_settles_accepted`). Acceptance is not a premise. It comes from the executable hub's
checks (`packet_checks_force_accept`) on the very packet the node's actual push step built,
taken from its request (`Bodies`), not from some packet that `Emit` would allow.

The bridge to the executable hub is explicit and per request: for each push request the hub
answers, a decision of the executable hub (`HubDecision`), its state before and after bound to
the system's hub (sequence, head, records) and its packet to the request's. Records are bound by
decoding: the system's records are an opaque identity of the native ordered list, which `decode`
reads as the executable hub's records. Nothing is encoded, and no injectivity is assumed, since
two native lists may name the same records. The binding is the adapter's correspondence, not a
success: every outcome is a decision, refusals and rejections included. The packet's primitive
laws (`PacketPrimitives`: ancestry, survival, upload closure) are native laws of a push from the
hub's head with its records, stated as such. Requests are answered fairly one by one. With the
system's own facts at the push (the node's invariant at its first push, its write, its scoped
embedding), the checks hold, the hub's only decision is to accept, and its sequence would move.
-/
import Musubi.SysFreshCuts
import Musubi.PacketAcceptance
import Musubi.RequestBounds
import Musubi.RecordStability
import Musubi.SerialReply
import Musubi.NotificationControl
import Musubi.NodeSysExec

namespace Musubi.SysAcceptance

open Musubi Musubi.NodeSettle Musubi.EarlyEntry Musubi.NodeSys Musubi.NodeSysEntry
  Musubi.SysFreshCuts

/-- The executable hub's decision on the push `P` that a system step answered: its state
before and after, the executable packet and its decision, the packet bound to `P` and the
hub's states to the system's hub before and after, records read through `decode`. Any
decision: none is assumed to accept. -/
structure HubDecision (M : Nat) (decode : Nat → List Exec.Rec) (g g' : Sys) (P : Pkt) where
  before : Exec.SEState
  after : Exec.SEState
  packet : Exec.PushPacket
  handled : Exec.PacketHandled M before packet after
  expected : packet.expected = P.expected
  new : packet.new = P.new
  records : packet.applied = decode P.recs
  head : before.es.hub.head = g.hub.head
  recs : before.recs = decode g.hub.recs
  seqBefore : before.es.hub.seq = g.hub.seq
  seqAfter : after.es.hub.seq = g'.hub.seq

/-- The adapter's actual decision and the conditional primitive laws of that same decision.
Other executable states with matching sequence fields are not adapter decisions. -/
structure LawfulDecision (M : Nat) (decode : Nat → List Exec.Rec) (g g' : Sys) (P : Pkt)
    extends HubDecision M decode g g' P where
  primitives : P.expected = g.hub.head → P.recs = g.hub.recs → P.new ≠ g.hub.head →
    Exec.PacketPrimitives before packet

section Accept

variable {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}

/-- Only a newly issued push call must finish. Orphan requests from an earlier client
session may stay in the network forever; they are not a fairness obligation. -/
def PushFair (ρ : Nat → Sys) (acts : Nat → Act) (n k : Nat) : Prop :=
  ∀ i, k ≤ i → acts i = .issue n .push → ∀ q ∈ (ρ (i + 1)).reqs,
    q ∉ (ρ i).reqs → q.node = n →
    ∃ j, i + 1 ≤ j ∧ q ∈ (ρ j).reqs ∧ q ∉ (ρ (j + 1)).reqs

/-- The first push from the hub's head after the simulation starts, with what the simulation
keeps holding there: every step before it is a NodeSettle event. -/
theorem first_emit (ρ : Nat → Sys) (acts : Nat → Act) (n k k' h : Nat) (st : Snap)
    (hstep : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (hkk : k ≤ k') (hstable : ∀ i, k ≤ i → (ρ i).hub = st)
    (hold : ∀ i, k' ≤ i → ∀ r ∈ (ρ i).reps, r ∉ (ρ (i + 1)).reps → r.node = n →
      (ρ k).time ≤ r.time)
    (hnotes : ∀ i, k' ≤ i → ∀ nt, acts i = .notice n nt → nt.snap = st)
    (h0 : SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ k'))
    (hem : ∃ i, k' ≤ i ∧ labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) = .emit) :
    ∃ i, k' ≤ i ∧ labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) = .emit ∧
      SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ i) := by
  obtain ⟨i, hi, he⟩ := hem
  obtain ⟨d0, hd0, hmin⟩ := exists_first
    (P := fun d => labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ (k' + d)) (acts (k' + d)) = .emit)
    ⟨i - k', by rw [show k' + (i - k') = i by omega]; exact he⟩
  have hinv : ∀ d, d ≤ d0 →
      SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ (k' + d)) := by
    intro d
    induction d with
    | zero => intro _; exact h0
    | succ d ih =>
      intro hd
      exact (sim_step rfl (ih (by omega)) (hstep (k' + d) (by omega))
        (hstable _ (by omega)) (hstable _ (by omega)) (hold (k' + d) (by omega))
        (fun nt ha => hnotes (k' + d) (by omega) nt ha) (hmin d (by omega))).2
  exact ⟨k' + d0, by omega, hd0, hinv d0 (Nat.le_refl _)⟩

/-- A push from the settled hub's head, sent while the simulation holds, is impossible: its
request is answered, and the executable hub's checks on the very packet the push step built
leave it only accepting, which moves the hub. -/
theorem no_accepting_emit (ρ : Nat → Sys) (acts : Nat → Act) (n k i h M : Nat) (st : Snap)
    (decode : Nat → List Exec.Rec)
    (hstep : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (hstable : ∀ i, k ≤ i → (ρ i).hub = st) (hi : k ≤ i)
    (I : SimInv law D n ⟨st.seq, h, st.recs, D n⟩ (ρ k).time st h (ρ i))
    (hlab : labOf n ⟨st.seq, h, st.recs, D n⟩ (ρ i) (acts i) = .emit)
    (hreqfair : PushFair ρ acts n k)
    (hdecide : ∀ j, k ≤ j → ∀ q ∈ (ρ j).reqs, q ∉ (ρ (j + 1)).reqs → q.node = n →
      ∀ P, q.body = .push P → Nonempty (LawfulDecision M decode (ρ j) (ρ (j + 1)) P)) :
    False := by
  obtain ⟨hact, hknown⟩ := lab_emit.1 hlab
  have hs := hstep i hi
  rw [hact] at hs
  cases hs with
  | issue _ _ post new emb1 rq hw hissue hgrow hbodies hslot hnodup hnode hreqs hslot' hrest
      htime hdropped =>
    -- the actual push step is NodeSettle's `Emit`, with the node's invariant there
    obtain ⟨hact', hgo, hlen, hloc, hdesc, hannc, hdiffer, hwork, hwrite, hnew⟩ := hissue
    have hemit : Emit ⟨st.seq, h, st.recs, D n⟩ ((ρ i).node n).ns post new :=
      ⟨hact', go_congr rfl hgo, hlen, hloc, hdesc, hannc, hdiffer, hwork, hknown, hwrite, hnew⟩
    obtain ⟨-, hap, -, hneH, -⟩ := emit_packet I.sinv hemit
    -- the written state, its labels scoped into the raw graph
    have hscope := scoped_growR I.node.scope I.node.inv.parLt hgrow
    have hpostHeads : post.heads = [new] := by
      obtain ⟨y, hy, (⟨-, F⟩ | ⟨-, he, rfl⟩)⟩ := hwrite
      · exact F.heads
      · rw [he]; exact hy
    have hpostInv : LInv post := linv_of_sinv (post_inv
      (d := D n) (k := .push) (new := new)
      ⟨hact', hgo, hlen, hloc, hdesc, hannc, hdiffer, hwork, hwrite, hnew⟩ I.sinv)
    have hnewLt : new < post.next := hpostInv.headsLt new (by rw [hpostHeads]; simp)
    have hlabelLt : h < post.next := Nat.lt_of_lt_of_le I.hl hgrow.next
    have hheadRaw : emb1 h = st.head := (hgrow.embOld h I.hl).trans I.he
    have hnewRaw : emb1 new ≠ st.head := fun e =>
      hneH (hscope.inj new h hnewLt hlabelLt (e.trans hheadRaw.symm))
    have hpostKnown : post.known = ((ρ i).node n).ns.known := by
      have known := writeRes_known hwrite
      exact known
    have hpostAp : post.ap = ((ρ i).node n).ns.ap := by
      have ap := write_ap hwrite
      exact ap
    -- the actual request: the packet the push step built
    obtain ⟨q, hrq, hqbody⟩ : ∃ q, rq = [q] ∧ q.body = .push
        (pkt n (((ρ i).node n).gen + (post.next - ((ρ i).node n).ns.next)) post emb1
          new) := by
      simp only [Bodies] at hbodies
      cases rq with
      | nil => simp at hbodies
      | cons q t =>
        cases t with
        | nil => exact ⟨q, rfl, by simpa using hbodies⟩
        | cons q2 t2 => simp at hbodies
    have hqnode : q.node = n := (hslot q (by rw [hrq]; simp)).1
    have hqin : q ∈ (ρ (i + 1)).reqs := by rw [hreqs, hrq]; simp
    have hqfresh : q ∉ (ρ i).reqs := by
      intro hq
      have old := I.sys.reqs q hq
      have fresh := (hslot q (by rw [hrq]; simp)).2.1
      omega
    -- it is answered, by a decision of the executable hub
    obtain ⟨j, hj, hqj, hqj'⟩ := hreqfair i hi hact q hqin hqfresh hqnode
    obtain ⟨decision⟩ := hdecide j (by omega) q hqj hqj' hqnode _ hqbody
    have hhubJ := hstable j (by omega)
    have hhubJ' := hstable (j + 1) (by omega)
    have hexpected : (pkt n (((ρ i).node n).gen + (post.next - ((ρ i).node n).ns.next))
        post emb1 new).expected = st.head := by
      show emb1 post.known.2 = st.head
      rw [hpostKnown, hknown]
      exact hheadRaw
    have hrecs : (pkt n (((ρ i).node n).gen + (post.next - ((ρ i).node n).ns.next))
        post emb1 new).recs = st.recs := by
      show post.ap = st.recs
      rw [hpostAp, hap]
    have hprimitives := decision.primitives
      (by rw [hhubJ]; exact hexpected) (by rw [hhubJ]; exact hrecs)
      (by rw [hhubJ]; exact hnewRaw)
    have checks : Exec.PacketChecks decision.before decision.packet := by
      refine ⟨hprimitives, ?_, ?_, ?_⟩
      · rw [decision.records, decision.recs, hhubJ, hrecs]
        exact Exec.recEq_self _
      · rw [decision.head, decision.new, hhubJ]
        exact fun e => hnewRaw e.symm
      · rw [decision.head, decision.expected, hhubJ]
        exact hexpected.symm
    obtain ⟨-, -, hseq⟩ := Exec.packet_checks_force_accept checks decision.handled
    rw [decision.seqAfter, decision.seqBefore, hhubJ, hhubJ'] at hseq
    omega

/-- `node_settles_fresh` without its alternative: node `n` in the system, from a well-formed
start, once the hub has settled at `st`, settles at the stable hub's head under a label `H` of
it. Fair scheduling of its events and of the hub's answers to its requests, housekeeping that
writes stopping, the executable hub deciding each push request the system's hub answers, and the
primitive laws of a push from the hub's head with its records are assumed; records are read
through `decode`, with no injectivity. No acceptance, and no cut on old replies or
notifications. -/
theorem node_settles_accepted (ρ : Nat → Sys) (acts : Nat → Act) (n k0 k kf M : Nat) (st : Snap)
    (decode : Nat → List Exec.Rec)
    (hstep : ∀ i, k0 ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : RunOK law D n (ρ k0)) (hk : k0 ≤ k) (hstable : ∀ i, k ≤ i → (ρ i).hub = st)
    (hfair : Fair ρ acts n kf) (hmaint : ∃ kb, ∀ i, kb ≤ i → acts i ≠ .core n .maint)
    (hreqfair : PushFair ρ acts n k)
    (hdecide : ∀ j, k ≤ j → ∀ q ∈ (ρ j).reqs, q ∉ (ρ (j + 1)).reqs → q.node = n →
      ∀ P, q.body = .push P → Nonempty (LawfulDecision M decode (ρ j) (ρ (j + 1)) P)) :
    ∃ k' H, k < k' ∧ H < ((ρ k').node n).ns.next ∧ ((ρ k').node n).emb H = st.head ∧
      ∃ K, ∀ i, K ≤ i → NodeSettle.Settled ⟨st.seq, H, st.recs, D n⟩ ((ρ i).node n).ns := by
  have hK := runOK_run ρ acts hstep h0
  have hstepk : ∀ i, k ≤ i → SysStep N D law (acts i) (ρ i) (ρ (i + 1)) :=
    fun i hi => hstep i (by omega)
  obtain ⟨kr, hkr, hold⟩ := old_replies_stop ρ acts n k hstepk (hK k hk).sys
  obtain ⟨kn, hkn, hnold⟩ := old_notes_stop ρ acts n k hstepk
  have hNf := notes_from_stable ρ acts k st hstepk (hK k hk).time hstable
  have hnotes : ∀ i, kr + kn + kf ≤ i → ∀ nt, acts i = .notice n nt → nt.snap = st := by
    intro i hi nt ha
    have hs := hstep i (by omega)
    rw [ha] at hs
    cases hs with
    | notice _ _ _ _ _ _ _ _ _ hn =>
      exact hNf i (by omega) nt hn (hnold i (by omega) nt ha)
  have hR : ∀ i, k ≤ i → StableReps (ρ k).time st (ρ i) := by
    intro i hi
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction d with
    | zero => exact stable_init (hK k hk).time
    | succ d ih =>
      exact stable_step (ih (by omega)) (hstep _ (by omega)) (hstable _ (by omega))
        (hstable _ (by omega))
  obtain ⟨j, hj, hobs⟩ := observes ρ acts n k (kr + kn + kf) st hstepk
    (fun i hi => hK i (by omega)) (by omega) hR (fun i hi => hold i (by omega))
    (fair_mono hfair (by omega)) hmaint
  obtain ⟨H, I⟩ := entry_of_obs (hK j (by omega)) (hK (j + 1) (by omega)) (hR j (by omega))
    (hR (j + 1) (by omega)) (hold j (by omega)) (hnotes j hj) (hstep j (by omega)) hobs
  refine ⟨j + 1, H, by omega, I.hl, I.he, ?_⟩
  rcases node_settles_sys ρ acts n k (j + 1) H st hstepk (by omega) hstable
      (fun i hi => hold i (by omega)) (fun i hi => hnotes i (by omega)) I
      (fair_mono hfair (by omega)) hmaint with hem | hset
  · exfalso
    obtain ⟨i, hi, hlab, -⟩ := hem
    obtain ⟨i0, hi0, hlab0, I0⟩ := first_emit ρ acts n k (j + 1) H st hstepk (by omega) hstable
      (fun i hi => hold i (by omega)) (fun i hi => hnotes i (by omega)) I ⟨i, hi, hlab⟩
    exact no_accepting_emit ρ acts n k i0 H M st decode hstepk hstable (by omega) I0 hlab0
      hreqfair hdecide
  · exact hset

end Accept

/-- Composition for eligible nodes of the same joint system: hub stabilization is proved
from its events, then a proper push would contradict it. This is a suffix theorem; deriving
entry and making every surviving native node eligible are separate obligations. -/
theorem eligible_system_converges {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {w : Nat} (ρ : Nat → Sys) (acts : Nat → Act) (initial : Nat → Nat)
    (M : Nat) (decode : Nat → List Exec.Rec)
    (hs : ∀ i, SysStep N D law (acts i) (ρ i) (ρ (i + 1)))
    (h0 : ∀ n, RunOK law D n (ρ 0))
    (hd : ∀ i x, x < (ρ i).next → ∀ p ∈ (ρ i).par x, p < x)
    (hb : Recovery.HubSys.RequestBounds (ρ 0))
    (hi : Recovery.HistoryWindow w (Recovery.HubSys.state (ρ 0) initial))
    (hknown : ∀ n, E n → Recovery.HubNodeSteps.HonestSnap w initial (ρ 0)
      ⟨(Recovery.HubSys.known (ρ 0) n).1, (Recovery.HubSys.known (ρ 0) n).2, (ρ 0).hub.recs⟩)
    (hl : ∀ i, Recovery.HubSys.SuffixStepLaws E D law (ρ 0).reqs w
      (Recovery.HubSys.histories ρ initial i) (acts i) (ρ i) (ρ (i + 1)))
    (hN : ∀ n, E n → n < N) (kb : Nat)
    (hm : ∀ i, kb ≤ i → ∀ n, E n → acts i ≠ .core n .maint)
    (hr : ∀ i, (ρ i).hub.recs = (ρ 0).hub.recs)
    (hf : ∀ n, E n → ∃ kf, Fair ρ acts n kf)
    (hq : ∀ n, E n → PushFair ρ acts n 0)
    (hdecide : ∀ n, E n → ∀ j q, q ∈ (ρ j).reqs → q ∉ (ρ (j + 1)).reqs → q.node = n →
      ∀ P, q.body = .push P → Nonempty (LawfulDecision M decode (ρ j) (ρ (j + 1)) P)) :
    ∃ k cut, k ≤ cut ∧ (∀ i, cut ≤ i → (ρ i).hub = (ρ k).hub) ∧
      ∀ n, E n → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(ρ k).hub.seq, H, (ρ k).hub.recs, D n⟩ ((ρ i).node n).ns ∧
        ((ρ i).node n).emb H = (ρ k).hub.head ∧
        ∀ x, Recovery.HubSys.heads (ρ i) n x ↔ x = (ρ k).hub.head := by
  obtain ⟨k, hinv, hk⟩ := Recovery.HubSys.hub_stabilizes_sys ρ acts initial hs h0 hd hb hi hknown
    hl hN kb hm
  have stable : ∀ i, k ≤ i → (ρ i).hub = (ρ k).hub := by
    have snap_eq : ∀ a b : Snap, a.seq = b.seq → a.head = b.head → a.recs = b.recs → a = b := by
      intro a b hsq hh hr
      cases a
      cases b
      simp_all
    intro i hi
    exact snap_eq _ _ (hk i hi).2 (hk i hi).1 ((hr i).trans (hr k).symm)
  have each : ∀ n, n < N → ∃ cut, ∀ i, cut ≤ i →
      (E n → ∃ H, ∀ j, i ≤ j →
        NodeSettle.Settled ⟨(ρ k).hub.seq, H, (ρ k).hub.recs, D n⟩ ((ρ j).node n).ns ∧
        ((ρ j).node n).emb H = (ρ k).hub.head ∧
        ∀ x, Recovery.HubSys.heads (ρ j) n x ↔ x = (ρ k).hub.head) := by
    intro n _
    by_cases he : E n
    · obtain ⟨kf, hfair⟩ := hf n he
      obtain ⟨_, H, _, _, _, K, hK⟩ := node_settles_accepted ρ acts n 0 k kf M (ρ k).hub decode
        (fun i _ => hs i) (h0 n) (Nat.zero_le _) stable hfair
        ⟨kb, fun i hi => hm i hi n he⟩ (fun j _ => hq n he j (Nat.zero_le _))
        (fun j _ => hdecide n he j)
      refine ⟨max k K, fun i hi _ => ⟨H, fun j hj => ?_⟩⟩
      have sj : k ≤ j := by omega
      have settled := hK j (by omega)
      have current : NodeSettle.Settled
          ⟨(ρ j).hub.seq, H, (ρ j).hub.recs, D n⟩ ((ρ j).node n).ns := by
        rw [stable j sj]
        exact settled
      have node := (runOK_run ρ acts (fun i _ => hs i) (h0 n) j (Nat.zero_le _)).node
      obtain ⟨raw, heads⟩ := Recovery.HubSys.settled_raw_head (hinv j) he node current
      rw [stable j sj] at raw heads
      exact ⟨settled, raw, heads⟩
    · exact ⟨0, fun _ _ hn => False.elim (he hn)⟩
  obtain ⟨cut, hc⟩ := Recovery.finite_common_cut N _ each
  exact ⟨k, max k cut, by omega, fun i hi => stable i (by omega),
    fun n hn => hc (max k cut) (by omega) n (hN n hn) hn⟩

end Musubi.SysAcceptance

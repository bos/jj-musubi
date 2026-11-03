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

/-! ## A pending node on a stable hub

The non-E counterpart of `node_settles_accepted`, on raw ids: a node whose drops stay pending
after the cuts, on a hub that stays as it is, is impossible. Its control is computed from its
states and the bits its native core reports (`Control.rawControl`), never from what it chose;
the survey's guard and the branches it can take are derived (`Control.rawControl_guarded`),
each step's effect is the native law of that step (a burst step checked by `Control.callB`; a
`Fetch` or `GetObjects` reply), so it pushes (`Control.pending_push_reached`). That push is
the core's pending push; the hub's checks of it, each a native law of its own, have the hub
accept it (`RawPublish.stable_no_pendingPush`), and the hub would move. No push is assumed, and
nothing is read in original ids. -/

open Musubi.EarlyEntry.Control in
theorem choose_fetch {r : Reads} (h : choose r = .fetch) : r.missOps = true := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · assumption
    split at h <;> cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h <;> cases h

open Musubi.EarlyEntry.Control in
theorem choose_objects {r : Reads} (h : choose r = .objects) : r.missObjs = true := by
  unfold choose at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    split at h
    · cases h
    split at h
    · assumption
    · cases h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  split at h
  · split at h <;> cases h
  split at h <;> cases h

/-- (Archived: the proof now goes through `not_dropped_of`, with the cache's cause.) The hub does
not drop the head a push sends. The hub's `is_superseded` is a dropped name (`named`) or a key of
its cached renamings (`cached`): a cached key is renamed (`current_R` of it is not itself,
identity renamings being filtered), and the sent head is fixed by the hub's naming, so it is no
cached key; the sent head is no dropped name; and the push's own drops do not hold it. So
`is_dropped` of it is false. No ancestry witness is used, and `current_R` is not asked of dropped
names outside the hub head's closure, which are named but have no image. -/
theorem not_dropped_fixed {cur : Nat → List Nat} {named cached : Nat → Bool} {x : Nat}
    {dropped : List Nat} (hren : ∀ y, cached y = true → cur y ≠ [y]) (hfix : cur x = [x])
    (hnn : named x = false) (hnot : x ∉ dropped) :
    ((named x || cached x) || decide (x ∈ dropped)) = false := by
  cases hc : cached x
  · simpa [hnn] using hnot
  · exact absurd hfix (hren x hc)

/-- The hub does not drop the head a push sends: it is no dropped name, no cached renaming key,
and not among the push's own drops. -/
theorem not_dropped_of {named cached : Nat → Bool} {x : Nat} {dropped : List Nat}
    (hnn : named x = false) (hnc : cached x = false) (hnot : x ∉ dropped) :
    ((named x || cached x) || decide (x ∈ dropped)) = false := by
  simpa [hnn, hnc] using hnot

open Musubi.EarlyEntry Musubi.EarlyEntry.Control in
/-- No node keeps drops pending forever on a stable hub, given at each core step of its round
(`active`: the run starts at one, and each of its steps that merges, realizes, advances, fetches
or gets its objects goes on with it): the cuts' bits (nothing announced, no op head dropped by
them, records not differing from those last heard, and the new head of a fix-up never the known
one), with drops pending throughout, the case refuted; the native law of the step it takes (a
burst step as checked; a `Fetch` reply about the stable head giving each operation of the closure
not local a body or locality; a `GetObjects` reply giving each walked operation with a body but
not its objects them, or locality; neither moving the op heads or the plan, nothing lost); and, at
a push, the fields the native core gives it (from the known raw head, the fix-up's head or the op
head, the pending drops), the records it offers, those it last heard and the hub's own, and the
hub's checks of it (its records compared; whether it is dropped, which is the hub's
`is_superseded` of the sent head, a dropped name or a key of its cached renamings, or its
membership in the push's drops: the sent head is a complete canonical body written under the
node's drops that survives them (`normal`), which include the hub's records when the node's
applied ones match; so it is no name those records drop (`hsurvive`), and no key of the hub's
cached renamings, a cached key having a body or ancestor those records drop (`hnoCache`); and it
is not among its own drops; so not dropped, `not_dropped_of`; whether its closure is stored, which
is the executable hub's closure check after it stores this packet together with the hub's other
validations of it (no operation missing or abandoned, no original repeated, `valid`), the sender's
cache covering all the hub lacks of it, so stored, `Exec.packet_upload_closes_split`; and
`descends` naming the known head by its images), the hub, stable, staying.

The states are read off the native ones as inputs: `stg x` when the node has `x`'s body, staged or
canonical; `obj x` only when it has that body and every object the body requires is here, never
when the body is unknown (an unknown body's objects are unknown, so an operation without one is
not ready, and a body arriving that requires objects keeps `Grows`).

`differ` compares the records the node offers with those it last heard (`NodeCore::step`); the hub
compares them with its own. They agree at a push because the hub's records when it handles the
packet are the ones the node last heard (`hheard`). Deriving this needs a current stored value or
a fresh post-cut Head, Fetched or Refused reply, as well as fixed records and no old reply still
to come: draining old replies alone does not update a stored old value. `differ` alone says
nothing of the hub's records.

The hub stays, so the known head does: naming settles inside the run (`Naming.settles`), and the
checked burst, `Fetch` and `GetObjects` laws are asked only of steps naming does not change
across. No naming cutoff is assumed. A `GetObjects` reply may lack what it was asked for
(`failed`), and the round then fails; that none does (`hserve`) is not a law of the run, but is to
be derived from the hub keeping what it can serve (the `SerialReply` credit). The round never ends
(derived): a push at one of its steps would have the hub accept it, and every other step the
guards allow goes on with it; so no notice or round start is read as a core step. -/
theorem no_forever_pending {ρ α : Type} [DecidableEq ρ] (raw : List Nat) (nm : Naming α)
    (par : Nat → List Nat)
    (anc : Nat → Nat → Bool)
    (trans : ∀ a b c, anc a b = true → anc b c = true → anc a c = true)
    (hlt : ParLt par) (hub : RawPublish.Hub) (hraw : ∀ x, Anc par x hub.head → x ∈ raw)
    (run after : Nat → Control.State) (prims : Nat → Prims)
    (pkt : Nat → RawPublish.Push) (checks : Nat → RawPublish.Checks) (failed : Nat → Prop)
    (active : Nat → Bool) (h0 : active 0 = true)
    (hnaming : nm.Laws par hub.head fun i => active i = true)
    (hnext : ∀ i, active i = true →
      (rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .realize ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .advance ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .fetch ∨
        (rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .objects ∧
          ¬ failed i)) →
      active (i + 1) = true)
    (hguard : ∀ i, active i = true → (prims i).announced = false ∧ (prims i).dropHead = false ∧
      (prims i).differ = false ∧ (prims i).pending = true ∧ (prims i).newIsKnown = false)
    (hburst : ∀ i, active i = true → nm.Still i →
      (rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .merge ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .realize ∨
        rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .advance) →
      ∃ k, callB raw (nm.images i) anc (.burst k) (run i) (after i) = true)
    (hfetch : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .fetch →
      (∀ x ∈ raw, (run i).burst.loc x = false →
        (after i).stg x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true)
    (hobjects : ∀ i, active i = true → nm.Still i →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .objects →
      failed i ∨
      ((∀ x, walkB par (run i).burst.loc (run i).stg hub.head x = true →
        (run i).burst.loc x = false → (run i).stg x = true → (run i).obj x = false →
        (after i).obj x = true ∨ (after i).burst.loc x = true) ∧
      (after i).burst.heads = (run i).burst.heads ∧
      (after i).burst.plan = (run i).burst.plan ∧
      growsB raw (run i) (after i) = true))
    (hframe : ∀ i, active i = true → active (i + 1) = true → nm.Still i →
      Control.Frame raw (after i) (run (i + 1)))
    (hpkt : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (pkt i).expected = hub.head ∧
      (prims i).newIsKnown = decide ((pkt i).new = hub.head) ∧
      (prims i).pending = !(pkt i).dropped.isEmpty ∧
      ∀ h ∈ (run i).burst.heads, anc h (pkt i).new = true)
    (offered : Nat → ρ) (heard : Nat → Option ρ) (current : ρ)
    (hdiffer : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (prims i).differ = match heard i with
        | some h => !decide (h = offered i)
        | none => (prims i).pending)
    (hmatch : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).recordsMatch = decide (offered i = current))
    (hheard : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      heard i = some current)
    (hubNamed hubCached : Nat → Nat → Bool)
    (normal : Nat → Nat → Bool) (valid : Nat → Bool)
    (hdroppedB : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).dropped = ((hubNamed i (pkt i).new || hubCached i (pkt i).new) ||
        decide ((pkt i).new ∈ (pkt i).dropped)))
    (hwitness : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      normal i (pkt i).new = true)
    (hnoCache : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      offered i = current → ∀ y, normal i y = true → hubCached i y = false)
    (hsurvive : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      offered i = current → ∀ y, normal i y = true → hubNamed i y = false)
    (hassert : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (pkt i).new ∉ (pkt i).dropped)
    (es : Nat → Exec.EState) (xp : Nat → Exec.PushPacket) (opBases objectBases : Nat → List Nat)
    (hclosedB : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).closed = (((es i).hubStore (xp i).ops (xp i).objs).closedB (xp i).new && valid i))
    (hvalid : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push → valid i = true)
    (hparF : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      ParLt (es i).parF)
    (hbases : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      ∀ b ∈ opBases i, ClosedAt (Exec.abs (es i)) b)
    (hretained : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      ∀ b ∈ objectBases i, ∀ x, Anc (es i).parF x b → ∀ o ∈ (es i).objsF x, o ∈ (es i).hub.objs)
    (hcovers : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      Exec.UploadCoversSplit (es i) (xp i) (opBases i) (objectBases i))
    (hname : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      (checks i).descends =
        (!(nm.images i).isEmpty && (nm.images i).all fun j => anc j (pkt i).new))
    (hstable : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) = .push →
      RawPublish.after hub (pkt i) (checks i) = hub)
    (hserve : ∀ i, active i = true → ¬ failed i) :
    False := by
  -- a push at a step of the round has the hub accept it, so the hub would move
  have nopush : ∀ i, active i = true →
      rawControl raw (nm.images i) par anc hub.head (run i) (prims i) ≠ .push := by
    intro i hact hpush
    have hi : choose (rawReads raw (nm.images i) par anc hub.head (run i) (prims i)) = .push :=
      hpush
    obtain ⟨hdesc, -, -⟩ := choose_push hi
    obtain ⟨-, -, hd, hp, hn⟩ := hguard i hact
    obtain ⟨he, hnk, hpend, habove⟩ := hpkt i hact hpush
    have b : RawPublish.PendingPush (hub.seq, hub.head) (pkt i) := by
      refine ⟨he, ?_, ?_⟩
      · intro h
        rw [hn] at hnk
        exact absurd (decide_eq_true h) (by rw [← hnk]; exact Bool.false_ne_true)
      · intro h
        rw [hp, h] at hpend
        cases hpend
    have heq : current = offered i := by
      have hdi := hdiffer i hact hpush
      rw [hheard i hact hpush, hd] at hdi
      simp only at hdi
      cases h : decide (current = offered i)
      · rw [h] at hdi; cases hdi
      · exact of_decide_eq_true h
    have hr : (checks i).recordsMatch = true := by
      rw [hmatch i hact hpush]
      exact decide_eq_true heq.symm
    -- the hub does not drop the sent head: no name, no cached key, not among its own drops
    have hnd : (checks i).dropped = false :=
      (hdroppedB i hact hpush).trans (not_dropped_of
        (hsurvive i hact hpush heq.symm _ (hwitness i hact hpush))
        (hnoCache i hact hpush heq.symm _ (hwitness i hact hpush)) (hassert i hact hpush))
    -- and stores its closure, once it stores the packet: the sender's cache covers the rest
    have hcl : (checks i).closed = true := by
      rw [hclosedB i hact hpush, Exec.packet_upload_closes_split (hparF i hact hpush)
        (hbases i hact hpush) (hretained i hact hpush) (hcovers i hact hpush),
        hvalid i hact hpush]
      rfl
    have hdescends : (checks i).descends = true := by
      rw [hname i hact hpush]
      change (!(nm.images i).isEmpty && (run i).burst.heads.any fun h =>
        (nm.images i).all fun j => anc j h) = true at hdesc
      simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true] at hdesc ⊢
      obtain ⟨hne, h, hh, hall⟩ := hdesc
      exact ⟨hne, fun x hx => trans x h _ (hall x hx) (habove h hh)⟩
    exact RawPublish.stable_no_pendingPush b rfl hr hnd hcl hdescends (hstable i hact hpush)
  -- so the round never ends: each of its steps is a burst step or a call, which goes on with it
  have hall : ∀ i, active i = true := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih =>
      obtain ⟨ha, hdh, hd, hp, hn⟩ := hguard i ih
      apply hnext i ih
      rcases rawControl_guarded (images := nm.images i) (anc := anc) (s := run i) (q := prims i)
          hlt hraw ha hdh hd hp hn with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hserve i ih⟩)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact absurd h (nopush i ih)
  -- the hub stays, so does the known head: naming settles, at a step derived here
  obtain ⟨T, hT⟩ := nm.settles hnaming hall
  have hwalk : ∀ (s : Control.State) x,
      Walk (rawSurvey surveyBase par s.burst.loc s.stg s.obj hub.head) x → x ∈ raw :=
    fun _ _ hw => walk_mem hraw hw
  have himg : ∀ j, nm.images (T + j) = nm.images T := fun j => (hT (T + j) (by omega)).2
  have hst : ∀ j, nm.Still (T + j) := fun j => (hT (T + j) (by omega)).1
  obtain ⟨j, hj⟩ := pending_push_reached raw (nm.images T) anc trans (fun j => run (T + j))
    (fun j => after (T + j))
    (fun j => rawReads raw (nm.images T) par anc hub.head (run (T + j)) (prims (T + j)))
    (fun j => hframe (T + j) (hall _) (hall _) (hst j))
    (fun j => hguard (T + j) (hall _))
    (fun j => rawReads_survey hlt hraw)
    (fun j hc => by
      have hc' : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
          (prims (T + j)) = .merge ∨
          rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .realize ∨
          rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .advance := by
        rw [himg j]; exact hc
      obtain ⟨k, hk⟩ := hburst (T + j) (hall _) (hst j) hc'
      rw [himg j] at hk
      simp only [callB, Bool.and_eq_true] at hk
      exact ⟨Burst.stepB_sound hk.2, growsB_sound hk.1⟩)
    (fun j hc => by
      rcases hc with hc | hc
      · have hc' : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .fetch := by rw [himg j]; exact hc
        obtain ⟨hs, hh, hp, hg⟩ := hfetch (T + j) (hall _) (hst j) hc'
        exact fetch_call (base := surveyBase) ((missOpsB_iff hlt hraw).1 (choose_fetch hc))
          (hwalk (run (T + j))) hs hh hp (growsB_sound hg)
      · have hc' : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
            (prims (T + j)) = .objects := by rw [himg j]; exact hc
        obtain ⟨hb, hh, hp, hg⟩ :=
          (hobjects (T + j) (hall _) (hst j) hc').resolve_left (hserve _ (hall _))
        exact objects_call (base := surveyBase)
          ((missObjsB_iff hlt hraw).1 (choose_objects hc)) (hwalk (run (T + j)))
          (fun x hw => hb x ((walkB_iff hlt).2 hw)) hh hp (growsB_sound hg))
  have hpush : rawControl raw (nm.images (T + j)) par anc hub.head (run (T + j))
      (prims (T + j)) = .push := by
    show choose _ = _
    rw [himg j]; exact hj
  exact nopush (T + j) (hall _) hpush

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

/-! ## Native events, projected

A native event is observed by its own physical data, and its projection into the hive's `Sys`
is built from that data by a theorem, never assumed as a `SysStep`. The first events projected
are the hub's answers. To a `Fetch` and to a `GetObjects`, `handle` answers one request at a
time per hive (hub.rs:1-4), from the hub's `(seq, head)` and records then (`storage.head()`,
`storage.records()`, hub.rs:154-188), and changes nothing the system reads (its `report` of what
the machine took is kept in memory only, and an objects answer only exports). To a `Push`, the
hub first writes (what the push uploads, and contraction bodies it generates), a raw step, unless
it refuses the push first, which writes nothing, then decides from the state that leaves
(`HubAnswer.push_handled`). -/

/-- The hub answering one call, as observed: the call, by node, virtual slot (the call batch's
injective map of its wire id) and body, and the hub's `(seq, head, records)` when it answers,
projected to raw ids and record states. -/
structure HubAnswer where
  req : Req
  snap : Snap

/-- What the observation of that event must bind, the source obligations of its projection: the
call is one in flight, the snapshot is the hub's in the projected state before, and the
projected state after is the one before with the call answered (it leaves the requests, its
reply joins the replies at the system's time, and the clock ticks), nothing else moving. -/
structure HubAnswer.Binds (e : HubAnswer) (g g' : Sys) (ans : Ans) : Prop where
  inFlight : e.req ∈ g.reqs
  snap : e.snap = g.hub
  after : g' = { g with
    reqs := g.reqs.erase e.req
    reps := g.reps ++ [⟨e.req.node, e.req.slot, g.time, e.req.body, false, ans⟩]
    time := g.time + 1 }

/-- The hub's answer to a `Fetch`, projected, is the system's `answer` step. -/
theorem HubAnswer.fetch_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : HubAnswer} {g g' : Sys} (hb : e.req.body = .fetch)
    (B : e.Binds g g' (.fetched e.snap)) : SysStep N D law .answer g g' := by
  obtain ⟨hr, hs, rfl⟩ := B
  exact .answer e.req (.fetched e.snap) hr rfl false
    (Or.inl ⟨hb, rfl, by rw [hs], rfl, rfl⟩) rfl ⟨rfl, rfl, rfl, rfl⟩ rfl

/-- The hub's answer to a `GetObjects`, projected, is the system's `answer` step. -/
theorem HubAnswer.objects_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : HubAnswer} {g g' : Sys} (hb : e.req.body = .objs)
    (B : e.Binds g g' .objects) : SysStep N D law .answer g g' := by
  obtain ⟨hr, -, rfl⟩ := B
  exact .answer e.req .objects hr rfl false
    (Or.inr (Or.inl ⟨hb, rfl, rfl, rfl, rfl⟩)) rfl ⟨rfl, rfl, rfl, rfl⟩ rfl

/-- In the eligible nodes' system: the answer to an eligible node's call, or to one in flight at
the entry cut, is its `answer` step; the answer to another node's call is a raw step. -/
theorem HubAnswer.hive_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : HubAnswer} {g g' : Sys} {ans : Ans}
    (hs : SysStep N D law .answer g g') (B : e.Binds g g' ans) :
    (E e.req.node ∨ e.req ∈ old → HiveStep N D law E old .answer g g') ∧
      (¬ E e.req.node → e.req ∉ old → HiveStep N D law E old .env g g') := by
  obtain ⟨hr, -, hg⟩ := B
  refine ⟨fun hk => .answer hs fun rep hrep => ?_, fun hn hold => ?_⟩
  · have h1 : ([⟨e.req.node, e.req.slot, g.time, e.req.body, false, ans⟩] : List Rep) = [rep] :=
      List.append_cancel_left (as := g.reps) (by rw [← hrep, hg])
    simp only [List.cons.injEq, and_true] at h1
    subst h1
    exact hk
  · subst hg
    exact .answerRaw e.req hr hn hold _ ⟨rfl, rfl, rfl⟩ rfl rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- The system's state after the hub decides the push `r` carrying `p` with the native outcome
`o`, from the state its writes left (`HubAnswer.stored`): an accepted push moves the hub's
`(seq, head)` and records (`set_head`), and publishes the new head to every node; a refused one
gets the hub's records; any other gets the hub's head. The call leaves the requests, its reply
joins the replies, and the clock ticks. The notifications to every node are GHOSTS, potential
notifications: the native hub publishes to its subscribers only, and a node not subscribed
never consumes the one the model sends it (no step needs it to). -/
def pushAfter (N : Nat) (law : HubLaw) (g : Sys) (r : Req) (p : Pkt) (o : RawPublish.Outcome) :
    Sys :=
  if o = .accepted then
    { g with
      hub := ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩
      notes := g.notes ++ (List.range N).map
        (fun m => ⟨m, g.time, ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩⟩)
      reqs := g.reqs.erase r
      reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, true,
        .head ⟨g.hub.seq + 1, p.new, law.recsAfter g.hub.recs p.pending⟩⟩]
      time := g.time + 1 }
  else if o = .refused then
    { g with
      reqs := g.reqs.erase r
      reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, false, .refused g.hub.recs⟩]
      time := g.time + 1 }
  else
    { g with
      reqs := g.reqs.erase r
      reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, false, .head g.hub⟩]
      time := g.time + 1 }

/-- `Push::answer` refuses exactly for other records or a dropped head. -/
theorem answer_refused_iff {h : RawPublish.Hub} {q : RawPublish.Push} {c : RawPublish.Checks} :
    RawPublish.answer h q c = .refused ↔ (c.recordsMatch = false ∨ c.dropped = true) := by
  unfold RawPublish.answer
  by_cases hc : c.recordsMatch = false ∨ c.dropped = true
  · simp [hc]
  · simp only [hc, ↓reduceIte, iff_false]
    split
    · simp
    · split
      · simp
      · split <;> simp

/-- `Push::answer` never answers `Incomplete` when, in the one branch that consults it (the
records match, the new head is not dropped and not the hub's, and the push is from the hub's
head), the closure is stored. A refused push is refused before anything is stored, so nothing
is asked of its closure. -/
theorem answer_ne_incomplete {h : RawPublish.Hub} {q : RawPublish.Push} {c : RawPublish.Checks}
    (hc : c.recordsMatch = true → c.dropped = false → q.new ≠ h.head → h.head = q.expected →
      c.closed = true) : RawPublish.answer h q c ≠ .incomplete := by
  unfold RawPublish.answer
  split
  · simp
  · rename_i h1
    split
    · simp
    · rename_i h2
      split
      · rename_i h3
        have hm : c.recordsMatch = true := by
          cases hm : c.recordsMatch
          · exact absurd (Or.inl hm) h1
          · rfl
        have hd : c.dropped = false := by
          cases hd : c.dropped
          · rfl
          · exact absurd (Or.inr hd) h1
        rw [hc hm hd h2 h3.1] at h3
        exact absurd h3.2 (by decide)
      · split <;> simp

/-- The hub's DECISION on a push, projected, from the native decision on that very packet, in
the state after the hub's writes for it (`HubAnswer.push_handled` composes the two): the hub's
checks of it (`RawPublish.Checks`), its records compared and `is_dropped` bound to the law's, its
closure stored in the one branch that consults it (so never `Incomplete`; a refused push is
asked nothing of its closure), and the law accepting exactly when `Push::answer` accepts.
Whatever the outcome, the step is the system's `answer`. -/
theorem HubAnswer.push_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    {r : Req} {p : Pkt} {c : RawPublish.Checks}
    (hr : r ∈ g.reqs) (hb : r.body = .push p)
    (hrec : c.recordsMatch = true ↔ p.recs = g.hub.recs)
    (hdrop : c.dropped = true ↔ law.dropped g.hub.recs p)
    (hclosed : c.recordsMatch = true → c.dropped = false → p.new ≠ g.hub.head →
      g.hub.head = p.expected → c.closed = true)
    (hacc : RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c =
      .accepted ↔ law.accepts g.hub g.par p) :
    RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c ≠ .incomplete ∧
    SysStep N D law .answer g
      (pushAfter N law g r p
        (RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c)) := by
  refine ⟨answer_ne_incomplete hclosed, ?_⟩
  have href := (answer_refused_iff (h := ⟨g.hub.seq, g.hub.head⟩)
    (q := ⟨p.expected, p.new, p.pending⟩) (c := c))
  generalize RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c = o
    at hacc href
  have hnot : o ≠ .accepted → ¬ law.accepts g.hub g.par p := fun h ha => h (hacc.2 ha)
  -- the refusal is the records' or the drop's, and only it
  have href' : o = .refused ↔ (p.recs ≠ g.hub.recs ∨ law.dropped g.hub.recs p) := by
    rw [href]
    constructor
    · rintro (h | h)
      · exact Or.inl fun he => by rw [hrec.2 he] at h; cases h
      · exact Or.inr (hdrop.1 h)
    · rintro (h | h)
      · left
        cases hm : c.recordsMatch
        · rfl
        · exact absurd (hrec.1 hm) h
      · exact Or.inr (hdrop.2 h)
  unfold pushAfter
  by_cases ha : o = .accepted
  · simp only [ha, ↓reduceIte]
    exact .answer r _ hr rfl true
      (Or.inr (Or.inr ⟨p, hb, Or.inl ⟨hacc.1 ha, rfl, rfl, rfl, rfl⟩⟩)) rfl
      ⟨rfl, rfl, rfl, rfl⟩ rfl
  · simp only [ha, ↓reduceIte]
    by_cases hf : o = .refused
    · simp only [hf, ↓reduceIte]
      exact .answer r _ hr rfl false
        (Or.inr (Or.inr ⟨p, hb, Or.inr (Or.inl ⟨hnot ha, rfl, href'.1 hf, rfl, rfl, rfl⟩)⟩))
        rfl ⟨rfl, rfl, rfl, rfl⟩ rfl
    · simp only [hf, ↓reduceIte]
      have hok : p.recs = g.hub.recs ∧ ¬ law.dropped g.hub.recs p :=
        ⟨Classical.byContradiction fun h => hf (href'.2 (Or.inl h)),
          fun h => hf (href'.2 (Or.inr h))⟩
      exact .answer r _ hr rfl false
        (Or.inr (Or.inr ⟨p, hb, Or.inr (Or.inr ⟨hnot ha, rfl, hok, rfl, rfl, rfl⟩)⟩))
        rfl ⟨rfl, rfl, rfl, rfl⟩ rfl

/-- The hub's writes before it decides a push, projected: `store_ops`, `store_objects` and the
contraction bodies it generates itself (`with_contracted`), which it writes even for a push it
then rejects or finds idempotent. A push it refuses (other records, or a dropped head) is refused
before them (hub.rs:264-272): no growth, `next' = g.next` and `par' = g.par`. The raw graph grows
by ids above every one in use, the parents of those in use unchanged; nothing else moves. -/
def HubAnswer.stored (g : Sys) (next' : Nat) (par' : Nat → List Nat) : Sys :=
  { g with next := next', par := par', time := g.time + 1 }

/-- Those writes are a raw step of the system (`env`, raw growth only). -/
theorem HubAnswer.store_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    {next' : Nat} {par' : Nat → List Nat} (hn : g.next ≤ next')
    (hpar : ∀ y, y < g.next → par' y = g.par y) :
    SysStep N D law .env g (HubAnswer.stored g next' par') :=
  .env ⟨hn, hpar⟩ rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- The native `Push` handler, projected: its writes, a raw step, then its decision from the state
they leave, the `answer` step `push_step` builds. Every binding of the decision (the call in
flight, the records compared, `is_dropped`, the closure stored, the law accepting exactly when
`Push::answer` does) is of that post-write state, whose raw graph holds what the push uploaded
and what the hub generated. -/
theorem HubAnswer.push_handled {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {g : Sys}
    {next' : Nat} {par' : Nat → List Nat} {r : Req} {p : Pkt} {c : RawPublish.Checks}
    (hn : g.next ≤ next') (hpar : ∀ y, y < g.next → par' y = g.par y)
    (hr : r ∈ g.reqs) (hb : r.body = .push p)
    (hrec : c.recordsMatch = true ↔ p.recs = g.hub.recs)
    (hdrop : c.dropped = true ↔ law.dropped g.hub.recs p)
    (hclosed : c.recordsMatch = true → c.dropped = false → p.new ≠ g.hub.head →
      g.hub.head = p.expected → c.closed = true)
    (hacc : RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c =
      .accepted ↔ law.accepts g.hub par' p) :
    SysStep N D law .env g (HubAnswer.stored g next' par') ∧
    SysStep N D law .answer (HubAnswer.stored g next' par')
      (pushAfter N law (HubAnswer.stored g next' par') r p
        (RawPublish.answer ⟨g.hub.seq, g.hub.head⟩ ⟨p.expected, p.new, p.pending⟩ c)) :=
  ⟨HubAnswer.store_step hn hpar,
    (HubAnswer.push_step (g := HubAnswer.stored g next' par') hr hb hrec hdrop hclosed hacc).2⟩

/-! ### The answer, as a conformance test observes it

A small computable view of a hub answer, for a native test to compare against: the hub's
`(seq, head, records)` before and after, the reply's kind, and what it carries. A `Fetch` or
`GetObjects` answer passes `checkAnswer` exactly when the hub did not move and the reply is the
one `handle` gives; a passing observation is the system's `answer` step
(`HubAnswer.observed_step`). -/

inductive AnswerKind
  | fetched
  | objects
  | head
  | refused
  deriving DecidableEq, Repr

/-- One hub answer, observed: the hub's snapshot before and after, the reply's kind, and the
snapshot or records it carries. -/
structure AnswerObs where
  before : Snap
  after : Snap
  kind : AnswerKind
  replySnap : Option Snap
  replyRecs : Option Nat
  deriving DecidableEq

/-- The observation of the answer `ans`, the hub's snapshot going from `before` to `after`. -/
def AnswerObs.ofAns (before after : Snap) : Ans → AnswerObs
  | .fetched s => ⟨before, after, .fetched, some s, none⟩
  | .objects => ⟨before, after, .objects, none, none⟩
  | .head s => ⟨before, after, .head, some s, none⟩
  | .refused r => ⟨before, after, .refused, none, some r⟩

/-- What `handle` gives for a call of body `b`, from the hub at `s`, if it is a `Fetch` or a
`GetObjects`: the hub unmoved, and the reply. -/
def expectAnswer (b : Body) (s : Snap) : Option AnswerObs :=
  match b with
  | .fetch => some (AnswerObs.ofAns s s (.fetched s))
  | .objs => some (AnswerObs.ofAns s s .objects)
  | .push _ => none

/-- A `Fetch` or `GetObjects` answer conforms when it is what `handle` gives from the hub's
snapshot before. -/
def checkAnswer (b : Body) (o : AnswerObs) : Bool := expectAnswer b o.before == some o

/-- The system after the hub answers the call `r` with `ans`, the hub's snapshot left as it is. -/
def HubAnswer.apply (g : Sys) (r : Req) (ans : Ans) : Sys :=
  { g with
    reqs := g.reqs.erase r
    reps := g.reps ++ [⟨r.node, r.slot, g.time, r.body, false, ans⟩]
    time := g.time + 1 }

/-- An observed `Fetch` or `GetObjects` answer that conforms is the system's `answer` step, the
projected state after being `apply` with the hub's observed snapshot after. -/
theorem HubAnswer.observed_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {g : Sys} {r : Req} {ans : Ans} {after : Snap} (hr : r ∈ g.reqs)
    (hok : checkAnswer r.body (AnswerObs.ofAns g.hub after ans) = true) :
    SysStep N D law .answer g { HubAnswer.apply g r ans with hub := after } := by
  unfold checkAnswer expectAnswer at hok
  cases hb : r.body with
  | fetch =>
    rw [hb] at hok
    cases ans with
    | fetched s =>
      simp only [AnswerObs.ofAns, beq_iff_eq, Option.some.injEq, AnswerObs.mk.injEq,
        true_and, and_true] at hok
      obtain ⟨rfl, rfl⟩ := hok
      exact .answer r _ hr rfl false (Or.inl ⟨hb, rfl, rfl, rfl, rfl⟩) rfl
        ⟨rfl, rfl, rfl, rfl⟩ rfl
    | objects => simp [AnswerObs.ofAns] at hok
    | head s => simp [AnswerObs.ofAns] at hok
    | refused x => simp [AnswerObs.ofAns] at hok
  | objs =>
    rw [hb] at hok
    cases ans with
    | objects =>
      simp only [AnswerObs.ofAns, beq_iff_eq, Option.some.injEq, AnswerObs.mk.injEq,
        true_and, and_true] at hok
      subst hok
      exact .answer r _ hr rfl false (Or.inr (Or.inl ⟨hb, rfl, rfl, rfl, rfl⟩)) rfl
        ⟨rfl, rfl, rfl, rfl⟩ rfl
    | fetched s => simp [AnswerObs.ofAns] at hok
    | head s => simp [AnswerObs.ofAns] at hok
    | refused x => simp [AnswerObs.ofAns] at hok
  | push p =>
    rw [hb] at hok
    simp at hok

/-- And `handle`'s own answer passes the check. -/
theorem checkAnswer_expect (b : Body) (s : Snap) (o : AnswerObs)
    (h : expectAnswer b s = some o) : checkAnswer b o = true := by
  unfold checkAnswer
  cases b <;> simp only [expectAnswer, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> simp [AnswerObs.ofAns, expectAnswer]

/-! ### A node's events

A node's step that sends calls, and its handling of their replies, are observed by the node's own
data: the kind of step and the state its writes leave, its batch of calls by virtual slot and
body, the replies by slot, and the structural projection of its labels into raw ids. A raw id
names one canonical body, so a write that coincides with an operation that exists takes no fresh
raw id, and one the node holds already takes no new label. The projection is checked on the
observation (`NodeSys.Exec.growB`); what is not read off the data is a named law of the native
call that does it, a correspondence obligation: the decision relations (`Issue`, `Handle`, `Loc`,
`Idle`, `HeadRep`) have no checker of their own yet. A label a reply teaches is structure only:
its parents and raw id. What the node holds of it is what it held of that label before, which is
nothing for a state holding nothing above its labels (`Bare`, `learn_new_bare`): a label is new
only for an operation the node did not hold. -/

/-- A node's step that sends calls, as observed: the node, the kind of step, its state after its
writes and their embedding, the head it pushes, and the calls of its batch, by virtual slot (the
batch's injective map of its wire ids) and body. -/
structure NodeIssue where
  node : Nat
  kind : Kind
  post : NS
  new : Nat
  emb : Nat → Nat
  calls : List Req

/-- The node's generation after the step: one more for each label its writes add. -/
def NodeIssue.gen (g : Sys) (e : NodeIssue) : Nat :=
  (g.node e.node).gen + (e.post.next - (g.node e.node).ns.next)

/-- The system after the step: the raw graph as its writes leave it (`next'`, `par'`), the node
waiting on its calls with its state as it was, the calls in flight, and the slots below `slot'`
given out. -/
def NodeIssue.apply (g : Sys) (e : NodeIssue) (next' : Nat) (par' : Nat → List Nat)
    (slot' : Nat) : Sys :=
  { g with
    next := next'
    par := par'
    node := upd g.node e.node ⟨(g.node e.node).ns, (g.node e.node).emb, e.gen g,
      some ⟨e.kind, e.calls.map Req.slot, e.post, e.new, e.emb⟩⟩
    reqs := g.reqs ++ e.calls
    slot := slot'
    time := g.time + 1 }

/-- What the observation of the step must bind, each a law of the native call that does it:
- `idle`: the node has no calls out, the core taking a step only once the last one's replies are
  handled (`NodeCore`);
- `decide`: it is a step the core takes, with its writes (`NodeCore::step`, `Issue`): a
  correspondence obligation of that call, which no checker of this exact relation tests (the
  existing tests cover the core's behaviour in parts) and nothing here proves;
- `grow`: the structural check of its writes passes (`Exec.growB`: each new label a fresh raw id
  or an operation that exists already, labels and raw ids below unmoved);
- `bodies`: the calls are the ones the step returns (`Bodies`);
- `slots`, `nodup`, `slotLe`: the batch's calls take virtual slots of their own, from `g.slot` to
  below `slot'`, none twice (`CallBatch`);
- `notDropped`: the head it pushes is not one its own records or drops drop (the node). -/
structure NodeIssue.Binds (D : Nat → Nat → Nat → Prop) (law : HubLaw) (e : NodeIssue) (g : Sys)
    (next' : Nat) (par' : Nat → List Nat) (slot' : Nat) : Prop where
  idle : (g.node e.node).wait = none
  decide : Issue (D e.node) (g.node e.node).ns e.kind e.post e.new
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe (e.apply g next' par' slot') e.post e.emb) = true
  bodies : Bodies (g.node e.node).ns e.kind (pkt e.node (e.gen g) e.post e.emb e.new)
    (e.calls.map Req.body)
  slots : ∀ q ∈ e.calls, q.node = e.node ∧ g.slot ≤ q.slot ∧ q.slot < slot'
  nodup : (e.calls.map Req.slot).Nodup
  slotLe : g.slot ≤ slot'
  notDropped : ∀ q ∈ e.calls, ∀ p, q.body = .push p → ¬ law.dropped p.recs p

/-- A node's observed step that sends calls is the system's `issue` step. -/
theorem NodeIssue.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw} {e : NodeIssue}
    {g : Sys} {next' : Nat} {par' : Nat → List Nat} {slot' : Nat}
    (B : e.Binds D law g next' par' slot') :
    SysStep N D law (.issue e.node e.kind) g (e.apply g next' par' slot') :=
  .issue e.node e.kind e.post e.new e.emb e.calls B.idle B.decide (Exec.growB_sound B.grow)
    B.bodies B.slots B.nodup rfl rfl B.slotLe ⟨rfl, rfl, rfl⟩ rfl B.notDropped

/-- In the eligible nodes' system: an eligible node's step is its `issue` step. -/
theorem NodeIssue.hive_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : NodeIssue} {g : Sys} {next' : Nat}
    {par' : Nat → List Nat} {slot' : Nat} (hE : E e.node) (B : e.Binds D law g next' par' slot') :
    HiveStep N D law E old (.issue e.node e.kind) g (e.apply g next' par' slot') :=
  .node e.node hE rfl (NodeIssue.step B)

/-- Another node's step, with the slots as they were, is a raw step: its writes grow the raw
graph (`Exec.growB`'s check on its own labels), and its calls, none of them in flight at the entry
cut, join those in flight. -/
theorem NodeIssue.raw_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : NodeIssue} {g : Sys} {next' : Nat}
    {par' : Nat → List Nat} (hn : ¬ E e.node)
    (hgrow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
      (Exec.observe (e.apply g next' par' g.slot) e.post e.emb) = true)
    (hcalls : ∀ q ∈ e.calls, q.node = e.node ∧ q ∉ old) :
    HiveStep N D law E old .env g (e.apply g next' par' g.slot) := by
  have G := Exec.growB_sound hgrow
  refine .raw e.node hn e.calls ⟨G.rawGrows, G.parRaw⟩ (fun m hm => ?_) rfl hcalls
    ⟨rfl, rfl, rfl, rfl⟩ rfl
  have hmn : m ≠ e.node := fun h => hn (h ▸ hm)
  exact upd_ne _ _ hmn

/-- The head the replies of a step name, if one does. -/
def namedHead (rs : List Rep) : Option Nat := (rs.filterMap fun r => r.ans.head?).head?

/-- At most one of the replies names a head: then it is the head they name. -/
theorem namedHead_of_le {rs : List Rep} (h1 : (rs.filterMap fun r => r.ans.head?).length ≤ 1) :
    (∀ r ∈ rs, ∀ h, r.ans.head? = some h → namedHead rs = some h) ∧
      ∀ h, namedHead rs = some h → ∃ r ∈ rs, r.ans.head? = some h := by
  constructor
  · intro r hr h hh
    have hm : h ∈ rs.filterMap fun r => r.ans.head? := List.mem_filterMap.2 ⟨r, hr, hh⟩
    unfold namedHead
    generalize (rs.filterMap fun r => r.ans.head?) = L at hm h1 ⊢
    match L, h1, hm with
    | [], _, hm => cases hm
    | [x], _, hm => rw [List.mem_singleton.1 hm]; rfl
    | _ :: _ :: _, h1, _ => simp at h1
  · intro h hh
    unfold namedHead at hh
    exact List.mem_filterMap.1 (List.mem_of_mem_head? hh)

/-- What a reply or a notification teaches, from the structural check: the labels it adds are
for raw operations that exist (the raw graph does not grow), with their parents, numbered above
the node's and parents first; the node's other fields are as they were (`ctl`), so what it holds
of a new label (local, staged, objects) is what it held there before (`learn_new_bare`). With the
adapter's laws that it labels only what is missing (`nothing`) and that a step that wrote nothing
has its state as its state after (`same`), that is `Learn`. -/
theorem learn_of_growB {g : Sys} {σ post : NS} {emb : Nat → Nat} {hd : Option Nat}
    {σi posti : NS} {embi : Nat → Nat} (S : Scoped post emb g) (hlt : ParLt post.par)
    (hgrow : Exec.growB (Exec.observe g post emb) (Exec.observe g posti embi) = true)
    (hnothing : (∀ h, hd = some h → Closed post emb g h) → σi = σ ∧ posti = post ∧ embi = emb)
    (hsame : post = σ → posti = σi)
    (hctl : σi = { σ with par := σi.par, next := σi.next } ∧
      posti = { post with par := posti.par, next := posti.next })
    (hgrows : σ.next ≤ σi.next) (hparLt : ParLt posti.par) :
    Learn g σ post emb hd σi posti embi := by
  have G := Exec.growB_sound hgrow
  exact ⟨hnothing, scoped_growR S hlt G, hsame, hctl, ⟨G.next, hgrows⟩, G.parOld, G.embOld,
    hparLt⟩

/-- The node holds nothing from label `k` on: no such operation is local, staged, or has its
objects. -/
def BareFrom (k : Nat) (σ : NS) : Prop := ∀ x, k ≤ x → ¬ σ.loc x ∧ ¬ σ.stg x ∧ ¬ σ.obj x

/-- The node holds nothing above its labels: an operation it has no label for is not local,
not staged, and has no objects. The structural projection builds the node's states so. -/
def Bare (σ : NS) : Prop := BareFrom σ.next σ

/-- A label a reply or a notification teaches is structure only: of a node that holds nothing
above its labels, a new label stands for an operation that is not local, not staged and has no
objects, until its body and objects arrive. -/
theorem learn_new_bare {g : Sys} {σ post : NS} {emb : Nat → Nat} {hd : Option Nat}
    {σi posti : NS} {embi : Nat → Nat} (hl : Learn g σ post emb hd σi posti embi) (hσ : Bare σ)
    (hpost : Bare post) : BareFrom σ.next σi ∧ BareFrom post.next posti := by
  have e1 := hl.ctl.1
  have e2 := hl.ctl.2
  have l1 : σi.loc = σ.loc := by rw [e1]
  have s1 : σi.stg = σ.stg := by rw [e1]
  have o1 : σi.obj = σ.obj := by rw [e1]
  have l2 : posti.loc = post.loc := by rw [e2]
  have s2 : posti.stg = post.stg := by rw [e2]
  have o2 : posti.obj = post.obj := by rw [e2]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [l1, s1, o1]; exact hσ x hx
  · rw [l2, s2, o2]; exact hpost x hx

/-- A node handling the replies to its step's calls, as observed: the node, the replies by slot,
the hub's context they teach, the node's states with what they teach labelled (`σi` before the
step's writes, `posti` after) and its state after, and the embedding with what they teach. -/
structure NodeHandle where
  node : Nat
  replies : List Rep
  ctx : Ctx
  σi : NS
  posti : NS
  after : NS
  embi : Nat → Nat

/-- The system after the node handles the replies: its state after, done waiting, and the
replies in flight `reps'`. -/
def NodeHandle.apply (g : Sys) (e : NodeHandle) (reps' : List Rep) : Sys :=
  { g with
    node := upd g.node e.node ⟨e.after, e.embi, (g.node e.node).gen, none⟩
    reps := reps'
    time := g.time + 1 }

/-- What the observation of the handling must bind, for the step `w` whose calls are out, each a
law of the native call that does it:
- `waiting`: the node waits on the step `w`;
- `replies`, `complete`: the replies are to the step's calls, one for each slot, matched by slot
  (`CallBatch`, which finishes only when every call has its reply);
- `oneHead`: at most one of them names a head, a computable check (a step's batch has one `Fetch`
  or `Push`, and a `GetObjects` reply names none);
- `grow`: the structural check of what they teach passes (`Exec.growB`, on an unmoved raw graph);
- `nothing`, `same`, `ctl`, `grows`, `parLt`: the adapter labels only what is missing below the
  head they name, adds labels and nothing else, parents first, and a step that wrote nothing has
  its state as its state after;
- `drops`, `fits`: the context they teach is the replies' (the head's label, sequence and
  records), with the node's drops;
- `handle`: the core's handling of the replies (`Handle`), a correspondence obligation of that
  handling, which no checker of this exact relation tests;
- `reps`: the replies leave the ones in flight, nothing else. -/
structure NodeHandle.Binds (D : Nat → Nat → Nat → Prop) (e : NodeHandle) (g : Sys) (w : Wait)
    (reps' : List Rep) : Prop where
  waiting : (g.node e.node).wait = some w
  replies : ∀ r ∈ e.replies, r ∈ g.reps ∧ r.node = e.node ∧ r.slot ∈ w.slots
  complete : ∀ s ∈ w.slots, ∃ r ∈ e.replies, r.slot = s
  oneHead : (e.replies.filterMap fun r => r.ans.head?).length ≤ 1
  grow : Exec.growB (Exec.observe g w.post w.emb) (Exec.observe g e.posti e.embi) = true
  nothing : (∀ h, namedHead e.replies = some h → Closed w.post w.emb g h) →
    e.σi = (g.node e.node).ns ∧ e.posti = w.post ∧ e.embi = w.emb
  same : w.post = (g.node e.node).ns → e.posti = e.σi
  ctl : e.σi = { (g.node e.node).ns with par := e.σi.par, next := e.σi.next } ∧
    e.posti = { w.post with par := e.posti.par, next := e.posti.next }
  grows : (g.node e.node).ns.next ≤ e.σi.next
  parLt : ParLt e.posti.par
  drops : e.ctx.drops = D e.node
  fits : ∀ r ∈ e.replies, Fits e.embi e.posti.next e.ctx r.ans
  handle : Handle e.ctx e.σi w.kind e.posti (e.replies.map Rep.ans) e.after
  reps : ∀ r, r ∈ reps' ↔ (r ∈ g.reps ∧ r ∉ e.replies)

/-- A node's observed handling of its step's replies is the system's `handle` step, given the
node's invariants then (`NodeOK`, which a run keeps). -/
theorem NodeHandle.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeHandle} {g : Sys} {w : Wait} {reps' : List Rep} (K : NodeSys.NodeOK D e.node g)
    (B : e.Binds D g w reps') : SysStep N D law (.handle e.node) g (e.apply g reps') := by
  have W := K.wait w B.waiting
  have hpost : LInv w.post := linv_of_sinv (post_inv W.issue (K.inv.sinv 0 (D e.node)))
  obtain ⟨hhd, hhd'⟩ := namedHead_of_le B.oneHead
  exact .handle e.node w e.replies (namedHead e.replies) e.ctx e.σi e.posti e.after e.embi
    B.waiting B.replies B.complete hhd hhd'
    (learn_of_growB W.scope hpost.parLt B.grow B.nothing B.same B.ctl B.grows B.parLt)
    B.drops B.fits B.handle rfl B.reps ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- In the eligible nodes' system: an eligible node's handling is its `handle` step. -/
theorem NodeHandle.hive_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {E : Nat → Prop} {old : List Req} {e : NodeHandle} {g : Sys} {w : Wait} {reps' : List Rep}
    (hE : E e.node) (K : NodeSys.NodeOK D e.node g) (B : e.Binds D g w reps') :
    HiveStep N D law E old (.handle e.node) g (e.apply g reps') :=
  .node e.node hE rfl (NodeHandle.step K B)

/-- A node's core step that sends nothing, as observed: the node, its state after, and the
embedding of what it wrote. -/
structure NodeCore where
  node : Nat
  after : NS
  emb : Nat → Nat

/-- The system after a core step, its writes leaving the raw graph at `next'` and `par'`, and
the node's generation at `gen'`. -/
def NodeCore.apply (g : Sys) (e : NodeCore) (next' : Nat) (par' : Nat → List Nat) (gen' : Nat) :
    Sys :=
  { g with
    next := next'
    par := par'
    node := upd g.node e.node ⟨e.after, e.emb, gen', none⟩
    time := g.time + 1 }

/-- What the observation of a core step that sends nothing must bind: the node has no calls out
and its round runs (`NodeCore`); the step is one the core takes (`NodeCore::step`, `Loc`), a
correspondence obligation of that call, which no checker of this exact relation tests; and the
structural check of its writes passes (`Exec.growB`). -/
structure NodeCore.Binds (D : Nat → Nat → Nat → Prop) (e : NodeCore) (g : Sys) (next' : Nat)
    (par' : Nat → List Nat) : Prop where
  idle : (g.node e.node).wait = none
  active : (g.node e.node).ns.act = true
  decide : Loc (D e.node) (g.node e.node).ns e.after
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe (e.apply g next' par' (g.node e.node).gen) e.after e.emb) = true

/-- A node's observed core step that sends nothing is the system's `busy` step. -/
theorem NodeCore.busy_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeCore} {g : Sys} {next' : Nat} {par' : Nat → List Nat}
    (B : e.Binds D g next' par') :
    SysStep N D law (.core e.node .busy) g (e.apply g next' par' (g.node e.node).gen) :=
  .busy e.node e.after e.emb B.idle B.active B.decide (Exec.growB_sound B.grow) rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- What the observation of the core idling must bind: no calls out, its round running, the
core idling (`NodeCore::step`, `Idle`), and housekeeping (`when_idle`) then writing nothing: the
raw graph does not move. -/
structure NodeCore.IdleBinds (D : Nat → Nat → Nat → Prop) (e : NodeCore) (g : Sys) : Prop where
  idle : (g.node e.node).wait = none
  active : (g.node e.node).ns.act = true
  decide : Idle (lctx (D e.node) (g.node e.node).ns) (g.node e.node).ns e.after
  emb : e.emb = (g.node e.node).emb

/-- The core idling, observed, with nothing written, is the system's `idle` step: the round
ends. -/
theorem NodeCore.idle_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeCore} {g : Sys} (B : e.IdleBinds D g) :
    SysStep N D law (.core e.node .idle) g (e.apply g g.next g.par (g.node e.node).gen) := by
  have h := B.emb
  refine .idle e.node e.after B.idle B.active B.decide ?_ ⟨rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl
  show upd g.node e.node ⟨e.after, e.emb, (g.node e.node).gen, none⟩ = _
  rw [h]

/-- What the observation of housekeeping that writes must bind: no calls out, its round running,
the core idling first (`Idle`, to `σ1`), then housekeeping (`when_idle`) writing from that state
with the round going on (`Ext`), and the structural check of its writes (`Exec.growB`). -/
structure NodeCore.MaintBinds (D : Nat → Nat → Nat → Prop) (e : NodeCore) (g : Sys) (σ1 : NS)
    (next' : Nat) (par' : Nat → List Nat) : Prop where
  idle : (g.node e.node).wait = none
  active : (g.node e.node).ns.act = true
  decide : Idle (lctx (D e.node) (g.node e.node).ns) (g.node e.node).ns σ1
  writes : Ext { σ1 with act := true } e.after
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe (e.apply g next' par' (g.node e.node).gen) e.after e.emb) = true

/-- Observed housekeeping that writes is the system's `maint` step: the round goes on. -/
theorem NodeCore.maint_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeCore} {g : Sys} {σ1 : NS} {next' : Nat} {par' : Nat → List Nat}
    (B : e.MaintBinds D g σ1 next' par') :
    SysStep N D law (.core e.node .maint) g (e.apply g next' par'
      ((g.node e.node).gen + (e.after.next - (g.node e.node).ns.next))) := by
  have G := Exec.growB_sound B.grow
  exact .maint e.node σ1 e.after e.emb B.idle B.active B.decide B.writes ⟨G.next, G.rawGrows,
    G.embOld, G.parRaw, G.parOld, G.bound, G.parNew, G.reuse, G.injNew, G.cover⟩ rfl
    ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- A node taking a notification between rounds, as observed: the node, the notification, the
context it teaches, the node's state with what it teaches labelled (`σi`), its state after, and
the embedding with what it teaches. -/
structure NodeNotice where
  node : Nat
  note : Note
  ctx : Ctx
  σi : NS
  after : NS
  embi : Nat → Nat

/-- The system after the node takes the notification: its state after, and the notification
gone from those in flight, that one copy. -/
def NodeNotice.apply (g : Sys) (e : NodeNotice) : Sys :=
  { g with
    node := upd g.node e.node ⟨e.after, e.embi, (g.node e.node).gen, none⟩
    notes := g.notes.erase e.note
    time := g.time + 1 }

/-- What the observation of a notification taken must bind: the node has no calls out and no round
running; the notification is its own and in flight; it names a newer pair than the node knows (the
filter of `NotificationControl`); what it teaches passes the structural check (`Exec.growB`) and
the adapter's laws, as for a reply; its context is the notification's, with the node's drops; and
the core takes it (`HeadRep`), a correspondence obligation of that handling, which no checker of
this exact relation tests. -/
structure NodeNotice.Binds (D : Nat → Nat → Nat → Prop) (e : NodeNotice) (g : Sys) : Prop where
  idle : (g.node e.node).wait = none
  between : (g.node e.node).ns.act = false
  inFlight : e.note ∈ g.notes
  own : e.note.node = e.node
  newer : (g.node e.node).ns.known.1 < e.note.snap.seq ∨
    (e.note.snap.seq = (g.node e.node).ns.known.1 ∧
      (g.node e.node).emb (g.node e.node).ns.known.2 = e.note.snap.head)
  grow : Exec.growB (Exec.observe g (g.node e.node).ns (g.node e.node).emb)
    (Exec.observe g e.σi e.embi) = true
  nothing : Closed (g.node e.node).ns (g.node e.node).emb g e.note.snap.head →
    e.σi = (g.node e.node).ns ∧ e.embi = (g.node e.node).emb
  ctl : e.σi = { (g.node e.node).ns with par := e.σi.par, next := e.σi.next }
  parLt : ParLt e.σi.par
  drops : e.ctx.drops = D e.node
  fits : Fits e.embi e.σi.next e.ctx (.head e.note.snap)
  handle : HeadRep e.ctx e.σi e.after

/-- A node's observed notification, taken, is the system's `notice` step, given the node's
invariants then. -/
theorem NodeNotice.step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {e : NodeNotice} {g : Sys} (K : NodeSys.NodeOK D e.node g) (B : e.Binds D g) :
    SysStep N D law (.notice e.node e.note) g (e.apply g) := by
  have G := Exec.growB_sound B.grow
  have hl : Learn g (g.node e.node).ns (g.node e.node).ns (g.node e.node).emb
      (some e.note.snap.head) e.σi e.σi e.embi :=
    learn_of_growB K.scope K.inv.parLt B.grow
      (fun h => by
        obtain ⟨h1, h2⟩ := B.nothing (h _ rfl)
        exact ⟨h1, h1, h2⟩)
      (fun _ => rfl) ⟨B.ctl, B.ctl⟩ G.next B.parLt
  exact .notice e.node e.note e.ctx e.σi e.σi e.after e.embi B.idle B.between B.inFlight B.own
    B.newer hl B.drops B.fits B.handle rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

/-- A node dropping a notification that names no newer pair, observed, is the system's `ignore`
step: between rounds, its own notification in flight leaves, the node unchanged. -/
theorem NodeNotice.ignore_step {N : Nat} {D : Nat → Nat → Nat → Prop} {law : HubLaw}
    {g : Sys} {n : Nat} {nt : Note} (hw : (g.node n).wait = none) (ha : (g.node n).ns.act = false)
    (hn : nt ∈ g.notes) (hnn : nt.node = n)
    (hold : nt.snap.seq < (g.node n).ns.known.1 ∨ (nt.snap.seq = (g.node n).ns.known.1 ∧
      (g.node n).emb (g.node n).ns.known.2 ≠ nt.snap.head)) :
    SysStep N D law (.ignore n) g { g with notes := g.notes.erase nt, time := g.time + 1 } :=
  .ignore n nt hw ha hn hnn hold rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl

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

The laws fall in four kinds. PRIMITIVE LOCAL CORRESPONDENCE, each binding the observation to one
native call or effect: `inboxStep`, `callIds`, `notesOld`, `ownHead`, `noteHead`, `quietKnown`,
`clock`, `maintBind`, `noteBind`, `replyBind`, `freshOwn`, `doneIn`, `rootSeq`, `latchKnown`,
`latchLe`, `latchMono`, `latchAtSample`, `hubSeqStep`, `histBind`, `answer`, `readyKeep`,
`readyFail`, `reopenWhy`, the record and drop effects, and the per-call laws inside `EntryLaws`,
`FetchLaws` and `PendingLaws`. ENVIRONMENT premises: `envFinal`, `failFinal`, `autoWritesStop`,
`userFinal`. FAIRNESS: `schedMono`, `idleStart`, `startCore`, and Fair and PushFair inside
`FineAt`. And what `FineAt` takes beyond them, its doc says from where. Everything else is
DERIVED liveness.

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

section Phases

open Musubi.EarlyEntry.Control

variable {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}

/-- From any hive time `c`, a node stops handling own replies to calls it made before `c` and
notices published before `c`: each old call has its slot, which a reply or a reopen retires
(`Retry.old_slots_eventually_stop`, reopens allowed), and old notices are finitely many in
flight and queued (`Retry.Notifications.old_notifications_stop`). No fair draining is assumed. -/
theorem old_effects_stop
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    (c n : Nat) (hn : n < N) :
    ∃ T, c ≤ T ∧ ∀ t, T ≤ t → (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
      ∀ a, O.note n t = some a → c ≤ a := by
  let c' := (O.inbox n c).next
  have hstep : ∀ i, ∃ b, Retry.InboxStep c' (O.inbox n (c + i)) (O.inbox n (c + i + 1)) b ∧
      ∀ id a, O.own n (c + i) = some (id, a) → id < c' → b = true :=
    fun i => C.inboxStep c' n (c + i) hn
  let old := fun i => Classical.choose (hstep i)
  have hold : ∀ i, Retry.InboxStep c' (O.inbox n (c + i)) (O.inbox n (c + i + 1)) (old i) ∧
      ∀ id a, O.own n (c + i) = some (id, a) → id < c' → old i = true :=
    fun i => Classical.choose_spec (hstep i)
  obtain ⟨T2, hT2⟩ := Retry.old_slots_eventually_stop c' (fun i => O.inbox n (c + i)) old
    (Nat.le_refl _) (fun i => (hold i).1)
  have nstep : ∀ i, ∃ h, Retry.Notifications.Step (O.oldNotes c n (c + i))
      (O.oldNotes c n (c + i + 1)) h ∧ ∀ a, O.note n (c + i) = some a → a < c → h = true :=
    fun i => C.notesOld c n (c + i) hn (by omega)
  let oldN := fun i => Classical.choose (nstep i)
  have holdN : ∀ i, Retry.Notifications.Step (O.oldNotes c n (c + i))
      (O.oldNotes c n (c + i + 1)) (oldN i) ∧
      ∀ a, O.note n (c + i) = some a → a < c → oldN i = true :=
    fun i => Classical.choose_spec (nstep i)
  obtain ⟨T3, hT3⟩ := Retry.Notifications.old_notifications_stop
    (fun i => O.oldNotes c n (c + i)) oldN (fun i => (holdN i).1)
  refine ⟨c + max T2 T3, by omega, fun t ht => ⟨fun id a h => ?_, fun a h => ?_⟩⟩
  · obtain ⟨d, rfl⟩ : ∃ d, t = c + d := ⟨t - c, by omega⟩
    have hid : c' ≤ id := Nat.le_of_not_lt fun hlt => by
      have hb := (hold d).2 id a h hlt
      rw [hT2 d (by omega)] at hb
      cases hb
    exact C.callIds n c (c + d) id a hn h hid
  · obtain ⟨d, rfl⟩ : ∃ d, t = c + d := ⟨t - c, by omega⟩
    exact Nat.le_of_not_lt fun hlt => by
      have hb := (holdN d).2 a h hlt
      rw [hT3 d (by omega)] at hb
      cases hb

/-- So, for all nodes at once. -/
theorem old_gone
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    (c : Nat) : ∃ k, c ≤ k ∧ OldGone N O c k := by
  obtain ⟨k, hk⟩ := Recovery.finite_common_cut N
    (fun n t => (∀ id a, O.own n t = some (id, a) → c ≤ O.callAt n id) ∧
      ∀ a, O.note n t = some a → c ≤ a)
    (fun n hn => (old_effects_stop C c n hn).elim fun T h => ⟨T, h.2⟩)
  exact ⟨max c k, Nat.le_max_left _ _, fun n hn t ht => hk t (by omega) n hn⟩

/-- An entered node never reopened, past the cut, comes to know a pair the hub had past the
cut, by a fresh own reply once its old calls' replies and old notices have stopped, and keeps
knowing one: own replies and notices then name such pairs, and nothing else moves it. -/
theorem known_truthful
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    {k k4' kS : Nat} (hcut : CutAt N recs adopts fails k) (hq : QuietAt N O k)
    (hnr : ∀ n, n < N → ∀ i, max k k4' ≤ i → ¬ O.reopen n i)
    (hkS : ∀ t, kS ≤ t → ∀ n, n < N → ¬ O.objFail n t) (n : Nat) (hn : n < N) :
    ∃ tT, ∀ i, tT ≤ i → KnownTrue run O k n i := by
  have hschedBound := HiveObs.sched_ge C.schedMono
  obtain ⟨T, hkT, hT⟩ := old_effects_stop C k n hn
  obtain ⟨p, hp⟩ : ∃ p, p = max T (max (max k k4') kS) := ⟨_, rfl⟩
  have L := C.entry _ hcut hq n hn p (by have := hschedBound n p; omega)
  obtain ⟨j, hfresh, -⟩ := L.enters fun j _ _ _ i _ =>
    hkS (O.sched n (p + j + 1 + i)) (by have := hschedBound n (p + j + 1 + i); omega) n hn
  have htj : p ≤ O.sched n (p + j) := by have := hschedBound n (p + j); omega
  obtain ⟨u, id, a, htu, -, hown, hcall⟩ := C.freshOwn n (O.sched n (p + j)) hn hfresh
  obtain ⟨hca, hau, hkn⟩ := C.ownHead n u id a hn (hnr n hn u (by omega)) hown
  have h0 : KnownTrue run O k n (u + 1) := ⟨a, by omega, by omega, by
    rw [hkn]; exact Retry.Serial.own_reply_learns _ _ _ (C.rootSeq a)⟩
  have stay : ∀ d, KnownTrue run O k n (u + 1 + d) := by
    intro d
    induction d with
    | zero => exact h0
    | succ d ih =>
      have hrt : ¬ O.reopen n (u + 1 + d) := hnr n hn _ (by omega)
      have hTt := hT (u + 1 + d) (by omega)
      show KnownTrue run O k n (u + 1 + d + 1)
      cases ho : O.own n (u + 1 + d) with
      | some r =>
        obtain ⟨id', a'⟩ := r
        obtain ⟨h1, h1', h2⟩ := C.ownHead n _ id' a' hn hrt ho
        exact ⟨a', Nat.le_trans (hTt.1 id' a' ho) h1, by omega, by
          rw [h2]; exact Retry.Serial.own_reply_learns _ _ _ (C.rootSeq a')⟩
      | none =>
        cases hn' : O.note n (u + 1 + d) with
        | some a' =>
          obtain ⟨ha', h2⟩ := C.noteHead n _ a' hn hrt hn'
          rcases handleHead_notice_or O.root (O.seq n (u + 1 + d), O.known n (u + 1 + d))
            ((run a').hub.seq, (run a').hub.head) with h | h
          · obtain ⟨b, hb, hbi, he⟩ := ih
            exact ⟨b, hb, by omega, by rw [h2, h, he]⟩
          · exact ⟨a', hTt.2 a' hn', by omega, by rw [h2, h]⟩
        | none =>
          obtain ⟨b, hb, hbi, he⟩ := ih
          exact ⟨b, hb, by omega, by rw [C.quietKnown n _ hn hrt ho hn', he]⟩
  refine ⟨u + 1, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact stay d

/-- Past the cut, every node has a core step of a running round at or after any of its scheduled
events: one between rounds starts one, fairly, and the round's first event is a core step. -/
theorem active_after
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    {kc : Nat} (hcut : CutAt N recs adopts fails kc) (hq : QuietAt N O kc) (n : Nat)
    (hn : n < N) (p : Nat) (hp : kc ≤ O.sched n p) :
    ∃ q, p ≤ q ∧ O.active n (O.sched n q) = true := by
  cases ha : O.active n (O.sched n p)
  · obtain ⟨q, hpq, hs⟩ := C.idleStart _ hcut hq n p hn hp ha
    exact ⟨q + 1, by omega, C.startCore _ hcut hq n q hn
      (Nat.le_trans hp (HiveObs.sched_le C.schedMono n hpq)) hs⟩
  · exact ⟨p, Nat.le_refl _, ha⟩

/-- A node past the cut, entered and never reopened, on a hub stable from `cut`, comes to know
the stable head, by an own reply to a call made after the hub stopped, and keeps it once its
old calls' replies and old notices (from before then) have stopped. -/
theorem knows_stable_head
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    {kc k4' kS cut K : Nat} (hcut : CutAt N recs adopts fails kc) (hq : QuietAt N O kc)
    (hnr : ∀ n, n < N → ∀ i, max kc k4' ≤ i → ¬ O.reopen n i)
    (hhub : ∀ i, cut ≤ i → (run i).hub = (run K).hub)
    (hkS : ∀ t, kS ≤ t → ∀ n, n < N → ¬ O.objFail n t) (n : Nat) (hn : n < N) :
    ∃ tk, ∀ t, tk ≤ t → O.known n t = (run K).hub.head := by
  have hschedBound := HiveObs.sched_ge C.schedMono
  obtain ⟨T1, hT1⟩ : ∃ T1, T1 = max cut (max (max kc k4') kS) := ⟨_, rfl⟩
  obtain ⟨Tq, hTq1, hT⟩ := old_effects_stop C T1 n hn
  have L := C.entry _ hcut hq n hn Tq (by have := hschedBound n Tq; omega)
  obtain ⟨j, hfresh, -⟩ := L.enters fun j _ _ _ i _ =>
    hkS (O.sched n (Tq + j + 1 + i)) (by have := hschedBound n (Tq + j + 1 + i); omega) n hn
  have htj : Tq ≤ O.sched n (Tq + j) := by have := hschedBound n (Tq + j); omega
  obtain ⟨u, id, a, htu, -, hown, hcall⟩ := C.freshOwn n (O.sched n (Tq + j)) hn hfresh
  obtain ⟨hca, -, hkn⟩ := C.ownHead n u id a hn (hnr n hn u (by omega)) hown
  let P : Retry.Serial.Head := ((run K).hub.seq, (run K).hub.head)
  have hP : (O.seq n (u + 1), O.known n (u + 1)) = P := by
    rw [hkn, hhub a (by omega)]
    exact Retry.Serial.own_reply_learns _ _ P (C.rootSeq K)
  have stay : ∀ d, (O.seq n (u + 1 + d), O.known n (u + 1 + d)) = P := by
    intro d
    induction d with
    | zero => exact hP
    | succ d ih =>
      have hrt : ¬ O.reopen n (u + 1 + d) := hnr n hn _ (by omega)
      have hTt := hT (u + 1 + d) (by omega)
      show (O.seq n (u + 1 + d + 1), O.known n (u + 1 + d + 1)) = P
      cases ho : O.own n (u + 1 + d) with
      | some r =>
        obtain ⟨id', a'⟩ := r
        obtain ⟨h1, -, h2⟩ := C.ownHead n _ id' a' hn hrt ho
        rw [h2, hhub a' (by have := hTt.1 id' a' ho; omega), ih]
        exact handleHead_same _ P
      | none =>
        cases hn' : O.note n (u + 1 + d) with
        | some a' =>
          rw [(C.noteHead n _ a' hn hrt hn').2, hhub a' (by have := hTt.2 a' hn'; omega), ih]
          exact handleHead_notice_le _ P P (Nat.le_refl _)
        | none => rw [C.quietKnown n _ hn hrt ho hn', ih]
  refine ⟨u + 1, fun t ht => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact congrArg Prod.snd (stay d)

end Phases

open Musubi.EarlyEntry.Control Musubi.Recovery.HubSys in
/-- The hive converges: from the native laws of its actual run, its hub settles, and every node
settles at the hub's head, its physical raw heads that head. The phases, in order: records and
drops stop changing; then the effects of old calls and notices from before that; then
adoptions and stale-plan failures, failed `GetObjects` replies and their recovering reopens,
ordinary failures, automatic writes and user work; every node enters, raw, and stays entered;
every node comes to know a pair the hub had past the cut; the eligible nodes' system converges,
so the hub is stable; every node comes to know its head; and a node that is not eligible is
impossible there. What the eligible nodes' system takes at the fine cut the proof chooses, once
every node has entered and completed a core step since, past the old-effects cut of calls and
notices from before the cut (`OldGone`), is a premise apart from the contracts (`fine`):
`FineAssembly.hive_converges_observed` builds it from the replay of observed native events. -/
theorem hive_converges {ρ α : Type} [DecidableEq ρ] {N : Nat} {D : Nat → Nat → Nat → Prop}
    {law : HubLaw} {run : Nat → Sys} {acts : Nat → Act} {recs : Nat → Exec.SEState} {B : Nat}
    {epoch : Nat → Nat → Retry.Records.State} {adopts fails : Nat → Nat → Bool}
    {recLabel : Nat → Nat} {Rof : Nat → ρ} {wOf : Nat → Nat} {O : HiveObs ρ α}
    (C : HiveContracts N D law run acts recs B epoch adopts fails recLabel Rof wOf O)
    (fine : ∀ k k4, CutAt N recs adopts fails k → QuietAt N O k → k ≤ k4 →
      (∀ n, n < N → ∀ i, k4 ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
      (∃ kG, OldGone N O k kG ∧ ∀ n, n < N → ∃ q, kG ≤ O.sched n q ∧
        O.doneAt n (O.sched n q) < k4 ∧ O.active n (O.sched n q) = true ∧
        ∀ i, O.sched n q ≤ i → RawEntry (Rof k) (wOf k) (O.rawAt n i)) →
      Nonempty (FineAt N D law (EligibleAt N recs k) run acts k4 (run k).hub.seq O.hist)) :
    ∃ K cut, K ≤ cut ∧ (∀ i, cut ≤ i → (run i).hub = (run K).hub) ∧
      ∀ n, n < N → ∃ H, ∀ i, cut ≤ i →
        NodeSettle.Settled ⟨(run K).hub.seq, H, (run K).hub.recs, D n⟩ ((run i).node n).ns ∧
        ((run i).node n).emb H = (run K).hub.head ∧
        ∀ x, heads (run i) n x ↔ x = (run K).hub.head := by
  -- records and drops stop changing
  obtain ⟨k1, hk1⟩ := Exec.record_and_drop_sets_stabilize N B recs C.recStep C.prune C.pruneLe
    C.dropsGrow C.hubBound C.nodeBound
  -- then the effects of old calls and notices from before that stop
  obtain ⟨kO, hkO1, hkO⟩ := old_gone C k1
  -- then adoptions and stale-plan failures
  have each : ∀ n, n < N → ∃ c, ∀ i, c ≤ i →
      adopts n i = false ∧ fails n i = false := by
    intro n hn
    obtain ⟨c, hc⟩ := Retry.Records.record_disturbances_stop (recLabel k1)
      (fun i => epoch n (kO + i)) (fun i => adopts n (kO + i)) (fun i => fails n (kO + i))
      (fun i => by
        have := C.epochStep k1 kO hk1 hkO1 hkO n hn (kO + i) (by omega)
        simpa [Nat.add_assoc] using this)
    refine ⟨kO + c, fun i hi => ?_⟩
    have := hc (i - kO) (by omega)
    simpa [show kO + (i - kO) = i by omega] using this
  obtain ⟨k2, hk2⟩ := Recovery.finite_common_cut N
    (fun n i => adopts n i = false ∧ fails n i = false) each
  -- past the environment's last loss, each node's object credit is spent at most once, so its
  -- failed `GetObjects` replies stop
  obtain ⟨kE, hkE⟩ := C.envFinal
  have S : ∀ n, n < N → ∃ c, ∀ t, c ≤ t → ¬ O.objFail n t := by
    intro n hn
    classical
    obtain ⟨c, hc⟩ := Retry.Serial.object_recoveries_stop (fun i => O.objReady n (kE + i))
      (fun i => decide (O.objFail n (kE + i)))
      (fun i h => C.readyKeep n (kE + i) hn (hkE _ (by omega)) h)
      (fun i h => C.readyFail n (kE + i) hn (hkE _ (by omega)) (of_decide_eq_true h))
    refine ⟨kE + c, fun t ht hf => ?_⟩
    have h := hc (t - kE) (by omega)
    rw [show kE + (t - kE) = t by omega] at h
    exact absurd hf (of_decide_eq_false h)
  obtain ⟨kS, hkS⟩ := Recovery.finite_common_cut N (fun n t => ¬ O.objFail n t) S
  -- then each node reopens to recover from a failed `GetObjects` once more at most
  have recov : ∀ n, n < N → ∃ kR, ∀ i, kR ≤ i → O.reopen n i → ∀ t, t ≤ i →
      O.objFail n t → ∃ s, t < s ∧ s < i ∧ O.reopen n s := by
    intro n hn
    by_cases h : ∃ s, kS ≤ s ∧ O.reopen n s
    · obtain ⟨s0, hs0, hr0⟩ := h
      refine ⟨s0 + 1, fun i hi _ t _ hf => ⟨s0, ?_, by omega, hr0⟩⟩
      exact Nat.lt_of_lt_of_le (Nat.lt_of_not_le fun ht => hkS t ht n hn hf) hs0
    · exact ⟨kS, fun i hi hr => absurd ⟨i, hi, hr⟩ h⟩
  obtain ⟨kR, hkR⟩ := Recovery.finite_common_cut N (fun n i => O.reopen n i → ∀ t, t ≤ i →
    O.objFail n t → ∃ s, t < s ∧ s < i ∧ O.reopen n s) recov
  -- ordinary failures and automatic writes stop: explicit premises, joined into the cut
  obtain ⟨kF, hkF⟩ := C.failFinal
  obtain ⟨kH, hkH⟩ := Recovery.finite_common_cut N (fun n t => ¬ O.autoWrite n t)
    C.autoWritesStop
  obtain ⟨kU, hkU⟩ := C.userFinal
  obtain ⟨kc, hkc⟩ : ∃ kc,
      kc = max (max k1 (max kO k2)) (max (max kF (max kH kU)) (max kS (max kR kE))) :=
    ⟨_, rfl⟩
  have hcut : CutAt N recs adopts fails kc := by
    refine ⟨fun i hi => ?_, fun n hn i hi => hk2 i (by omega) n hn⟩
    obtain ⟨h1, h2⟩ := hk1 i (by omega)
    obtain ⟨h3, h4⟩ := hk1 kc (by omega)
    exact ⟨h1.trans h3.symm, fun n hn x => (h2 n hn x).trans (h4 n hn x).symm⟩
  have hq : QuietAt N O kc :=
    ⟨fun t ht => hkF t (by omega), fun n hn t ht => hkH t (by omega) n hn,
      fun n hn t ht => hkU t (by omega) n hn, fun n hn t ht => hkS t (by omega) n hn,
      fun t ht => hkE t (by omega)⟩
  have hschedBound := HiveObs.sched_ge C.schedMono
  -- past the cut, only `Incomplete` reopens a node
  have reopenInc : ∀ n i, n < N → kc ≤ i → O.reopen n i → O.incomplete n i = true := by
    intro n i hn hi hr
    rcases C.reopenWhy _ hcut hq n i hn hi hr with h | ⟨t, hti, hf, hno⟩
    · exact h
    · obtain ⟨s, hts, hbetween, hrs⟩ := hkR i (by omega) n hn hr t hti hf
      exact absurd hrs (hno s hts hbetween)
  have serve : ∀ n, n < N → ∀ p, kS ≤ p → ∀ j, Before (O.entryData n p).reply j →
      (O.entryData n p).fetchCall j → (O.entryData n p).reply j = .fresh → ∀ i,
      ((O.entryData n p).round j).active i = true → ¬ ((O.entryData n p).round j).failed i :=
    fun n hn p hp j _ _ _ i _ =>
      hkS (O.sched n (p + j + 1 + i)) (by have := hschedBound n (p + j + 1 + i); omega) n hn
  -- every node enters, at an actual event of its own, and stays entered
  have hentered : ∀ n, n < N → ∃ j, ∀ i, j ≤ i →
      RawEntry (Rof kc) (wOf kc) (O.rawAt n i) := by
    intro n hn
    let p0 := max kc kS
    have L := C.entry _ hcut hq n hn p0 (by have := hschedBound n p0; omega)
    obtain ⟨j, -, hap, hrec, -, hseq, hann⟩ := L.enters (serve n hn p0 (by omega))
    have hej : RawEntry (Rof kc) (wOf kc) (O.rawAt n (O.doneAt n (O.sched n (p0 + j)) + 1)) :=
      ⟨hap, hseq, hann, hrec⟩
    have hle : kc ≤ O.doneAt n (O.sched n (p0 + j)) + 1 := by
      have := hschedBound n (p0 + j); have := (C.doneIn n (p0 + j) hn).1; omega
    exact ⟨_, raw_entry_persists _ _ (O.rawAt n) (O.reopen n) (fun i => O.incomplete n i = true)
      (O.expectedIsHead n) (O.closed n) _ hej
      (fun i hi => reopenInc n i hn (by omega))
      (fun i hi => C.incHead _ hcut n i hn (by omega))
      (fun i hi => C.closure _ hcut hq n i hn (by omega))
      (fun i hi => C.keep _ hcut hq n i hn (by omega))⟩
  obtain ⟨k4', hk4'⟩ := Recovery.finite_common_cut N
    (fun n i => RawEntry (Rof kc) (wOf kc) (O.rawAt n i)) hentered
  have hk4 : ∀ n, n < N → ∀ i, max kc k4' ≤ i → RawEntry (Rof kc) (wOf kc) (O.rawAt n i) :=
    fun n hn i hi => hk4' i (by omega) n hn
  -- an entered node is not reopened: only `Incomplete` reopens it, and its push is closed
  have hnr : ∀ n, n < N → ∀ i, max kc k4' ≤ i → ¬ O.reopen n i := by
    intro n hn i hi hr
    obtain ⟨hh, hc⟩ := C.incHead _ hcut n i hn (by omega)
      (reopenInc n i hn (by omega) hr)
    rw [C.closure _ hcut hq n i hn (by omega) (hk4 n hn i hi) hh] at hc
    cases hc
  -- every node comes to know a pair the hub had past the cut, and keeps knowing one; so does the
  -- Sys model's latched snapshot of it, from the node's sampled event past that on
  obtain ⟨k5, hk5⟩ := Recovery.finite_common_cut N
    (fun n i => KnownTrue run O kc n (O.latch n i))
    (fun n hn => by
      obtain ⟨tT, htT⟩ := known_truthful C hcut hq hnr hkS n hn
      refine ⟨O.sched n tT, fun i hi => htT _ ?_⟩
      have h1 := C.latchMono n _ _ hn hi
      rw [C.latchAtSample n tT hn] at h1
      have := hschedBound n tT
      omega)
  -- the effects of calls and notices from before the cut itself stop
  obtain ⟨kG, hkG, hG⟩ := old_gone C kc
  -- every node has, once entered and past those, a COMPLETED core step of a running round,
  -- whose prelude completes any realignment its records' taking left unfinished, after which
  -- its canonical op heads are distinct (an alias forces a merge, which leaves one)
  obtain ⟨k6, hk6⟩ := Recovery.finite_common_cut N
    (fun n i => ∃ q, kG ≤ O.sched n q ∧ O.doneAt n (O.sched n q) < i ∧
      O.active n (O.sched n q) = true ∧
      ∀ i', O.sched n q ≤ i' → RawEntry (Rof kc) (wOf kc) (O.rawAt n i'))
    (fun n hn => by
      obtain ⟨q, hpq, hact⟩ := active_after C hcut hq n hn (max (max kc k4') kG)
        (by have := hschedBound n (max (max kc k4') kG); omega)
      have hsq : max (max kc k4') kG ≤ O.sched n q := by have := hschedBound n q; omega
      exact ⟨O.doneAt n (O.sched n q) + 1, fun i hi =>
        ⟨q, by omega, by omega, hact, fun i' hi' => hk4 n hn i' (by omega)⟩⟩)
  -- the eligible nodes' system converges, so the hub is stable
  obtain ⟨k4, hk4d⟩ : ∃ k4, k4 = max (max (max kc k4') k5) k6 := ⟨_, rfl⟩
  obtain ⟨F⟩ := fine kc k4 hcut hq (by omega) (fun n hn i hi => hk4 n hn i (by omega))
    ⟨kG, hG, fun n hn => (hk6 k4 (by omega) n hn).elim fun q h =>
      ⟨q, h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩
  -- the Sys model's known pair at k4 is an honest snapshot of the hub's history from the cut
  have hknownF : ∀ n, EligibleAt N recs kc n →
      Recovery.HubNodeSteps.HonestSnap (run kc).hub.seq O.hist (run k4)
        ⟨(Recovery.HubSys.known (run k4) n).1, (Recovery.HubSys.known (run k4) n).2,
          (run k4).hub.recs⟩ := by
    intro n hE
    obtain ⟨a, hka, hal, he⟩ := hk5 k4 (by omega) n hE.1
    have hl := C.latchLe n k4 hE.1
    have hnl : ∀ s, kc ≤ s → ¬ O.lost s := fun s hs => hkE s (by omega)
    rw [C.latchKnown n k4 hE.1, he]
    exact ⟨seq_chain C.hubSeqStep hka (fun s h1 _ => hnl s h1),
      seq_chain C.hubSeqStep (by omega) (fun s h1 _ => hnl s (by omega)),
      C.histBind a (fun s h => hnl s (by omega))⟩
  obtain ⟨K, cut, -, hKc, hhub, hnodes⟩ := F.converges hknownF (fun n h => h.1)
  have hknows : ∀ n, n < N → ∃ tk, ∀ t, tk ≤ t → O.known n t = (run K).hub.head :=
    knows_stable_head C hcut hq hnr hhub hkS
  -- the laws of a node that is not eligible, on the stable hub it knows, cannot hold
  have hall : ∀ n, n < N → EligibleAt N recs kc n := by
    intro n hn
    apply Classical.byContradiction
    intro hne
    obtain ⟨tk, htk⟩ := hknows n hn
    -- from a core step of a running round, which comes: a node between rounds starts one
    obtain ⟨p0, hp0⟩ : ∃ p0, p0 = max (max cut (max (max kc k4') kS)) tk := ⟨_, rfl⟩
    obtain ⟨p, hpp, hact⟩ := active_after C hcut hq n hn p0 (by have := hschedBound n p0; omega)
    have hp := hschedBound n p
    have hstay : ∀ i, O.sched n p ≤ i → (run i).hub = (run (O.sched n p)).hub :=
      fun i hi => (hhub i (by omega)).trans (hhub _ (by omega)).symm
    have hknown : ∀ i, O.sched n p ≤ i → O.known n i = (run (O.sched n p)).hub.head :=
      fun i hi => (htk i (by omega)).trans (by rw [hhub (O.sched n p) (by omega)])
    apply (C.pending _ hcut hq n p hn hstay hknown (fun i hi => hk4 n hn i (by omega))
      hne).absurd (HiveObs.roundActive_zero O hact) _
      fun j _ => hkS (O.sched n (p + j)) (by have := hschedBound n (p + j); omega) n hn
    -- each push it sends is handled on the stable hub, which the handling leaves as it is
    intro j hpush
    have hsj := HiveObs.sched_le C.schedMono n (Nat.le_add_right p j)
    obtain ⟨hle, heq⟩ := C.answer _ hcut hq n (O.sched n (p + j)) hn (by omega) hpush
    rw [hstay (O.answerAt n (O.sched n (p + j))) (by omega),
      hstay (O.answerAt n (O.sched n (p + j)) + 1) (by omega)] at heq
    exact heq.symm
  exact ⟨K, cut, hKc, hhub, fun n hn => hnodes n (hall n hn)⟩

end Musubi.SysAcceptance

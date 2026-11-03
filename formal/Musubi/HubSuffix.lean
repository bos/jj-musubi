/-
The hub settles in the asynchronous suffix after the record and node-drop cuts
(`hub_suffix_stabilizes`). Its vertices are hub-space raw operations, read through
`Model.State`'s `U.par`; the universe may grow by merges, maintenance writes and other nodes'
operations. Eligible nodes `E` are fixed. The window `w` is where the hub's history is a strict
ancestry chain: before it, history need not be comparable at all.

The suffix keeps the hub's head and sequence still except to accept a push: any packet in a
list, from an eligible node or not, whose expected head is the hub's head and whose new head
is above it. Nothing here assumes the hub stops accepting, that ranks descend, that a sender
still holds its pushed head when the hub accepts it, or that accepts are finitely many. The
sender's state at an accept is derived (`Inv.pushInv`) for packets of its current maintenance
generation. Other packets, sent before the suffix, by another node, or before a maintenance
write, form a finite list once maintenance writes stop, and the strict chain pays for them:
each moves the hub's head at most once.

Eligible nodes' knowledge must already be truthful within the window when the suffix starts
(`inv_entry`): the caller must show they learned an honest reply from the window after the
cut. A known pair whose head is the hub's head under a wrong sequence number is not
consistent, and is not assumed to be.
-/
import Musubi.AsyncLiveness

namespace Musubi.HubSuffix

open Musubi

/-! ## The suffix -/

/-- A push the hub can accept: its sender; the maintenance generation the sender was in when
it sent it, or `none` for one sent before the suffix or of no generation; the sequence number
and head the sender knew; and its single head. -/
structure Packet where
  node : Nat
  tag : Option Nat
  ksq : Nat
  exp : Nat
  new : Nat

/-- The model's state, each node's maintenance generation, and every push the hub can still
accept. -/
structure GState where
  s : State
  bk : Nat → Nat
  pk : List Packet

/-- The hub's head, sequence and history are as they were. -/
def HubSame (s t : State) : Prop :=
  t.hub.head = s.hub.head ∧ t.hub.seq = s.hub.seq ∧ t.hub.hist = s.hub.hist

/-- Node `n`'s heads and knowledge are as they were. -/
def NodeSame (s t : State) (n : Nat) : Prop :=
  (t.node n).heads = (s.node n).heads ∧ (t.node n).known = (s.node n).known

/-- The universe is as it was. -/
def USame (s t : State) : Prop := t.U.par = s.U.par ∧ t.U.next = s.U.next

/-- The universe gains one fresh operation, `s.U.next`, whose parents are older. -/
def UExt (s t : State) : Prop :=
  t.U.next = s.U.next + 1 ∧ (∀ x, x ≠ s.U.next → t.U.par x = s.U.par x) ∧
    ∀ p ∈ t.U.par s.U.next, p < s.U.next

/-- A packet of its sender's current maintenance generation. -/
def Packet.current (g : GState) (p : Packet) : Prop := p.tag = some (g.bk p.node)

/-- The fresh packet node `n` sends with its single head `d`. -/
def sent (g : GState) (n d : Nat) : Packet :=
  ⟨n, some (g.bk n), (g.s.node n).known.1, (g.s.node n).known.2, d⟩

/-- One step of the suffix. Eligible nodes learn any honest reply from the window, newer than
what they know or not, advance and merge as the policy does, write maintenance operations (each
a new generation), and push their single head. Other nodes may add operations (`grow`). The
hub accepts any listed packet whose expected head is its head and whose new head is above it.
Everything else (realization, staging, transfers, other nodes' work and messages) changes no
eligible node's heads or knowledge, nor the hub's head, sequence or history. There is no
rollback, crash, user operation or abandonment. -/
inductive Step (E : Nat → Prop) (w : Nat) : GState → GState → Prop
  | frame {g g' : GState} (hU : USame g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → NodeSame g.s g'.s m) (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) :
      Step E w g g'
  | grow {g g' : GState} (hU : UExt g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → NodeSame g.s g'.s m) (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) :
      Step E w g g'
  | learn {g g' : GState} (n sq : Nat) (hE : E n) (hw : w ≤ sq) (hsq : sq ≤ g.s.hub.seq)
      (hU : USame g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m)
      (hheads : (g'.s.node n).heads = (g.s.node n).heads)
      (hknown : (g'.s.node n).known = (sq, g.s.hub.hist sq))
      (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) : Step E w g g'
  | advance {g g' : GState} (n : Nat) (hE : E n)
      (hna : ¬ ∃ h, (g.s.node n).heads h ∧ Anc g.s.U.par (g.s.node n).known.2 h)
      (hU : USame g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m)
      (hheads : (g'.s.node n).heads =
        maxSet g.s.U.par (fun y => (g.s.node n).heads y ∨ y = (g.s.node n).known.2))
      (hknown : (g'.s.node n).known = (g.s.node n).known)
      (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) : Step E w g g'
  | merge {g g' : GState} (n : Nat) (hE : E n)
      (h2 : ∃ a b, (g.s.node n).heads a ∧ (g.s.node n).heads b ∧ a ≠ b)
      (hU : UExt g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m)
      (hheads : ∀ y, (g'.s.node n).heads y ↔ y = g.s.U.next)
      (hknown : (g'.s.node n).known = (g.s.node n).known)
      (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) : Step E w g g'
  /-- An eligible node's merge of its heads, two or more, leaves one operation that EXISTS
  already: the same canonical merge another copy wrote (identical content, one raw vertex), or
  the one head jj keeps, the others its ancestors. The universe does not grow. -/
  | mergeExisting {g g' : GState} (n y : Nat) (hE : E n)
      (h2 : ∃ a b, (g.s.node n).heads a ∧ (g.s.node n).heads b ∧ a ≠ b)
      (hy : y < g.s.U.next) (hU : USame g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m)
      (hheads : ∀ y', (g'.s.node n).heads y' ↔ y' = y)
      (hknown : (g'.s.node n).known = (g.s.node n).known)
      (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) : Step E w g g'
  | maintain {g g' : GState} (n : Nat) (hE : E n)
      (hU : UExt g.s g'.s) (hh : HubSame g.s g'.s)
      (hn : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m)
      (hheads : ∀ y, (g'.s.node n).heads y ↔ y = g.s.U.next)
      (hknown : (g'.s.node n).known = (g.s.node n).known)
      (hbk : g'.bk = upd g.bk n (g.bk n + 1)) (hpk : g'.pk = g.pk) : Step E w g g'
  | send {g g' : GState} (n d : Nat) (hE : E n)
      (hhd : ∀ y, (g.s.node n).heads y ↔ y = d)
      (hU : USame g.s g'.s) (hh : HubSame g.s g'.s) (hn : ∀ m, E m → NodeSame g.s g'.s m)
      (hbk : g'.bk = g.bk) (hpk : g'.pk = sent g n d :: g.pk) : Step E w g g'
  | accept {g g' : GState} (p : Packet) (hp : p ∈ g.pk) (he : p.exp = g.s.hub.head)
      (hne : p.new ≠ g.s.hub.head) (hanc : Anc g.s.U.par g.s.hub.head p.new)
      (hU : USame g.s g'.s) (hhead : g'.s.hub.head = p.new)
      (hseq : g'.s.hub.seq = g.s.hub.seq + 1)
      (hhist : g'.s.hub.hist = upd g.s.hub.hist (g.s.hub.seq + 1) p.new)
      (hn : ∀ m, E m → NodeSame g.s g'.s m)
      (hbk : g'.bk = g.bk) (hpk : g'.pk = g.pk) : Step E w g g'

/-! ## The invariant -/

/-- What the suffix needs of a state: the hub's history a strict ancestry chain from the
window on, eligible nodes' knowledge truthful within the window, and of each current packet
from an eligible node that the hub could accept now, its expected head the hub's head and its
new head descending from it, that its sender still holds exactly the pushed head (`pushInv`).
That last is kept, not assumed: a sender moves on only by advancing, impossible while its head
descends from the hub's head and so from what it knows; by merging, impossible with one head;
or by a maintenance write, which ends the packet's generation. No original-history chain
before the window, and no creator ownership. -/
structure Inv (E : Nat → Prop) (w : Nat) (g : GState) : Prop where
  parLt : ParLt g.s.U.par
  headLt : g.s.hub.head < g.s.U.next
  histHead : g.s.hub.hist g.s.hub.seq = g.s.hub.head
  window : w ≤ g.s.hub.seq
  chain : ∀ i j, w ≤ i → i ≤ j → j ≤ g.s.hub.seq →
    Anc g.s.U.par (g.s.hub.hist i) (g.s.hub.hist j)
  strict : ∀ i j, w ≤ i → i < j → j ≤ g.s.hub.seq → g.s.hub.hist i < g.s.hub.hist j
  known : ∀ n, E n → w ≤ (g.s.node n).known.1 ∧ (g.s.node n).known.1 ≤ g.s.hub.seq ∧
    g.s.hub.hist (g.s.node n).known.1 = (g.s.node n).known.2
  headsLt : ∀ n, E n → ∀ y, (g.s.node n).heads y → y < g.s.U.next
  pkLt : ∀ p ∈ g.pk, p.new < g.s.U.next
  tagLe : ∀ p ∈ g.pk, ∀ k, p.tag = some k → k ≤ g.bk p.node
  pkExp : ∀ p ∈ g.pk, E p.node → p.current g →
    w ≤ p.ksq ∧ p.ksq ≤ g.s.hub.seq ∧ g.s.hub.hist p.ksq = p.exp
  pushInv : ∀ p ∈ g.pk, E p.node → p.current g → p.exp = g.s.hub.head →
    Anc g.s.U.par p.exp p.new → ∀ y, (g.s.node p.node).heads y ↔ y = p.new

/-! ## Good nodes and the measure -/

/-- An eligible node only a maintenance write makes bad: its knowledge is in the hub's history,
and its single head is at or below the hub's head and comparable with every head the hub
accepted in the window. The sender of a current push the hub accepts was bad, and is good
after it. -/
def GoodW (w : Nat) (s : State) (n : Nat) : Prop :=
  (s.node n).known.1 ≤ s.hub.seq ∧ s.hub.hist (s.node n).known.1 = (s.node n).known.2 ∧
    ∃ x, (∀ y, (s.node n).heads y ↔ y = x) ∧ Anc s.U.par x s.hub.head ∧
      ∀ i, w ≤ i → i ≤ s.hub.seq → Anc s.U.par x (s.hub.hist i) ∨ Anc s.U.par (s.hub.hist i) x

/-- Eligible nodes that are not good. -/
noncomputable def mBadW (N : Nat) (E : Nat → Prop) (w : Nat) (s : State) : Nat :=
  cnt N (fun n => E n ∧ ¬ GoodW w s n)

/-- The suffix can start wherever the hub's history is a strict chain from the window on and
eligible nodes know a pair from it, with every outstanding push tagged with no generation:
such pushes are paid for by the credit, never by `pushInv`. -/
theorem inv_entry {E : Nat → Prop} {w : Nat} {g : GState} (hlt : ParLt g.s.U.par)
    (hhead : g.s.hub.head < g.s.U.next) (hh : g.s.hub.hist g.s.hub.seq = g.s.hub.head)
    (hw : w ≤ g.s.hub.seq)
    (hchain : ∀ i j, w ≤ i → i ≤ j → j ≤ g.s.hub.seq →
      Anc g.s.U.par (g.s.hub.hist i) (g.s.hub.hist j))
    (hstrict : ∀ i j, w ≤ i → i < j → j ≤ g.s.hub.seq → g.s.hub.hist i < g.s.hub.hist j)
    (hknown : ∀ n, E n → w ≤ (g.s.node n).known.1 ∧ (g.s.node n).known.1 ≤ g.s.hub.seq ∧
      g.s.hub.hist (g.s.node n).known.1 = (g.s.node n).known.2)
    (hheads : ∀ n, E n → ∀ y, (g.s.node n).heads y → y < g.s.U.next)
    (hpk : ∀ p ∈ g.pk, p.new < g.s.U.next ∧ p.tag = none) : Inv E w g where
  parLt := hlt
  headLt := hhead
  histHead := hh
  window := hw
  chain := hchain
  strict := hstrict
  known := hknown
  headsLt := hheads
  pkLt p hp := (hpk p hp).1
  tagLe p hp k hk := by rw [(hpk p hp).2] at hk; cases hk
  pkExp p hp _ hc := by unfold Packet.current at hc; rw [(hpk p hp).2] at hc; cases hc
  pushInv p hp _ hc := by unfold Packet.current at hc; rw [(hpk p hp).2] at hc; cases hc

/-! ## Growing the universe -/

theorem uext_par {s t : State} (h : UExt s t) :
    t.U.par = upd s.U.par s.U.next (t.U.par s.U.next) := by
  funext x
  by_cases hx : x = s.U.next
  · subst hx; simp
  · rw [upd_ne _ _ hx]; exact h.2.1 x hx

theorem parLt_ext {s t : State} (h : UExt s t) (hlt : ParLt s.U.par) : ParLt t.U.par := by
  rw [uext_par h]; exact parLt_upd hlt h.2.2

theorem anc_ext_iff {s t : State} (h : UExt s t) (hlt : ParLt s.U.par) {a x : Nat}
    (hx : x < s.U.next) : Anc t.U.par a x ↔ Anc s.U.par a x := by
  rw [uext_par h]; exact anc_upd_iff hlt h.2.2 hx

/-! ## Facts the invariant gives -/

section Facts

variable {E : Nat → Prop} {w : Nat} {g : GState}

theorem Inv.histAnc (I : Inv E w g) {i : Nat} (hw : w ≤ i) (hi : i ≤ g.s.hub.seq) :
    Anc g.s.U.par (g.s.hub.hist i) g.s.hub.head := by
  have := I.chain i g.s.hub.seq hw hi (Nat.le_refl _)
  rwa [I.histHead] at this

theorem Inv.histLe (I : Inv E w g) {i : Nat} (hw : w ≤ i) (hi : i ≤ g.s.hub.seq) :
    g.s.hub.hist i ≤ g.s.hub.head := (I.histAnc hw hi).le I.parLt

theorem Inv.histLt (I : Inv E w g) {i : Nat} (hw : w ≤ i) (hi : i ≤ g.s.hub.seq) :
    g.s.hub.hist i < g.s.U.next := Nat.lt_of_le_of_lt (I.histLe hw hi) I.headLt

theorem Inv.knownLt (I : Inv E w g) {n : Nat} (hE : E n) :
    (g.s.node n).known.2 < g.s.U.next := by
  obtain ⟨hw, hle, hh⟩ := I.known n hE
  rw [← hh]; exact I.histLt hw hle

end Facts

/-! ## The invariant is kept -/

theorem inv_step {E : Nat → Prop} {w : Nat} {g g' : GState} (I : Inv E w g)
    (hs : Step E w g g') : Inv E w g' := by
  cases hs with
  | frame hU hh hn hbk hpk =>
    obtain ⟨hpar, hnext⟩ := hU
    obtain ⟨hhd, hsq, hhi⟩ := hh
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpar]; exact I.parLt
    · rw [hhd, hnext]; exact I.headLt
    · rw [hhi, hsq, hhd]; exact I.histHead
    · rw [hsq]; exact I.window
    · rw [hhi, hsq, hpar]; exact I.chain
    · rw [hhi, hsq]; exact I.strict
    · intro m hm; rw [(hn m hm).2, hsq, hhi]; exact I.known m hm
    · intro m hm; rw [(hn m hm).1, hnext]; exact I.headsLt m hm
    · rw [hpk, hnext]; exact I.pkLt
    · rw [hpk, hbk]; exact I.tagLe
    · intro p hp hE hc
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hsq, hhi]; exact I.pkExp p hp hE hc
    · intro p hp hE hc he ha
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hhd] at he
      rw [hpar] at ha
      rw [(hn p.node hE).1]
      exact I.pushInv p hp hE hc he ha
  | grow hU hh hn hbk hpk =>
    obtain ⟨hhd, hsq', hhi⟩ := hh
    have hlt' := parLt_ext hU I.parLt
    refine ⟨hlt', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhd, hU.1]; exact Nat.lt_succ_of_lt I.headLt
    · rw [hhi, hsq', hhd]; exact I.histHead
    · rw [hsq']; exact I.window
    · intro i j hi hij hj
      rw [hsq'] at hj; rw [hhi]
      exact (anc_ext_iff hU I.parLt (I.histLt (by omega) hj)).2 (I.chain i j hi hij hj)
    · rw [hhi, hsq']; exact I.strict
    · intro m hm; rw [(hn m hm).2, hsq', hhi]; exact I.known m hm
    · intro m hm y hy
      rw [(hn m hm).1] at hy; rw [hU.1]; exact Nat.lt_succ_of_lt (I.headsLt m hm y hy)
    · intro p hp; rw [hpk] at hp; rw [hU.1]; exact Nat.lt_succ_of_lt (I.pkLt p hp)
    · rw [hpk, hbk]; exact I.tagLe
    · intro p hp hE' hc
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hsq', hhi]; exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hhd] at he
      rw [(hn p.node hE').1]
      exact I.pushInv p hp hE' hc he ((anc_ext_iff hU I.parLt (I.pkLt p hp)).1 ha)
  | learn n sq hE hw hsq hU hh hn hheads hknown hbk hpk =>
    obtain ⟨hpar, hnext⟩ := hU
    obtain ⟨hhd, hsq', hhi⟩ := hh
    have nodeEq : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpar]; exact I.parLt
    · rw [hhd, hnext]; exact I.headLt
    · rw [hhi, hsq', hhd]; exact I.histHead
    · rw [hsq']; exact I.window
    · rw [hhi, hsq', hpar]; exact I.chain
    · rw [hhi, hsq']; exact I.strict
    · intro m hm
      rw [hsq', hhi]
      by_cases hmn : m = n
      · subst hmn; rw [hknown]; exact ⟨hw, hsq, rfl⟩
      · rw [(nodeEq m hm hmn).2]; exact I.known m hm
    · intro m hm
      rw [hnext]
      by_cases hmn : m = n
      · subst hmn; rw [hheads]; exact I.headsLt m hm
      · rw [(nodeEq m hm hmn).1]; exact I.headsLt m hm
    · rw [hpk, hnext]; exact I.pkLt
    · rw [hpk, hbk]; exact I.tagLe
    · intro p hp hE' hc
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hsq', hhi]; exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hhd] at he
      rw [hpar] at ha
      have hsame : (g'.s.node p.node).heads = (g.s.node p.node).heads := by
        by_cases hpn : p.node = n
        · rw [hpn]; exact hheads
        · exact (nodeEq p.node hE' hpn).1
      rw [hsame]
      exact I.pushInv p hp hE' hc he ha
  | advance n hE hna hU hh hn hheads hknown hbk hpk =>
    obtain ⟨hpar, hnext⟩ := hU
    obtain ⟨hhd, hsq', hhi⟩ := hh
    have nodeEq : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpar]; exact I.parLt
    · rw [hhd, hnext]; exact I.headLt
    · rw [hhi, hsq', hhd]; exact I.histHead
    · rw [hsq']; exact I.window
    · rw [hhi, hsq', hpar]; exact I.chain
    · rw [hhi, hsq']; exact I.strict
    · intro m hm
      rw [hsq', hhi]
      by_cases hmn : m = n
      · subst hmn; rw [hknown]; exact I.known m hm
      · rw [(nodeEq m hm hmn).2]; exact I.known m hm
    · intro m hm y hy
      rw [hnext]
      by_cases hmn : m = n
      · subst hmn
        rw [hheads] at hy
        rcases hy.1 with hy | hy
        · exact I.headsLt m hm y hy
        · rw [hy]; exact I.knownLt hm
      · rw [(nodeEq m hm hmn).1] at hy; exact I.headsLt m hm y hy
    · rw [hpk, hnext]; exact I.pkLt
    · rw [hpk, hbk]; exact I.tagLe
    · intro p hp hE' hc
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hsq', hhi]; exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hhd] at he
      rw [hpar] at ha
      have h1 := I.pushInv p hp hE' hc he ha
      by_cases hpn : p.node = n
      · rw [hpn] at h1
        obtain ⟨hw, hle, hhk⟩ := I.known n hE
        have h3' : Anc g.s.U.par g.s.hub.head p.new := by rw [← he]; exact ha
        have hk : Anc g.s.U.par (g.s.node n).known.2 p.new := by
          rw [← hhk]; exact (I.histAnc hw hle).trans h3'
        exact absurd ⟨p.new, (h1 p.new).2 rfl, hk⟩ hna
      · rw [(nodeEq p.node hE' hpn).1]
        exact h1
  | merge n hE h2 hU hh hn hheads hknown hbk hpk =>
    obtain ⟨hhd, hsq', hhi⟩ := hh
    have nodeEq : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m := hn
    have hlt' := parLt_ext hU I.parLt
    refine ⟨hlt', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhd, hU.1]; exact Nat.lt_succ_of_lt I.headLt
    · rw [hhi, hsq', hhd]; exact I.histHead
    · rw [hsq']; exact I.window
    · intro i j hi hij hj
      rw [hsq'] at hj; rw [hhi]
      exact (anc_ext_iff hU I.parLt (I.histLt (by omega) hj)).2 (I.chain i j hi hij hj)
    · rw [hhi, hsq']; exact I.strict
    · intro m hm
      rw [hsq', hhi]
      by_cases hmn : m = n
      · subst hmn; rw [hknown]; exact I.known m hm
      · rw [(nodeEq m hm hmn).2]; exact I.known m hm
    · intro m hm y hy
      rw [hU.1]
      by_cases hmn : m = n
      · subst hmn; rw [(hheads y).1 hy]; exact Nat.lt_succ_self _
      · rw [(nodeEq m hm hmn).1] at hy; exact Nat.lt_succ_of_lt (I.headsLt m hm y hy)
    · intro p hp; rw [hpk] at hp; rw [hU.1]; exact Nat.lt_succ_of_lt (I.pkLt p hp)
    · rw [hpk, hbk]; exact I.tagLe
    · intro p hp hE' hc
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hsq', hhi]; exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hhd] at he
      have h1 := I.pushInv p hp hE' hc he ((anc_ext_iff hU I.parLt (I.pkLt p hp)).1 ha)
      by_cases hpn : p.node = n
      · rw [hpn] at h1
        obtain ⟨a, b, ha', hb, hab⟩ := h2
        exact absurd (((h1 a).1 ha').trans ((h1 b).1 hb).symm) hab
      · rw [(nodeEq p.node hE' hpn).1]
        exact h1
  | mergeExisting n y hE h2 hy hU hh hn hheads hknown hbk hpk =>
    obtain ⟨hpar, hnext⟩ := hU
    obtain ⟨hhd, hsq', hhi⟩ := hh
    have nodeEq : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m := hn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpar]; exact I.parLt
    · rw [hhd, hnext]; exact I.headLt
    · rw [hhi, hsq', hhd]; exact I.histHead
    · rw [hsq']; exact I.window
    · rw [hhi, hsq', hpar]; exact I.chain
    · rw [hhi, hsq']; exact I.strict
    · intro m hm
      rw [hsq', hhi]
      by_cases hmn : m = n
      · subst hmn; rw [hknown]; exact I.known m hm
      · rw [(nodeEq m hm hmn).2]; exact I.known m hm
    · intro m hm y' hy'
      rw [hnext]
      by_cases hmn : m = n
      · subst hmn; rw [(hheads y').1 hy']; exact hy
      · rw [(nodeEq m hm hmn).1] at hy'; exact I.headsLt m hm y' hy'
    · rw [hpk, hnext]; exact I.pkLt
    · rw [hpk, hbk]; exact I.tagLe
    · intro p hp hE' hc
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hsq', hhi]; exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk] at hp
      unfold Packet.current at hc; rw [hbk] at hc
      rw [hhd] at he
      rw [hpar] at ha
      have h1 := I.pushInv p hp hE' hc he ha
      by_cases hpn : p.node = n
      · rw [hpn] at h1
        obtain ⟨a, b, ha', hb, hab⟩ := h2
        exact absurd (((h1 a).1 ha').trans ((h1 b).1 hb).symm) hab
      · rw [(nodeEq p.node hE' hpn).1]
        exact h1
  | maintain n hE hU hh hn hheads hknown hbk hpk =>
    obtain ⟨hhd, hsq', hhi⟩ := hh
    have nodeEq : ∀ m, E m → m ≠ n → NodeSame g.s g'.s m := hn
    have hlt' := parLt_ext hU I.parLt
    have stale : ∀ p ∈ g.pk, p.node = n → ¬ p.tag = some (g'.bk p.node) := by
      intro p hp hpn hc
      rw [hbk, hpn, upd_same] at hc
      have := I.tagLe p hp _ hc
      rw [hpn] at this
      omega
    refine ⟨hlt', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hhd, hU.1]; exact Nat.lt_succ_of_lt I.headLt
    · rw [hhi, hsq', hhd]; exact I.histHead
    · rw [hsq']; exact I.window
    · intro i j hi hij hj
      rw [hsq'] at hj; rw [hhi]
      exact (anc_ext_iff hU I.parLt (I.histLt (by omega) hj)).2 (I.chain i j hi hij hj)
    · rw [hhi, hsq']; exact I.strict
    · intro m hm
      rw [hsq', hhi]
      by_cases hmn : m = n
      · subst hmn; rw [hknown]; exact I.known m hm
      · rw [(nodeEq m hm hmn).2]; exact I.known m hm
    · intro m hm y hy
      rw [hU.1]
      by_cases hmn : m = n
      · subst hmn; rw [(hheads y).1 hy]; exact Nat.lt_succ_self _
      · rw [(nodeEq m hm hmn).1] at hy; exact Nat.lt_succ_of_lt (I.headsLt m hm y hy)
    · intro p hp; rw [hpk] at hp; rw [hU.1]; exact Nat.lt_succ_of_lt (I.pkLt p hp)
    · intro p hp k hk
      rw [hpk] at hp; rw [hbk]
      have := I.tagLe p hp k hk
      by_cases hpn : p.node = n
      · rw [hpn, upd_same]; rw [hpn] at this; omega
      · rw [upd_ne _ _ hpn]; exact this
    · intro p hp hE' hc
      rw [hpk] at hp
      by_cases hpn : p.node = n
      · exact absurd hc (stale p hp hpn)
      · unfold Packet.current at hc; rw [hbk, upd_ne _ _ hpn] at hc
        rw [hsq', hhi]; exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk] at hp
      by_cases hpn : p.node = n
      · exact absurd hc (stale p hp hpn)
      · unfold Packet.current at hc; rw [hbk, upd_ne _ _ hpn] at hc
        rw [hhd] at he
        rw [(nodeEq p.node hE' hpn).1]
        exact I.pushInv p hp hE' hc he ((anc_ext_iff hU I.parLt (I.pkLt p hp)).1 ha)
  | send n d hE hhd hU hh hn hbk hpk =>
    obtain ⟨hpar, hnext⟩ := hU
    obtain ⟨hhd', hsq', hhi⟩ := hh
    have hd : d < g.s.U.next := I.headsLt n hE d ((hhd d).2 rfl)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpar]; exact I.parLt
    · rw [hhd', hnext]; exact I.headLt
    · rw [hhi, hsq', hhd']; exact I.histHead
    · rw [hsq']; exact I.window
    · rw [hhi, hsq', hpar]; exact I.chain
    · rw [hhi, hsq']; exact I.strict
    · intro m hm; rw [(hn m hm).2, hsq', hhi]; exact I.known m hm
    · intro m hm; rw [(hn m hm).1, hnext]; exact I.headsLt m hm
    · intro p hp
      rw [hpk, List.mem_cons] at hp; rw [hnext]
      rcases hp with rfl | hp
      · exact hd
      · exact I.pkLt p hp
    · intro p hp k hk
      rw [hpk, List.mem_cons] at hp; rw [hbk]
      rcases hp with rfl | hp
      · simp only [sent, Option.some.injEq] at hk; rw [← hk]; exact Nat.le_refl _
      · exact I.tagLe p hp k hk
    · intro p hp hE' hc
      rw [hpk, List.mem_cons] at hp
      rw [hsq', hhi]
      rcases hp with rfl | hp
      · exact I.known n hE
      · unfold Packet.current at hc; rw [hbk] at hc
        exact I.pkExp p hp hE' hc
    · intro p hp hE' hc he ha
      rw [hpk, List.mem_cons] at hp
      rw [hhd'] at he
      rw [hpar] at ha
      rcases hp with rfl | hp
      · show ∀ y, (g'.s.node n).heads y ↔ y = d
        rw [(hn n hE).1]
        exact hhd
      · unfold Packet.current at hc; rw [hbk] at hc
        rw [(hn p.node hE').1]
        exact I.pushInv p hp hE' hc he ha
  | accept p hp he hne hanc hU hhead hseq hhist hn hbk hpk =>
    obtain ⟨hpar, hnext⟩ := hU
    have hlt := I.parLt
    have hnew : p.new < g.s.U.next := I.pkLt p hp
    have hup : g.s.hub.head < p.new := Anc.lt_of_ne hlt hanc (Ne.symm hne)
    have hist_old : ∀ i, i ≤ g.s.hub.seq → g'.s.hub.hist i = g.s.hub.hist i := by
      intro i hi; rw [hhist, upd_ne _ _ (by omega)]
    have hist_new : g'.s.hub.hist (g.s.hub.seq + 1) = p.new := by rw [hhist, upd_same]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpar]; exact hlt
    · rw [hhead, hnext]; exact hnew
    · rw [hseq, hist_new, hhead]
    · rw [hseq]; exact Nat.le_succ_of_le I.window
    · intro i j hi hij hj
      rw [hseq] at hj; rw [hpar]
      by_cases hjs : j = g.s.hub.seq + 1
      · subst hjs
        rw [hist_new]
        by_cases his : i = g.s.hub.seq + 1
        · subst his; rw [hist_new]; exact Anc.refl
        · rw [hist_old i (by omega)]
          exact (I.histAnc hi (by omega)).trans hanc
      · rw [hist_old i (by omega), hist_old j (by omega)]
        exact I.chain i j hi hij (by omega)
    · intro i j hi hij hj
      rw [hseq] at hj
      by_cases hjs : j = g.s.hub.seq + 1
      · subst hjs
        rw [hist_new, hist_old i (by omega)]
        exact Nat.lt_of_le_of_lt (I.histLe hi (by omega)) hup
      · rw [hist_old i (by omega), hist_old j (by omega)]
        exact I.strict i j hi hij (by omega)
    · intro m hm
      obtain ⟨hw, hle, hh⟩ := I.known m hm
      rw [(hn m hm).2, hseq, hist_old _ hle]
      exact ⟨hw, Nat.le_succ_of_le hle, hh⟩
    · intro m hm; rw [(hn m hm).1, hnext]; exact I.headsLt m hm
    · rw [hpk, hnext]; exact I.pkLt
    · rw [hpk, hbk]; exact I.tagLe
    · intro q hq hE' hc
      rw [hpk] at hq
      unfold Packet.current at hc; rw [hbk] at hc
      obtain ⟨hw, hle, hh⟩ := I.pkExp q hq hE' hc
      rw [hseq, hist_old _ hle]
      exact ⟨hw, Nat.le_succ_of_le hle, hh⟩
    · intro q hq hE' hc he'
      rw [hpk] at hq
      unfold Packet.current at hc; rw [hbk] at hc
      obtain ⟨hw, hle, hh⟩ := I.pkExp q hq hE' hc
      rw [hhead] at he'
      have := I.histLe hw hle
      rw [hh, he'] at this
      exact absurd this (Nat.not_le_of_lt hup)

/-! ## Good nodes stay good -/

theorem goodW_same {s t : State} {w n : Nat} (hU : t.U.par = s.U.par) (hh : HubSame s t)
    (hn : NodeSame s t n) (h : GoodW w s n) : GoodW w t n := by
  obtain ⟨hhd, hsq, hhi⟩ := hh
  obtain ⟨hhe, hkn⟩ := hn
  unfold GoodW
  rw [hhd, hsq, hhi, hhe, hkn, hU]; exact h

theorem goodW_ext {E : Nat → Prop} {w : Nat} {g : GState} (I : Inv E w g) {t : State}
    (hU : UExt g.s t) (hh : HubSame g.s t) {n : Nat} (hE : E n) (hn : NodeSame g.s t n)
    (h : GoodW w g.s n) : GoodW w t n := by
  obtain ⟨hk1, hk2, x, hx, hxh, hxc⟩ := h
  have hxl : x < g.s.U.next := I.headsLt n hE x ((hx x).2 rfl)
  obtain ⟨hhd, hsq, hhi⟩ := hh
  obtain ⟨hhe, hkn⟩ := hn
  unfold GoodW
  rw [hhd, hsq, hhi, hhe, hkn]
  refine ⟨hk1, hk2, x, hx, (anc_ext_iff hU I.parLt I.headLt).2 hxh, ?_⟩
  intro i hi his
  rcases hxc i hi his with h | h
  · exact Or.inl ((anc_ext_iff hU I.parLt (I.histLt hi his)).2 h)
  · exact Or.inr ((anc_ext_iff hU I.parLt hxl).2 h)

/-- Every step but a maintenance write keeps every good eligible node good. -/
theorem good_step {E : Nat → Prop} {w : Nat} {g g' : GState} (I : Inv E w g)
    (hs : Step E w g g') (hbk : g'.bk = g.bk) {m : Nat} (hm : E m) (h : GoodW w g.s m) :
    GoodW w g'.s m := by
  cases hs with
  | frame hU hh hn _ _ => exact goodW_same hU.1 hh (hn m hm) h
  | grow hU hh hn _ _ => exact goodW_ext I hU hh hm (hn m hm) h
  | learn n sq _ _ hsq hU hh hn hheads hknown _ _ =>
    by_cases hmn : m = n
    · subst hmn
      obtain ⟨-, -, x, hx, hxh, hxc⟩ := h
      obtain ⟨hhd, hsq', hhi⟩ := hh
      unfold GoodW
      rw [hhd, hsq', hhi, hheads, hknown, hU.1]
      exact ⟨hsq, rfl, x, hx, hxh, hxc⟩
    · exact goodW_same hU.1 hh (hn m hm hmn) h
  | advance n _ hna hU hh hn hheads hknown _ _ =>
    by_cases hmn : m = n
    · subst hmn
      obtain ⟨hk1, hk2, x, hx, -, hxc⟩ := h
      obtain ⟨hw, hle, hhk⟩ := I.known m hm
      have hxk : Anc g.s.U.par x (g.s.node m).known.2 := by
        rcases hxc _ hw hle with h | h
        · rwa [hhk] at h
        · rw [hhk] at h
          exact absurd ⟨x, (hx x).2 rfl, h⟩ hna
      have hmax : ∀ y, (g'.s.node m).heads y ↔ y = (g.s.node m).known.2 := by
        intro y
        rw [hheads]
        constructor
        · rintro ⟨hy | hy, hmx⟩
          · have hyx := (hx y).1 hy
            subst hyx
            exact hmx _ (Or.inr rfl) hxk
          · exact hy
        · rintro rfl
          refine ⟨Or.inr rfl, ?_⟩
          rintro z (hz | rfl) hkz
          · rw [(hx z).1 hz] at hkz
            exact absurd ⟨x, (hx x).2 rfl, hkz⟩ hna
          · rfl
      obtain ⟨hhd, hsq', hhi⟩ := hh
      unfold GoodW
      rw [hhd, hsq', hhi, hknown, hU.1]
      refine ⟨hk1, hk2, _, hmax, ?_, ?_⟩
      · rw [← hhk]; exact I.histAnc hw hle
      · intro i hi his
        rw [← hhk]
        by_cases hki : (g.s.node m).known.1 ≤ i
        · exact Or.inl (I.chain _ _ hw hki his)
        · exact Or.inr (I.chain _ _ hi (by omega) hle)
    · exact goodW_same hU.1 hh (hn m hm hmn) h
  | merge n _ h2 hU hh hn _ _ _ _ =>
    by_cases hmn : m = n
    · subst hmn
      obtain ⟨-, -, x, hx, -, -⟩ := h
      obtain ⟨a, b, ha, hb, hab⟩ := h2
      exact absurd (((hx a).1 ha).trans ((hx b).1 hb).symm) hab
    · exact goodW_ext I hU hh hm (hn m hm hmn) h
  | mergeExisting n _ _ h2 _ hU hh hn _ _ _ _ =>
    by_cases hmn : m = n
    · subst hmn
      obtain ⟨-, -, x, hx, -, -⟩ := h
      obtain ⟨a, b, ha, hb, hab⟩ := h2
      exact absurd (((hx a).1 ha).trans ((hx b).1 hb).symm) hab
    · exact goodW_same hU.1 hh (hn m hm hmn) h
  | maintain n _ _ _ _ _ _ hbk' _ =>
    rw [hbk'] at hbk
    have := congrFun hbk n
    rw [upd_same] at this
    omega
  | send _ _ _ _ hU hh hn _ _ => exact goodW_same hU.1 hh (hn m hm) h
  | accept p _ _ _ hanc hU hhead hseq hhist hn _ _ =>
    obtain ⟨hk1, hk2, x, hx, hxh, hxc⟩ := h
    obtain ⟨hhe, hkn⟩ := hn m hm
    unfold GoodW
    rw [hhe, hkn, hU.1, hhead, hseq, hhist,
      upd_ne _ _ (by omega : (g.s.node m).known.1 ≠ g.s.hub.seq + 1)]
    refine ⟨Nat.le_succ_of_le hk1, hk2, x, hx, hxh.trans hanc, ?_⟩
    intro i hi his
    by_cases hie : i = g.s.hub.seq + 1
    · subst hie; rw [upd_same]; exact Or.inl (hxh.trans hanc)
    · rw [upd_ne _ _ hie]; exact hxc i hi (by omega)

/-! ## The measure -/

/-- Packets of `L` that could still move the hub: their new head is above its head. Each is
accepted at most once, since the hub's head only rises. -/
noncomputable def credit (L : List Packet) (s : State) : Nat :=
  cnt L.length (fun j => ∃ q, L[j]? = some q ∧ s.hub.head < q.new)

theorem credit_eq (L : List Packet) {s t : State} (h : t.hub.head = s.hub.head) :
    credit L t = credit L s := by
  unfold credit; rw [h]

theorem credit_le (L : List Packet) {s t : State} (h : s.hub.head ≤ t.hub.head) :
    credit L t ≤ credit L s :=
  cnt_le fun _ _ ⟨q, hq, hl⟩ => ⟨q, hq, Nat.lt_of_le_of_lt h hl⟩

theorem credit_lt (L : List Packet) {s t : State} {p : Packet} (hp : p ∈ L)
    (h : s.hub.head ≤ t.hub.head) (hs : s.hub.head < p.new) (ht : ¬ t.hub.head < p.new) :
    credit L t < credit L s := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
  obtain ⟨hjl, -⟩ := List.getElem?_eq_some_iff.1 hj
  refine cnt_lt (fun _ _ ⟨q, hq, hl⟩ => ⟨q, hq, Nat.lt_of_le_of_lt h hl⟩)
    ⟨j, hjl, ⟨p, hj, hs⟩, ?_⟩
  rintro ⟨q, hq, hl⟩
  rw [hj] at hq
  cases hq
  exact ht hl

theorem mBadW_le {N : Nat} {E : Nat → Prop} {w : Nat} {s t : State}
    (h : ∀ n, E n → GoodW w s n → GoodW w t n) : mBadW N E w t ≤ mBadW N E w s :=
  cnt_le fun n _ ⟨hE, hb⟩ => ⟨hE, fun hg => hb (h n hE hg)⟩

theorem mBadW_lt {N : Nat} {E : Nat → Prop} {w : Nat} {s t : State}
    (h : ∀ n, E n → GoodW w s n → GoodW w t n) {n : Nat} (hE : E n) (hN : n < N)
    (hb : ¬ GoodW w s n) (hg : GoodW w t n) : mBadW N E w t < mBadW N E w s :=
  cnt_lt (fun n _ ⟨hE, hb⟩ => ⟨hE, fun hg => hb (h n hE hg)⟩)
    ⟨n, hN, ⟨hE, hb⟩, fun ⟨_, hb'⟩ => hb' hg⟩

/-- With no maintenance write, no step raises the bad count plus the credit of `L`, and every
accept lowers it, when every listed packet is in `L` or is current and from an eligible node:
a packet of `L` spends its credit, and a current eligible packet's sender was bad and is good
once the hub takes its push. -/
theorem measure_step {N : Nat} {E : Nat → Prop} {w : Nat} {g g' : GState} (I : Inv E w g)
    (hs : Step E w g g') (hbk : g'.bk = g.bk) (hN : ∀ n, E n → n < N) (L : List Packet)
    (hL : ∀ p ∈ g.pk, p ∈ L ∨ (E p.node ∧ p.current g)) :
    mBadW N E w g'.s + credit L g'.s ≤ mBadW N E w g.s + credit L g.s ∧
      (¬ HubSame g.s g'.s →
        mBadW N E w g'.s + credit L g'.s < mBadW N E w g.s + credit L g.s) := by
  have hgood : ∀ n, E n → GoodW w g.s n → GoodW w g'.s n :=
    fun _ hE h => good_step I hs hbk hE h
  have hm := mBadW_le (N := N) hgood
  have still : HubSame g.s g'.s →
      mBadW N E w g'.s + credit L g'.s ≤ mBadW N E w g.s + credit L g.s ∧
        (¬ HubSame g.s g'.s →
          mBadW N E w g'.s + credit L g'.s < mBadW N E w g.s + credit L g.s) := by
    intro hh
    have hc := credit_eq L hh.1
    exact ⟨by omega, fun h => absurd hh h⟩
  cases hs with
  | frame _ hh => exact still hh
  | grow _ hh => exact still hh
  | learn _ _ _ _ _ _ hh => exact still hh
  | advance _ _ _ _ hh => exact still hh
  | merge _ _ _ _ hh => exact still hh
  | mergeExisting _ _ _ _ _ _ hh => exact still hh
  | maintain _ _ _ hh => exact still hh
  | send _ _ _ _ _ hh => exact still hh
  | accept p hp he hne hanc hU hhead hseq hhist hn _ _ =>
    have hup : g.s.hub.head < p.new := Anc.lt_of_ne I.parLt hanc (Ne.symm hne)
    have hle : g.s.hub.head ≤ g'.s.hub.head := by rw [hhead]; exact Nat.le_of_lt hup
    have hc := credit_le L hle
    have strict : mBadW N E w g'.s + credit L g'.s < mBadW N E w g.s + credit L g.s := by
      rcases hL p hp with hpL | ⟨hE, hcur⟩
      · have := credit_lt L hpL hle hup (by rw [hhead]; exact Nat.lt_irrefl _)
        omega
      · have h1 := I.pushInv p hp hE hcur he (by rw [he]; exact hanc)
        have hbad : ¬ GoodW w g.s p.node := by
          rintro ⟨-, -, x, hx, hxh, -⟩
          have hx' : x = p.new := (h1 x).1 ((hx x).2 rfl)
          rw [hx'] at hxh
          exact hne (Anc.antisymm I.parLt hxh hanc)
        have hgd : GoodW w g'.s p.node := by
          obtain ⟨hhe, hkn⟩ := hn p.node hE
          obtain ⟨-, hle, hhk⟩ := I.known p.node hE
          unfold GoodW
          rw [hhe, hkn, hU.1, hhead, hseq, hhist,
            upd_ne _ _ (by omega : (g.s.node p.node).known.1 ≠ g.s.hub.seq + 1)]
          refine ⟨Nat.le_succ_of_le hle, hhk, p.new, h1, Anc.refl, ?_⟩
          intro i hi his
          by_cases hie : i = g.s.hub.seq + 1
          · subst hie; rw [upd_same]; exact Or.inl Anc.refl
          · rw [upd_ne _ _ hie]
            exact Or.inr ((I.histAnc hi (by omega)).trans hanc)
        have := mBadW_lt (N := N) hgood hE (hN _ hE) hbad hgd
        omega
    exact ⟨by omega, fun _ => strict⟩

/-! ## Runs -/

theorem pk_step {E : Nat → Prop} {w : Nat} {g g' : GState} (hs : Step E w g g') :
    g'.pk = g.pk ∨ ∃ n d, E n ∧ g'.pk = sent g n d :: g.pk := by
  cases hs with
  | send n d hE _ _ _ _ _ hpk => exact Or.inr ⟨n, d, hE, hpk⟩
  | frame _ _ _ _ hpk => exact Or.inl hpk
  | grow _ _ _ _ hpk => exact Or.inl hpk
  | learn _ _ _ _ _ _ _ _ _ _ _ hpk => exact Or.inl hpk
  | advance _ _ _ _ _ _ _ _ _ hpk => exact Or.inl hpk
  | merge _ _ _ _ _ _ _ _ _ hpk => exact Or.inl hpk
  | mergeExisting _ _ _ _ _ _ _ _ _ _ _ hpk => exact Or.inl hpk
  | maintain _ _ _ _ _ _ _ _ hpk => exact Or.inl hpk
  | accept _ _ _ _ _ _ _ _ _ _ _ hpk => exact Or.inl hpk

theorem inv_run {E : Nat → Prop} {w : Nat} (run : Nat → GState) (h0 : Inv E w (run 0))
    (hs : ∀ i, Step E w (run i) (run (i + 1))) : ∀ i, Inv E w (run i)
  | 0 => h0
  | i + 1 => inv_step (inv_run run h0 hs i) (hs i)

/-- Once maintenance writes stop, every packet is one listed then, or a current packet from an
eligible node. -/
theorem pk_run {E : Nat → Prop} {w : Nat} (run : Nat → GState)
    (hs : ∀ i, Step E w (run i) (run (i + 1))) (kb : Nat)
    (hkb : ∀ i, kb ≤ i → (run (i + 1)).bk = (run i).bk) :
    ∀ j, ∀ p ∈ (run (kb + j)).pk, p ∈ (run kb).pk ∨ (E p.node ∧ p.current (run (kb + j))) := by
  intro j
  induction j with
  | zero => intro p hp; exact Or.inl hp
  | succ j ih =>
    intro p hp
    have hb : (run (kb + j + 1)).bk = (run (kb + j)).bk := hkb (kb + j) (Nat.le_add_right _ _)
    have cur : ∀ q : Packet, q.current (run (kb + j)) → q.current (run (kb + (j + 1))) := by
      intro q hq
      show q.tag = some ((run (kb + j + 1)).bk q.node)
      rw [hb]; exact hq
    rcases pk_step (hs (kb + j)) with h | ⟨n, d, hE, h⟩
    · have hp' : p ∈ (run (kb + j)).pk := by rw [← h]; exact hp
      rcases ih p hp' with h1 | ⟨hE, hc⟩
      · exact Or.inl h1
      · exact Or.inr ⟨hE, cur p hc⟩
    · have hp' : p ∈ sent (run (kb + j)) n d :: (run (kb + j)).pk := by rw [← h]; exact hp
      rcases List.mem_cons.1 hp' with rfl | hp''
      · refine Or.inr ⟨hE, ?_⟩
        show some ((run (kb + j)).bk n) = some ((run (kb + j + 1)).bk n)
        rw [hb]
      · rcases ih p hp'' with h1 | ⟨hE', hc⟩
        · exact Or.inl h1
        · exact Or.inr ⟨hE', cur p hc⟩

/-! ## The hub settles -/

/-- In the suffix, once maintenance writes stop, the hub's head and sequence stop moving. Accepts
are not assumed finite: each current eligible packet makes its sender good for good, each other
packet was listed when maintenance writes stopped and moves the hub's head at most once. -/
theorem hub_suffix_stabilizes {N : Nat} {E : Nat → Prop} {w : Nat} (run : Nat → GState)
    (h0 : Inv E w (run 0)) (hs : ∀ i, Step E w (run i) (run (i + 1)))
    (hN : ∀ n, E n → n < N) (kb : Nat)
    (hkb : ∀ i, kb ≤ i → (run (i + 1)).bk = (run i).bk) :
    ∃ k, ∀ i, k ≤ i →
      (run i).s.hub.head = (run k).s.hub.head ∧ (run i).s.hub.seq = (run k).s.hub.seq := by
  have hinv := inv_run run h0 hs
  have hpk := pk_run run hs kb hkb
  let f : Nat → Nat := fun j =>
    mBadW N E w (run (kb + j)).s + credit (run kb).pk (run (kb + j)).s
  have hm : ∀ j, f (j + 1) ≤ f j ∧
      (¬ HubSame (run (kb + j)).s (run (kb + j + 1)).s → f (j + 1) < f j) :=
    fun j => measure_step (hinv (kb + j)) (hs (kb + j)) (hkb _ (Nat.le_add_right _ _)) hN _
      (hpk j)
  obtain ⟨k, hk⟩ := nat_trace_stabilizes f (fun j => (hm j).1)
  have same : ∀ j, k ≤ j → HubSame (run (kb + j)).s (run (kb + j + 1)).s := by
    intro j hj
    apply Classical.byContradiction
    intro hne
    have h1 := (hm j).2 hne
    rw [hk j hj, hk (j + 1) (by omega)] at h1
    exact Nat.lt_irrefl _ h1
  refine ⟨kb + k, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih =>
    have h := same (k + d) (Nat.le_add_right _ _)
    rw [show kb + (k + d) = kb + k + d by omega] at h
    obtain ⟨ih1, ih2⟩ := ih (Nat.le_add_right _ _)
    exact ⟨h.1.trans ih1, h.2.1.trans ih2⟩

/-! ## What this rests on

Each `Step` constructor must be matched, on hub-space raw operation ids and with no projection
to originals, by PostCut or by the native code:

- `accept`: after the cuts, an accept moves the hub from `e` to `d` with `Anc e d` and `e ≠ d`
  in the hub store's raw parent graph (PostCut's `post_cut_step` in the model; natively R1, no
  renamed version once records stop, and R2, `descends` is raw ancestry). `pk` holds every
  push that can still move the hub. PacketCoupling's `packet_sender_aligned`, coupled to
  the fixed node-drop sets, identifies the actual sender of each new move-capable packet
  as eligible (`send` needs `E n`). Other nodes may append ledger entries and send packets
  forever; those packets cannot move the hub and need not enter `pk`. Idempotent acceptance
  replies that leave the head and sequence unchanged are quiet steps too.
- `learn`: a node takes only replies the hub sent from the window. A reply newer than what it
  knows is one, by `Inv.known`; an older one must be checked to be.
- `advance`, `merge`, `send`: the policy's guards. Advance only when no head descends from the
  known head; merge only with two heads; push only a single head, naming the known head as
  expected (root's `sourceMatchesB`). That the pushed head descends from the known head is not
  needed: the hub's own guard refuses a push that doesn't.
- `maintain`: an idle maintenance write leaves one fresh head. `kb` says they stop: an
  assumption, since endless maintenance legitimately keeps moving the hub.
- `frame`, `grow`: every other step leaves eligible nodes' heads and knowledge and the hub's
  head, sequence and history alone, and the universe only gains operations whose parents it
  has. Ids need only be a topological order of that growth, not the store's order, which an
  import need not keep parent-first: R3 is that the accepted closure is finite and acyclic.
- A packet's generation tag and `ksq`, and every node's generation `bk`, are ghost state.

Not given here: that misaligned nodes align, since `E` is fixed (a node joining `E` restarts
the argument, at most `N` times, and must enter with truthful knowledge); that knowledge is
truthful when the suffix starts (`inv_entry`); and fairness, which the hub needs not to
settle, only for its settled head to be every node's.
-/

end Musubi.HubSuffix

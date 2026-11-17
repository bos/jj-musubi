/-
A hub that goes back. `protocol.md` requires the hub to keep `head`, `seq` and
`closure(head)`, and the rest of the model assumes it does. musubi's hub syncs nothing to
disk, so a power cut can lose the heads it accepted last, and a hub that finds a hive's store
corrupt makes the hive again, empty. This file adds that failure, the hub going back to a
head it accepted (`State.regress`; the oracle's action `hubRegress`), to the asynchronous
model, as a separate system (`RStep`, `RReachable`), so that the theorems of `Safety.lean`
and `Liveness.lean`, which do not hold once the hub can go back, keep their statements.

What still holds in every state of the extended system (`InvR`): the universe is a DAG, the
hub's history is a chain ending in its head, the hub holds `closure(head)`, and every node's
repository is closed with an antichain of heads. Locality, MergeOwnership, HubMonotone and
KnownIsHubHistory do not hold: a node can hold operations of other nodes that the hub no
longer has, and know a head the hub has forgotten, and two nodes can then merge the same
heads (`duplicateMerge`).

Liveness: a node that gets a reply to its own request carrying a head older than the one it
knows, or another head at the same sequence number, restarts and takes the reply. With that
rule (`PStepR`), once the hub stops going back every policy run ends with every node at the
hub's head, and every operation any node made in it.
-/
import Musubi.Liveness
import Musubi.Contract

namespace Musubi

variable {N : Nat}

/-! ## The hub goes back -/

namespace State

/-- The hub goes back to the head it accepted at sequence number `i`. History above `i` is
left as it was, to be overwritten by later accepts. -/
def regress (s : State) (i : Nat) : State :=
  { s with hub := { s.hub with head := s.hub.hist i, seq := i } }

/-- A hive made again, empty: the hub at the root, with nothing stored but the root. -/
def remake (s : State) : State :=
  { s with hub := { s.hub with head := root, seq := 0, ops := (· = root),
                               objs := fun _ => False } }

end State

/-- One step of the asynchronous system, or the hub going back to a head it accepted. -/
def RStep (N : Nat) (s s' : State) : Prop :=
  Step N s s' ∨ ∃ i, i ≤ s.hub.seq ∧ s' = s.regress i

inductive RReachable (N : Nat) : State → Prop
  | init : RReachable N init
  | step {s s' : State} : RReachable N s → RStep N s s' → RReachable N s'

theorem Reachable.rreachable {s : State} (h : Reachable N s) : RReachable N s := by
  induction h with
  | init => exact RReachable.init
  | step _ hs ih => exact ih.step (Or.inl hs)

theorem RReachable.sync {s s' : State} (h : RReachable N s) (hs : SyncStep N s s') :
    RReachable N s' := h.step (Or.inl (Or.inr hs))

theorem RReachable.env {s s' : State} (h : RReachable N s) (hs : EnvStep N s s') :
    RReachable N s' := h.step (Or.inl (Or.inl hs))

/-! ## The invariant that survives -/

/-- What every in-flight message guarantees once the hub can go back: the operations it
names exist. -/
def MsgR (s : State) : Msg → Prop
  | .ops _ S => ∀ x, S x → x < s.U.next
  | .putOps _ S => ∀ x, S x → x < s.U.next
  | .cas _ _ d => d < s.U.next
  | .push _ S _ _ d => (∀ x, S x → x < s.U.next) ∧ d < s.U.next
  | .head _ _ _ h => h < s.U.next
  | _ => True

/-- What every state satisfies once the hub can go back, a push can contract its expected
head, and records a node takes can drop its own work (`Supersede.lean`): `Base`, with the
stored, known, staged and in-flight operations bounded by the universe. -/
structure InvC (N : Nat) (s : State) : Prop extends Base N s where
  objsRoot : s.U.objs root = []
  hubOpsLt : ∀ x, s.hub.ops x → x < s.U.next
  knownLt : ∀ n, (s.node n).known.head < s.U.next
  stagedLt : ∀ n x, (s.node n).sops x → x < s.U.next
  msgs : ∀ m, s.net m → MsgR s m

/-- The invariant of the extended system: `Core` and `InvC`, without what relates nodes to the
hub's history. -/
structure InvR (N : Nat) (s : State) : Prop extends Core N s, InvC N s

theorem MsgR.grow {s s' : State} (hn : s.U.next ≤ s'.U.next) {m : Msg} (h : MsgR s m) :
    MsgR s' m := by
  cases m with
  | ops _ S => exact fun x hx => Nat.lt_of_lt_of_le (h x hx) hn
  | putOps _ S => exact fun x hx => Nat.lt_of_lt_of_le (h x hx) hn
  | cas _ _ d => exact Nat.lt_of_lt_of_le h hn
  | push _ S _ _ d => exact ⟨fun x hx => Nat.lt_of_lt_of_le (h.1 x hx) hn,
      Nat.lt_of_lt_of_le h.2 hn⟩
  | head _ _ _ h' => exact Nat.lt_of_lt_of_le h hn
  | getHead => trivial
  | putObjs => trivial
  | getOps => trivial
  | getObjs => trivial
  | objs => trivial
  | stored => trivial
  | fetch => trivial

theorem invR_init (N : Nat) : InvR N init := by
  refine
    { toCore := core_init N, objsRoot := ?_, hubOpsLt := ?_, knownLt := ?_, stagedLt := ?_,
      msgs := ?_ }
  all_goals simp [init, initNode]

/-! ## Preservation

Every step keeps `InvC` (`invC_step`), the hub going back included when the head it goes back to
is still closed (`invC_regress`). `InvR` adds the history chain, which only an accept extends,
and `ownInHeads`, which a step keeps since each node's heads keep what they reached
(`step_heads_cover`). -/

theorem InvC.send {s : State} {m : Msg} (hI : InvC N s) (hm : MsgR s m) :
    InvC N (s.send m) :=
  { hI with
    msgs := by
      intro m' hm'
      rcases hm' with h | h
      · exact hI.msgs m' h
      · subst h; exact hm }

/-- The per-node part of `InvC`, for a candidate new state `nd` of node `n`. -/
structure NodeInv (s : State) (n : Nat) (nd : Node) : Prop extends BaseNode s n nd where
  knownLt : nd.known.head < s.U.next
  stagedLt : ∀ x, nd.sops x → x < s.U.next

theorem InvC.nodeInv {s : State} (hI : InvC N s) (n : Nat) : NodeInv s n (s.node n) where
  toBaseNode := hI.baseNode n
  knownLt := hI.knownLt n
  stagedLt := hI.stagedLt n

theorem invC_setNode {s : State} {n : Nat} {nd : Node} (hI : InvC N s) (h : NodeInv s n nd) :
    InvC N (s.setNode n nd) :=
  { hI with
    toBase := hI.toBase.setNode h.toBaseNode
    knownLt := forall_setNode (P := fun _ nd => nd.known.head < s.U.next) hI.knownLt h.knownLt
    stagedLt := forall_setNode (P := fun _ nd => ∀ x, nd.sops x → x < s.U.next)
      hI.stagedLt h.stagedLt }

/-- The general preservation lemma for creating an operation on node `n`. -/
theorem invC_createOp {s : State} {n : Nat} {L O : List Nat} {mg : Bool} {H' : OSet}
    (hI : InvC N s) (hn : n < N)
    (hL : ∀ p ∈ L, (s.node n).lops p) (hLne : L ≠ [])
    (hHo : H' s.U.next)
    (hHsub : ∀ y, H' y → (s.node n).heads y ∨ y = s.U.next)
    (hHanti : ∀ x y, H' x → H' y → Anc (upd s.U.par s.U.next L) x y → x = y) :
    InvC N (s.createOp n L O mg H') := by
  have hne0 : s.U.next ≠ root := Nat.ne_of_gt hI.nextPos
  refine
    { toBase := Base.createOp hI.toBase hn hL hLne hHo hHsub hHanti, objsRoot := ?_,
      hubOpsLt := ?_, knownLt := ?_, stagedLt := ?_, msgs := ?_ }
  · simp only [createOp_U, create_objs]
    rw [upd_ne _ _ (Ne.symm hne0)]; exact hI.objsRoot
  · intro x hx
    have := hI.hubOpsLt x hx
    simp; omega
  · intro i
    simp only [createOp_U, create_next]
    by_cases hi : i = n
    · subst hi; simp only [createOp_known]; have := hI.knownLt i; omega
    · rw [createOp_node_ne hi]; have := hI.knownLt i; omega
  · intro i x hx
    simp only [createOp_U, create_next]
    by_cases hi : i = n
    · subst hi; simp only [createOp_sops] at hx; have := hI.stagedLt i x hx; omega
    · rw [createOp_node_ne hi] at hx; have := hI.stagedLt i x hx; omega
  · intro m hm
    exact (hI.msgs m hm).grow (by simp)

theorem invC_userOp {s : State} (hI : InvC N s) {n p : Nat} {O : List Nat} (hn : n < N)
    (hp : (s.node n).lops p) : InvC N (s.userOp n p O) := by
  have H := fun y => userOp_heads_iff_of (y := y) hI.parLt (hI.lLt n p hp)
    (fun _ h => hI.headsLt h) (hI.headsAnti n)
  apply invC_createOp hI hn
  · intro q hq; simp at hq; subst hq; exact hp
  · simp
  · exact (H _).2 (Or.inl rfl)
  · intro y hy
    rcases (H y).1 hy with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  · intro x y hx hy hA
    exact hx.2 y hy.1 hA

theorem invC_merge {s : State} (hI : InvC N s) {n : Nat} {L O : List Nat} (hn : n < N)
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    InvC N (s.mergeOp n L O) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  apply invC_createOp hI hn
  · intro q hq; exact hI.headsLocal n q ((hL q).1 hq)
  · intro h; rw [h] at ha; simp at ha
  · rfl
  · intro y hy; exact Or.inr hy
  · intro x y hx hy _; rw [hx, hy]

theorem invC_realize {s : State} (hI : InvC N s) {n x : Nat} (hx : (s.node n).sops x)
    (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) :
    InvC N (s.realize n x) := by
  refine invC_setNode hI
    { hI.nodeInv n with
      lroot := Or.inl (hI.lroot n), lLt := ?_, lParents := ?_, lObjs := ?_,
      headsLocal := fun y hy => Or.inl (hI.headsLocal n y hy) }
  · rintro y (hy | rfl)
    · exact hI.lLt n y hy
    · exact hI.stagedLt n y hx
  · rintro y q (hy | rfl) hq
    · exact Or.inl (hI.lParents n y q hy hq)
    · exact Or.inl (hp q hq)
  · rintro y o (hy | rfl) ho
    · exact Or.inl (hI.lObjs n y o hy ho)
    · exact Or.inr ho

theorem invC_advance {s : State} (hI : InvC N s) {n : Nat}
    (hk : (s.node n).lops (s.node n).known.head)
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.head h) :
    InvC N (s.advance n) := by
  have H := fun y => advance_heads_iff_of (y := y) (hI.headsAnti n) hna
  refine invC_setNode hI
    { hI.nodeInv n with headsLocal := ?_, headsAnti := ?_, headsNonempty := ?_ }
  · intro y hy
    rcases (H y).1 hy with rfl | ⟨hy, -⟩
    · exact hk
    · exact hI.headsLocal n y hy
  · intro x y hx hy hA
    exact hx.2 y hy.1 hA
  · exact ⟨_, (H _).2 (Or.inl rfl)⟩

theorem invC_hubStore {s : State} (hI : InvC N s) {S O : OSet}
    (hS : ∀ x, S x → x < s.U.next) : InvC N (s.hubStore S O) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨Or.inl h1, fun o ho => Or.inl (h2 o ho)⟩
    hubOpsLt := by
      rintro x (hx | hx)
      · exact hI.hubOpsLt x hx
      · exact hS x hx }

theorem invC_hubStoreOps {s : State} (hI : InvC N s) {S : OSet}
    (hS : ∀ x, S x → x < s.U.next) : InvC N (s.hubStoreOps S) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨Or.inl h1, h2⟩
    hubOpsLt := by
      rintro x (hx | hx)
      · exact hI.hubOpsLt x hx
      · exact hS x hx }

theorem invC_hubStoreObjs {s : State} (hI : InvC N s) {S : OSet} :
    InvC N (s.hubStoreObjs S) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨h1, fun o ho => Or.inl (h2 o ho)⟩ }

/-- The hub accepts a closed head `d`, replying to `n0` and notifying every node, whether or not
`d` descends from the head it had. -/
theorem invC_accept {s : State} (hI : InvC N s) {n0 d : Nat} (hd : d < s.U.next)
    (hc : ClosedAt s d) :
    InvC N (((s.hubAccept d).send (.head n0 .accepted (s.hub.seq + 1) d)).notifyAll
      (s.hub.seq + 1) d) := by
  refine { hI with headLt := hd, histHead := ?_, hist0 := ?_, hubClosed := hc, msgs := ?_ }
  · show upd s.hub.hist (s.hub.seq + 1) d (s.hub.seq + 1) = d
    simp
  · show upd s.hub.hist (s.hub.seq + 1) d 0 = root
    rw [upd_ne _ _ (by omega)]; exact hI.hist0
  · rintro m ((hm | rfl) | ⟨i, rfl⟩)
    · exact hI.msgs m hm
    · exact hd
    · exact hd

/-- The hub goes back to the head it accepted at `i`, which it still holds the closure of. -/
theorem invC_regress {s : State} (hI : InvC N s) {i : Nat} (hc : ClosedAt s (s.hub.hist i)) :
    InvC N (s.regress i) :=
  { hI with
    headLt := hI.hubOpsLt _ (hc _ Anc.refl).1
    histHead := rfl
    hubClosed := hc }

theorem invC_syncStep {s s' : State} (hI : InvC N s) (h : SyncStep N s s') : InvC N s' := by
  cases h with
  | getHead n hn => exact hI.send trivial
  | learn n k sq h hn hm hs =>
    exact invC_setNode hI { hI.nodeInv n with knownLt := hI.msgs _ hm }
  | learnUnfiltered n k sq h hn hm =>
    exact invC_setNode hI { hI.nodeInv n with knownLt := hI.msgs _ hm }
  | fetchOps n S hn hS => exact hI.send trivial
  | fetchObjs n S hn => exact hI.send trivial
  | recvOps n S hn hm =>
    refine invC_setNode hI { hI.nodeInv n with stagedLt := ?_ }
    rintro x (hx | hx)
    · exact hI.stagedLt n x hx
    · exact (hI.msgs _ hm : MsgR s (.ops n S)) x hx
  | recvObjs n S hn hm => exact invC_setNode hI { hI.nodeInv n with }
  | realize n x hn hx hp ho => exact invC_realize hI hx hp
  | advance n hn hk hna => exact invC_advance hI hk hna
  | uploadOps n S hn hS => exact hI.send (fun x hx => hI.lLt n x (hS x hx))
  | uploadObjs n S hn hS => exact hI.send trivial
  | push n e d hn hd => exact hI.send (hI.lLt n d hd)
  | pushAll n S O e d hn hS hO hd =>
    exact hI.send ⟨fun x hx => hI.lLt n x (hS x hx), hI.lLt n d hd⟩
  | fetchAll n b H hn => exact hI.send trivial
  | crashNode n hn => exact hI
  | loseKnown n hn => exact invC_setNode hI { hI.nodeInv n with knownLt := hI.nextPos }
  | loseVolatile n hn =>
    refine invC_setNode hI { hI.nodeInv n with knownLt := hI.nextPos, stagedLt := ?_ }
    intro x hx; exact hx.elim
  | hubGetHead n hm => exact hI.send hI.headLt
  | hubPutOps n S hm =>
    exact (invC_hubStoreOps hI (hI.msgs _ hm : MsgR s (.putOps n S))).send trivial
  | hubPutObjs n S hm => exact (invC_hubStoreObjs hI).send trivial
  | hubGetOps n S hm => exact hI.send (fun x hx => hI.hubOpsLt x hx.2)
  | hubGetObjs n S hm => exact hI.send trivial
  | casIdem n e d hm hh => exact hI.send hI.headLt
  | casAccept n e d hm hne he ha hc =>
    exact invC_accept hI (hI.msgs _ hm : MsgR s (.cas n e d)) hc
  | casReject n e d hm hne hrej => exact hI.send hI.headLt
  | hubPushIdem n S O e d hm hh =>
    have hI' := invC_hubStore (O := O) hI (hI.msgs _ hm : MsgR s (.push n S O e d)).1
    exact hI'.send hI'.headLt
  | hubPushAccept n S O e d hm hne he ha hc =>
    have hmsg : MsgR s (.push n S O e d) := hI.msgs _ hm
    exact invC_accept (invC_hubStore (O := O) hI hmsg.1) hmsg.2 hc
  | hubPushReject n S O e d hm hne hrej =>
    have hI' := invC_hubStore (O := O) hI (hI.msgs _ hm : MsgR s (.push n S O e d)).1
    exact hI'.send hI'.headLt
  | hubPushIncomplete n S O e d hm hne he hc =>
    have hI' := invC_hubStore (O := O) hI (hI.msgs _ hm : MsgR s (.push n S O e d)).1
    exact hI'.send hI'.headLt
  | hubFetch n b H hm =>
    have h1 := hI.send (m := .head n .head s.hub.seq s.hub.head) hI.headLt
    have h2 := h1.send (m := .ops n (s.sinceOps b)) (fun x hx => hI.hubOpsLt x hx.2.2)
    exact h2.send trivial
  | crashHub => exact hI
  | hubForget O J hO hJ hc =>
    exact { hI with hubClosed := hc, hubOpsLt := fun x hx => hI.hubOpsLt x (hO x hx) }

theorem invC_envStep {s s' : State} (hI : InvC N s) (h : EnvStep N s s') : InvC N s' := by
  cases h with
  | userOp n p O hn hp => exact invC_userOp hI hn hp
  | merge n L O hn hL h2 => exact invC_merge hI hn hL h2

theorem invC_step {s s' : State} (hI : InvC N s) (h : Step N s s') : InvC N s' :=
  h.elim (invC_envStep hI) (invC_syncStep hI)

/-- A step of the protocol keeps the hub's sequence number, or adds one; history up to the old
number stays. -/
theorem step_hub {s t : State} (hs : Step N s t) :
    (t.hub.seq = s.hub.seq ∧ t.hub.head = s.hub.head ∧ t.hub.hist = s.hub.hist) ∨
      (t.hub.seq = s.hub.seq + 1 ∧ (∀ i, i ≤ s.hub.seq → t.hub.hist i = s.hub.hist i) ∧
        t.hub.hist (s.hub.seq + 1) = t.hub.head ∧ t.U = s.U ∧ t.node = s.node ∧
        Anc s.U.par s.hub.head t.hub.head ∧ s.hub.head ≠ t.hub.head) := by
  rcases hs with hs | hs
  · cases hs <;> exact Or.inl ⟨rfl, rfl, rfl⟩
  · cases hs with
    | casAccept n e d hm hne he ha =>
      exact Or.inr ⟨rfl, fun i hi => upd_ne _ _ (by omega), upd_same _ _ _, rfl, rfl, he ▸ ha, hne⟩
    | hubPushAccept n S O e d hm hne he ha =>
      exact Or.inr ⟨rfl, fun i hi => upd_ne _ _ (show i ≠ s.hub.seq + 1 by omega),
        upd_same _ _ _, rfl, rfl, he ▸ ha, hne⟩
    | _ => exact Or.inl ⟨rfl, rfl, rfl⟩

/-- A step of the protocol keeps the operations created so far as they were. -/
theorem step_par {s t : State} (hs : Step N s t) :
    s.U.next ≤ t.U.next ∧ ∀ y, y < s.U.next → t.U.par y = s.U.par y := by
  rcases hs with hs | hs
  · cases hs with
    | userOp n p O => exact ⟨Nat.le_succ _, fun y hy => upd_ne _ _ (Nat.ne_of_lt hy)⟩
    | merge n L O => exact ⟨Nat.le_succ _, fun y hy => upd_ne _ _ (Nat.ne_of_lt hy)⟩
  · have := noFeedback hs
    rw [this]; exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

-- Each sync step's node update unfolds through a different few of these definitions.
set_option linter.unusedSimpArgs false in
/-- What a node's heads reach only grows: every protocol step keeps each operation below some
head of each node. -/
theorem step_heads_cover {s t : State} (hI : InvC N s) (hs : Step N s t) {m x : Nat}
    (hx : ∃ h, (s.node m).heads h ∧ Anc s.U.par x h) :
    ∃ h, (t.node m).heads h ∧ Anc t.U.par x h := by
  obtain ⟨h, hh, hA⟩ := hx
  rcases hs with hs | hs
  · cases hs with
    | userOp n p O hn hp =>
      have hLlt : ∀ q ∈ [p], q < s.U.next := by
        intro q hq; simp at hq; rw [hq]; exact hI.lLt n p hp
      have hlt' := parLt_upd hI.parLt hLlt
      have hA' : Anc (upd s.U.par s.U.next [p]) x h :=
        (anc_upd_iff hI.parLt hLlt (hI.headsLt hh)).2 hA
      by_cases hmn : m = n
      · subst hmn
        let S' : OSet := fun y => ((s.node m).heads y ∧ y ≠ p) ∨ y = s.U.next
        have hB : ∀ y, S' y → y < s.U.next + 1 := by
          rintro y (⟨hy, -⟩ | rfl)
          · exact Nat.lt_succ_of_lt (hI.headsLt hy)
          · exact Nat.lt_succ_self _
        by_cases hhp : h = p
        · subst hhp
          obtain ⟨y, hy, hAy⟩ := maxSet_covers hlt' hB (x := s.U.next) (Or.inr rfl)
          refine ⟨y, by simpa [State.userOp, State.createOp] using hy, ?_⟩
          exact hA'.trans ((Anc.parent (by simp)).trans hAy)
        · obtain ⟨y, hy, hAy⟩ := maxSet_covers hlt' hB (x := h) (Or.inl ⟨hh, hhp⟩)
          exact ⟨y, by simpa [State.userOp, State.createOp] using hy, hA'.trans hAy⟩
      · refine ⟨h, ?_, hA'⟩
        simpa [State.userOp, State.createOp, hmn] using hh
    | merge n L O hn hL h2 =>
      have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
      have hA' : Anc (upd s.U.par s.U.next L) x h :=
        (anc_upd_iff hI.parLt hLlt (hI.headsLt hh)).2 hA
      by_cases hmn : m = n
      · subst hmn
        refine ⟨s.U.next, by simp [State.mergeOp, State.createOp], ?_⟩
        exact hA'.trans (Anc.parent (by simp; exact (hL h).2 hh))
      · exact ⟨h, by simpa [State.mergeOp, State.createOp, hmn] using hh, hA'⟩
  · have hU := noFeedback hs
    cases hs with
    | advance n hn hk hna =>
      by_cases hmn : m = n
      · subst hmn
        have hB : ∀ y, ((s.node m).heads y ∨ y = (s.node m).known.head) → y < s.U.next := by
          rintro y (hy | rfl)
          · exact hI.headsLt hy
          · exact hI.knownLt m
        obtain ⟨y, hy, hAy⟩ := maxSet_covers hI.parLt hB (Or.inl hh)
        exact ⟨y, by simpa [State.advance, State.setNode] using hy, hA.trans hAy⟩
      · exact ⟨h, by simpa [State.advance, State.setNode, upd, hmn] using hh, hA⟩
    | _ =>
      refine ⟨h, ?_, hA⟩
      first
        | exact hh
        | (simp only [State.learn, State.recvOps, State.recvObjs, State.realize,
            State.setNode, State.send, State.hubStoreOps, State.hubStoreObjs, State.hubStore,
            State.hubAccept, State.notifyAll]
           unfold upd; split <;> (try subst_vars) <;> exact hh)

/-- A step keeps the hub's history a chain: only an accept extends it, to a head that descends
from the one before. -/
theorem histStep_step {s t : State} (hI : InvR N s) (hs : Step N s t) :
    ∀ i, i < t.hub.seq →
      Anc t.U.par (t.hub.hist i) (t.hub.hist (i + 1)) ∧ t.hub.hist i ≠ t.hub.hist (i + 1) := by
  obtain ⟨-, hpar⟩ := step_par hs
  have keep : ∀ {a x}, x < s.U.next → Anc s.U.par a x → Anc t.U.par a x := fun hx ha =>
    (Contract.anc_congr hI.parLt (fun y hy => (hpar y (Nat.lt_of_le_of_lt hy hx)).symm)).1 ha
  rcases step_hub hs with ⟨hq, -, hh⟩ | ⟨hq, hold, hnew, hU, -, ha, hne⟩
  · intro i hi
    rw [hh]; rw [hq] at hi
    obtain ⟨h1, h2⟩ := hI.histStep i hi
    exact ⟨keep (hI.histLt (by omega)) h1, h2⟩
  · intro i hi
    rw [hU]
    by_cases his : i = s.hub.seq
    · subst his
      rw [hold _ (Nat.le_refl _), hnew, hI.histHead]
      exact ⟨ha, hne⟩
    · rw [hold i (by omega), hold (i + 1) (by omega)]
      exact hI.histStep i (by omega)

/-- A step keeps an operation a node made below one of its heads, if it was before: a new
operation is a head of the node that made it, and a node's heads keep what they reached. -/
theorem own_step {s t : State} (hI : InvC N s) (hs : Step N s t) {n x : Nat}
    (hx : x < t.U.next) (hc : t.U.creator x = some n)
    (hown : x < s.U.next → s.U.creator x = some n → ∃ h, (s.node n).heads h ∧ Anc s.U.par x h) :
    ∃ h, (t.node n).heads h ∧ Anc t.U.par x h := by
  have old : x < s.U.next → s.U.creator x = some n → ∃ h, (t.node n).heads h ∧ Anc t.U.par x h :=
    fun hx hc => step_heads_cover hI hs (hown hx hc)
  rcases hs with hs | hs
  · cases hs with
    | userOp m p O hm hp =>
      simp only [State.userOp, createOp_U, create_next, create_creator] at hx hc
      by_cases hxo : x = s.U.next
      · subst hxo
        rw [upd_same] at hc
        cases hc
        have H := fun y => userOp_heads_iff_of (y := y) hI.parLt (hI.lLt n p hp)
          (fun _ h => hI.headsLt h) (hI.headsAnti n)
        exact ⟨s.U.next, by simpa [State.userOp] using (H _).2 (Or.inl rfl), Anc.refl⟩
      · rw [upd_ne _ _ hxo] at hc
        exact old (by omega) hc
    | merge m L O hm hL h2 =>
      simp only [State.mergeOp, createOp_U, create_next, create_creator] at hx hc
      by_cases hxo : x = s.U.next
      · subst hxo
        rw [upd_same] at hc
        cases hc
        exact ⟨s.U.next, by simp [State.mergeOp], Anc.refl⟩
      · rw [upd_ne _ _ hxo] at hc
        exact old (by omega) hc
  · have hU := noFeedback hs
    rw [hU] at hx hc
    exact old hx hc

/-- A step keeps every operation a node made below one of its heads. -/
theorem ownInHeads_step {s t : State} (hI : InvR N s) (hs : Step N s t) :
    ∀ n x, x < t.U.next → t.U.creator x = some n →
      ∃ h, (t.node n).heads h ∧ Anc t.U.par x h :=
  fun _ _ hx hc => own_step hI.toInvC hs hx hc (hI.ownInHeads _ _)

theorem invR_step {s s' : State} (hI : InvR N s) (h : Step N s s') : InvR N s' :=
  { invC_step hI.toInvC h with
    histStep := histStep_step hI h
    ownInHeads := ownInHeads_step hI h }

theorem invR_regress {s : State} (hI : InvR N s) {i : Nat} (hi : i ≤ s.hub.seq) :
    InvR N (s.regress i) :=
  { invC_regress hI.toInvC (fun y hy => hI.hubClosed y (hy.trans (hI.histAnc hi))) with
    histStep := fun j hj => hI.histStep j (Nat.lt_of_lt_of_le hj hi)
    ownInHeads := hI.ownInHeads }

theorem invR_rstep {s s' : State} (hI : InvR N s) (h : RStep N s s') : InvR N s' := by
  rcases h with h | ⟨i, hi, rfl⟩
  · exact invR_step hI h
  · exact invR_regress hI hi

theorem invR_reachable {s : State} (h : RReachable N s) : InvR N s := by
  induction h with
  | init => exact invR_init N
  | step _ hst ih => exact invR_rstep ih hst

/-! ## Safety that survives -/

/-- **HubClosed**, with a hub that goes back: `closure(head) ⊆ ops ∪ objects`. -/
theorem hubClosedR {s : State} (h : RReachable N s) :
    ∀ y, Anc s.U.par y s.hub.head → s.hub.ops y ∧ ∀ o ∈ s.U.objs y, s.hub.objs o :=
  (invR_reachable h).hubClosed

/-- The hub's history is still a chain of strictly increasing heads from the root to its
head, though going back drops its newest entries. -/
theorem hubHistoryR {s : State} (h : RReachable N s) :
    s.hub.hist 0 = root ∧ s.hub.hist s.hub.seq = s.hub.head ∧
    ∀ i, i < s.hub.seq →
      Anc s.U.par (s.hub.hist i) (s.hub.hist (i + 1)) ∧ s.hub.hist i ≠ s.hub.hist (i + 1) :=
  have hI := invR_reachable h
  ⟨hI.hist0, hI.histHead, hI.histStep⟩

/-- **NodeClosed**, with a hub that goes back: every node's repository stays whole. -/
theorem nodeClosedR {s : State} (h : RReachable N s) (n : Nat) :
    (∀ x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p) ∧
    (∀ x o, (s.node n).lops x → o ∈ s.U.objs x → (s.node n).lobj o) ∧
    (∀ x, (s.node n).heads x → (s.node n).lops x) ∧
    (∀ x y, (s.node n).heads x → (s.node n).heads y → Anc s.U.par x y → x = y) ∧
    (∃ x, (s.node n).heads x) :=
  have hI := invR_reachable h
  ⟨hI.lParents n, hI.lObjs n, hI.headsLocal n, hI.headsAnti n, hI.headsNonempty n⟩

/-- **No feedback**, with a hub that goes back: neither sync actions nor the hub going back
create operations. -/
theorem noFeedbackR {s s' : State} (hs : SyncStep N s s' ∨ ∃ i, s' = s.regress i) :
    s'.U = s.U := by
  rcases hs with hs | ⟨i, rfl⟩
  · exact noFeedback hs
  · rfl

/-- Making a hive again, empty, is a run of the extended system: the hub goes back to the
root, then forgets everything else. -/
theorem remake_reachable {s : State} (h : RReachable N s) : RReachable N s.remake := by
  have hI := invR_reachable h
  have r1 : RReachable N (s.regress 0) := h.step (Or.inr ⟨0, Nat.zero_le _, rfl⟩)
  have hroot : ∀ y, Anc s.U.par y root → y = root := fun y hy =>
    Nat.le_zero.1 (hy.le hI.parLt)
  have r2 := r1.sync (SyncStep.hubForget (s.regress 0) (· = root) (fun _ => False)
    (fun x hx => by
      subst hx
      exact (hI.hubClosed root (hI.rootAnc _ hI.headLt)).1)
    (fun _ ho => ho.elim)
    (fun y hy => by
      have hy' : Anc s.U.par y root := by
        have : (s.regress 0).hub.head = root := hI.hist0
        rw [this] at hy; exact hy
      have := hroot y hy'
      subst this
      refine ⟨rfl, fun o ho => ?_⟩
      have ho' : o ∈ s.U.objs root := ho
      rw [hI.objsRoot] at ho'
      cases ho'))
  have e : ({ s.regress 0 with
      hub := { (s.regress 0).hub with ops := (· = root), objs := fun _ => False } } : State) =
      s.remake := by
    unfold State.remake State.regress
    rw [hI.hist0]
  rw [← e]; exact r2

/-! ## Liveness after the hub stops going back -/

/-- Node `n` has one head, accepted, and comparable with every head in the hub's history. -/
def Settled (s : State) (n : Nat) : Prop :=
  ∃ x, (∀ y, (s.node n).heads y ↔ y = x) ∧ Anc s.U.par x s.hub.head ∧
    ∀ i, i ≤ s.hub.seq → Anc s.U.par x (s.hub.hist i) ∨ Anc s.U.par (s.hub.hist i) x

/-- A node that no policy step can make push again. After the hub goes back a node can hold
two accepted heads that are not comparable, and merging them makes it dirty; a good node
has neither. -/
def Good (s : State) (n : Nat) : Prop := Consistent s n ∧ Settled s n

theorem InvR.consistentAnc {s : State} (hI : InvR N s) {n : Nat} (hc : Consistent s n) :
    Anc s.U.par (s.node n).known.head s.hub.head := by
  rw [← hc.2]; exact hI.histAnc hc.1

/-- The policy, with a hub that may have gone back. It is `PStep` but for two steps. A node
takes the head in a reply to its own request whenever it differs from the one it knows,
older or not (`NodeCore::handle_reply` restarts the node, as `loseKnown` does, and then
learns it). And it realizes only below a head in the hub's current history: the core clears
its realization plan whenever `handle` changes `known`, and every sync starts with a `Fetch`
whose reply sets `known`. -/
inductive PStepR (N : Nat) : State → State → Prop
  | learn (s : State) (n : Nat) (hn : n < N) (hs : (s.node n).known ≠ ⟨s.hub.seq, s.hub.head⟩) :
      PStepR N s (s.pLearn n)
  | realize (s : State) (n x : Nat) (hn : n < N) (hc : Consistent s n)
      (hx : Anc s.U.par x (s.node n).known.head)
      (hnl : ¬ (s.node n).lops x) (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) :
      PStepR N s (s.pRealize n x)
  | advance (s : State) (n : Nat) (hn : n < N) (hk : (s.node n).lops (s.node n).known.head)
      (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.head h) :
      PStepR N s (s.advance n)
  | merge (s : State) (n : Nat) (L O : List Nat) (hn : n < N)
      (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
      PStepR N s (s.mergeOp n L O)
  | pushAccept (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.head) (hk : Anc s.U.par (s.node n).known.head h)
      (hacc : s.hub.head = (s.node n).known.head) : PStepR N s (s.pPushAccept n h)
  | pushIdem (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.head) (hk : Anc s.U.par (s.node n).known.head h)
      (hidem : s.hub.head = h) : PStepR N s (s.pPushIdem n h)
  | pushReject (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.head) (hk : Anc s.U.par (s.node n).known.head h)
      (hrej : s.hub.head ≠ (s.node n).known.head) (hrej' : s.hub.head ≠ h) :
      PStepR N s (s.pPushReject n h)

/-- Runs of policy steps. -/
abbrev PStepsR (N : Nat) : State → State → Prop := Steps (PStepR N)

/-! ### Policy steps are runs of the extended system -/

theorem pUpload_rreachable {s : State} (h : RReachable N s) {n hd : Nat} (hn : n < N)
    (hh : (s.node n).heads hd) : RReachable N (s.pUpload n hd) := by
  have hI := invR_reachable h
  exact pUpload_run (fun h st => h.sync st) h hn (hI.lParents n) (hI.lObjs n)
    (hI.headsLocal n hd hh)

/-- Every policy step is a run of the extended system. A node learns the hub's head with
`learnUnfiltered`, which has the effect of `loseKnown` and then `learn`. -/
theorem pstepR_reachable {s s' : State} (h : RReachable N s) (hp : PStepR N s s') :
    RReachable N s' := by
  have hI := invR_reachable h
  cases hp with
  | learn n hn hs =>
    have r1 := h.sync (SyncStep.getHead s n hn)
    have r2 := r1.sync (SyncStep.hubGetHead _ n (Or.inr rfl))
    exact r2.sync (SyncStep.learnUnfiltered _ n .head s.hub.seq s.hub.head hn (Or.inr rfl))
  | realize n x hn hc hx hnl hp =>
    exact pRealize_run (fun h st => h.sync st) h hn hx
      (hI.hubClosed x (hx.trans (hI.consistentAnc hc))) hp
  | advance n hn hk hna => exact h.sync (SyncStep.advance s n hn hk hna)
  | merge n L O hn hL h2 => exact h.env (EnvStep.merge s n L O hn hL h2)
  | pushAccept n hd hn hh hne hk hacc =>
    have r := pUpload_rreachable h hn ((hh hd).2 rfl)
    have r' := r.sync (SyncStep.casAccept _ n (s.node n).known.head hd (Or.inr rfl)
      (fun e => hne ((show s.hub.head = hd from e).symm.trans hacc)) hacc hk
      (pUpload_closed_of hI.hubClosed (by rw [hacc]; exact Anc.refl)))
    exact r'.sync (SyncStep.learnUnfiltered _ n .accepted (s.hub.seq + 1) hd hn
      (Or.inl (Or.inr rfl)))
  | pushIdem n hd hn hh hne hk hidem =>
    have r := pUpload_rreachable h hn ((hh hd).2 rfl)
    have r' := r.sync (SyncStep.casIdem _ n (s.node n).known.head hd (Or.inr rfl) hidem)
    exact r'.sync (SyncStep.learnUnfiltered _ n .accepted s.hub.seq s.hub.head hn
      (Or.inr rfl))
  | pushReject n hd hn hh hne hk hrej hrej' =>
    have r := pUpload_rreachable h hn ((hh hd).2 rfl)
    have r' := r.sync (SyncStep.casReject _ n (s.node n).known.head hd (Or.inr rfl)
      hrej' (fun ⟨e, _, _⟩ => hrej e))
    exact r'.sync (SyncStep.learnUnfiltered _ n .rejected s.hub.seq s.hub.head hn
      (Or.inr rfl))

theorem pstepsR_reachable {s s' : State} (h : RReachable N s) (hp : PStepsR N s s') :
    RReachable N s' :=
  Steps.invariant (inv := RReachable N) pstepR_reachable h hp

/-! ### The measure -/

noncomputable def mBad (N : Nat) (s : State) : Nat := cnt N (fun n => ¬ Good s n)

noncomputable def mIncons (N : Nat) (s : State) : Nat := cnt N (fun n => ¬ Consistent s n)

open Classical in
/-- How far behind the hub a consistent node is; nothing for an inconsistent one, which
`mIncons` counts. -/
noncomputable def mStaleR (s : State) (n : Nat) : Nat :=
  if Consistent s n then s.hub.seq - (s.node n).known.seq else 0

/-- The lexicographic measure: (nodes not good, then `measure`'s last four components with
inconsistency first and staleness counted only for consistent nodes). -/
noncomputable def rmeasure (N : Nat) (s : State) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (mBad N s, mIncons N s, sumN N (mStaleR s), sumN N (mMiss s), sumN N (mAdv s),
    sumN N (mMulti s))

def Lex6 : Nat × Nat × Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat × Nat × Nat → Prop :=
  Prod.Lex (· < ·) Lex5

theorem lex6_wf : WellFounded Lex6 :=
  (Prod.lex Nat.lt_wfRel ⟨Lex5, lex5_wf⟩).wf

/-- The first component does not grow, and if it stays, the rest decreases. -/
theorem lex6_of {a a' : Nat} {r r' : Nat × Nat × Nat × Nat × Nat} (h : a' ≤ a)
    (hr : a' = a → Lex5 r' r) : Lex6 (a', r') (a, r) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ (hr rfl)

/-- `s'` differs from `s` at most in node `n`, the network, and hub stores. -/
structure RFrame (s s' : State) (n : Nat) : Prop where
  U : s'.U = s.U
  head : s'.hub.head = s.hub.head
  seq : s'.hub.seq = s.hub.seq
  hist : s'.hub.hist = s.hub.hist
  other : ∀ i, i ≠ n → s'.node i = s.node i

theorem RFrame.frame {s s' : State} {n : Nat} (f : RFrame s s' n) : Frame s s' n :=
  ⟨f.U, f.head, f.seq, f.other⟩

section congr

variable {s s' : State} {i : Nat} (hU : s'.U = s.U) (hh : s'.hub.head = s.hub.head)
  (hs : s'.hub.seq = s.hub.seq) (hhist : s'.hub.hist = s.hub.hist)
  (hheads : (s'.node i).heads = (s.node i).heads) (hk : (s'.node i).known = (s.node i).known)

include hs hhist hk in
theorem consistent_congr : Consistent s' i ↔ Consistent s i := by
  unfold Consistent; rw [hs, hhist, hk]

include hU hh hs hhist hheads in
theorem settled_congr : Settled s' i ↔ Settled s i := by
  unfold Settled; rw [hU, hh, hs, hhist, hheads]

include hU hh hs hhist hheads hk in
theorem good_congr : Good s' i ↔ Good s i := by
  unfold Good
  rw [consistent_congr hs hhist hk, settled_congr hU hh hs hhist hheads]

include hs hhist hk in
theorem staleR_congr : mStaleR s' i = mStaleR s i := by
  have e := consistent_congr hs hhist hk
  unfold mStaleR
  by_cases hc : Consistent s i
  · have hc' := e.2 hc
    simp only [hc, hc', ↓reduceIte, hs, hk]
  · have hc' : ¬ Consistent s' i := fun h => hc (e.1 h)
    simp only [hc, hc', ↓reduceIte]

end congr

namespace RFrame

variable {s s' : State} {n : Nat} (f : RFrame s s' n)

include f in
theorem good_ne {i : Nat} (hi : i ≠ n) : Good s' i ↔ Good s i :=
  good_congr f.U f.head f.seq f.hist (by rw [f.other i hi]) (by rw [f.other i hi])

include f in
theorem consistent_ne {i : Nat} (hi : i ≠ n) : Consistent s' i ↔ Consistent s i :=
  consistent_congr f.seq f.hist (by rw [f.other i hi])

include f in
theorem staleR_ne {i : Nat} (hi : i ≠ n) : mStaleR s' i = mStaleR s i :=
  staleR_congr f.seq f.hist (by rw [f.other i hi])

include f in
/-- When node `n` keeps its heads and `known`, nothing the first three components read
changes. -/
theorem same_head3 (hheads : (s'.node n).heads = (s.node n).heads)
    (hk : (s'.node n).known = (s.node n).known) :
    mBad N s' = mBad N s ∧ mIncons N s' = mIncons N s ∧
      sumN N (mStaleR s') = sumN N (mStaleR s) := by
  refine ⟨cnt_congr fun i _ => ?_, cnt_congr fun i _ => ?_, sumN_congr fun i _ => ?_⟩
  all_goals by_cases hi : i = n
  · subst hi; exact not_congr (good_congr f.U f.head f.seq f.hist hheads hk)
  · exact not_congr (f.good_ne hi)
  · subst hi; exact not_congr (consistent_congr f.seq f.hist hk)
  · exact not_congr (f.consistent_ne hi)
  · subst hi; exact staleR_congr f.seq f.hist hk
  · exact f.staleR_ne hi

end RFrame

/-! ### Each policy step decreases the measure -/

/-- Node `n` takes the hub's head, which differs from the one it knew: `learn`, and the replies
to `pushIdem` and `pushReject`. -/
theorem measureR_learn {s s' : State} (hI : InvR N s) {n : Nat} (hn : n < N)
    (f : RFrame s s' n) (hheads : (s'.node n).heads = (s.node n).heads)
    (hknown : (s'.node n).known = ⟨s.hub.seq, s.hub.head⟩)
    (hne : (s.node n).known ≠ ⟨s.hub.seq, s.hub.head⟩) :
    Lex6 (rmeasure N s') (rmeasure N s) := by
  have hcons' : Consistent s' n := by
    unfold Consistent; rw [hknown, f.seq, f.hist]; exact ⟨Nat.le_refl _, hI.histHead⟩
  have hset : Settled s' n ↔ Settled s n := settled_congr f.U f.head f.seq f.hist hheads
  apply lex6_of
  · apply cnt_le
    intro i _ hng hg
    by_cases hi : i = n
    · subst hi; exact hng ⟨hcons', hset.2 hg.2⟩
    · exact hng ((f.good_ne hi).2 hg)
  · intro _
    apply lex5_of
    by_cases hc : Consistent s n
    · have hlt : (s.node n).known.seq < s.hub.seq := by
        rcases Nat.lt_or_eq_of_le hc.1 with h | h
        · exact h
        · exfalso; apply hne
          refine Known.ext h ?_
          show (s.node n).known.head = s.hub.head
          rw [← hc.2, h, hI.histHead]
      right; refine ⟨?_, Or.inl ?_⟩
      · apply cnt_congr; intro i _
        by_cases hi : i = n
        · subst hi; exact ⟨fun h => absurd hcons' h, fun h => absurd hc h⟩
        · exact not_congr (f.consistent_ne hi)
      · apply sumN_lt hn
        · unfold mStaleR; simp only [hcons', hc, ↓reduceIte]; rw [hknown, f.seq]; simp; omega
        · intro i _ hi; exact f.staleR_ne hi
    · left
      apply cnt_lt
      · intro i _ h1 h2
        by_cases hi : i = n
        · subst hi; exact h1 hcons'
        · exact h1 ((f.consistent_ne hi).2 h2)
      · exact ⟨n, hn, hc, fun h => h hcons'⟩

theorem measureR_realize {s : State} (hI : InvR N s) {n x : Nat} (hn : n < N)
    (hc : Consistent s n) (hx : Anc s.U.par x (s.node n).known.head)
    (hnl : ¬ (s.node n).lops x) :
    Lex6 (rmeasure N (s.pRealize n x)) (rmeasure N s) := by
  have f : RFrame s (s.pRealize n x) n :=
    ⟨rfl, rfl, rfl, rfl, fun i hi => by
      simp [State.pRealize, State.realize, State.recvObjs, State.recvOps, setNode_ne hi]⟩
  have hnode : ((s.pRealize n x).node n).heads = (s.node n).heads ∧
      ((s.pRealize n x).node n).known = (s.node n).known ∧
      ((s.pRealize n x).node n).lops = fun y => (s.node n).lops y ∨ y = x := by
    simp [State.pRealize, State.realize, State.recvObjs, State.recvOps]
  have hxa : Anc s.U.par x s.hub.head := hx.trans (hI.consistentAnc hc)
  obtain ⟨e1, e2, e3⟩ := f.same_head3 (N := N) hnode.1 hnode.2.1
  apply lex6_of (Nat.le_of_eq e1)
  intro _
  apply lex5_of
  right; refine ⟨e2, Or.inr ⟨e3, Or.inl ?_⟩⟩
  apply f.frame.sum_lt hn (fun i hi => f.frame.miss_ne hi)
  unfold mMiss; rw [hnode.2.2, f.U, f.head]
  apply cnt_lt
  · intro y _ ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
  · exact ⟨x, Nat.lt_succ_of_le (hxa.le hI.parLt), ⟨hxa, hnl⟩, fun ⟨_, h⟩ => h (Or.inr rfl)⟩

theorem measureR_advance {s : State} (hI : InvR N s) {n : Nat} (hn : n < N)
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.head h) :
    Lex6 (rmeasure N (s.advance n)) (rmeasure N s) := by
  have f : RFrame s (s.advance n) n :=
    ⟨rfl, rfl, rfl, rfl, fun i hi => by simp [State.advance, setNode_ne hi]⟩
  have H := fun y => advance_heads_iff_of (y := y) (hI.headsAnti n) hna
  have hheads : ((s.advance n).node n).heads =
      maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.head) := by
    simp [State.advance]
  have hknown : ((s.advance n).node n).known = (s.node n).known := by simp [State.advance]
  have hlops : ((s.advance n).node n).lops = (s.node n).lops := by simp [State.advance]
  have hcons : Consistent (s.advance n) n ↔ Consistent s n :=
    consistent_congr f.seq f.hist hknown
  -- a good node advances to `known.head`, and stays good
  have hgood : Good s n → Good (s.advance n) n := by
    rintro ⟨hc, x, hx, hxa, hcmp⟩
    have hxk : Anc s.U.par x (s.node n).known.head := by
      rcases hcmp _ hc.1 with h | h
      · rw [hc.2] at h; exact h
      · rw [hc.2] at h; exact absurd ⟨x, (hx x).2 rfl, h⟩ hna
    refine ⟨hcons.2 hc, (s.node n).known.head, fun y => ?_, ?_, ?_⟩
    · rw [hheads, H y]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact h
        · rw [(hx y).1 h1] at h2; exact absurd hxk h2
      · intro h; exact Or.inl h
    · exact hI.consistentAnc hc
    · intro i hi
      rw [← hc.2]
      rcases Nat.le_total (s.node n).known.seq i with h | h
      · exact Or.inl (hI.chain h hi)
      · exact Or.inr (hI.chain h hc.1)
  apply lex6_of
  · apply cnt_le
    intro i _ hng hg
    by_cases hi : i = n
    · subst hi; exact hng (hgood hg)
    · exact hng ((f.good_ne hi).2 hg)
  · intro _
    apply lex5_of
    right
    refine ⟨?_, Or.inr ⟨?_, Or.inr ⟨?_, Or.inl ?_⟩⟩⟩
    · apply cnt_congr; intro i _
      by_cases hi : i = n
      · subst hi; exact not_congr hcons
      · exact not_congr (f.consistent_ne hi)
    · apply sumN_congr; intro i _
      by_cases hi : i = n
      · subst hi; exact staleR_congr f.seq f.hist hknown
      · exact f.staleR_ne hi
    · apply f.frame.sum_eq (fun i hi => f.frame.miss_ne hi)
      unfold mMiss; rw [hlops, f.U, f.head]
    · apply f.frame.sum_lt hn (fun i hi => f.frame.adv_ne hi)
      unfold mAdv; rw [hheads, hknown, f.U]
      have h1 : ∃ h, maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.head) h ∧
          Anc s.U.par (s.node n).known.head h := ⟨_, (H _).2 (Or.inl rfl), Anc.refl⟩
      simp only [h1, hna, ↓reduceIte]
      omega

open Classical in
theorem measureR_merge {s : State} (hI : InvR N s) {n : Nat} {L O : List Nat} (hn : n < N)
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    Lex6 (rmeasure N (s.mergeOp n L O)) (rmeasure N s) := by
  have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next L) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have hpar : (s.mergeOp n L O).U.par = upd s.U.par s.U.next L := rfl
  have hhub : (s.mergeOp n L O).hub = s.hub := rfl
  have hother : ∀ i, i ≠ n → (s.mergeOp n L O).node i = s.node i :=
    fun i hi => createOp_node_ne hi
  have hknown : ((s.mergeOp n L O).node n).known = (s.node n).known := createOp_known
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  have hcons : ∀ i, Consistent (s.mergeOp n L O) i ↔ Consistent s i := by
    intro i
    by_cases hi : i = n
    · subst hi; exact consistent_congr (by rw [hhub]) (by rw [hhub]) hknown
    · exact consistent_congr (by rw [hhub]) (by rw [hhub]) (by rw [hother i hi])
  have hk : ∀ i, (s.node i).known.head < s.U.next := fun i => hI.knownLt i
  apply lex6_of
  · -- a node with two heads is not good; the others stay as they were
    apply cnt_le
    intro i _ hng hg
    by_cases hi : i = n
    · subst hi
      obtain ⟨-, x, hx, -⟩ := hg
      exact hab (((hx a).1 ((hL a).1 ha)).trans ((hx b).1 ((hL b).1 hb)).symm)
    · apply hng
      obtain ⟨hc, x, hx, hxa, hcmp⟩ := hg
      have hxl : x < s.U.next := hI.headsLt ((hx x).2 rfl)
      refine ⟨(hcons i).2 hc, x, ?_, ?_, ?_⟩
      · rw [hother i hi]; exact hx
      · rw [hpar, hhub]; exact (T hI.headLt).2 hxa
      · intro j hj
        rw [hpar, hhub] at *
        rcases hcmp j hj with h | h
        · exact Or.inl ((T (hI.histLt hj)).2 h)
        · exact Or.inr ((T hxl).2 h)
  · intro _
    apply lex5_of
    right
    obtain ⟨t1, t2, t3⟩ := merge_tail (O := O) hn hI.parLt hI.headLt (fun _ _ h => hI.headsLt h)
      hk hL ⟨a, b, ha, hb, hab⟩
    refine ⟨cnt_congr (fun i _ => not_congr (hcons i)), Or.inr ⟨?_, Or.inr ⟨t1, Or.inr ⟨t2, t3⟩⟩⟩⟩
    · apply sumN_congr; intro i _
      by_cases hi : i = n
      · subst hi; exact staleR_congr (by rw [hhub]) (by rw [hhub]) hknown
      · exact staleR_congr (by rw [hhub]) (by rw [hhub]) (by rw [hother i hi])

/-- An accepted push makes its node good. It was not good: its head is new to the hub. -/
theorem measureR_pushAccept {s : State} (hI : InvR N s) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd) (hne : hd ≠ (s.node n).known.head)
    (hk : Anc s.U.par (s.node n).known.head hd) (hacc : s.hub.head = (s.node n).known.head) :
    Lex6 (rmeasure N (s.pPushAccept n hd)) (rmeasure N s) := by
  have hU : (s.pPushAccept n hd).U = s.U := rfl
  have hhead : (s.pPushAccept n hd).hub.head = hd := rfl
  have hseq : (s.pPushAccept n hd).hub.seq = s.hub.seq + 1 := rfl
  have hhist : (s.pPushAccept n hd).hub.hist = upd s.hub.hist (s.hub.seq + 1) hd := rfl
  have hheads : ∀ i, ((s.pPushAccept n hd).node i).heads = (s.node i).heads := by
    intro i
    by_cases hi : i = n
    · subst hi; simp [State.pPushAccept, State.learn]
    · simp [State.pPushAccept, State.learn, setNode_ne hi]
  have hknown : ((s.pPushAccept n hd).node n).known = ⟨s.hub.seq + 1, hd⟩ := by
    simp [State.pPushAccept, State.learn]
  have hother : ∀ i, i ≠ n → (s.pPushAccept n hd).node i = s.node i := by
    intro i hi; simp [State.pPushAccept, State.learn, setNode_ne hi]
  have hed : Anc s.U.par s.hub.head hd := hacc ▸ hk
  have histOld : ∀ {i}, i ≤ s.hub.seq → upd s.hub.hist (s.hub.seq + 1) hd i = s.hub.hist i :=
    fun hi => upd_ne _ _ (by omega)
  -- the pusher was not good
  have hbad : ¬ Good s n := by
    rintro ⟨-, x, hx, hxa, -⟩
    have : x = hd := ((hx hd).1 ((hh hd).2 rfl)).symm
    subst this
    rw [hacc] at hxa
    exact hne (Anc.antisymm hI.parLt hxa hk)
  -- and is good now
  have hgood : Good (s.pPushAccept n hd) n := by
    refine ⟨?_, hd, ?_, ?_, ?_⟩
    · unfold Consistent; rw [hknown, hseq, hhist]; simp
    · intro y; rw [hheads]; exact hh y
    · rw [hhead, hU]; exact Anc.refl
    · intro i hi
      rw [hseq] at hi
      rw [hhist, hU]
      by_cases his : i = s.hub.seq + 1
      · subst his; rw [upd_same]; exact Or.inl Anc.refl
      · rw [histOld (by omega)]
        exact Or.inr ((hI.histAnc (by omega)).trans hed)
  apply Prod.Lex.left
  apply cnt_lt
  · intro i _ hng hg
    by_cases hi : i = n
    · subst hi; exact hbad hg
    · apply hng
      obtain ⟨hc, x, hx, hxa, hcmp⟩ := hg
      refine ⟨?_, x, ?_, ?_, ?_⟩
      · unfold Consistent; rw [hother i hi, hseq, hhist, histOld hc.1]
        exact ⟨Nat.le_succ_of_le hc.1, hc.2⟩
      · intro y; rw [hheads]; exact hx y
      · rw [hhead, hU]; exact hxa.trans hed
      · intro j hj
        rw [hseq] at hj
        rw [hhist, hU]
        by_cases hjs : j = s.hub.seq + 1
        · subst hjs; rw [upd_same]; exact Or.inl (hxa.trans hed)
        · rw [histOld (by omega)]; exact hcmp j (by omega)
  · exact ⟨n, hn, hbad, fun h => h hgood⟩

theorem measureR_decreases {s s' : State} (hI : InvR N s) (hp : PStepR N s s') :
    Lex6 (rmeasure N s') (rmeasure N s) := by
  cases hp with
  | learn n hn hs =>
    refine measureR_learn hI hn ⟨rfl, rfl, rfl, rfl, fun i hi => ?_⟩ ?_ ?_ hs
    · simp [State.pLearn, State.learn, setNode_ne hi]
    · simp [State.pLearn, State.learn]
    · simp [State.pLearn, State.learn]
  | realize n x hn hc hx hnl hp => exact measureR_realize hI hn hc hx hnl
  | advance n hn hk hna => exact measureR_advance hI hn hna
  | merge n L O hn hL h2 => exact measureR_merge hI hn hL h2
  | pushAccept n hd hn hh hne hk hacc => exact measureR_pushAccept hI hn hh hne hk hacc
  | pushIdem n hd hn hh hne hk hidem =>
    refine measureR_learn hI hn ⟨rfl, rfl, rfl, rfl, fun i hi => ?_⟩ ?_ ?_ ?_
    · simp [State.pPushIdem, State.learn, setNode_ne hi]
    · simp [State.pPushIdem, State.learn]
    · simp [State.pPushIdem, State.learn]
    · intro e; apply hne; rw [← hidem, e]
  | pushReject n hd hn hh hne hk hrej hrej' =>
    refine measureR_learn hI hn ⟨rfl, rfl, rfl, rfl, fun i hi => ?_⟩ ?_ ?_ ?_
    · simp [State.pPushReject, State.learn, setNode_ne hi]
    · simp [State.pPushReject, State.learn]
    · simp [State.pPushReject, State.learn]
    · intro e; apply hrej; rw [e]

/-! ### Termination -/

theorem pstepR_wf : WellFounded (fun s' s => RReachable N s ∧ PStepR N s s') :=
  Subrelation.wf (fun ⟨h, hp⟩ => measureR_decreases (invR_reachable h) hp) (InvImage.wf (rmeasure N) lex6_wf)

/-- **Termination** once the hub stops going back: no infinite sequence of policy steps
starts from a state of the extended system, whatever the scheduling. -/
theorem no_infinite_policy_runR {s : State} (h : RReachable N s) :
    ¬ ∃ f : Nat → State, f 0 = s ∧ ∀ i, PStepR N (f i) (f (i + 1)) :=
  no_infinite_run_of_invariant pstepR_wf pstepR_reachable h

/-! ### Progress -/

/-- **Progress**: in every state of the extended system that is not converged, some policy
step is enabled. -/
theorem progressR {s : State} (hI : InvR N s) (hc : ¬ Converged N s) :
    ∃ s', PStepR N s s' := by
  unfold Converged at hc
  rw [Classical.not_forall] at hc
  obtain ⟨n, hc⟩ := hc
  rw [Classical.not_imp] at hc
  obtain ⟨hn, hc⟩ := hc
  -- 1. merge
  by_cases hmulti : ∃ a b, (s.node n).heads a ∧ (s.node n).heads b ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := hmulti
    have hmem := fun x => mem_headsList_of (s := s) (n := n) (x := x) (fun _ h => hI.headsLt h)
    exact ⟨_, PStepR.merge s n (headsList s n) [] hn hmem
      ⟨a, b, (hmem a).2 ha, (hmem b).2 hb, hab⟩⟩
  -- 2. learn
  by_cases hk : (s.node n).known ≠ ⟨s.hub.seq, s.hub.head⟩
  · exact ⟨_, PStepR.learn s n hn hk⟩
  have hk := Classical.not_not.1 hk
  have hk2 : (s.node n).known.head = s.hub.head := by rw [hk]
  have hcons : Consistent s n := by
    unfold Consistent; rw [hk]; exact ⟨Nat.le_refl _, hI.histHead⟩
  -- 3. fetch and realize
  by_cases hnloc : ¬ (s.node n).lops (s.node n).known.head
  · have hloc := hnloc
    obtain ⟨x, ⟨hxa, hxl⟩, hmin⟩ := exists_min
      (fun x => Anc s.U.par x (s.node n).known.head ∧ ¬ (s.node n).lops x)
      (a := (s.node n).known.head) ⟨Anc.refl, hloc⟩
    refine ⟨_, PStepR.realize s n x hn hcons hxa hxl (fun p hp => ?_)⟩
    refine Classical.byContradiction fun hpl => ?_
    exact hmin p (hI.parLt x p hp) ⟨(Anc.parent hp).trans hxa, hpl⟩
  have hloc := Classical.not_not.1 hnloc
  -- 4. advance
  by_cases hnadv : ¬ ∃ g, (s.node n).heads g ∧ Anc s.U.par (s.node n).known.head g
  · exact ⟨_, PStepR.advance s n hn hloc hnadv⟩
  have hadv := Classical.not_not.1 hnadv
  -- 5. push
  obtain ⟨g, hg, hkg⟩ := hadv
  have hsingle : ∀ y, (s.node n).heads y ↔ y = g := by
    intro y
    constructor
    · intro hy
      refine Classical.byContradiction fun hne => ?_
      exact hmulti ⟨y, g, hy, hg, hne⟩
    · rintro rfl; exact hg
  have hne : g ≠ (s.node n).known.head := by
    intro e
    apply hc
    refine ⟨fun y => ?_, hk⟩
    rw [hsingle y, e, hk2]
  exact ⟨_, PStepR.pushAccept s n g hn hsingle hne hkg hk2.symm⟩

/-! ### Convergence -/

/-- Converged states enable no policy step. -/
theorem converged_quiescentR {s : State} (hI : InvR N s) (hc : Converged N s)
    {s' : State} : ¬ PStepR N s s' := by
  intro hp
  cases hp with
  | learn n hn hs => exact hs (hc n hn).2
  | realize n x hn _ hx hnl hp =>
    exact hnl (hc.lops_below hn (hI.lParents n) (hI.headsLocal n) hx)
  | advance n hn hk hna => exact hna (hc.known_in_heads hn)
  | merge n L O hn hL h2 =>
    obtain ⟨a, b, ha, hb, hab⟩ := h2
    exact hab (hc.heads_eq hn ((hL a).1 ha) ((hL b).1 hb))
  | pushAccept n hd hn hh hne => exact hne (hc.head_known hn hh)
  | pushIdem n hd hn hh hne => exact hne (hc.head_known hn hh)
  | pushReject n hd hn hh hne => exact hne (hc.head_known hn hh)

/-- A state of the extended system with no enabled policy step is converged, and
conversely. -/
theorem terminal_iff_convergedR {s : State} (h : RReachable N s) :
    (∀ s', ¬ PStepR N s s') ↔ Converged N s :=
  terminal_iff_of_progress (progressR (invR_reachable h))
    (fun hc _ => converged_quiescentR (invR_reachable h) hc)

/-- **A remade hive fills from its machines**: once converged, every operation any node
created is in `anc*(hub.head)`, however much the hub lost on the way. -/
theorem converged_all_acceptedR {s : State} (hI : InvR N s) (hc : Converged N s)
    {x : Nat} (hx : x < s.U.next) : Anc s.U.par x s.hub.head :=
  hI.toCore.converged_all_accepted hc hx

/-- **Liveness** once the hub stops going back: from every state of the extended system,
policy steps reach a converged state. -/
theorem eventually_convergesR {s : State} (h : RReachable N s) :
    ∃ s', PStepsR N s s' ∧ Converged N s' :=
  eventually_done_of_progress (inv := RReachable N) (done := Converged N) pstepR_wf
    pstepR_reachable (fun h => progressR (invR_reachable h)) h

/-- **Liveness**, maximal-run form: every policy run from a state of the extended system that
cannot be extended ends in a converged state. -/
theorem maximal_run_convergesR {s s' : State} (h : RReachable N s) (hr : PStepsR N s s')
    (hmax : ∀ s'', ¬ PStepR N s' s'') : Converged N s' :=
  done_of_maximal_run (inv := RReachable N) pstepR_reachable
    (fun h => progressR (invR_reachable h)) h hr hmax

end Musubi

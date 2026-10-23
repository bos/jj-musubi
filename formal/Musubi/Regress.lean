/-
A hub that goes back. `protocol.md` requires the hub to keep `head`, `seq` and
`closure(head)`, and the rest of the model assumes it does. musubi's hub syncs nothing to
disk, so a power cut can lose the heads it accepted last, and a hub that finds a hive's store
corrupt makes the hive again, empty. This file adds that failure, `hubRegress`, to the
asynchronous model, as a separate system (`RStep`, `RReachable`) so that the theorems of
`Safety.lean` and `Liveness.lean`, which do not hold once the hub can go back, keep their
statements.

What still holds in every state of the extended system (`InvR`): the universe is a DAG, the
hub's history is a chain ending in its head, the hub holds `closure(head)`, and every node's
repository is closed with an antichain of heads. Locality, MergeOwnership and HubMonotone are
not claimed: a node can hold operations of other nodes that the hub no longer has, so two
nodes can come to merge the same heads.

Liveness: a node that gets a reply to its own request carrying a head older than the one it
knows, or another head at the same sequence number, restarts and takes the reply. With that
rule (`PStepR`), once the hub stops going back every policy run ends with every node at the
hub's head, and every operation any node made in it.
-/
import Musubi.Liveness

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

/-- The invariant of the extended system: `Inv` without what relates nodes to the hub's
history. -/
structure InvR (N : Nat) (s : State) : Prop where
  -- universe
  parLt : ParLt s.U.par
  nextPos : 0 < s.U.next
  rootAnc : ∀ x, x < s.U.next → Anc s.U.par root x
  creatorSome : ∀ x, 0 < x → x < s.U.next → ∃ n, n < N ∧ s.U.creator x = some n
  creatorRoot : s.U.creator root = none
  objsRoot : s.U.objs root = []
  -- hub
  headLt : s.hub.head < s.U.next
  histHead : s.hub.hist s.hub.seq = s.hub.head
  hist0 : s.hub.hist 0 = root
  histStep : ∀ i, i < s.hub.seq →
    Anc s.U.par (s.hub.hist i) (s.hub.hist (i + 1)) ∧ s.hub.hist i ≠ s.hub.hist (i + 1)
  hubClosed : ClosedAt s s.hub.head
  hubOpsLt : ∀ x, s.hub.ops x → x < s.U.next
  -- nodes
  lroot : ∀ n, (s.node n).lops root
  lLt : ∀ n x, (s.node n).lops x → x < s.U.next
  lParents : ∀ n x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p
  lObjs : ∀ n x o, (s.node n).lops x → o ∈ s.U.objs x → (s.node n).lobj o
  headsLocal : ∀ n x, (s.node n).heads x → (s.node n).lops x
  headsAnti : ∀ n x y, (s.node n).heads x → (s.node n).heads y → Anc s.U.par x y → x = y
  headsNonempty : ∀ n, ∃ h, (s.node n).heads h
  ownInHeads : ∀ n x, x < s.U.next → s.U.creator x = some n →
    ∃ h, (s.node n).heads h ∧ Anc s.U.par x h
  knownLt : ∀ n, (s.node n).known.2 < s.U.next
  stagedLt : ∀ n x, (s.node n).sops x → x < s.U.next
  -- messages
  msgs : ∀ m, s.net m → MsgR s m

namespace InvR

variable {s : State}

theorem chain (hI : InvR N s) {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.hub.seq) :
    Anc s.U.par (s.hub.hist i) (s.hub.hist j) := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact Anc.refl
  | succ j ih =>
    by_cases h : i = j + 1
    · subst h; exact Anc.refl
    · exact (ih (by omega) (by omega)).trans (hI.histStep j (by omega)).1

theorem histAnc (hI : InvR N s) {i : Nat} (hi : i ≤ s.hub.seq) :
    Anc s.U.par (s.hub.hist i) s.hub.head := by
  have := hI.chain hi (Nat.le_refl _)
  rwa [hI.histHead] at this

theorem accLt (hI : InvR N s) {x : Nat} (h : Anc s.U.par x s.hub.head) : x < s.U.next :=
  Nat.lt_of_le_of_lt (h.le hI.parLt) hI.headLt

theorem histLt (hI : InvR N s) {i : Nat} (hi : i ≤ s.hub.seq) : s.hub.hist i < s.U.next :=
  hI.accLt (hI.histAnc hi)

theorem headsLt (hI : InvR N s) {n x : Nat} (h : (s.node n).heads x) : x < s.U.next :=
  hI.lLt n x (hI.headsLocal n x h)

theorem lopsAnc (hI : InvR N s) {n x a : Nat} (hx : (s.node n).lops x)
    (ha : Anc s.U.par a x) : (s.node n).lops a :=
  Anc.closed (S := (s.node n).lops) (fun y p hy hp => hI.lParents n y p hy hp) ha hx

end InvR

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
  have anc0 : ∀ a x, Anc init.U.par a x → a = x := by
    intro a x h
    cases h with
    | refl => rfl
    | step hp _ => simp [init] at hp
  refine
    { parLt := ?_, nextPos := ?_, rootAnc := ?_, creatorSome := ?_, creatorRoot := ?_,
      objsRoot := ?_, headLt := ?_, histHead := ?_, hist0 := ?_, histStep := ?_,
      hubClosed := ?_, hubOpsLt := ?_, lroot := ?_, lLt := ?_, lParents := ?_,
      lObjs := ?_, headsLocal := ?_, headsAnti := ?_, headsNonempty := ?_,
      ownInHeads := ?_, knownLt := ?_, stagedLt := ?_, msgs := ?_ }
  all_goals simp [init, initNode, ClosedAt, HubHas]
  · intro y p hp; simp at hp
  · exact Anc.refl
  · intro x hx h; omega
  · intro y h; exact anc0 _ _ h

/-! ## Preservation -/

theorem InvR.send {s : State} {m : Msg} (hI : InvR N s) (hm : MsgR s m) :
    InvR N (s.send m) :=
  { hI with
    msgs := by
      intro m' hm'
      rcases hm' with h | h
      · exact hI.msgs m' h
      · subst h; exact hm }

/-- The per-node part of `InvR`, for a candidate new state `nd` of node `n`. -/
structure NodeR (s : State) (n : Nat) (nd : Node) : Prop where
  lroot : nd.lops root
  lLt : ∀ x, nd.lops x → x < s.U.next
  lParents : ∀ x p, nd.lops x → p ∈ s.U.par x → nd.lops p
  lObjs : ∀ x o, nd.lops x → o ∈ s.U.objs x → nd.lobj o
  headsLocal : ∀ x, nd.heads x → nd.lops x
  headsAnti : ∀ x y, nd.heads x → nd.heads y → Anc s.U.par x y → x = y
  headsNonempty : ∃ h, nd.heads h
  ownInHeads : ∀ x, x < s.U.next → s.U.creator x = some n →
    ∃ h, nd.heads h ∧ Anc s.U.par x h
  knownLt : nd.known.2 < s.U.next
  stagedLt : ∀ x, nd.sops x → x < s.U.next

theorem InvR.nodeR {s : State} (hI : InvR N s) (n : Nat) : NodeR s n (s.node n) where
  lroot := hI.lroot n
  lLt := hI.lLt n
  lParents := hI.lParents n
  lObjs := hI.lObjs n
  headsLocal := hI.headsLocal n
  headsAnti := hI.headsAnti n
  headsNonempty := hI.headsNonempty n
  ownInHeads := hI.ownInHeads n
  knownLt := hI.knownLt n
  stagedLt := hI.stagedLt n

theorem invR_setNode {s : State} {n : Nat} {nd : Node} (hI : InvR N s) (h : NodeR s n nd) :
    InvR N (s.setNode n nd) := by
  refine
    { hI with
      lroot := ?_, lLt := ?_, lParents := ?_, lObjs := ?_, headsLocal := ?_,
      headsAnti := ?_, headsNonempty := ?_, ownInHeads := ?_, knownLt := ?_,
      stagedLt := ?_ }
  all_goals
    intro i
    by_cases hi : i = n
    · subst hi; simp only [setNode_self, setNode_U]
      first
        | exact h.lroot | exact h.lLt | exact h.lParents | exact h.lObjs
        | exact h.headsLocal | exact h.headsAnti | exact h.headsNonempty
        | exact h.ownInHeads | exact h.knownLt | exact h.stagedLt
    · rw [setNode_ne hi]
      first
        | exact hI.lroot i | exact hI.lLt i | exact hI.lParents i | exact hI.lObjs i
        | exact hI.headsLocal i | exact hI.headsAnti i | exact hI.headsNonempty i
        | exact hI.ownInHeads i | exact hI.knownLt i | exact hI.stagedLt i

/-- The general preservation lemma for creating an operation on node `n`. -/
theorem invR_createOp {s : State} {n : Nat} {L O : List Nat} {mg : Bool} {H' : OSet}
    (hI : InvR N s) (hn : n < N)
    (hL : ∀ p ∈ L, (s.node n).lops p) (hLne : L ≠ [])
    (hHo : H' s.U.next)
    (hHsub : ∀ y, H' y → (s.node n).heads y ∨ y = s.U.next)
    (hHanti : ∀ x y, H' x → H' y → Anc (upd s.U.par s.U.next L) x y → x = y)
    (hHmono : ∀ x h, (s.node n).heads h → Anc s.U.par x h →
      ∃ h', H' h' ∧ Anc (upd s.U.par s.U.next L) x h') :
    InvR N (s.createOp n L O mg H') := by
  have hLlt : ∀ p ∈ L, p < s.U.next := fun p hp => hI.lLt n p (hL p hp)
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next L) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have hlt' := parLt_upd hI.parLt hLlt
  have hne0 : s.U.next ≠ root := Nat.ne_of_gt hI.nextPos
  refine
    { parLt := hlt', nextPos := by simp, rootAnc := ?_, creatorSome := ?_,
      creatorRoot := ?_, objsRoot := ?_, headLt := ?_, histHead := hI.histHead,
      hist0 := hI.hist0, histStep := ?_, hubClosed := ?_, hubOpsLt := ?_, lroot := ?_,
      lLt := ?_, lParents := ?_, lObjs := ?_, headsLocal := ?_, headsAnti := ?_,
      headsNonempty := ?_, ownInHeads := ?_, knownLt := ?_, stagedLt := ?_, msgs := ?_ }
  · -- rootAnc
    intro x hx
    simp only [createOp_U, create_next, create_par] at hx ⊢
    by_cases hxo : x = s.U.next
    · rw [hxo, anc_upd_new hI.parLt hLlt]
      right
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil L hLne
      exact ⟨q, hq, hI.rootAnc q (hLlt q hq)⟩
    · have hx' : x < s.U.next := by omega
      exact (T hx').2 (hI.rootAnc x hx')
  · -- creatorSome
    intro x hx0 hx
    simp only [createOp_U, create_next, create_creator] at hx ⊢
    by_cases hxo : x = s.U.next
    · rw [hxo, upd_same]; exact ⟨n, hn, rfl⟩
    · rw [upd_ne _ _ hxo]; exact hI.creatorSome x hx0 (by omega)
  · simp only [createOp_U, create_creator]
    rw [upd_ne _ _ (Ne.symm hne0)]; exact hI.creatorRoot
  · simp only [createOp_U, create_objs]
    rw [upd_ne _ _ (Ne.symm hne0)]; exact hI.objsRoot
  · simp; have := hI.headLt; omega
  · intro i hi
    have hi' : i < s.hub.seq := hi
    obtain ⟨h1, h2⟩ := hI.histStep i hi'
    exact ⟨(T (hI.histLt (by omega))).2 h1, h2⟩
  · -- hubClosed
    intro y hy
    simp only [HubHas, createOp_U, createOp_hub, create_par, create_objs] at hy ⊢
    have hy' := (T hI.headLt).1 hy
    obtain ⟨h1, h2⟩ := hI.hubClosed y hy'
    refine ⟨h1, ?_⟩
    rw [upd_lt _ _ (hI.accLt hy')]
    exact h2
  · intro x hx
    have := hI.hubOpsLt x hx
    simp; omega
  · intro i
    by_cases hi : i = n
    · subst hi; simp; exact Or.inl (hI.lroot i)
    · rw [createOp_node_ne hi]; exact hI.lroot i
  · intro i x hx
    simp only [createOp_U, create_next]
    by_cases hi : i = n
    · subst hi
      simp only [createOp_lops] at hx
      rcases hx with hx | hx
      · have := hI.lLt i x hx; omega
      · omega
    · rw [createOp_node_ne hi] at hx; have := hI.lLt i x hx; omega
  · -- lParents
    intro i x p hx hp
    simp only [createOp_U, create_par] at hp
    by_cases hi : i = n
    · subst hi
      simp only [createOp_lops] at hx ⊢
      rcases hx with hx | rfl
      · have hxl := hI.lLt i x hx
        rw [upd_ne _ _ (Nat.ne_of_lt hxl)] at hp
        exact Or.inl (hI.lParents i x p hx hp)
      · rw [upd_same] at hp; exact Or.inl (hL p hp)
    · rw [createOp_node_ne hi] at hx ⊢
      have hxl := hI.lLt i x hx
      rw [upd_ne _ _ (Nat.ne_of_lt hxl)] at hp
      exact hI.lParents i x p hx hp
  · -- lObjs
    intro i x o hx ho
    simp only [createOp_U, create_objs] at ho
    by_cases hi : i = n
    · subst hi
      simp only [createOp_lops, createOp_lobj] at hx ⊢
      rcases hx with hx | rfl
      · have hxl := hI.lLt i x hx
        rw [upd_ne _ _ (Nat.ne_of_lt hxl)] at ho
        exact Or.inl (hI.lObjs i x o hx ho)
      · rw [upd_same] at ho; exact Or.inr ho
    · rw [createOp_node_ne hi] at hx ⊢
      have hxl := hI.lLt i x hx
      rw [upd_ne _ _ (Nat.ne_of_lt hxl)] at ho
      exact hI.lObjs i x o hx ho
  · -- headsLocal
    intro i x hx
    by_cases hi : i = n
    · subst hi
      simp only [createOp_heads] at hx
      simp only [createOp_lops]
      rcases hHsub x hx with h | h
      · exact Or.inl (hI.headsLocal i x h)
      · exact Or.inr h
    · rw [createOp_node_ne hi] at hx ⊢; exact hI.headsLocal i x hx
  · -- headsAnti
    intro i x y hx hy hA
    simp only [createOp_U, create_par] at hA
    by_cases hi : i = n
    · subst hi
      simp only [createOp_heads] at hx hy
      exact hHanti x y hx hy hA
    · rw [createOp_node_ne hi] at hx hy
      exact hI.headsAnti i x y hx hy ((T (hI.headsLt hy)).1 hA)
  · intro i
    by_cases hi : i = n
    · subst hi; exact ⟨s.U.next, by simpa using hHo⟩
    · rw [createOp_node_ne hi]; exact hI.headsNonempty i
  · -- ownInHeads
    intro i x hx hc
    simp only [createOp_U, create_next, create_creator, create_par] at hx hc ⊢
    by_cases hxo : x = s.U.next
    · subst hxo
      rw [upd_same] at hc
      cases hc
      exact ⟨s.U.next, by simpa using hHo, Anc.refl⟩
    · rw [upd_ne _ _ hxo] at hc
      have hx' : x < s.U.next := by omega
      obtain ⟨h, hh, hA⟩ := hI.ownInHeads i x hx' hc
      by_cases hi : i = n
      · subst hi
        obtain ⟨h', hh', hA'⟩ := hHmono x h hh hA
        exact ⟨h', by simpa using hh', hA'⟩
      · rw [createOp_node_ne hi]
        exact ⟨h, hh, (T (hI.headsLt hh)).2 hA⟩
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

theorem invR_userOp {s : State} (hI : InvR N s) {n p : Nat} {O : List Nat} (hn : n < N)
    (hp : (s.node n).lops p) : InvR N (s.userOp n p O) := by
  have hLlt : ∀ q ∈ [p], q < s.U.next := by
    intro q hq; simp at hq; subst hq; exact hI.lLt n q hp
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next [p]) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have Tnew : ∀ {a : Nat}, Anc (upd s.U.par s.U.next [p]) a s.U.next ↔
      a = s.U.next ∨ Anc s.U.par a p := by
    intro a; rw [anc_upd_new hI.parLt hLlt]; simp
  have H := fun y => userOp_heads_iff_of (y := y) hI.parLt (hI.lLt n p hp)
    (fun _ h => hI.headsLt h) (hI.headsAnti n)
  apply invR_createOp hI hn
  · intro q hq; simp at hq; subst hq; exact hp
  · simp
  · exact (H _).2 (Or.inl rfl)
  · intro y hy
    rcases (H y).1 hy with h | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  · intro x y hx hy hA
    exact hx.2 y hy.1 hA
  · intro x h hh hA
    by_cases hc : h = p ∨ Anc s.U.par h p
    · refine ⟨s.U.next, (H _).2 (Or.inl rfl), Tnew.2 (Or.inr ?_)⟩
      rcases hc with hc | hc
      · subst hc; exact hA
      · exact hA.trans hc
    · have hc' : h ≠ p ∧ ¬ Anc s.U.par h p := ⟨fun e => hc (Or.inl e), fun e => hc (Or.inr e)⟩
      exact ⟨h, (H h).2 (Or.inr ⟨hh, hc'.1, hc'.2⟩), (T (hI.headsLt hh)).2 hA⟩

theorem invR_merge {s : State} (hI : InvR N s) {n : Nat} {L O : List Nat} (hn : n < N)
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    InvR N (s.mergeOp n L O) := by
  have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  apply invR_createOp hI hn
  · intro q hq; exact hI.headsLocal n q ((hL q).1 hq)
  · intro h; rw [h] at ha; simp at ha
  · rfl
  · intro y hy; exact Or.inr hy
  · intro x y hx hy _; rw [hx, hy]
  · intro x h hh hA
    refine ⟨s.U.next, rfl, ?_⟩
    rw [anc_upd_new hI.parLt hLlt]
    exact Or.inr ⟨h, (hL h).2 hh, hA⟩

theorem invR_realize {s : State} (hI : InvR N s) {n x : Nat} (hx : (s.node n).sops x)
    (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) :
    InvR N (s.realize n x) := by
  refine invR_setNode hI
    { hI.nodeR n with
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

theorem invR_advance {s : State} (hI : InvR N s) {n : Nat}
    (hk : (s.node n).lops (s.node n).known.2)
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
    InvR N (s.advance n) := by
  have H := fun y => advance_heads_iff_of (y := y) (hI.headsAnti n) hna
  refine invR_setNode hI
    { hI.nodeR n with
      headsLocal := ?_, headsAnti := ?_, headsNonempty := ?_, ownInHeads := ?_ }
  · intro y hy
    rcases (H y).1 hy with rfl | ⟨hy, -⟩
    · exact hk
    · exact hI.headsLocal n y hy
  · intro x y hx hy hA
    exact hx.2 y hy.1 hA
  · exact ⟨_, (H _).2 (Or.inl rfl)⟩
  · intro x hx hc
    obtain ⟨h, hh, hA⟩ := hI.ownInHeads n x hx hc
    by_cases hhk : Anc s.U.par h (s.node n).known.2
    · exact ⟨_, (H _).2 (Or.inl rfl), hA.trans hhk⟩
    · exact ⟨h, (H h).2 (Or.inr ⟨hh, hhk⟩), hA⟩

theorem invR_hubStore {s : State} (hI : InvR N s) {S O : OSet}
    (hS : ∀ x, S x → x < s.U.next) : InvR N (s.hubStore S O) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨Or.inl h1, fun o ho => Or.inl (h2 o ho)⟩
    hubOpsLt := by
      rintro x (hx | hx)
      · exact hI.hubOpsLt x hx
      · exact hS x hx }

theorem invR_hubStoreOps {s : State} (hI : InvR N s) {S : OSet}
    (hS : ∀ x, S x → x < s.U.next) : InvR N (s.hubStoreOps S) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨Or.inl h1, h2⟩
    hubOpsLt := by
      rintro x (hx | hx)
      · exact hI.hubOpsLt x hx
      · exact hS x hx }

theorem invR_hubStoreObjs {s : State} (hI : InvR N s) {S : OSet} :
    InvR N (s.hubStoreObjs S) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨h1, fun o ho => Or.inl (h2 o ho)⟩ }

theorem invR_casAccept {s : State} (hI : InvR N s) {n0 e d : Nat}
    (hd : d < s.U.next) (hne : s.hub.head ≠ d) (he : s.hub.head = e)
    (ha : Anc s.U.par e d) (hc : ClosedAt s d) :
    InvR N (((s.hubAccept d).send (.head n0 .accepted (s.hub.seq + 1) d)).notifyAll
      (s.hub.seq + 1) d) := by
  have hed : Anc s.U.par s.hub.head d := he ▸ ha
  have histOld : ∀ {i}, i ≤ s.hub.seq → upd s.hub.hist (s.hub.seq + 1) d i = s.hub.hist i :=
    fun hi => upd_ne _ _ (by omega)
  refine
    { hI with
      headLt := hd, histHead := ?_, hist0 := ?_, histStep := ?_, hubClosed := hc,
      msgs := ?_ }
  · show upd s.hub.hist (s.hub.seq + 1) d (s.hub.seq + 1) = d
    simp
  · show upd s.hub.hist (s.hub.seq + 1) d 0 = root
    rw [upd_ne _ _ (by omega)]; exact hI.hist0
  · intro i hi
    show Anc s.U.par (upd s.hub.hist (s.hub.seq + 1) d i)
        (upd s.hub.hist (s.hub.seq + 1) d (i + 1)) ∧
      upd s.hub.hist (s.hub.seq + 1) d i ≠ upd s.hub.hist (s.hub.seq + 1) d (i + 1)
    have hi' : i < s.hub.seq + 1 := hi
    rw [histOld (by omega)]
    by_cases his : i = s.hub.seq
    · subst his
      rw [upd_same, hI.histHead]
      exact ⟨hed, hne⟩
    · rw [histOld (by omega)]
      exact hI.histStep i (by omega)
  · rintro m ((hm | rfl) | ⟨i, rfl⟩)
    · exact hI.msgs m hm
    · exact hd
    · exact hd

theorem invR_regress {s : State} (hI : InvR N s) {i : Nat} (hi : i ≤ s.hub.seq) :
    InvR N (s.regress i) :=
  { hI with
    headLt := hI.histLt hi
    histHead := rfl
    histStep := fun j hj => hI.histStep j (Nat.lt_of_lt_of_le hj hi)
    hubClosed := fun y hy => hI.hubClosed y (hy.trans (hI.histAnc hi)) }

theorem invR_syncStep {s s' : State} (hI : InvR N s) (h : SyncStep N s s') : InvR N s' := by
  cases h with
  | getHead n hn => exact hI.send trivial
  | learn n k sq h hn hm hs =>
    exact invR_setNode hI { hI.nodeR n with knownLt := hI.msgs _ hm }
  | learnUnfiltered n k sq h hn hm =>
    exact invR_setNode hI { hI.nodeR n with knownLt := hI.msgs _ hm }
  | fetchOps n S hn hS => exact hI.send trivial
  | fetchObjs n S hn => exact hI.send trivial
  | recvOps n S hn hm =>
    refine invR_setNode hI { hI.nodeR n with stagedLt := ?_ }
    rintro x (hx | hx)
    · exact hI.stagedLt n x hx
    · exact (hI.msgs _ hm : MsgR s (.ops n S)) x hx
  | recvObjs n S hn hm => exact invR_setNode hI { hI.nodeR n with }
  | realize n x hn hx hp ho => exact invR_realize hI hx hp
  | advance n hn hk hna => exact invR_advance hI hk hna
  | uploadOps n S hn hS => exact hI.send (fun x hx => hI.lLt n x (hS x hx))
  | uploadObjs n S hn hS => exact hI.send trivial
  | push n e d hn hd => exact hI.send (hI.lLt n d hd)
  | pushAll n S O e d hn hS hO hd =>
    exact hI.send ⟨fun x hx => hI.lLt n x (hS x hx), hI.lLt n d hd⟩
  | fetchAll n b H hn => exact hI.send trivial
  | crashNode n hn => exact hI
  | loseKnown n hn => exact invR_setNode hI { hI.nodeR n with knownLt := hI.nextPos }
  | loseVolatile n hn =>
    refine invR_setNode hI { hI.nodeR n with knownLt := hI.nextPos, stagedLt := ?_ }
    intro x hx; exact hx.elim
  | hubGetHead n hm => exact hI.send hI.headLt
  | hubPutOps n S hm =>
    exact (invR_hubStoreOps hI (hI.msgs _ hm : MsgR s (.putOps n S))).send trivial
  | hubPutObjs n S hm => exact (invR_hubStoreObjs hI).send trivial
  | hubGetOps n S hm => exact hI.send (fun x hx => hI.hubOpsLt x hx.2)
  | hubGetObjs n S hm => exact hI.send trivial
  | casIdem n e d hm hh => exact hI.send hI.headLt
  | casAccept n e d hm hne he ha hc =>
    exact invR_casAccept hI (hI.msgs _ hm : MsgR s (.cas n e d)) hne he ha hc
  | casReject n e d hm hne hrej => exact hI.send hI.headLt
  | hubPushIdem n S O e d hm hh =>
    have hI' := invR_hubStore (O := O) hI (hI.msgs _ hm : MsgR s (.push n S O e d)).1
    exact hI'.send hI'.headLt
  | hubPushAccept n S O e d hm hne he ha hc =>
    have hmsg : MsgR s (.push n S O e d) := hI.msgs _ hm
    exact invR_casAccept (invR_hubStore (O := O) hI hmsg.1) hmsg.2 hne he ha hc
  | hubPushReject n S O e d hm hne hrej =>
    have hI' := invR_hubStore (O := O) hI (hI.msgs _ hm : MsgR s (.push n S O e d)).1
    exact hI'.send hI'.headLt
  | hubPushIncomplete n S O e d hm hne he hc =>
    have hI' := invR_hubStore (O := O) hI (hI.msgs _ hm : MsgR s (.push n S O e d)).1
    exact hI'.send hI'.headLt
  | hubFetch n b H hm =>
    have h1 := hI.send (m := .head n .head s.hub.seq s.hub.head) hI.headLt
    have h2 := h1.send (m := .ops n (s.sinceOps b)) (fun x hx => hI.hubOpsLt x hx.2.2)
    exact h2.send trivial
  | crashHub => exact hI
  | hubForget O J hO hJ hc =>
    exact { hI with hubClosed := hc, hubOpsLt := fun x hx => hI.hubOpsLt x (hO x hx) }

theorem invR_envStep {s s' : State} (hI : InvR N s) (h : EnvStep N s s') : InvR N s' := by
  cases h with
  | userOp n p O hn hp => exact invR_userOp hI hn hp
  | merge n L O hn hL h2 => exact invR_merge hI hn hL h2

theorem invR_rstep {s s' : State} (hI : InvR N s) (h : RStep N s s') : InvR N s' := by
  rcases h with (h | h) | ⟨i, hi, rfl⟩
  · exact invR_envStep hI h
  · exact invR_syncStep hI h
  · exact invR_regress hI hi

theorem invR_reachable {s : State} (h : RReachable N s) : InvR N s := by
  induction h with
  | init => exact invR_init N
  | step _ hst ih => exact invR_rstep ih hst

/-! ## Safety that survives -/

/-- **HubClosed**, with a hub that goes back: `closure(head) ⊆ ops ∪ objects`. -/
theorem rhubClosed {s : State} (h : RReachable N s) :
    ∀ y, Anc s.U.par y s.hub.head → s.hub.ops y ∧ ∀ o ∈ s.U.objs y, s.hub.objs o :=
  (invR_reachable h).hubClosed

/-- The hub's history is still a chain of strictly increasing heads from the root to its
head, though going back drops its newest entries. -/
theorem rhubHistory {s : State} (h : RReachable N s) :
    s.hub.hist 0 = root ∧ s.hub.hist s.hub.seq = s.hub.head ∧
    ∀ i, i < s.hub.seq →
      Anc s.U.par (s.hub.hist i) (s.hub.hist (i + 1)) ∧ s.hub.hist i ≠ s.hub.hist (i + 1) :=
  have hI := invR_reachable h
  ⟨hI.hist0, hI.histHead, hI.histStep⟩

/-- **NodeClosed**, with a hub that goes back: every node's repository stays whole. -/
theorem rnodeClosed {s : State} (h : RReachable N s) (n : Nat) :
    (∀ x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p) ∧
    (∀ x o, (s.node n).lops x → o ∈ s.U.objs x → (s.node n).lobj o) ∧
    (∀ x, (s.node n).heads x → (s.node n).lops x) ∧
    (∀ x y, (s.node n).heads x → (s.node n).heads y → Anc s.U.par x y → x = y) ∧
    (∃ x, (s.node n).heads x) :=
  have hI := invR_reachable h
  ⟨hI.lParents n, hI.lObjs n, hI.headsLocal n, hI.headsAnti n, hI.headsNonempty n⟩

/-- **No feedback**, with a hub that goes back: neither sync actions nor the hub going back
create operations. -/
theorem rnoFeedback {s s' : State} (hs : SyncStep N s s' ∨ ∃ i, s' = s.regress i) :
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

/-- Node `n`'s `known` is a head in the hub's current history, at its sequence number: what
`Inv.known` says of every node while the hub keeps its heads. -/
def Consistent (s : State) (n : Nat) : Prop :=
  (s.node n).known.1 ≤ s.hub.seq ∧ s.hub.hist (s.node n).known.1 = (s.node n).known.2

/-- Node `n` has one head, accepted, and comparable with every head in the hub's history. -/
def Settled (s : State) (n : Nat) : Prop :=
  ∃ x, (∀ y, (s.node n).heads y ↔ y = x) ∧ Anc s.U.par x s.hub.head ∧
    ∀ i, i ≤ s.hub.seq → Anc s.U.par x (s.hub.hist i) ∨ Anc s.U.par (s.hub.hist i) x

/-- A node that no policy step can make push again. After the hub goes back a node can hold
two accepted heads that are not comparable, and merging them makes it dirty; a good node
has neither. -/
def Good (s : State) (n : Nat) : Prop := Consistent s n ∧ Settled s n

theorem InvR.consistentAnc {s : State} (hI : InvR N s) {n : Nat} (hc : Consistent s n) :
    Anc s.U.par (s.node n).known.2 s.hub.head := by
  rw [← hc.2]; exact hI.histAnc hc.1

/-- The policy, with a hub that may have gone back. It is `PStep` but for two steps. A node
takes the head in a reply to its own request whenever it differs from the one it knows,
older or not: it restarts (`loseKnown`), then learns it. And it realizes only below a head
in the hub's current history, as it does after a `Fetch`, whose reply it learns first. -/
inductive PStepR (N : Nat) : State → State → Prop
  | learn (s : State) (n : Nat) (hn : n < N) (hs : (s.node n).known ≠ (s.hub.seq, s.hub.head)) :
      PStepR N s (s.pLearn n)
  | realize (s : State) (n x : Nat) (hn : n < N) (hc : Consistent s n)
      (hx : Anc s.U.par x (s.node n).known.2)
      (hnl : ¬ (s.node n).lops x) (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) :
      PStepR N s (s.pRealize n x)
  | advance (s : State) (n : Nat) (hn : n < N) (hk : (s.node n).lops (s.node n).known.2)
      (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
      PStepR N s (s.advance n)
  | merge (s : State) (n : Nat) (L O : List Nat) (hn : n < N)
      (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
      PStepR N s (s.mergeOp n L O)
  | pushAccept (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.2) (hk : Anc s.U.par (s.node n).known.2 h)
      (hacc : s.hub.head = (s.node n).known.2) : PStepR N s (s.pPushAccept n h)
  | pushIdem (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.2) (hk : Anc s.U.par (s.node n).known.2 h)
      (hidem : s.hub.head = h) : PStepR N s (s.pPushIdem n h)
  | pushReject (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.2) (hk : Anc s.U.par (s.node n).known.2 h)
      (hrej : s.hub.head ≠ (s.node n).known.2) (hrej' : s.hub.head ≠ h) :
      PStepR N s (s.pPushReject n h)

/-- Reflexive-transitive closure of `PStepR`. -/
inductive PStepsR (N : Nat) : State → State → Prop
  | refl (s : State) : PStepsR N s s
  | tail {s t u : State} : PStepsR N s t → PStepR N t u → PStepsR N s u

/-! ### Policy steps are runs of the extended system -/

theorem pUpload_closedR {s : State} (hI : InvR N s) {n h : Nat}
    (hacc : s.hub.head = (s.node n).known.2) : ClosedAt (s.pUpload n h) h := by
  intro y hy
  have hy' : Anc s.U.par y h := hy
  have hk : Anc s.U.par (s.node n).known.2 s.hub.head := by rw [hacc]; exact Anc.refl
  constructor
  · show (s.hub.ops y ∨ s.upOps n h y)
    by_cases hyk : Anc s.U.par y (s.node n).known.2
    · exact Or.inl (hI.hubClosed y (hyk.trans hk)).1
    · exact Or.inr ⟨hy', hyk⟩
  · intro o ho
    show s.hub.objs o ∨ s.upObjs n h o
    by_cases hz : ∃ z, Anc s.U.par z (s.node n).known.2 ∧ o ∈ s.U.objs z
    · obtain ⟨z, hz, hoz⟩ := hz
      exact Or.inl ((hI.hubClosed z (hz.trans hk)).2 o hoz)
    · exact Or.inr ⟨⟨y, hy', ho⟩, hz⟩

theorem pUpload_rreachable {s : State} (h : RReachable N s) {n hd : Nat} (hn : n < N)
    (hh : (s.node n).heads hd) : RReachable N (s.pUpload n hd) := by
  have hI := invR_reachable h
  have hl := hI.headsLocal n hd hh
  have r1 := h.sync (SyncStep.uploadOps s n (s.upOps n hd) hn
    (fun x hx => hI.lopsAnc hl hx.1))
  have r2 := r1.sync (SyncStep.hubPutOps _ n (s.upOps n hd) (Or.inr rfl))
  have r3 := r2.sync (SyncStep.uploadObjs _ n (s.upObjs n hd) hn
    (fun o ho => by
      obtain ⟨⟨y, hy, hoy⟩, -⟩ := ho
      exact hI.lObjs n y o (hI.lopsAnc hl hy) hoy))
  have r4 := r3.sync (SyncStep.hubPutObjs _ n (s.upObjs n hd) (Or.inr rfl))
  exact r4.sync (SyncStep.push _ n (s.node n).known.2 hd hn hl)

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
    have hxa : Anc s.U.par x s.hub.head := hx.trans (hI.consistentAnc hc)
    have hc := hI.hubClosed x hxa
    have r1 := h.sync (SyncStep.fetchOps s n (· = x) hn (fun y hy => hy ▸ hx))
    have r2 := r1.sync (SyncStep.hubGetOps _ n (· = x) (Or.inr rfl))
    have r3 := r2.sync (SyncStep.recvOps _ n (fun y => y = x ∧ s.hub.ops y) hn
      (Or.inr rfl))
    have r4 := r3.sync (SyncStep.fetchObjs _ n (· ∈ s.U.objs x) hn)
    have r5 := r4.sync (SyncStep.hubGetObjs _ n (· ∈ s.U.objs x) (Or.inr rfl))
    have r6 := r5.sync (SyncStep.recvObjs _ n
      (fun o => o ∈ s.U.objs x ∧ s.hub.objs o) hn (Or.inr rfl))
    refine r6.sync (SyncStep.realize _ n x hn ?_ ?_ ?_)
    · simp [State.recvObjs, State.recvOps, State.setNode, State.send, hc.1]
    · simpa [State.recvObjs, State.recvOps, State.setNode, State.send] using hp
    · intro o ho
      have ho' : o ∈ s.U.objs x := ho
      simp [State.recvObjs, State.recvOps, State.setNode, State.send, ho', hc.2 o ho']
  | advance n hn hk hna => exact h.sync (SyncStep.advance s n hn hk hna)
  | merge n L O hn hL h2 => exact h.env (EnvStep.merge s n L O hn hL h2)
  | pushAccept n hd hn hh hne hk hacc =>
    have r := pUpload_rreachable h hn ((hh hd).2 rfl)
    have r' := r.sync (SyncStep.casAccept _ n (s.node n).known.2 hd (Or.inr rfl)
      (fun e => hne ((show s.hub.head = hd from e).symm.trans hacc)) hacc hk
      (pUpload_closedR hI hacc))
    exact r'.sync (SyncStep.learnUnfiltered _ n .accepted (s.hub.seq + 1) hd hn
      (Or.inl (Or.inr rfl)))
  | pushIdem n hd hn hh hne hk hidem =>
    have r := pUpload_rreachable h hn ((hh hd).2 rfl)
    have r' := r.sync (SyncStep.casIdem _ n (s.node n).known.2 hd (Or.inr rfl) hidem)
    exact r'.sync (SyncStep.learnUnfiltered _ n .accepted s.hub.seq s.hub.head hn
      (Or.inr rfl))
  | pushReject n hd hn hh hne hk hrej hrej' =>
    have r := pUpload_rreachable h hn ((hh hd).2 rfl)
    have r' := r.sync (SyncStep.casReject _ n (s.node n).known.2 hd (Or.inr rfl)
      hrej' (fun ⟨e, _, _⟩ => hrej e))
    exact r'.sync (SyncStep.learnUnfiltered _ n .rejected s.hub.seq s.hub.head hn
      (Or.inr rfl))

theorem pstepsR_reachable {s s' : State} (h : RReachable N s) (hp : PStepsR N s s') :
    RReachable N s' := by
  induction hp with
  | refl => exact h
  | tail _ hst ih => exact pstepR_reachable ih hst

/-! ### The measure -/

noncomputable def mBad (N : Nat) (s : State) : Nat := cnt N (fun n => ¬ Good s n)

noncomputable def mIncons (N : Nat) (s : State) : Nat := cnt N (fun n => ¬ Consistent s n)

open Classical in
/-- How far behind the hub a consistent node is; nothing for an inconsistent one, which
`mIncons` counts. -/
noncomputable def mStaleR (s : State) (n : Nat) : Nat :=
  if Consistent s n then s.hub.seq - (s.node n).known.1 else 0

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
    (hknown : (s'.node n).known = (s.hub.seq, s.hub.head))
    (hne : (s.node n).known ≠ (s.hub.seq, s.hub.head)) :
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
    · have hlt : (s.node n).known.1 < s.hub.seq := by
        rcases Nat.lt_or_eq_of_le hc.1 with h | h
        · exact h
        · exfalso; apply hne
          refine Prod.ext h ?_
          show (s.node n).known.2 = s.hub.head
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
    (hc : Consistent s n) (hx : Anc s.U.par x (s.node n).known.2)
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
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
    Lex6 (rmeasure N (s.advance n)) (rmeasure N s) := by
  have f : RFrame s (s.advance n) n :=
    ⟨rfl, rfl, rfl, rfl, fun i hi => by simp [State.advance, setNode_ne hi]⟩
  have H := fun y => advance_heads_iff_of (y := y) (hI.headsAnti n) hna
  have hheads : ((s.advance n).node n).heads =
      maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) := by
    simp [State.advance]
  have hknown : ((s.advance n).node n).known = (s.node n).known := by simp [State.advance]
  have hlops : ((s.advance n).node n).lops = (s.node n).lops := by simp [State.advance]
  have hcons : Consistent (s.advance n) n ↔ Consistent s n :=
    consistent_congr f.seq f.hist hknown
  -- a good node advances to `known.head`, and stays good
  have hgood : Good s n → Good (s.advance n) n := by
    rintro ⟨hc, x, hx, hxa, hcmp⟩
    have hxk : Anc s.U.par x (s.node n).known.2 := by
      rcases hcmp _ hc.1 with h | h
      · rw [hc.2] at h; exact h
      · rw [hc.2] at h; exact absurd ⟨x, (hx x).2 rfl, h⟩ hna
    refine ⟨hcons.2 hc, (s.node n).known.2, fun y => ?_, ?_, ?_⟩
    · rw [hheads, H y]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact h
        · rw [(hx y).1 h1] at h2; exact absurd hxk h2
      · intro h; exact Or.inl h
    · exact hI.consistentAnc hc
    · intro i hi
      rw [← hc.2]
      rcases Nat.le_total (s.node n).known.1 i with h | h
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
      have h1 : ∃ h, maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) h ∧
          Anc s.U.par (s.node n).known.2 h := ⟨_, (H _).2 (Or.inl rfl), Anc.refl⟩
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
  have Tnew : ∀ {a : Nat}, Anc (upd s.U.par s.U.next L) a s.U.next ↔
      a = s.U.next ∨ ∃ p ∈ L, Anc s.U.par a p := anc_upd_new hI.parLt hLlt
  have hpar : (s.mergeOp n L O).U.par = upd s.U.par s.U.next L := rfl
  have hhub : (s.mergeOp n L O).hub = s.hub := rfl
  have hother : ∀ i, i ≠ n → (s.mergeOp n L O).node i = s.node i :=
    fun i hi => createOp_node_ne hi
  have hheads : ((s.mergeOp n L O).node n).heads = (· = s.U.next) := createOp_heads
  have hknown : ((s.mergeOp n L O).node n).known = (s.node n).known := createOp_known
  have hlops : ((s.mergeOp n L O).node n).lops = fun y => (s.node n).lops y ∨ y = s.U.next :=
    createOp_lops
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  have hcons : ∀ i, Consistent (s.mergeOp n L O) i ↔ Consistent s i := by
    intro i
    by_cases hi : i = n
    · subst hi; exact consistent_congr (by rw [hhub]) (by rw [hhub]) hknown
    · exact consistent_congr (by rw [hhub]) (by rw [hhub]) (by rw [hother i hi])
  have hk : ∀ i, (s.node i).known.2 < s.U.next := fun i => hI.knownLt i
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
    refine ⟨cnt_congr (fun i _ => not_congr (hcons i)), Or.inr ⟨?_, Or.inr ⟨?_, Or.inr ⟨?_, ?_⟩⟩⟩⟩
    · apply sumN_congr; intro i _
      by_cases hi : i = n
      · subst hi; exact staleR_congr (by rw [hhub]) (by rw [hhub]) hknown
      · exact staleR_congr (by rw [hhub]) (by rw [hhub]) (by rw [hother i hi])
    · apply sumN_congr; intro i _
      unfold mMiss; rw [hhub, hpar]
      apply cnt_congr; intro x hx
      have hxl : x < s.U.next := by have := hI.headLt; omega
      by_cases hi : i = n
      · subst hi; rw [hlops, T hI.headLt]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h.elim h2 (fun e => by omega)⟩
      · rw [hother i hi, T hI.headLt]
    · apply sumN_congr; intro i _
      unfold mAdv; rw [hpar]
      by_cases hi : i = n
      · subst hi
        rw [hheads, hknown]
        have : (∃ h, h = s.U.next ∧ Anc (upd s.U.par s.U.next L) (s.node i).known.2 h) ↔
            (∃ h, (s.node i).heads h ∧ Anc s.U.par (s.node i).known.2 h) := by
          constructor
          · rintro ⟨h, rfl, hA⟩
            rcases Tnew.1 hA with e | ⟨p, hp, hA'⟩
            · have := hk i; omega
            · exact ⟨p, (hL p).1 hp, hA'⟩
          · rintro ⟨h, hh, hA⟩
            exact ⟨s.U.next, rfl, Tnew.2 (Or.inr ⟨h, (hL h).2 hh, hA⟩)⟩
        exact ite_iff this
      · rw [hother i hi]
        have : (∃ h, (s.node i).heads h ∧ Anc (upd s.U.par s.U.next L) (s.node i).known.2 h) ↔
            (∃ h, (s.node i).heads h ∧ Anc s.U.par (s.node i).known.2 h) := by
          constructor
          · rintro ⟨h, hh, hA⟩; exact ⟨h, hh, (T (hI.headsLt hh)).1 hA⟩
          · rintro ⟨h, hh, hA⟩; exact ⟨h, hh, (T (hI.headsLt hh)).2 hA⟩
        exact ite_iff this
    · apply sumN_lt hn
      · unfold mMulti; rw [hheads]
        have h1 : ¬ ∃ a b, a = s.U.next ∧ b = s.U.next ∧ a ≠ b := by
          rintro ⟨a, b, rfl, rfl, h⟩; exact h rfl
        have h2 : ∃ a b, (s.node n).heads a ∧ (s.node n).heads b ∧ a ≠ b :=
          ⟨a, b, (hL a).1 ha, (hL b).1 hb, hab⟩
        simp only [h1, h2, ↓reduceIte]
        omega
      · intro i _ hi
        unfold mMulti; rw [hother i hi]

/-- An accepted push makes its node good. It was not good: its head is new to the hub. -/
theorem measureR_pushAccept {s : State} (hI : InvR N s) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd) (hne : hd ≠ (s.node n).known.2)
    (hk : Anc s.U.par (s.node n).known.2 hd) (hacc : s.hub.head = (s.node n).known.2) :
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
  have hknown : ((s.pPushAccept n hd).node n).known = (s.hub.seq + 1, hd) := by
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

theorem measureR_decreases {s s' : State} (h : RReachable N s) (hp : PStepR N s s') :
    Lex6 (rmeasure N s') (rmeasure N s) := by
  have hI := invR_reachable h
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
  Subrelation.wf (fun ⟨h, hp⟩ => measureR_decreases h hp) (InvImage.wf (rmeasure N) lex6_wf)

/-- **Termination** once the hub stops going back: no infinite sequence of policy steps
starts from a state of the extended system, whatever the scheduling. -/
theorem no_infinite_policy_runR {s : State} (h : RReachable N s) :
    ¬ ∃ f : Nat → State, f 0 = s ∧ ∀ i, PStepR N (f i) (f (i + 1)) := by
  rintro ⟨f, hf0, hf⟩
  have hreach : ∀ i, RReachable N (f i) := by
    intro i
    induction i with
    | zero => exact hf0 ▸ h
    | succ i ih => exact pstepR_reachable ih (hf i)
  exact no_infinite_run_aux (pstepR_wf.apply s) f hf0 (fun i => ⟨hreach i, hf i⟩)

/-! ### Progress -/

theorem mem_headsListR {s : State} (hI : InvR N s) {n x : Nat} :
    x ∈ headsList s n ↔ (s.node n).heads x := by
  unfold headsList
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hI.headsLt h, h⟩⟩

/-- **Progress**: in every state of the extended system that is not converged, some policy
step is enabled. -/
theorem progressR {s : State} (h : RReachable N s) (hc : ¬ Converged N s) :
    ∃ s', PStepR N s s' := by
  have hI := invR_reachable h
  unfold Converged at hc
  rw [Classical.not_forall] at hc
  obtain ⟨n, hc⟩ := hc
  rw [Classical.not_imp] at hc
  obtain ⟨hn, hc⟩ := hc
  -- 1. merge
  by_cases hmulti : ∃ a b, (s.node n).heads a ∧ (s.node n).heads b ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := hmulti
    exact ⟨_, PStepR.merge s n (headsList s n) [] hn (fun x => mem_headsListR hI)
      ⟨a, b, (mem_headsListR hI).2 ha, (mem_headsListR hI).2 hb, hab⟩⟩
  -- 2. learn
  by_cases hk : (s.node n).known ≠ (s.hub.seq, s.hub.head)
  · exact ⟨_, PStepR.learn s n hn hk⟩
  have hk := Classical.not_not.1 hk
  have hk2 : (s.node n).known.2 = s.hub.head := by rw [hk]
  have hcons : Consistent s n := by
    unfold Consistent; rw [hk]; exact ⟨Nat.le_refl _, hI.histHead⟩
  -- 3. fetch and realize
  by_cases hnloc : ¬ (s.node n).lops (s.node n).known.2
  · have hloc := hnloc
    obtain ⟨x, ⟨hxa, hxl⟩, hmin⟩ := exists_min
      (fun x => Anc s.U.par x (s.node n).known.2 ∧ ¬ (s.node n).lops x)
      (a := (s.node n).known.2) ⟨Anc.refl, hloc⟩
    refine ⟨_, PStepR.realize s n x hn hcons hxa hxl (fun p hp => ?_)⟩
    refine Classical.byContradiction fun hpl => ?_
    exact hmin p (hI.parLt x p hp) ⟨(Anc.parent hp).trans hxa, hpl⟩
  have hloc := Classical.not_not.1 hnloc
  -- 4. advance
  by_cases hnadv : ¬ ∃ g, (s.node n).heads g ∧ Anc s.U.par (s.node n).known.2 g
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
  have hne : g ≠ (s.node n).known.2 := by
    intro e
    apply hc
    refine ⟨fun y => ?_, hk⟩
    rw [hsingle y, e, hk2]
  exact ⟨_, PStepR.pushAccept s n g hn hsingle hne hkg hk2.symm⟩

/-! ### Convergence -/

/-- Converged states enable no policy step. -/
theorem converged_quiescentR {s : State} (h : RReachable N s) (hc : Converged N s)
    {s' : State} : ¬ PStepR N s s' := by
  have hI := invR_reachable h
  intro hp
  cases hp with
  | learn n hn hs => exact hs (hc n hn).2
  | realize n x hn _ hx hnl hp =>
    rw [(hc n hn).2] at hx
    have hl : (s.node n).lops s.hub.head := hI.headsLocal n _ (((hc n hn).1 _).2 rfl)
    exact hnl (hI.lopsAnc hl hx)
  | advance n hn hk hna =>
    rw [(hc n hn).2] at hna
    exact hna ⟨_, ((hc n hn).1 _).2 rfl, Anc.refl⟩
  | merge n L O hn hL h2 =>
    obtain ⟨a, b, ha, hb, hab⟩ := h2
    exact hab ((((hc n hn).1 a).1 ((hL a).1 ha)).trans
      (((hc n hn).1 b).1 ((hL b).1 hb)).symm)
  | pushAccept n hd hn hh hne =>
    apply hne; rw [(hc n hn).2]; exact ((hc n hn).1 hd).1 ((hh hd).2 rfl)
  | pushIdem n hd hn hh hne =>
    apply hne; rw [(hc n hn).2]; exact ((hc n hn).1 hd).1 ((hh hd).2 rfl)
  | pushReject n hd hn hh hne =>
    apply hne; rw [(hc n hn).2]; exact ((hc n hn).1 hd).1 ((hh hd).2 rfl)

/-- A state of the extended system with no enabled policy step is converged, and
conversely. -/
theorem terminal_iff_convergedR {s : State} (h : RReachable N s) :
    (∀ s', ¬ PStepR N s s') ↔ Converged N s := by
  constructor
  · intro ht
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨s', hs'⟩ := progressR h hc
    exact ht s' hs'
  · intro hc s'
    exact converged_quiescentR h hc

/-- **A remade hive fills from its machines**: once converged, every operation any node
created is in `anc*(hub.head)`, however much the hub lost on the way. -/
theorem converged_all_acceptedR {s : State} (h : RReachable N s) (hc : Converged N s)
    {x : Nat} (hx : x < s.U.next) : Anc s.U.par x s.hub.head := by
  have hI := invR_reachable h
  by_cases hx0 : x = 0
  · subst hx0; exact hI.rootAnc _ hI.headLt
  · obtain ⟨n, hn, hcr⟩ := hI.creatorSome x (by omega) hx
    obtain ⟨g, hg, hA⟩ := hI.ownInHeads n x hx hcr
    rw [((hc n hn).1 g).1 hg] at hA
    exact hA

theorem PStepsR.head {s t u : State} (h1 : PStepR N s t) (h2 : PStepsR N t u) :
    PStepsR N s u := by
  induction h2 with
  | refl => exact PStepsR.tail (PStepsR.refl _) h1
  | tail _ hst ih => exact PStepsR.tail ih hst

/-- **Liveness** once the hub stops going back: from every state of the extended system,
policy steps reach a converged state. -/
theorem eventually_convergesR {s : State} (h : RReachable N s) :
    ∃ s', PStepsR N s s' ∧ Converged N s' := by
  refine WellFounded.induction (C := fun s => RReachable N s → ∃ s', PStepsR N s s' ∧
    Converged N s') (pstepR_wf (N := N)) s (fun s ih h => ?_) h
  by_cases hc : Converged N s
  · exact ⟨s, PStepsR.refl s, hc⟩
  · obtain ⟨s', hs'⟩ := progressR h hc
    obtain ⟨u, hu, huc⟩ := ih s' ⟨h, hs'⟩ (pstepR_reachable h hs')
    exact ⟨u, PStepsR.head hs' hu, huc⟩

/-- **Liveness**, maximal-run form: every policy run from a state of the extended system that
cannot be extended ends in a converged state. -/
theorem maximal_run_convergesR {s s' : State} (h : RReachable N s) (hr : PStepsR N s s')
    (hmax : ∀ s'', ¬ PStepR N s' s'') : Converged N s' :=
  (terminal_iff_convergedR (pstepsR_reachable h hr)).1 hmax

end Musubi

/-
Preservation of the invariant by sync actions and hub request handling.
-/
import Musubi.PreserveEnv

namespace Musubi

variable {N : Nat}

/-! ## Updating one node -/

section setNode

variable {s : State} {n : Nat} {nd : Node}

@[simp] theorem setNode_U : (s.setNode n nd).U = s.U := rfl
@[simp] theorem setNode_hub : (s.setNode n nd).hub = s.hub := rfl
@[simp] theorem setNode_net : (s.setNode n nd).net = s.net := rfl
@[simp] theorem setNode_self : (s.setNode n nd).node n = nd := by simp [State.setNode]
theorem setNode_ne {i : Nat} (h : i ≠ n) : (s.setNode n nd).node i = s.node i := by
  simp [State.setNode, h]

end setNode

section simpLemmas

variable {s : State} {m : Msg} {S : OSet} {sq h : Nat}

@[simp] theorem send_U : (s.send m).U = s.U := rfl
@[simp] theorem send_hub : (s.send m).hub = s.hub := rfl
@[simp] theorem send_node : (s.send m).node = s.node := rfl
@[simp] theorem hubStoreOps_U : (s.hubStoreOps S).U = s.U := rfl
@[simp] theorem hubStoreOps_node : (s.hubStoreOps S).node = s.node := rfl
@[simp] theorem hubStoreOps_head : (s.hubStoreOps S).hub.head = s.hub.head := rfl
@[simp] theorem hubStoreOps_seq : (s.hubStoreOps S).hub.seq = s.hub.seq := rfl
@[simp] theorem hubStoreObjs_U : (s.hubStoreObjs S).U = s.U := rfl
@[simp] theorem hubStoreObjs_node : (s.hubStoreObjs S).node = s.node := rfl
@[simp] theorem hubStoreObjs_head : (s.hubStoreObjs S).hub.head = s.hub.head := rfl
@[simp] theorem hubStoreObjs_seq : (s.hubStoreObjs S).hub.seq = s.hub.seq := rfl
@[simp] theorem notifyAll_U : (s.notifyAll sq h).U = s.U := rfl
@[simp] theorem notifyAll_hub : (s.notifyAll sq h).hub = s.hub := rfl
@[simp] theorem notifyAll_node : (s.notifyAll sq h).node = s.node := rfl

end simpLemmas

/-- The per-node part of the invariant, for a candidate new state `nd` of node `n`. -/
structure NodeOK (N : Nat) (s : State) (n : Nat) (nd : Node) : Prop where
  lroot : nd.lops root
  lLt : ∀ x, nd.lops x → x < s.U.next
  lParents : ∀ x p, nd.lops x → p ∈ s.U.par x → nd.lops p
  lObjs : ∀ x o, nd.lops x → o ∈ s.U.objs x → nd.lobj o
  headsLocal : ∀ x, nd.heads x → nd.lops x
  headsAnti : ∀ x y, nd.heads x → nd.heads y → Anc s.U.par x y → x = y
  headsNonempty : ∃ h, nd.heads h
  known : nd.known.1 ≤ s.hub.seq ∧ s.hub.hist nd.known.1 = nd.known.2
  locality : ∀ x, nd.lops x → s.U.creator x = some n ∨ Anc s.U.par x s.hub.head
  staged : ∀ x, nd.sops x → Anc s.U.par x s.hub.head
  ownInHeads : ∀ x, x < s.U.next → s.U.creator x = some n →
    ∃ h, nd.heads h ∧ Anc s.U.par x h
  accHeads : ∀ x y, nd.heads x → nd.heads y →
    Anc s.U.par x s.hub.head → Anc s.U.par y s.hub.head → x = y
  comparable : ∀ x i, nd.heads x → Anc s.U.par x s.hub.head → i ≤ s.hub.seq →
    Anc s.U.par x (s.hub.hist i) ∨ Anc s.U.par (s.hub.hist i) x
  /-- `anc*(heads)` only grows. -/
  headsMono : ∀ d h, (s.node n).heads h → Anc s.U.par d h →
    ∃ h', nd.heads h' ∧ Anc s.U.par d h'

theorem Inv.nodeOK {s : State} (hI : Inv N s) (n : Nat) : NodeOK N s n (s.node n) where
  lroot := hI.lroot n
  lLt := hI.lLt n
  lParents := hI.lParents n
  lObjs := hI.lObjs n
  headsLocal := hI.headsLocal n
  headsAnti := hI.headsAnti n
  headsNonempty := hI.headsNonempty n
  known := hI.known n
  locality := hI.locality n
  staged := hI.staged n
  ownInHeads := hI.ownInHeads n
  accHeads := hI.accHeads n
  comparable := hI.comparable n
  headsMono := fun _ h hh hA => ⟨h, hh, hA⟩

theorem inv_setNode {s : State} {n : Nat} {nd : Node} (hI : Inv N s) (h : NodeOK N s n nd) :
    Inv N (s.setNode n nd) := by
  refine
    { hI with
      lroot := ?_, lLt := ?_, lParents := ?_, lObjs := ?_, headsLocal := ?_,
      headsAnti := ?_, headsNonempty := ?_, known := ?_, locality := ?_, staged := ?_,
      ownInHeads := ?_, accHeads := ?_, comparable := ?_, msgs := ?_ }
  all_goals first
    | (intro i
       by_cases hi : i = n
       · subst hi; simp only [setNode_self, setNode_U, setNode_hub]
         first
           | exact h.lroot | exact h.lLt | exact h.lParents | exact h.lObjs
           | exact h.headsLocal | exact h.headsAnti | exact h.headsNonempty | exact h.known
           | exact h.locality | exact h.staged | exact h.ownInHeads | exact h.accHeads
           | exact h.comparable
       · rw [setNode_ne hi]
         first
           | exact hI.lroot i | exact hI.lLt i | exact hI.lParents i | exact hI.lObjs i
           | exact hI.headsLocal i | exact hI.headsAnti i | exact hI.headsNonempty i
           | exact hI.known i | exact hI.locality i | exact hI.staged i
           | exact hI.ownInHeads i | exact hI.accHeads i | exact hI.comparable i)
    | skip
  -- remaining: messages
  intro m hm
  have hm' := hI.msgs m hm
  cases m with
  | cas i e d =>
    simp only [MsgOK, setNode_U, setNode_hub] at hm' ⊢
    rcases hm' with ⟨g, hg, hA⟩ | hA
    · by_cases hi : i = n
      · subst hi; simp only [setNode_self]; exact Or.inl (h.headsMono d g hg hA)
      · rw [setNode_ne hi]; exact Or.inl ⟨g, hg, hA⟩
    · exact Or.inr hA
  | getOps => exact hm'
  | ops => exact hm'
  | head => exact hm'
  | getHead => trivial
  | putOps => trivial
  | putObjs => trivial
  | getObjs => trivial
  | objs => trivial
  | stored => trivial

/-! ## Node-local sync actions -/

theorem inv_learn {s : State} (hI : Inv N s) {n : Nat} {k : HeadKind} {sq h : Nat}
    (hm : s.net (.head n k sq h)) : Inv N (s.learn n sq h) :=
  inv_setNode hI { hI.nodeOK n with known := hI.msgs _ hm }

theorem inv_recvOps {s : State} (hI : Inv N s) {n : Nat} {S : OSet}
    (hm : s.net (.ops n S)) : Inv N (s.recvOps n S) := by
  refine inv_setNode hI { hI.nodeOK n with staged := ?_ }
  rintro x (hx | hx)
  · exact hI.staged n x hx
  · exact hI.msgs _ hm x hx

theorem inv_recvObjs {s : State} (hI : Inv N s) {n : Nat} {S : OSet} :
    Inv N (s.recvObjs n S) :=
  inv_setNode hI { hI.nodeOK n with }

theorem inv_realize {s : State} (hI : Inv N s) {n x : Nat} (hx : (s.node n).sops x)
    (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) :
    Inv N (s.realize n x) := by
  have hxa := hI.staged n x hx
  refine inv_setNode hI
    { hI.nodeOK n with
      lroot := Or.inl (hI.lroot n), lLt := ?_, lParents := ?_, lObjs := ?_,
      headsLocal := fun y hy => Or.inl (hI.headsLocal n y hy), locality := ?_ }
  · rintro y (hy | rfl)
    · exact hI.lLt n y hy
    · exact hI.accLt hxa
  · rintro y q (hy | rfl) hq
    · exact Or.inl (hI.lParents n y q hy hq)
    · exact Or.inl (hp q hq)
  · rintro y o (hy | rfl) ho
    · exact Or.inl (hI.lObjs n y o hy ho)
    · exact Or.inr ho
  · rintro y (hy | rfl)
    · exact hI.locality n y hy
    · exact Or.inr hxa

/-- Characterization of `max(heads ∪ {k})` when `k ∉ anc*(heads)`. -/
theorem advance_heads_iff {s : State} (hI : Inv N s) {n : Nat}
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) {y : Nat} :
    maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) y ↔
      y = (s.node n).known.2 ∨ ((s.node n).heads y ∧ ¬ Anc s.U.par y (s.node n).known.2) := by
  constructor
  · rintro ⟨hy, hmax⟩
    rcases hy with hy | hy
    · by_cases hk : y = (s.node n).known.2
      · exact Or.inl hk
      · exact Or.inr ⟨hy, fun hA => hk (hmax _ (Or.inr rfl) hA)⟩
    · exact Or.inl hy
  · rintro (rfl | ⟨hy, hnk⟩)
    · refine ⟨Or.inr rfl, fun z hz hA => ?_⟩
      rcases hz with hz | hz
      · exact absurd ⟨z, hz, hA⟩ hna
      · exact hz.symm
    · refine ⟨Or.inl hy, fun z hz hA => ?_⟩
      rcases hz with hz | hz
      · exact hI.headsAnti n y z hy hz hA
      · subst hz; exact absurd hA hnk

theorem inv_advance {s : State} (hI : Inv N s) {n : Nat}
    (hk : (s.node n).lops (s.node n).known.2)
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
    Inv N (s.advance n) := by
  have H := fun y => advance_heads_iff (y := y) hI hna
  have hka := hI.knownAnc n
  -- an accepted old head that survives is impossible
  have oldAcc : ∀ y, (s.node n).heads y → ¬ Anc s.U.par y (s.node n).known.2 →
      ¬ Anc s.U.par y s.hub.head := by
    intro y hy hnk hya
    rcases hI.comparable n y _ hy hya (hI.known n).1 with h | h
    · rw [(hI.known n).2] at h; exact hnk h
    · rw [(hI.known n).2] at h; exact hna ⟨y, hy, h⟩
  refine inv_setNode hI
    { hI.nodeOK n with
      headsLocal := ?_, headsAnti := ?_, headsNonempty := ?_, ownInHeads := ?_,
      accHeads := ?_, comparable := ?_, headsMono := ?_ }
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
  · intro x y hx hy hxa hya
    have hx' : x = (s.node n).known.2 := by
      rcases (H x).1 hx with h | ⟨h1, h2⟩
      · exact h
      · exact absurd hxa (oldAcc x h1 h2)
    have hy' : y = (s.node n).known.2 := by
      rcases (H y).1 hy with h | ⟨h1, h2⟩
      · exact h
      · exact absurd hya (oldAcc y h1 h2)
    rw [hx', hy']
  · intro x i hx hxa hi
    rcases (H x).1 hx with rfl | ⟨h1, h2⟩
    · rw [← (hI.known n).2]
      rcases Nat.le_total (s.node n).known.1 i with h | h
      · exact Or.inl (hI.chain h hi)
      · exact Or.inr (hI.chain h (hI.known n).1)
    · exact absurd hxa (oldAcc x h1 h2)
  · intro d h hh hA
    by_cases hhk : Anc s.U.par h (s.node n).known.2
    · exact ⟨_, (H _).2 (Or.inl rfl), hA.trans hhk⟩
    · exact ⟨h, (H h).2 (Or.inr ⟨hh, hhk⟩), hA⟩

/-! ## Hub storage -/

theorem inv_hubStoreOps {s : State} (hI : Inv N s) {S : OSet} : Inv N (s.hubStoreOps S) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨Or.inl h1, h2⟩ }

theorem inv_hubStoreObjs {s : State} (hI : Inv N s) {S : OSet} : Inv N (s.hubStoreObjs S) :=
  { hI with
    hubClosed := fun y hy => by
      obtain ⟨h1, h2⟩ := hI.hubClosed y hy
      exact ⟨h1, fun o ho => Or.inl (h2 o ho)⟩ }

/-! ## Cas acceptance -/

section accept

variable {s : State} {d : Nat}

@[simp] theorem hubAccept_U : (s.hubAccept d).U = s.U := rfl
@[simp] theorem hubAccept_node : (s.hubAccept d).node = s.node := rfl
@[simp] theorem hubAccept_net : (s.hubAccept d).net = s.net := rfl
@[simp] theorem hubAccept_head : (s.hubAccept d).hub.head = d := rfl
@[simp] theorem hubAccept_seq : (s.hubAccept d).hub.seq = s.hub.seq + 1 := rfl
@[simp] theorem hubAccept_hist :
    (s.hubAccept d).hub.hist = upd s.hub.hist (s.hub.seq + 1) d := rfl
@[simp] theorem hubAccept_ops : (s.hubAccept d).hub.ops = s.hub.ops := rfl
@[simp] theorem hubAccept_objs : (s.hubAccept d).hub.objs = s.hub.objs := rfl

end accept

/-- The heart of `MergeOwnership`: a head of node `n` that becomes accepted when the hub
accepts `Cas(e, d)` from node `n0` is `d` itself. -/
theorem newly_accepted_head {s : State} (hI : Inv N s) {n0 e d : Nat}
    (hm : s.net (.cas n0 e d)) (he : s.hub.head = e) {n x : Nat}
    (hx : (s.node n).heads x) (hxd : Anc s.U.par x d) (hxe : ¬ Anc s.U.par x e) : x = d := by
  have hm' : MsgOK s (.cas n0 e d) := hI.msgs _ hm
  simp only [MsgOK] at hm'
  rcases hm' with ⟨g, hg, hdg⟩ | hde
  · -- x is local at n0, unaccepted, so created by n0; and created by n
    have hxl0 : (s.node n0).lops x := hI.lopsAnc (hI.headsLocal n0 g hg) (hxd.trans hdg)
    rw [← he] at hxe
    have c0 := hI.ownOfUnacc hxl0 hxe
    have c1 := hI.ownOfUnacc (hI.headsLocal n x hx) hxe
    rw [c0] at c1
    cases c1
    have hxg : x = g := hI.headsAnti n0 x g hx hg (hxd.trans hdg)
    subst hxg
    exact Anc.antisymm hI.parLt hxd hdg
  · rw [he] at hde
    exact absurd (hxd.trans hde) hxe

theorem inv_casAccept {s : State} (hI : Inv N s) {n0 e d : Nat}
    (hm : s.net (.cas n0 e d)) (hne : s.hub.head ≠ d) (he : s.hub.head = e)
    (ha : Anc s.U.par e d) (hc : ClosedAt s d) :
    Inv N (((s.hubAccept d).send (.head n0 .accepted (s.hub.seq + 1) d)).notifyAll
      (s.hub.seq + 1) d) := by
  have hed : Anc s.U.par s.hub.head d := he ▸ ha
  have grow : ∀ {x}, Anc s.U.par x s.hub.head → Anc s.U.par x d := fun h => h.trans hed
  have hdlt : d < s.U.next := by
    have hm' : MsgOK s (.cas n0 e d) := hI.msgs _ hm
    simp only [MsgOK] at hm'
    rcases hm' with ⟨g, hg, hdg⟩ | hde
    · exact Nat.lt_of_le_of_lt (hdg.le hI.parLt) (hI.headsLt hg)
    · exact hI.accLt hde
  have histOld : ∀ {i}, i ≤ s.hub.seq → upd s.hub.hist (s.hub.seq + 1) d i = s.hub.hist i :=
    fun hi => upd_ne _ _ (by omega)
  -- new accepted heads are `d`
  have newAcc : ∀ n x, (s.node n).heads x → Anc s.U.par x d →
      Anc s.U.par x s.hub.head ∨ x = d := by
    intro n x hx hxd
    by_cases hxe : Anc s.U.par x s.hub.head
    · exact Or.inl hxe
    · exact Or.inr (newly_accepted_head hI hm he hx hxd (he ▸ hxe))
  -- the post-state, field by field
  refine
    { parLt := hI.parLt, nextPos := hI.nextPos, rootAnc := hI.rootAnc,
      creatorSome := hI.creatorSome, headLt := hdlt, histHead := ?_, hist0 := ?_,
      histStep := ?_, hubClosed := hc, lroot := hI.lroot, lLt := hI.lLt,
      lParents := hI.lParents, lObjs := hI.lObjs, headsLocal := hI.headsLocal,
      headsAnti := hI.headsAnti, headsNonempty := hI.headsNonempty, known := ?_,
      locality := ?_, staged := ?_, ownInHeads := hI.ownInHeads, accHeads := ?_,
      comparable := ?_, mergeOwn := ?_, mergeForeign := ?_, birthLe := ?_,
      birthMono := hI.birthMono, creatorRoot := hI.creatorRoot, msgs := ?_ }
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
  · intro n
    show (s.node n).known.1 ≤ s.hub.seq + 1 ∧
      upd s.hub.hist (s.hub.seq + 1) d (s.node n).known.1 = (s.node n).known.2
    rw [histOld (hI.known n).1]
    exact ⟨Nat.le_succ_of_le (hI.known n).1, (hI.known n).2⟩
  · intro n x hx
    rcases hI.locality n x hx with h | h
    · exact Or.inl h
    · exact Or.inr (grow h)
  · intro n x hx; exact grow (hI.staged n x hx)
  · intro n x y hx hy hxa hya
    have hxa' : Anc s.U.par x d := hxa
    have hya' : Anc s.U.par y d := hya
    rcases newAcc n x hx hxa' with hx1 | hx1 <;> rcases newAcc n y hy hya' with hy1 | hy1
    · exact hI.accHeads n x y hx hy hx1 hy1
    · subst hy1; exact hI.headsAnti n x y hx hy (grow hx1)
    · subst hx1; exact (hI.headsAnti n y x hy hx (grow hy1)).symm
    · rw [hx1, hy1]
  · intro n x i hx hxa hi
    have hxa' : Anc s.U.par x d := hxa
    have hi' : i ≤ s.hub.seq + 1 := hi
    show Anc s.U.par x (upd s.hub.hist (s.hub.seq + 1) d i) ∨
      Anc s.U.par (upd s.hub.hist (s.hub.seq + 1) d i) x
    by_cases his : i = s.hub.seq + 1
    · subst his; rw [upd_same]; exact Or.inl hxa'
    · rw [histOld (by omega)]
      rcases newAcc n x hx hxa' with hx1 | hx1
      · exact hI.comparable n x i hx hx1 (by omega)
      · subst hx1; exact Or.inr (grow (hI.histAnc (by omega)))
  · intro m hm hmg
    show ∃ p ∈ s.U.par m, s.U.creator p = s.U.creator m ∧
      ¬ Anc s.U.par p (upd s.hub.hist (s.hub.seq + 1) d (s.U.birth m))
    rw [histOld (hI.birthLe m hm)]
    exact hI.mergeOwn m hm hmg
  · intro m hm hmg p hp hcr
    show Anc s.U.par p (upd s.hub.hist (s.hub.seq + 1) d (s.U.birth m))
    rw [histOld (hI.birthLe m hm)]
    exact hI.mergeForeign m hm hmg p hp hcr
  · intro m hm
    exact Nat.le_succ_of_le (hI.birthLe m hm)
  · intro msg hmsg
    rcases hmsg with (hmsg | hmsg) | ⟨i, hmsg⟩
    · have h' := hI.msgs msg hmsg
      cases msg with
      | getOps i S => intro x hx; exact grow (h' x hx)
      | ops i S => intro x hx; exact grow (h' x hx)
      | cas i e' d' =>
        simp only [MsgOK] at h' ⊢
        rcases h' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (grow h1)
      | head i k sq h =>
        simp only [MsgOK] at h' ⊢
        refine ⟨Nat.le_succ_of_le h'.1, ?_⟩
        show upd s.hub.hist (s.hub.seq + 1) d sq = h
        rw [histOld h'.1]; exact h'.2
      | getHead => trivial
      | putOps => trivial
      | putObjs => trivial
      | getObjs => trivial
      | objs => trivial
      | stored => trivial
    · subst hmsg
      show s.hub.seq + 1 ≤ s.hub.seq + 1 ∧ upd s.hub.hist (s.hub.seq + 1) d (s.hub.seq + 1) = d
      simp
    · subst hmsg
      show s.hub.seq + 1 ≤ s.hub.seq + 1 ∧ upd s.hub.hist (s.hub.seq + 1) d (s.hub.seq + 1) = d
      simp

/-! ## All steps -/

theorem MsgOK_headNow {s : State} (hI : Inv N s) (n : Nat) (k : HeadKind) :
    MsgOK s (.head n k s.hub.seq s.hub.head) :=
  ⟨Nat.le_refl _, hI.histHead⟩

theorem inv_syncStep {s s' : State} (hI : Inv N s) (h : SyncStep N s s') : Inv N s' := by
  cases h with
  | getHead n hn => exact hI.send trivial
  | learn n k sq h hn hm hs => exact inv_learn hI hm
  | learnUnfiltered n k sq h hn hm => exact inv_learn hI hm
  | fetchOps n S hn hS => exact hI.send (fun x hx => (hS x hx).trans (hI.knownAnc n))
  | fetchObjs n S hn => exact hI.send trivial
  | recvOps n S hn hm => exact inv_recvOps hI hm
  | recvObjs n S hn hm => exact inv_recvObjs hI
  | realize n x hn hx hp ho => exact inv_realize hI hx hp
  | advance n hn hk hna => exact inv_advance hI hk hna
  | uploadOps n S hn hS => exact hI.send trivial
  | uploadObjs n S hn hS => exact hI.send trivial
  | push n e d hn hd =>
    refine hI.send ?_
    show (∃ h, (s.node n).heads h ∧ Anc s.U.par d h) ∨ Anc s.U.par d s.hub.head
    rcases hI.locality n d hd with hc | hA
    · exact Or.inl (hI.ownInHeads n d (hI.lLt n d hd) hc)
    · exact Or.inr hA
  | crashNode n hn => exact hI
  | loseKnown n hn =>
    exact inv_setNode hI { hI.nodeOK n with known := ⟨Nat.zero_le _, hI.hist0⟩ }
  | loseVolatile n hn =>
    refine inv_setNode hI { hI.nodeOK n with known := ?_, staged := ?_ }
    · exact ⟨Nat.zero_le _, hI.hist0⟩
    · intro x hx; exact hx.elim
  | hubGetHead n hm => exact hI.send (MsgOK_headNow hI n _)
  | hubPutOps n S hm => exact (inv_hubStoreOps hI).send trivial
  | hubPutObjs n S hm => exact (inv_hubStoreObjs hI).send trivial
  | hubGetOps n S hm =>
    refine hI.send ?_
    intro x hx
    exact (hI.msgs _ hm : MsgOK s (.getOps n S)) x hx.1
  | hubGetObjs n S hm => exact hI.send trivial
  | casIdem n e d hm hh => exact hI.send (MsgOK_headNow hI n _)
  | casAccept n e d hm hne he ha hc => exact inv_casAccept hI hm hne he ha hc
  | casReject n e d hm hne hrej => exact hI.send (MsgOK_headNow hI n _)
  | crashHub => exact hI
  | hubForget O J hO hJ hc => exact { hI with hubClosed := hc }

theorem inv_envStep {s s' : State} (hI : Inv N s) (h : EnvStep N s s') : Inv N s' := by
  cases h with
  | userOp n p O hn hp => exact inv_userOp hI hn hp
  | merge n L O hn hL h2 => exact inv_merge hI hn hL h2

theorem inv_step {s s' : State} (hI : Inv N s) (h : Step N s s') : Inv N s' := by
  rcases h with h | h
  · exact inv_envStep hI h
  · exact inv_syncStep hI h

theorem inv_reachable {s : State} (h : Reachable N s) : Inv N s := by
  induction h with
  | init => exact inv_init N
  | step _ hst ih => exact inv_step ih hst

end Musubi

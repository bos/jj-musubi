/-
Safety facts that do not require accepted original heads to form an ancestry chain.
The existing SInv implies this view, but a surviving-image advance and a Below acceptance
need not preserve InvR.histStep. Network custody and concrete-name equality are separate
obligations; this file does not claim a complete protocol refinement.
-/
import Musubi.SurvivorAdvance
import Musubi.RetryControl

namespace Musubi.Contracted

open Contract

/-- The graph and stores viewed under each party's own contraction. The network and history
in `base` are retained, but no original-history-chain invariant is imposed on this view. -/
structure View where
  base : State
  hubD : Nat → Bool
  nodeD : Nat → Nat → Bool

/-- A store contains the surviving ancestors of each operation it contains. Dropped original
bodies may remain cached; membership alone does not make a dropped operation an op head. -/
def Closed (par : Nat → List Nat) (D : Nat → Bool) (ops : OSet) : Prop :=
  ∀ x a, ops x → Anc par a x → D a = false → ops a

structure Safe (v : View) : Prop where
  parLt : ParLt v.base.U.par
  nextPos : 0 < v.base.U.next
  rootAnc : ∀ x, x < v.base.U.next → Anc v.base.U.par root x
  hubRoot : v.hubD root = false
  nodeRoot : ∀ n, v.nodeD n root = false
  hubDropLt : ∀ x, v.hubD x = true → x < v.base.U.next
  nodeDropLt : ∀ n x, v.nodeD n x = true → x < v.base.U.next
  headLt : v.base.hub.head < v.base.U.next
  hubOpsLt : ∀ x, v.base.hub.ops x → x < v.base.U.next
  headSurvives : v.hubD v.base.hub.head = false
  /-- Only the current hub head's contracted closure is required, not every cached body. -/
  hubClosed : ∀ a, Anc v.base.U.par a v.base.hub.head → v.hubD a = false →
    HubHas v.base a
  localLt : ∀ n x, (v.base.node n).lops x → x < v.base.U.next
  localClosed : ∀ n, Closed v.base.U.par (v.nodeD n) (v.base.node n).lops
  localObjects : ∀ n x o, (v.base.node n).lops x → o ∈ v.base.U.objs x →
    (v.base.node n).lobj o
  headsLocal : ∀ n x, (v.base.node n).heads x → (v.base.node n).lops x
  headsSurvive : ∀ n x, (v.base.node n).heads x → v.nodeD n x = false
  headsAnti : ∀ n x y, (v.base.node n).heads x → (v.base.node n).heads y →
    Anc v.base.U.par x y → x = y
  headsNonempty : ∀ n, ∃ h, (v.base.node n).heads h

noncomputable def ofSState (s : SState) : View := by
  classical
  exact ⟨s.s, fun x => decide (s.hubD x), fun n x => decide (s.nodeD n x)⟩

/-- The legacy invariant is a strictly stronger source of these common facts. In particular,
this implication does not transfer its original-head-chain theorem to new transitions. -/
theorem safe_of_sinv (h : SInv N s) : Safe (ofSState s) := by
  classical
  refine {
    parLt := h.base.parLt
    nextPos := h.base.nextPos
    rootAnc := h.base.rootAnc
    hubRoot := ?_
    nodeRoot := ?_
    hubDropLt := by
      intro x hx
      exact (h.hub x (by simpa [ofSState] using hx)).2.1
    nodeDropLt := by
      intro n x hx
      exact (h.node n x (by simpa [ofSState] using hx)).2.1
    headLt := h.base.headLt
    hubOpsLt := h.base.hubOpsLt
    headSurvives := ?_
    hubClosed := ?_
    localLt := h.base.lLt
    localClosed := ?_
    localObjects := h.base.lObjs
    headsLocal := h.base.headsLocal
    headsSurvive := ?_
    headsAnti := h.base.headsAnti
    headsNonempty := h.base.headsNonempty }
  · simpa [ofSState] using (show ¬ s.hubD root from fun hr => (h.hub root hr).1 rfl)
  · intro n
    simpa [ofSState] using
      (show ¬ s.nodeD n root from fun hr => (h.node n root hr).1 rfl)
  · simpa [ofSState] using h.headOK
  · intro a ha _
    exact h.base.hubClosed a ha
  · intro n x a hx hax _
    exact Anc.closed (h.base.lParents n) hax hx
  · intro n x hx
    simpa [ofSState] using h.headsOK n x hx

def View.frontier (v : View) (n : Nat) (H : OSet) : View :=
  { v with base := v.base.setNode n { v.base.node n with heads := H } }

/-- A frontier replacement changes no stored body or object. The new frontier must consist
of local survivors, be an antichain, and remain nonempty. -/
theorem safe_frontier (h : Safe v)
    (hl : ∀ x, H x → (v.base.node n).lops x)
    (hs : ∀ x, H x → v.nodeD n x = false)
    (ha : ∀ x y, H x → H y → Anc v.base.U.par x y → x = y)
    (hne : ∃ x, H x) : Safe (v.frontier n H) := by
  have hn : (v.frontier n H).base.node n = { v.base.node n with heads := H } := by
    simp [View.frontier, State.setNode]
  have ho : ∀ m, m ≠ n → (v.frontier n H).base.node m = v.base.node m := by
    intro m hm; simp [View.frontier, State.setNode, hm]
  have hloc : ∀ m, ((v.frontier n H).base.node m).lops = (v.base.node m).lops := by
    intro m
    by_cases hm : m = n
    · subst m; rw [hn]
    · rw [ho m hm]
  have hobj : ∀ m, ((v.frontier n H).base.node m).lobj = (v.base.node m).lobj := by
    intro m
    by_cases hm : m = n
    · subst m; rw [hn]
    · rw [ho m hm]
  refine { h with
    localLt := ?_, localClosed := ?_, localObjects := ?_,
    headsLocal := ?_, headsSurvive := ?_, headsAnti := ?_, headsNonempty := ?_ }
  · intro m x hx; exact h.localLt m x (by rwa [hloc] at hx)
  · intro m x a hx hax hd
    rw [hloc]
    exact h.localClosed m x a (by rwa [hloc] at hx) hax hd
  · intro m x o hx hob
    rw [hobj]
    exact h.localObjects m x o (by rwa [hloc] at hx) hob
  · intro m x hx
    rw [hloc]
    by_cases hm : m = n
    · subst m; rw [hn] at hx; exact hl x hx
    · rw [ho m hm] at hx; exact h.headsLocal m x hx
  · intro m x hx
    by_cases hm : m = n
    · subst m; rw [hn] at hx; exact hs x hx
    · rw [ho m hm] at hx; exact h.headsSurvive m x hx
  · intro m x y hx hy hxy
    by_cases hm : m = n
    · subst m; rw [hn] at hx hy; exact ha x y hx hy hxy
    · rw [ho m hm] at hx hy; exact h.headsAnti m x y hx hy hxy
  · intro m
    by_cases hm : m = n
    · subst m; rw [hn]; exact hne
    · rw [ho m hm]; exact h.headsNonempty m

def View.advanceImages (v : View) (n known : Nat) : View :=
  { v with base := v.base.setNode n { v.base.node n with
      heads := maxSet v.base.U.par (fun x => (v.base.node n).heads x ∨
        x ∈ exp v.base.U.par (v.nodeD n) known) } }

/-- Survivor-image advancement preserves the common store/head invariant. Every new image
must already be local, which is exactly the backend's dropped-head locality contract. -/
theorem safe_advanceImages (h : Safe v) (hk : known < v.base.U.next)
    (hl : ∀ p ∈ exp v.base.U.par (v.nodeD n) known, (v.base.node n).lops p) :
    Safe (v.advanceImages n known) := by
  have hm : ∀ x, ((v.advanceImages n known).base.node n).heads x ↔
      maxSet v.base.U.par (fun x => (v.base.node n).heads x ∨
        x ∈ exp v.base.U.par (v.nodeD n) known) x := by
    intro x
    simp [View.advanceImages, State.setNode]
  have hn : ∀ m, m ≠ n → (v.advanceImages n known).base.node m = v.base.node m := by
    intro m hmn
    simp [View.advanceImages, State.setNode, hmn]
  have hlo : ∀ m, ((v.advanceImages n known).base.node m).lops = (v.base.node m).lops := by
    intro m
    by_cases he : m = n
    · subst m; simp [View.advanceImages, State.setNode]
    · rw [hn m he]
  have hobj : ∀ m, ((v.advanceImages n known).base.node m).lobj = (v.base.node m).lobj := by
    intro m
    by_cases he : m = n
    · subst m; simp [View.advanceImages, State.setNode]
    · rw [hn m he]
  refine { h with
    localLt := ?_
    localClosed := ?_
    localObjects := ?_
    headsLocal := ?_
    headsSurvive := ?_
    headsAnti := ?_
    headsNonempty := ?_ }
  · intro m x hx
    change x < v.base.U.next
    exact h.localLt m x (by rwa [← hlo m])
  · intro m x a hx hax ha
    rw [hlo m]
    exact h.localClosed m x a (by rwa [← hlo m]) hax ha
  · intro m x o hx ho
    rw [hobj m]
    exact h.localObjects m x o (by rwa [← hlo m]) ho
  · intro m x hx
    by_cases he : m = n
    · subst m
      have hx := ((hm x).1 hx).1
      rw [hlo n]
      exact hx.elim (h.headsLocal n x) (hl x)
    · rw [hn m he] at hx
      rw [hlo m]
      exact h.headsLocal m x hx
  · intro m x hx
    by_cases he : m = n
    · subst m
      have hx := ((hm x).1 hx).1
      exact hx.elim (h.headsSurvive n x) (fun hx => (mem_exp h.parLt hx).1)
    · rw [hn m he] at hx
      exact h.headsSurvive m x hx
  · intro m x y hx hy hxy
    by_cases he : m = n
    · subst m
      exact ((hm x).1 hx).2 y ((hm y).1 hy).1 hxy
    · rw [hn m he] at hx hy
      exact h.headsAnti m x y hx hy hxy
  · intro m
    by_cases he : m = n
    · subst m
      obtain ⟨x, hx⟩ := h.headsNonempty n
      have hb : ∀ y, (v.base.node n).heads y ∨
          y ∈ exp v.base.U.par (v.nodeD n) known → y < v.base.U.next := by
        intro y hy
        exact hy.elim (fun hy => h.localLt n y (h.headsLocal n y hy))
          (fun hy => Nat.lt_of_le_of_lt ((mem_exp h.parLt hy).2.le h.parLt) hk)
      obtain ⟨y, hy, _⟩ := below_max h.parLt hb (Or.inl hx)
      exact ⟨y, (hm y).2 hy⟩
    · obtain ⟨x, hx⟩ := h.headsNonempty m
      exact ⟨x, by rwa [hn m he]⟩

def View.merge (v : View) (n : Nat) (L O : List Nat) : View :=
  { v with base := v.base.mergeOp n L O }

/-- A full-frontier merge is ordinary operation creation after the image advance. The
fresh original survives every existing dropped set, and its required objects are local. -/
theorem safe_merge (h : Safe v)
    (hL : ∀ x, x ∈ L ↔ (v.base.node n).heads x) : Safe (v.merge n L O) := by
  let o := v.base.U.next
  have hl : ∀ p ∈ L, (v.base.node n).lops p := fun p hp => h.headsLocal n p ((hL p).1 hp)
  have hb : ∀ p ∈ L, p < o := fun p hp => h.localLt n p (hl p hp)
  have hlt := parLt_upd h.parLt hb
  have hnode : (v.merge n L O).base.node n =
      { v.base.node n with
        lops := fun x => (v.base.node n).lops x ∨ x = o
        lobj := fun x => (v.base.node n).lobj x ∨ x ∈ O
        heads := (· = o) } := by
    simp [View.merge, State.mergeOp, State.createOp, o]
  have hother : ∀ m, m ≠ n → (v.merge n L O).base.node m = v.base.node m := by
    intro m hm
    simp [View.merge, State.mergeOp, State.createOp, hm]
  have hold : ∀ {a x}, x < o → Anc (upd v.base.U.par o L) a x → Anc v.base.U.par a x :=
    fun hx ha => (anc_upd_iff h.parLt hb hx).1 ha
  have hobj : ∀ x, x < o → (v.merge n L O).base.U.objs x = v.base.U.objs x := by
    intro x hx
    exact upd_ne _ _ (Nat.ne_of_lt hx)
  have hd : v.nodeD n o = false := by
    cases he : v.nodeD n o
    · rfl
    · have := h.nodeDropLt n o he
      exact False.elim (Nat.lt_irrefl o this)
  refine {
    parLt := hlt
    nextPos := Nat.lt_trans h.nextPos (Nat.lt_succ_self _)
    rootAnc := ?_
    hubRoot := h.hubRoot
    nodeRoot := h.nodeRoot
    hubDropLt := fun x hx => Nat.lt_trans (h.hubDropLt x hx) (Nat.lt_succ_self _)
    nodeDropLt := fun m x hx => Nat.lt_trans (h.nodeDropLt m x hx) (Nat.lt_succ_self _)
    headLt := Nat.lt_trans h.headLt (Nat.lt_succ_self _)
    hubOpsLt := fun x hx => Nat.lt_trans (h.hubOpsLt x hx) (Nat.lt_succ_self _)
    headSurvives := h.headSurvives
    hubClosed := ?_
    localLt := ?_
    localClosed := ?_
    localObjects := ?_
    headsLocal := ?_
    headsSurvive := ?_
    headsAnti := ?_
    headsNonempty := ?_ }
  · intro x hx
    change x < o + 1 at hx
    change Anc (upd v.base.U.par o L) root x
    by_cases he : x = o
    · subst x
      obtain ⟨p, hp⟩ := h.headsNonempty n
      exact (anc_upd_new h.parLt hb).2
        (Or.inr ⟨p, (hL p).2 hp, h.rootAnc p (h.localLt n p (h.headsLocal n p hp))⟩)
    · exact (anc_upd_iff h.parLt hb (by omega)).2 (h.rootAnc x (by omega))
  · intro a ha hs
    have hao := hold h.headLt ha
    obtain ⟨hop, hob⟩ := h.hubClosed a hao hs
    refine ⟨hop, ?_⟩
    intro obj ho
    rw [hobj a (Nat.lt_of_le_of_lt (hao.le h.parLt) h.headLt)] at ho
    exact hob obj ho
  · intro m x hx
    by_cases he : m = n
    · subst m
      rw [hnode] at hx
      rcases hx with hx | rfl
      · exact Nat.lt_trans (h.localLt n x hx) (Nat.lt_succ_self _)
      · exact Nat.lt_succ_self _
    · rw [hother m he] at hx
      exact Nat.lt_trans (h.localLt m x hx) (Nat.lt_succ_self _)
  · intro m x a hx hax ha
    by_cases he : m = n
    · subst m
      rw [hnode] at hx ⊢
      rcases hx with hx | rfl
      · exact Or.inl (h.localClosed n x a hx (hold (h.localLt n x hx) hax) ha)
      · rcases (anc_upd_new h.parLt hb).1 hax with rfl | ⟨p, hp, hap⟩
        · exact Or.inr rfl
        · exact Or.inl (h.localClosed n p a (hl p hp) hap ha)
    · rw [hother m he] at hx ⊢
      exact h.localClosed m x a hx (hold (h.localLt m x hx) hax) ha
  · intro m x obj hx ho
    by_cases he : m = n
    · subst m
      rw [hnode] at hx ⊢
      rcases hx with hx | rfl
      · rw [hobj x (h.localLt n x hx)] at ho
        exact Or.inl (h.localObjects n x obj hx ho)
      · apply Or.inr
        simpa [View.merge, State.mergeOp, State.createOp, State.create, o] using ho
    · rw [hother m he] at hx ⊢
      rw [hobj x (h.localLt m x hx)] at ho
      exact h.localObjects m x obj hx ho
  · intro m x hx
    by_cases he : m = n
    · subst m
      rw [hnode] at hx ⊢
      exact Or.inr hx
    · rw [hother m he] at hx ⊢
      exact h.headsLocal m x hx
  · intro m x hx
    by_cases he : m = n
    · subst m
      rw [hnode] at hx
      change x = o at hx
      exact hx ▸ hd
    · rw [hother m he] at hx
      exact h.headsSurvive m x hx
  · intro m x y hx hy hxy
    by_cases he : m = n
    · subst m
      rw [hnode] at hx hy
      exact hx.trans hy.symm
    · rw [hother m he] at hx hy
      exact h.headsAnti m x y hx hy
        (hold (h.localLt m y (h.headsLocal m y hy)) hxy)
  · intro m
    by_cases he : m = n
    · subst m
      exact ⟨o, by rw [hnode]⟩
    · obtain ⟨x, hx⟩ := h.headsNonempty m
      exact ⟨x, by rwa [hother m he]⟩

def View.accept (v : View) (D : Nat → Bool) (head : Nat) : View :=
  { v with base := v.base.hubAccept head, hubD := D }

/-- Every old frontier's surviving work remains below a new frontier. The dropped sets
may differ, so survival is tested in the resulting party's history. -/
def Retains (v w : View) : Prop :=
  ∀ n a, w.nodeD n a = false →
    (∃ h, (v.base.node n).heads h ∧ Anc v.base.U.par a h) →
    ∃ h, (w.base.node n).heads h ∧ Anc w.base.U.par a h

theorem advanceImages_retains (h : Safe v) (hk : known < v.base.U.next) :
    Retains v (v.advanceImages n known) := by
  intro m a _ ⟨x, hx, hax⟩
  by_cases he : m = n
  · subst m
    have hb : ∀ y, (v.base.node n).heads y ∨
        y ∈ exp v.base.U.par (v.nodeD n) known → y < v.base.U.next := by
      intro y hy
      exact hy.elim (fun hy => h.localLt n y (h.headsLocal n y hy))
        (fun hy => Nat.lt_of_le_of_lt ((mem_exp h.parLt hy).2.le h.parLt) hk)
    obtain ⟨y, hy, hxy⟩ := below_max h.parLt hb (Or.inl hx)
    refine ⟨y, ?_, hax.trans hxy⟩
    simpa [View.advanceImages, State.setNode] using hy
  · refine ⟨x, ?_, hax⟩
    simpa [View.advanceImages, State.setNode, he] using hx

theorem merge_retains (h : Safe v) (hL : ∀ x, x ∈ L ↔ (v.base.node n).heads x) :
    Retains v (v.merge n L O) := by
  have hb : ∀ p ∈ L, p < v.base.U.next :=
    fun p hp => h.localLt n p (h.headsLocal n p ((hL p).1 hp))
  intro m a _ ⟨x, hx, hax⟩
  by_cases he : m = n
  · subst m
    refine ⟨v.base.U.next, ?_, ?_⟩
    · simp [View.merge, State.mergeOp, State.createOp]
    · exact (anc_upd_new h.parLt hb).2 (Or.inr ⟨x, (hL x).2 hx, hax⟩)
  · refine ⟨x, ?_, ?_⟩
    · simpa [View.merge, State.mergeOp, State.createOp, he] using hx
    · exact (anc_upd_iff h.parLt hb (h.localLt m x (h.headsLocal m x hx))).2 hax

/-- Acceptance checks the required contracted closure before moving the head. It needs no
original-ancestry history invariant; all node stores and frontiers remain unchanged. -/
theorem safe_accept (h : Safe v) (hr : D root = false)
    (hb : ∀ x, D x = true → x < v.base.U.next) (hl : head < v.base.U.next)
    (hs : D head = false)
    (hc : ∀ a, Anc v.base.U.par a head → D a = false → HubHas v.base a) :
    Safe (v.accept D head) := by
  exact { h with
    hubRoot := hr
    hubDropLt := hb
    headLt := hl
    headSurvives := hs
    hubClosed := hc }

/-- New backend boundaries missing from the original-history relation. This is a local
relation: request custody, record equality and the other protocol actions still have to be
composed with it. The CAS compares canonical names on either side of the contraction. -/
inductive Step (content : Nat → Nat) : View → View → Prop
  | advance (v : View) (n known : Nat)
      (hk : known < v.base.U.next)
      (hl : ∀ p ∈ exp v.base.U.par (v.nodeD n) known, (v.base.node n).lops p)
      (hna : ¬ ∃ h, (v.base.node n).heads h ∧ Below v.base.U.par (v.nodeD n) known h) :
      Step content v (v.advanceImages n known)
  | merge (v : View) (n : Nat) (L O : List Nat)
      (hL : ∀ x, x ∈ L ↔ (v.base.node n).heads x)
      (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) : Step content v (v.merge n L O)
  | accept (v : View) (pending : Nat → Bool) (head : Nat)
      (hr : union v.hubD pending root = false)
      (hb : ∀ x, union v.hubD pending x = true → x < v.base.U.next)
      (hl : head < v.base.U.next)
      (hs : union v.hubD pending head = false)
      (hc : ∀ a, Anc v.base.U.par a head → union v.hubD pending a = false →
        HubHas v.base a)
      (hi : exp v.base.U.par (union v.hubD pending) v.base.hub.head ≠ [])
      (ha : Below v.base.U.par (union v.hubD pending) v.base.hub.head head)
      (hne : cid content v.base.U.par v.hubD v.base.hub.head ≠
        cid content v.base.U.par (union v.hubD pending) head) :
      Step content v (v.accept (union v.hubD pending) head)

theorem step_safe (h : Safe v) (hs : Step content v w) : Safe w := by
  cases hs with
  | advance _ _ hk hl _ => exact safe_advanceImages h hk hl
  | merge _ _ _ hL _ => exact safe_merge h hL
  | accept _ _ hr hb hl hs hc _ _ _ => exact safe_accept h hr hb hl hs hc

theorem step_retains (h : Safe v) (hs : Step content v w) : Retains v w := by
  cases hs with
  | advance _ _ hk _ _ => exact advanceImages_retains h hk
  | merge _ _ _ hL _ => exact merge_retains h hL
  | accept => exact fun _ _ _ hx => hx

/-- Once the hub's dropped set is fixed, the expected head survives that set. The actual
contracted acceptance guard then gives strict original ancestry again: unequal canonical
names cannot be two names of the same original under the same contraction. -/
theorem accept_fixed_drops (h : Safe v)
    (hd : union v.hubD pending = v.hubD)
    (ha : Below v.base.U.par (union v.hubD pending) v.base.hub.head head)
    (hne : cid content v.base.U.par v.hubD v.base.hub.head ≠
      cid content v.base.U.par (union v.hubD pending) head) :
    Anc v.base.U.par v.base.hub.head head ∧ v.base.hub.head < head := by
  rw [hd] at ha hne
  have hac := (below_survivor_iff h.parLt h.headSurvives).1 ha
  refine ⟨hac, hac.lt_of_ne h.parLt ?_⟩
  intro he
  exact hne (congrArg (cid content v.base.U.par v.hubD) he)

theorem step_hub_mono_fixed_drops (h : Safe v) (hs : Step content v w)
    (hd : w.hubD = v.hubD) : v.base.hub.head ≤ w.base.hub.head := by
  cases hs with
  | advance => exact Nat.le_refl _
  | merge => exact Nat.le_refl _
  | accept _ _ _ _ _ _ _ _ ha hne =>
    exact Nat.le_of_lt (accept_fixed_drops h hd ha hne).2

theorem step_hub_strict_fixed_drops (h : Safe v) (hs : Step content v w)
    (hd : w.hubD = v.hubD) (hm : v.base.hub.seq < w.base.hub.seq) :
    v.base.hub.head < w.base.hub.head := by
  cases hs with
  | advance => exact False.elim (Nat.lt_irrefl _ hm)
  | merge => exact False.elim (Nat.lt_irrefl _ hm)
  | accept _ _ _ _ _ _ _ _ ha hne => exact (accept_fixed_drops h hd ha hne).2

/-- A packet sent before a finite operation cut has an expected original below that cut.
After records stop changing, such a packet can move the hub only while its head is below
the cut. Strict movement consumes a bounded natural credit, even if the client retired the
request slot and the network keeps delivering the packet. No packet-draining premise is used.
-/
theorem old_expected_accepts_eventually_stop (run : Nat → View)
    (h0 : Safe (run 0)) (hs : ∀ i, Step content (run i) (run (i + 1)))
    (hd : ∀ i, (run (i + 1)).hubD = (run i).hubD) (B : Nat) :
    ∃ k, ∀ i, k ≤ i → ¬ ((run i).base.hub.head < B ∧
      (run i).base.hub.seq < (run (i + 1)).base.hub.seq) := by
  have hsafe : ∀ i, Safe (run i) := by
    intro i
    induction i with
    | zero => exact h0
    | succ i ih => exact step_safe ih (hs i)
  have hmono : ∀ i, (run i).base.hub.head ≤ (run (i + 1)).base.hub.head :=
    fun i => step_hub_mono_fixed_drops (hsafe i) (hs i) (hd i)
  have hcredit : ∀ i, B - (run (i + 1)).base.hub.head ≤ B - (run i).base.hub.head := by
    intro i
    have := hmono i
    omega
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => B - (run i).base.hub.head) hcredit
  refine ⟨k, fun i hi ⟨hB, hm⟩ => ?_⟩
  have hg := step_hub_strict_fixed_drops (hsafe i) (hs i) (hd i) hm
  have hc : B - (run (i + 1)).base.hub.head < B - (run i).base.hub.head := by omega
  rw [hk i hi, hk (i + 1) (by omega)] at hc
  exact Nat.lt_irrefl _ hc

end Musubi.Contracted

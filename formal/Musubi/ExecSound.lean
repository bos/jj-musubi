/-
Soundness of the executable model: every action `execStep` accepts is a relational `Step`
between the abstracted states, and `abs initE = init`. Hence every state reachable through
`execStep` is `Reachable`, and all safety theorems apply to it.
-/
import Musubi.Exec

namespace Musubi.Exec

open Musubi

/-! ## List and lookup lemmas -/

@[simp] theorem mem_union {x : Nat} {l S : List Nat} : x ∈ union l S ↔ x ∈ l ∨ x ∈ S := by
  unfold union
  rw [List.mem_append, List.mem_filter]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hl : x ∈ l
      · exact Or.inl hl
      · exact Or.inr ⟨h, by simp [hl]⟩

theorem seteq_setP {a b : List Nat} (h : seteq a b = true) : setP a = setP b := by
  unfold seteq at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  funext x
  exact propext ⟨h.1 x, h.2 x⟩

theorem find?_cons_if {α : Type} (a : α) (l : List α) (p : α → Bool) :
    (a :: l).find? p = if p a then some a else l.find? p := by
  simp only [List.find?_cons]
  split <;> simp_all

theorem find?_filter_ne (l : List (Nat × ENode)) {n i : Nat} (hi : i ≠ n) :
    (l.filter (fun p => p.1 != n)).find? (fun p => p.1 == i) =
      l.find? (fun p => p.1 == i) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.1 = n
    · have hne : (a.1 == i) = false := by simp; omega
      simp [ha, find?_cons_if, ih] at *
      simp [hne]
    · simp [ha, find?_cons_if, ih]

theorem nodeAt_setN (l : List (Nat × ENode)) (n : Nat) (nd : ENode) (i : Nat) :
    nodeAt (setN l n nd) i = if i = n then nd else nodeAt l i := by
  unfold nodeAt setN
  rw [find?_cons_if]
  by_cases hi : i = n
  · subst hi; simp
  · have : ((n, nd).1 == i) = false := by simp; omega
    rw [this, find?_filter_ne l hi]
    simp [hi]

theorem state_ext {s t : State} (h1 : s.U = t.U) (h2 : s.hub = t.hub) (h3 : s.node = t.node)
    (h4 : s.net = t.net) : s = t := by
  cases s; cases t
  cases h1; cases h2; cases h3; cases h4; rfl

theorem node_eq {a b : Node} (h1 : ∀ x, a.lops x ↔ b.lops x) (h2 : ∀ x, a.lobj x ↔ b.lobj x)
    (h3 : ∀ x, a.heads x ↔ b.heads x) (h4 : a.known = b.known) (h5 : ∀ x, a.sops x ↔ b.sops x)
    (h6 : ∀ x, a.sobj x ↔ b.sobj x) : a = b := by
  cases a; cases b
  simp only at h1 h2 h3 h4 h5 h6
  have e1 := funext fun x => propext (h1 x)
  have e2 := funext fun x => propext (h2 x)
  have e3 := funext fun x => propext (h3 x)
  have e5 := funext fun x => propext (h5 x)
  have e6 := funext fun x => propext (h6 x)
  subst e1 e2 e3 h4 e5 e6
  rfl

/-! ## Well-formedness gives acyclicity -/

theorem parOK_parLt {es : EState} (h : es.parOK = true) : ParLt es.parF := by
  intro y p hp
  unfold EState.parF EState.findOp at hp
  cases hf : es.ops.find? (fun o => o.id == y) with
  | none => rw [hf] at hp; simp at hp
  | some o =>
    rw [hf] at hp
    simp only [Option.map_some, Option.getD_some] at hp
    have hid : o.id = y := by simpa using List.find?_some hf
    have hmem := List.mem_of_find?_eq_some hf
    unfold EState.parOK at h
    rw [List.all_eq_true] at h
    have := h o hmem
    rw [List.all_eq_true] at this
    have := this p hp
    simp at this
    omega

/-! ## Deciding `anc*` -/

theorem anc_rev {par : Nat → List Nat} {y x : Nat} :
    Anc par y x ↔ y = x ∨ ∃ z, Anc par z x ∧ y ∈ par z := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @step p x' hp _ ih =>
      rcases ih with rfl | ⟨z, hz, hyz⟩
      · exact Or.inr ⟨x', Anc.refl, hp⟩
      · exact Or.inr ⟨z, hz.trans (Anc.parent hp), hyz⟩
  · rintro (rfl | ⟨z, hz, hyz⟩)
    · exact Anc.refl
    · exact (Anc.parent hyz).trans hz

theorem marks_spec {par : Nat → List Nat} (hlt : ParLt par) {x : Nat} :
    ∀ k, k ≤ x → ∀ y, y ∈ marks par x k ↔ (x - k ≤ y ∧ Anc par y x) := by
  intro k
  induction k with
  | zero =>
    intro _ y
    simp only [marks, List.mem_singleton, Nat.sub_zero]
    constructor
    · rintro rfl; exact ⟨Nat.le_refl _, Anc.refl⟩
    · rintro ⟨h1, h2⟩; have := h2.le hlt; omega
  | succ k ih =>
    intro hk y
    have ih' := ih (by omega)
    have cond : (marks par x k).any (fun z => (par z).contains (x - (k + 1))) = true ↔
        Anc par (x - (k + 1)) x := by
      rw [List.any_eq_true]
      constructor
      · rintro ⟨z, hz, hc⟩
        rw [List.contains_iff_mem] at hc
        exact (Anc.parent hc).trans ((ih' z).1 hz).2
      · intro hA
        rcases anc_rev.1 hA with he | ⟨z, hz, hyz⟩
        · omega
        · refine ⟨z, (ih' z).2 ⟨?_, hz⟩, List.contains_iff_mem.2 hyz⟩
          have := hlt z _ hyz
          omega
    simp only [marks]
    split
    · rename_i hc
      have hA := cond.1 hc
      simp only [List.mem_cons, ih']
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Nat.le_refl _, hA⟩
        · exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hy : y = x - (k + 1)
        · exact Or.inl hy
        · exact Or.inr ⟨by omega, h2⟩
    · rename_i hc
      rw [ih']
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        by_cases hy : y = x - (k + 1)
        · subst hy
          exact absurd (cond.2 h2) (by simpa using hc)
        · exact ⟨by omega, h2⟩

theorem mem_ancL {par : Nat → List Nat} (hlt : ParLt par) {x y : Nat} :
    y ∈ ancL par x ↔ Anc par y x := by
  unfold ancL
  rw [marks_spec hlt x (Nat.le_refl _)]
  simp

theorem ancB_iff {par : Nat → List Nat} (hlt : ParLt par) {a x : Nat} :
    ancB par a x = true ↔ Anc par a x := by
  unfold ancB
  rw [List.contains_iff_mem, mem_ancL hlt]

theorem setP_maxL {par : Nat → List Nat} (hlt : ParLt par) (T : List Nat) :
    setP (maxL par T) = maxSet par (setP T) := by
  funext x
  apply propext
  unfold maxL maxSet setP
  simp only [List.mem_filter, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq]
  constructor
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun y hy hA => ?_⟩
    rcases hall y hy with h | h
    · rw [← Bool.not_eq_true, ancB_iff hlt] at h; exact absurd hA h
    · exact h
  · rintro ⟨hx, hall⟩
    refine ⟨hx, fun y hy => ?_⟩
    by_cases hA : Anc par x y
    · exact Or.inr (hall y hy hA)
    · left; rw [← Bool.not_eq_true, ancB_iff hlt]; exact hA

theorem closedB_iff {es : EState} (hlt : ParLt es.parF) {d : Nat} :
    es.closedB d = true ↔ ClosedAt (abs es) d := by
  unfold EState.closedB ClosedAt HubHas
  simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, mem_ancL hlt]
  rfl

/-! ## Messages -/

theorem covers_self (m : EMsg) (hm : ∀ s h, m ≠ .notifyAll s h) : m.covers m.toMsg := by
  cases m with
  | notifyAll s h => exact absurd rfl (hm s h)
  | _ => rfl

theorem covers_iff (m : EMsg) (hm : ∀ s h, m ≠ .notifyAll s h) (m' : Msg) :
    m.covers m' ↔ m' = m.toMsg := by
  cases m with
  | notifyAll s h => exact absurd rfl (hm s h)
  | _ => exact Iff.rfl

theorem matchB_covers {em t : EMsg} (h : matchB em t = true) {m : Msg} (ht : t.covers m) :
    em.covers m := by
  cases em <;> cases t <;> simp only [matchB, Bool.and_eq_true, beq_iff_eq,
    Bool.false_eq_true] at h <;> simp only [EMsg.covers] at ht ⊢
  all_goals first
    | (obtain ⟨rfl, h2⟩ := h; rw [ht, seteq_setP h2])
    | (obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ht)
    | (obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := h; exact ht)
    | (obtain rfl := h; exact ht)
    | (obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ⟨_, ht⟩)
    | (obtain ⟨rfl, rfl⟩ := h; exact ht)
    | (obtain ⟨⟨⟨⟨rfl, h2⟩, h3⟩, rfl⟩, rfl⟩ := h; rw [ht, seteq_setP h2, seteq_setP h3])
    | (obtain ⟨⟨rfl, rfl⟩, h2⟩ := h; rw [ht, seteq_setP h2])

theorem inNet_net {es : EState} {m : EMsg} (hm : ∀ s h, m ≠ .notifyAll s h)
    (h : es.inNet m = true) : (abs es).net m.toMsg := by
  unfold EState.inNet at h
  obtain ⟨em, hem, hmatch⟩ := List.any_eq_true.1 h
  exact ⟨em, hem, matchB_covers hmatch (covers_self m hm)⟩

/-! ## Abstraction commutes with the transitions -/

section commute

variable {es : EState}

theorem abs_send_net (m : EMsg) :
    (abs (es.send m)).net = fun m' => (abs es).net m' ∨ m.covers m' := by
  funext m'
  apply propext
  unfold EState.send
  split
  · rename_i hin
    constructor
    · exact Or.inl
    · rintro (h | h)
      · exact h
      · unfold EState.inNet at hin
        obtain ⟨em, hem, hmatch⟩ := List.any_eq_true.1 hin
        exact ⟨em, hem, matchB_covers hmatch h⟩
  · show (∃ em ∈ es.net ++ [m], em.covers m') ↔ _
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨em, hem | rfl, hc⟩
      · exact Or.inl ⟨em, hem, hc⟩
      · exact Or.inr hc
    · rintro (⟨em, hem, hc⟩ | hc)
      · exact ⟨em, Or.inl hem, hc⟩
      · exact ⟨m, Or.inr rfl, hc⟩

theorem abs_send_rest (m : EMsg) :
    (abs (es.send m)).U = (abs es).U ∧ (abs (es.send m)).hub = (abs es).hub ∧
      (abs (es.send m)).node = (abs es).node := by
  unfold EState.send; split <;> exact ⟨rfl, rfl, rfl⟩

theorem abs_send (m : EMsg) (hm : ∀ s h, m ≠ .notifyAll s h) :
    abs (es.send m) = (abs es).send m.toMsg := by
  obtain ⟨h1, h2, h3⟩ := abs_send_rest (es := es) m
  refine state_ext h1 h2 h3 ?_
  rw [abs_send_net]
  funext m'
  simp only [State.send, covers_iff m hm]

theorem abs_send_notify (sq h : Nat) :
    abs (es.send (.notifyAll sq h)) = (abs es).notifyAll sq h := by
  obtain ⟨h1, h2, h3⟩ := abs_send_rest (es := es) (.notifyAll sq h)
  refine state_ext h1 h2 h3 ?_
  rw [abs_send_net]
  rfl

theorem abs_setNode (n : Nat) (nd : ENode) :
    abs (es.setNode n nd) = (abs es).setNode n nd.abs := by
  refine state_ext rfl rfl ?_ rfl
  funext i
  show (nodeAt (setN es.nodes n nd) i).abs = upd (fun i => (es.nodeOf i).abs) n nd.abs i
  rw [nodeAt_setN]
  by_cases hi : i = n
  · subst hi; simp
  · simp [hi]; rfl

theorem findOp_createOp {n : Nat} {L O : List Nat} {mg : Bool} {H' : List Nat} {x : Nat} :
    (es.createOp n L O mg H').findOp x =
      if x = es.next then some ⟨es.next, L, O, some n, mg, es.hub.seq⟩ else es.findOp x := by
  unfold EState.findOp EState.createOp
  rw [find?_cons_if]
  by_cases hx : x = es.next
  · subst hx; simp
  · have : (es.next == x) = false := by simp; omega
    simp only [this]; simp [hx]

theorem abs_createOp (n : Nat) (L O : List Nat) (mg : Bool) (H' : List Nat) :
    abs (es.createOp n L O mg H') = (abs es).createOp n L O mg (setP H') := by
  refine state_ext ?_ rfl ?_ rfl
  · show Univ.mk _ _ _ _ _ _ = Univ.mk _ _ _ _ _ _
    congr 1 <;> funext x <;> by_cases hx : x = es.next <;>
      simp [EState.parF, EState.objsF, EState.creatorF, EState.isMergeF, EState.birthF,
        findOp_createOp, upd, abs, hx]
  · funext i
    show (nodeAt (setN es.nodes n _) i).abs = upd (fun i => (es.nodeOf i).abs) n _ i
    rw [nodeAt_setN]
    by_cases hi : i = n
    · subst hi
      simp only [↓reduceIte, upd_same]
      apply node_eq <;> intros <;> simp [ENode.abs, setP, abs]
    · simp [hi]; rfl

theorem abs_userOp (hlt : ParLt es.parF) {n p : Nat} (O : List Nat) (hp : p < es.next) :
    abs (es.userOp n p O) = (abs es).userOp n p O := by
  unfold EState.userOp State.userOp
  rw [abs_createOp]
  have hlt' : ParLt (upd es.parF es.next [p]) :=
    parLt_upd hlt (by intro q hq; simp at hq; omega)
  rw [setP_maxL hlt']
  congr 2
  funext y
  simp only [setP, List.mem_append, List.mem_filter, bne_iff_ne, List.mem_singleton]
  rfl

theorem abs_mergeOp {n : Nat} (L O : List Nat) :
    abs (es.mergeOp n L O) = (abs es).mergeOp n L O := by
  unfold EState.mergeOp State.mergeOp
  rw [abs_createOp]
  congr 1
  funext y
  simp [setP]
  rfl

theorem abs_hubStoreOps (S : List Nat) :
    abs (es.hubStoreOps S) = (abs es).hubStoreOps (setP S) := by
  refine state_ext rfl ?_ rfl rfl
  show Hub.mk _ _ _ _ _ = Hub.mk _ _ _ _ _
  congr 1
  funext x
  simp [setP, EState.hubStoreOps, abs]

theorem abs_hubStoreObjs (S : List Nat) :
    abs (es.hubStoreObjs S) = (abs es).hubStoreObjs (setP S) := by
  refine state_ext rfl ?_ rfl rfl
  show Hub.mk _ _ _ _ _ = Hub.mk _ _ _ _ _
  congr 1
  funext x
  simp [setP, EState.hubStoreObjs, abs]

theorem abs_hubStore (S O : List Nat) :
    abs (es.hubStore S O) = (abs es).hubStore (setP S) (setP O) := by
  unfold EState.hubStore State.hubStore
  rw [abs_hubStoreObjs, abs_hubStoreOps]

theorem mem_sinceOpsL (hlt : ParLt es.parF) {b x : Nat} :
    x ∈ es.sinceOpsL b ↔ (abs es).sinceOps b x := by
  unfold EState.sinceOpsL State.sinceOps
  simp only [List.mem_filter, mem_ancL hlt, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_iff_mem]
  have hb : ancB es.parF x b = false ↔ ¬ Anc es.parF x b := by
    rw [← ancB_iff hlt]; simp
  rw [hb]
  rfl

theorem mem_sinceObjsL (hlt : ParLt es.parF) {b o : Nat} {H : List Nat} :
    o ∈ es.sinceObjsL b H ↔ (abs es).sinceObjs b (setP H) o := by
  unfold EState.sinceObjsL State.sinceObjs
  simp only [List.mem_filter, List.mem_flatMap, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_iff_mem, mem_sinceOpsL hlt]
  have hH : H.contains o = false ↔ ¬ o ∈ H := by
    rw [← List.contains_iff_mem]; simp
  rw [hH]
  rfl

theorem abs_hubAccept (d : Nat) : abs (es.hubAccept d) = (abs es).hubAccept d := by
  refine state_ext rfl ?_ rfl rfl
  show Hub.mk _ _ _ _ _ = Hub.mk _ _ _ _ _
  congr 1
  funext i
  simp only [EState.hubAccept, EHub.histF, upd]
  rw [find?_cons_if]
  by_cases hi : i = es.hub.seq + 1
  · subst hi; simp [abs]
  · have : (es.hub.seq + 1 == i) = false := by simp; omega
    simp only [this]; simp [hi, abs, EHub.histF]

end commute

/-! ## Soundness -/

theorem not_bcast_getHead (n : Nat) : ∀ s h, EMsg.getHead n ≠ .notifyAll s h := by
  intros; exact fun h => by cases h

/-- `n` is not the broadcast notification (for any non-broadcast constructor). -/
macro "nb" : term => `(fun _ _ h => by cases h)

theorem execCore_sound {N : Nat} {es es' : EState} {a : Action} (hlt : ParLt es.parF)
    (h : execCore N es a = .ok es') : Step N (abs es) (abs es') := by
  cases a with
  | userOp n p O =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    cases h
    rw [abs_userOp hlt O (of_decide_eq_true h3)]
    exact Or.inl (EnvStep.userOp _ n p O (of_decide_eq_true h1) (List.contains_iff_mem.1 h2))
  | merge n L O =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    obtain ⟨_, h⟩ := req_ok h
    cases h
    rw [abs_mergeOp]
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h2
    obtain ⟨a, ha, hb⟩ := List.any_eq_true.1 h3
    obtain ⟨b, hb, hab⟩ := List.any_eq_true.1 hb
    refine Or.inl (EnvStep.merge _ n L O (of_decide_eq_true h1)
      (fun x => ⟨h2.1 x, h2.2 x⟩) ⟨a, b, ha, hb, by simpa using hab⟩)
  | getHead n =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.getHead _ n (of_decide_eq_true h1))
  | learn n k sq hd =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    cases h
    rw [abs_setNode]
    exact Or.inr (SyncStep.learn _ n k sq hd (of_decide_eq_true h1) (inNet_net nb h2)
      (of_decide_eq_true h3))
  | fetchOps n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    refine Or.inr (SyncStep.fetchOps _ n (setP S) (of_decide_eq_true h1) ?_)
    intro x hx
    exact (ancB_iff hlt).1 (List.all_eq_true.1 h2 x hx)
  | fetchObjs n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.fetchObjs _ n (setP S) (of_decide_eq_true h1))
  | recvOps n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    have e : abs (es.setNode n { es.nodeOf n with sops := union (es.nodeOf n).sops S }) =
        (abs es).recvOps n (setP S) := by
      rw [abs_setNode]; unfold State.recvOps; congr 1
      apply node_eq <;> intros <;> simp [ENode.abs, setP, abs]
    rw [e]
    exact Or.inr (SyncStep.recvOps _ n (setP S) (of_decide_eq_true h1) (inNet_net nb h2))
  | recvObjs n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    have e : abs (es.setNode n { es.nodeOf n with sobj := union (es.nodeOf n).sobj S }) =
        (abs es).recvObjs n (setP S) := by
      rw [abs_setNode]; unfold State.recvObjs; congr 1
      apply node_eq <;> intros <;> simp [ENode.abs, setP, abs]
    rw [e]
    exact Or.inr (SyncStep.recvObjs _ n (setP S) (of_decide_eq_true h1) (inNet_net nb h2))
  | realize n x =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    obtain ⟨h4, h⟩ := req_ok h
    cases h
    have e : abs (es.setNode n { es.nodeOf n with
        lops := union (es.nodeOf n).lops [x]
        lobj := union (es.nodeOf n).lobj (es.objsF x) }) = (abs es).realize n x := by
      rw [abs_setNode]; unfold State.realize; congr 1
      apply node_eq <;> intros <;> simp [ENode.abs, setP, abs]
    rw [e]
    refine Or.inr (SyncStep.realize _ n x (of_decide_eq_true h1)
      (List.contains_iff_mem.1 h2) ?_ ?_)
    · intro p hp
      exact List.contains_iff_mem.1 (List.all_eq_true.1 h3 p hp)
    · intro o ho
      have := List.all_eq_true.1 h4 o ho
      simp only [Bool.or_eq_true, List.contains_iff_mem] at this
      exact this
  | advance n =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    cases h
    have e : abs (es.setNode n { es.nodeOf n with
        heads := maxL es.parF ((es.nodeOf n).heads ++ [(es.nodeOf n).known.2]) }) =
        (abs es).advance n := by
      rw [abs_setNode]; unfold State.advance; congr 1
      simp only [ENode.abs]
      rw [setP_maxL hlt]
      congr 2
      funext y
      simp [setP]
      rfl
    rw [e]
    refine Or.inr (SyncStep.advance _ n (of_decide_eq_true h1) (List.contains_iff_mem.1 h2) ?_)
    rintro ⟨g, hg, hA⟩
    simp only [Bool.not_eq_true', List.any_eq_false] at h3
    exact h3 g hg (by rw [ancB_iff hlt]; exact hA)
  | uploadOps n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.uploadOps _ n (setP S) (of_decide_eq_true h1)
      (fun x hx => List.contains_iff_mem.1 (List.all_eq_true.1 h2 x hx)))
  | uploadObjs n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.uploadObjs _ n (setP S) (of_decide_eq_true h1)
      (fun x hx => List.contains_iff_mem.1 (List.all_eq_true.1 h2 x hx)))
  | push n e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.push _ n e d (of_decide_eq_true h1) (List.contains_iff_mem.1 h2))
  | pushAll n S O e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    obtain ⟨h4, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.pushAll _ n (setP S) (setP O) e d (of_decide_eq_true h1)
      (fun x hx => List.contains_iff_mem.1 (List.all_eq_true.1 h2 x hx))
      (fun o ho => List.contains_iff_mem.1 (List.all_eq_true.1 h3 o ho))
      (List.contains_iff_mem.1 h4))
  | fetchAll n b H =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.fetchAll _ n b (setP H) (of_decide_eq_true h1))
  | crashNode n =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    exact Or.inr (SyncStep.crashNode _ n (of_decide_eq_true h1))
  | loseKnown n =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_setNode]
    exact Or.inr (SyncStep.loseKnown _ n (of_decide_eq_true h1))
  | loseVolatile n =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    have e : abs (es.setNode n { es.nodeOf n with known := (0, root), sops := [], sobj := [] }) =
        (abs es).setNode n { (abs es).node n with known := (0, root), sops := fun _ => False,
                                                  sobj := fun _ => False } := by
      rw [abs_setNode]; congr 1
      apply node_eq <;> intros <;> simp [ENode.abs, setP, abs]
    rw [e]
    exact Or.inr (SyncStep.loseVolatile _ n (of_decide_eq_true h1))
  | hubGetHead n =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.hubGetHead _ n (inNet_net nb h1))
  | hubPutOps n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb, abs_hubStoreOps]
    exact Or.inr (SyncStep.hubPutOps _ n (setP S) (inNet_net nb h1))
  | hubPutObjs n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb, abs_hubStoreObjs]
    exact Or.inr (SyncStep.hubPutObjs _ n (setP S) (inNet_net nb h1))
  | hubGetOps n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    have e : (EMsg.ops n (S.filter (es.hub.ops.contains ·))).toMsg =
        Msg.ops n (fun x => setP S x ∧ (abs es).hub.ops x) := by
      show Msg.ops n _ = Msg.ops n _
      congr 1; funext x; simp [setP, abs]
    rw [e]
    exact Or.inr (SyncStep.hubGetOps _ n (setP S) (inNet_net nb h1))
  | hubGetObjs n S =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    have e : (EMsg.objs n (S.filter (es.hub.objs.contains ·))).toMsg =
        Msg.objs n (fun x => setP S x ∧ (abs es).hub.objs x) := by
      show Msg.objs n _ = Msg.objs n _
      congr 1; funext x; simp [setP, abs]
    rw [e]
    exact Or.inr (SyncStep.hubGetObjs _ n (setP S) (inNet_net nb h1))
  | casIdem n e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    exact Or.inr (SyncStep.casIdem _ n e d (inNet_net nb h1) (of_decide_eq_true h2))
  | casAccept n e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    obtain ⟨h4, h⟩ := req_ok h; obtain ⟨h5, h⟩ := req_ok h
    cases h
    rw [abs_send_notify, abs_send _ nb, abs_hubAccept]
    exact Or.inr (SyncStep.casAccept _ n e d (inNet_net nb h1) (of_decide_eq_true h2)
      (of_decide_eq_true h3) ((ancB_iff hlt).1 h4) ((closedB_iff hlt).1 h5))
  | casReject n e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb]
    refine Or.inr (SyncStep.casReject _ n e d (inNet_net nb h1) (of_decide_eq_true h2) ?_)
    rintro ⟨he, ha, hc⟩
    have : (decide (es.hub.head = e) && ancB es.parF e d && es.closedB d) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨he, (ancB_iff hlt).2 ha⟩, (closedB_iff hlt).2 hc⟩
    rw [this] at h3
    cases h3
  | hubPushIdem n S O e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb, abs_hubStore]
    exact Or.inr (SyncStep.hubPushIdem _ n (setP S) (setP O) e d (inNet_net nb h1)
      (of_decide_eq_true h2))
  | hubPushAccept n S O e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    obtain ⟨h4, h⟩ := req_ok h; obtain ⟨h5, h⟩ := req_ok h
    cases h
    rw [abs_send_notify, abs_send _ nb, abs_hubAccept, abs_hubStore]
    have hc : ClosedAt ((abs es).hubStore (setP S) (setP O)) d := by
      rw [← abs_hubStore]; exact (closedB_iff (es := es.hubStore S O) hlt).1 h5
    exact Or.inr (SyncStep.hubPushAccept _ n (setP S) (setP O) e d (inNet_net nb h1)
      (of_decide_eq_true h2) (of_decide_eq_true h3) ((ancB_iff hlt).1 h4) hc)
  | hubPushReject n S O e d =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h; obtain ⟨h2, h⟩ := req_ok h; obtain ⟨h3, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb, abs_hubStore]
    refine Or.inr (SyncStep.hubPushReject _ n (setP S) (setP O) e d (inNet_net nb h1)
      (of_decide_eq_true h2) ?_)
    rintro ⟨he, ha, hc⟩
    have : (decide (es.hub.head = e) && ancB es.parF e d && (es.hubStore S O).closedB d)
        = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨he, (ancB_iff hlt).2 ha⟩, (closedB_iff (es := es.hubStore S O) hlt).2 ?_⟩
      rw [abs_hubStore]; exact hc
    rw [this] at h3
    cases h3
  | hubFetch n b H =>
    simp only [execCore] at h
    obtain ⟨h1, h⟩ := req_ok h
    cases h
    rw [abs_send _ nb, abs_send _ nb, abs_send _ nb]
    have e1 : (EMsg.ops n (es.sinceOpsL b)).toMsg = Msg.ops n ((abs es).sinceOps b) := by
      show Msg.ops n _ = Msg.ops n _
      congr 1; funext x; exact propext (mem_sinceOpsL hlt)
    have e2 : (EMsg.objs n (es.sinceObjsL b H)).toMsg =
        Msg.objs n ((abs es).sinceObjs b (setP H)) := by
      show Msg.objs n _ = Msg.objs n _
      congr 1; funext o; exact propext (mem_sinceObjsL hlt)
    rw [e1, e2]
    exact Or.inr (SyncStep.hubFetch _ n b (setP H) (inNet_net nb h1))
  | crashHub =>
    simp only [execCore] at h
    cases h
    exact Or.inr (SyncStep.crashHub _)

/-- **Soundness of the executable model**: every action `execStep` accepts is a step of the
relational model between the abstracted states. -/
theorem exec_sound {N : Nat} {es es' : EState} {a : Action}
    (h : execStep N es a = .ok es') : Step N (abs es) (abs es') := by
  obtain ⟨hwf, h⟩ := req_ok h
  exact execCore_sound (parOK_parLt hwf) h

/-- The executable initial state abstracts to the relational one. -/
theorem abs_initE : abs initE = init := by
  refine state_ext ?_ ?_ ?_ ?_
  · rfl
  · show Hub.mk _ _ _ _ _ = Hub.mk _ _ _ _ _
    congr 1 <;> funext x <;> simp [setP, initE]
  · funext i
    show ENode.init.abs = initNode
    apply node_eq <;> intros <;> simp [ENode.abs, ENode.init, initNode, setP]
  · funext m
    show (∃ em ∈ ([] : List EMsg), em.covers m) = False
    simp

/-- States reachable through `execStep` from `initE`. -/
inductive ExecReachable (N : Nat) : EState → Prop
  | init : ExecReachable N initE
  | step {es es' : EState} (a : Action) : ExecReachable N es → execStep N es a = .ok es' →
      ExecReachable N es'

/-- Every state reachable through `execStep` is abstractly reachable, so every safety
theorem applies to it. -/
theorem exec_reachable {N : Nat} {es : EState} (h : ExecReachable N es) :
    Reachable N (abs es) := by
  induction h with
  | init => rw [abs_initE]; exact Reachable.init
  | step a _ hs ih => exact ih.step (exec_sound hs)

/-- For example: the invariant, hence HubClosed, Locality, MergeOwnership and the rest, hold
in every executable state. -/
theorem exec_inv {N : Nat} {es : EState} (h : ExecReachable N es) : Inv N (abs es) :=
  inv_reachable (exec_reachable h)

end Musubi.Exec

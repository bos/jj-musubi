/-
Preservation of the invariant by environment actions (`UserOp`, `Merge`) and by pure
message sends. Both environment actions are instances of `createOp`, which allocates the
fresh operation `next`.
-/
import Musubi.Invariant

namespace Musubi

variable {N : Nat}

/-! ## Sending a message -/

theorem Inv.send {s : State} {m : Msg} (hI : Inv N s) (hm : MsgOK s m) : Inv N (s.send m) :=
  { hI with
    msgs := by
      intro m' hm'
      rcases hm' with h | h
      · exact hI.msgs m' h
      · subst h; exact hm }

/-! ## Creating an operation -/

section createOp

variable {s : State} {n : Nat} {L O : List Nat} {mg : Bool} {H' : OSet}

@[simp] theorem createOp_U : (s.createOp n L O mg H').U = s.create n L O mg := rfl
@[simp] theorem createOp_hub : (s.createOp n L O mg H').hub = s.hub := rfl
@[simp] theorem createOp_net : (s.createOp n L O mg H').net = s.net := rfl
@[simp] theorem create_next : (s.create n L O mg).next = s.U.next + 1 := rfl
@[simp] theorem create_par : (s.create n L O mg).par = upd s.U.par s.U.next L := rfl
@[simp] theorem create_objs : (s.create n L O mg).objs = upd s.U.objs s.U.next O := rfl
@[simp] theorem create_creator :
    (s.create n L O mg).creator = upd s.U.creator s.U.next (some n) := rfl
@[simp] theorem create_isMerge : (s.create n L O mg).isMerge = upd s.U.isMerge s.U.next mg :=
  rfl
@[simp] theorem create_birth : (s.create n L O mg).birth = upd s.U.birth s.U.next s.hub.seq :=
  rfl

theorem createOp_node_ne {i : Nat} (h : i ≠ n) : (s.createOp n L O mg H').node i = s.node i := by
  simp [State.createOp, h]

@[simp] theorem createOp_lops :
    ((s.createOp n L O mg H').node n).lops = fun y => (s.node n).lops y ∨ y = s.U.next := by
  simp [State.createOp]
@[simp] theorem createOp_lobj :
    ((s.createOp n L O mg H').node n).lobj = fun y => (s.node n).lobj y ∨ y ∈ O := by
  simp [State.createOp]
@[simp] theorem createOp_heads : ((s.createOp n L O mg H').node n).heads = H' := by
  simp [State.createOp]
@[simp] theorem createOp_known :
    ((s.createOp n L O mg H').node n).known = (s.node n).known := by
  simp [State.createOp]
@[simp] theorem createOp_sops : ((s.createOp n L O mg H').node n).sops = (s.node n).sops := by
  simp [State.createOp]

/-- The general preservation lemma for creating an operation on node `n`. -/
theorem inv_createOp (hI : Inv N s) (hn : n < N)
    (hL : ∀ p ∈ L, (s.node n).lops p) (hLne : L ≠ [])
    (hHo : H' s.U.next)
    (hHsub : ∀ y, H' y → (s.node n).heads y ∨ y = s.U.next)
    (hHanti : ∀ x y, H' x → H' y → Anc (upd s.U.par s.U.next L) x y → x = y)
    (hHmono : ∀ x h, (s.node n).heads h → Anc s.U.par x h →
      ∃ h', H' h' ∧ Anc (upd s.U.par s.U.next L) x h')
    (hMerge : mg = true →
      (∃ p ∈ L, s.U.creator p = some n ∧ ¬ Anc s.U.par p s.hub.head) ∧
      (∀ p ∈ L, s.U.creator p ≠ some n → Anc s.U.par p s.hub.head)) :
    Inv N (s.createOp n L O mg H') := by
  have hLlt : ∀ p ∈ L, p < s.U.next := fun p hp => hI.lLt n p (hL p hp)
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next L) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have hlt' := parLt_upd hI.parLt hLlt
  have hHlt : ∀ y, H' y → y < s.U.next + 1 := by
    intro y hy
    rcases hHsub y hy with h | h
    · have := hI.headsLt h; omega
    · omega
  -- elements of `H'` that are accepted are old heads
  have hHacc : ∀ y, H' y → Anc (upd s.U.par s.U.next L) y s.hub.head →
      (s.node n).heads y ∧ y < s.U.next := by
    intro y hy hA
    have hA' := (T hI.headLt).1 hA
    have hylt := hI.accLt hA'
    rcases hHsub y hy with h | h
    · exact ⟨h, hylt⟩
    · omega
  refine
    { parLt := hlt', nextPos := ?_, rootAnc := ?_, creatorSome := ?_, headLt := ?_,
      histHead := hI.histHead, hist0 := hI.hist0, histStep := ?_, hubClosed := ?_,
      lroot := ?_, lLt := ?_, lParents := ?_, lObjs := ?_, headsLocal := ?_,
      headsAnti := ?_, headsNonempty := ?_, known := ?_, locality := ?_, staged := ?_,
      ownInHeads := ?_, accHeads := ?_, comparable := ?_, mergeOwn := ?_,
      mergeForeign := ?_, birthLe := ?_, birthMono := ?_, creatorRoot := ?_, msgs := ?_ }
  · simp
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
  · simp; have := hI.headLt; omega
  · -- histStep
    intro i hi
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
  · -- lroot
    intro i
    by_cases hi : i = n
    · subst hi; simp; exact Or.inl (hI.lroot i)
    · rw [createOp_node_ne hi]; exact hI.lroot i
  · -- lLt
    intro i x hx
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
      rcases hx with hx | hx
      · rw [upd_lt _ _ (hI.lLt i x hx)] at hp
        exact Or.inl (hI.lParents i x p hx hp)
      · subst hx; rw [upd_same] at hp; exact Or.inl (hL p hp)
    · rw [createOp_node_ne hi] at hx ⊢
      rw [upd_lt _ _ (hI.lLt i x hx)] at hp
      exact hI.lParents i x p hx hp
  · -- lObjs
    intro i x o hx ho
    simp only [createOp_U, create_objs] at ho
    by_cases hi : i = n
    · subst hi
      simp only [createOp_lops, createOp_lobj] at hx ⊢
      rcases hx with hx | hx
      · rw [upd_lt _ _ (hI.lLt i x hx)] at ho
        exact Or.inl (hI.lObjs i x o hx ho)
      · subst hx; rw [upd_same] at ho; exact Or.inr ho
    · rw [createOp_node_ne hi] at hx ⊢
      rw [upd_lt _ _ (hI.lLt i x hx)] at ho
      exact hI.lObjs i x o hx ho
  · -- headsLocal
    intro i x hx
    by_cases hi : i = n
    · subst hi
      simp only [createOp_heads, createOp_lops] at hx ⊢
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
  · -- headsNonempty
    intro i
    by_cases hi : i = n
    · subst hi; exact ⟨s.U.next, by simpa using hHo⟩
    · rw [createOp_node_ne hi]; exact hI.headsNonempty i
  · -- known
    intro i
    by_cases hi : i = n
    · subst hi; simp only [createOp_known, createOp_hub]; exact hI.known i
    · rw [createOp_node_ne hi]; exact hI.known i
  · -- locality
    intro i x hx
    simp only [createOp_U, create_creator, create_par, createOp_hub]
    by_cases hi : i = n
    · subst hi
      simp only [createOp_lops] at hx
      rcases hx with hx | hx
      · rw [upd_lt _ _ (hI.lLt i x hx)]
        rcases hI.locality i x hx with h | h
        · exact Or.inl h
        · exact Or.inr ((T hI.headLt).2 h)
      · subst hx; exact Or.inl (upd_same _ _ _)
    · rw [createOp_node_ne hi] at hx
      rw [upd_lt _ _ (hI.lLt i x hx)]
      rcases hI.locality i x hx with h | h
      · exact Or.inl h
      · exact Or.inr ((T hI.headLt).2 h)
  · -- staged
    intro i x hx
    simp only [createOp_U, create_par, createOp_hub]
    by_cases hi : i = n
    · subst hi
      simp only [createOp_sops] at hx
      exact (T hI.headLt).2 (hI.staged i x hx)
    · rw [createOp_node_ne hi] at hx
      exact (T hI.headLt).2 (hI.staged i x hx)
  · -- ownInHeads
    intro i x hx hc
    simp only [createOp_U, create_next, create_creator, create_par] at hx hc ⊢
    by_cases hxo : x = s.U.next
    · subst hxo
      rw [upd_same] at hc
      cases hc
      exact ⟨s.U.next, by simpa using hHo, Anc.refl⟩
    · have hx' : x < s.U.next := by omega
      rw [upd_ne _ _ hxo] at hc
      obtain ⟨h, hh, hA⟩ := hI.ownInHeads i x hx' hc
      by_cases hi : i = n
      · subst hi
        obtain ⟨h', hh', hA'⟩ := hHmono x h hh hA
        exact ⟨h', by simpa using hh', hA'⟩
      · rw [createOp_node_ne hi]
        exact ⟨h, hh, (T (hI.headsLt hh)).2 hA⟩
  · -- accHeads
    intro i x y hx hy hxa hya
    simp only [createOp_U, create_par, createOp_hub] at hxa hya
    by_cases hi : i = n
    · subst hi
      simp only [createOp_heads] at hx hy
      obtain ⟨hx', -⟩ := hHacc x hx hxa
      obtain ⟨hy', -⟩ := hHacc y hy hya
      exact hI.accHeads i x y hx' hy' ((T hI.headLt).1 hxa) ((T hI.headLt).1 hya)
    · rw [createOp_node_ne hi] at hx hy
      exact hI.accHeads i x y hx hy ((T hI.headLt).1 hxa) ((T hI.headLt).1 hya)
  · -- comparable
    intro i x j hx hxa hj
    simp only [createOp_U, create_par, createOp_hub] at hxa hj ⊢
    have hhl := hI.histLt hj
    have key : (s.node i).heads x → x < s.U.next → Anc s.U.par x s.hub.head →
        Anc (upd s.U.par s.U.next L) x (s.hub.hist j) ∨
          Anc (upd s.U.par s.U.next L) (s.hub.hist j) x := by
      intro hx' hxl hxa'
      rcases hI.comparable i x j hx' hxa' hj with h | h
      · exact Or.inl ((T hhl).2 h)
      · exact Or.inr ((T hxl).2 h)
    by_cases hi : i = n
    · subst hi
      simp only [createOp_heads] at hx
      obtain ⟨hx', hxl⟩ := hHacc x hx hxa
      exact key hx' hxl ((T hI.headLt).1 hxa)
    · rw [createOp_node_ne hi] at hx
      exact key hx (hI.headsLt hx) ((T hI.headLt).1 hxa)
  · -- mergeOwn
    intro m hm hmg
    simp only [createOp_U, create_next, create_par, create_creator, create_isMerge,
      create_birth, createOp_hub] at hm hmg ⊢
    by_cases hmo : m = s.U.next
    · subst hmo
      rw [upd_same] at hmg
      obtain ⟨⟨p, hpL, hc, hna⟩, -⟩ := hMerge hmg
      refine ⟨p, by rw [upd_same]; exact hpL, ?_, ?_⟩
      · rw [upd_lt _ _ (hLlt p hpL), upd_same]; exact hc
      · rw [upd_same, hI.histHead]
        exact fun h => hna ((T hI.headLt).1 h)
    · have hm' : m < s.U.next := by omega
      rw [upd_ne _ _ hmo] at hmg
      rw [upd_ne _ _ hmo, upd_ne _ _ hmo, upd_ne _ _ hmo]
      obtain ⟨p, hp, hc, hna⟩ := hI.mergeOwn m hm' hmg
      have hpl : p < s.U.next := Nat.lt_trans (hI.parLt m p hp) hm'
      refine ⟨p, hp, by rw [upd_lt _ _ hpl]; exact hc, ?_⟩
      exact fun h => hna ((T (hI.histLt (hI.birthLe m hm'))).1 h)
  · -- mergeForeign
    intro m hm hmg p hp hc
    simp only [createOp_U, create_next, create_par, create_creator, create_isMerge,
      create_birth, createOp_hub] at hm hmg hp hc ⊢
    by_cases hmo : m = s.U.next
    · subst hmo
      rw [upd_same] at hmg hp
      rw [upd_same] at hc
      rw [upd_lt _ _ (hLlt p hp)] at hc
      rw [upd_same, hI.histHead]
      exact (T hI.headLt).2 ((hMerge hmg).2 p hp hc)
    · have hm' : m < s.U.next := by omega
      rw [upd_ne _ _ hmo] at hmg hp hc
      have hpl : p < s.U.next := Nat.lt_trans (hI.parLt m p hp) hm'
      rw [upd_lt _ _ hpl] at hc
      rw [upd_ne _ _ hmo]
      exact (T (hI.histLt (hI.birthLe m hm'))).2 (hI.mergeForeign m hm' hmg p hp hc)
  · -- birthLe
    intro m hm
    simp only [createOp_U, create_next, create_birth, createOp_hub] at hm ⊢
    by_cases hmo : m = s.U.next
    · subst hmo; rw [upd_same]; exact Nat.le_refl _
    · rw [upd_ne _ _ hmo]; exact hI.birthLe m (by omega)
  · -- birthMono
    intro x y hxy hy
    simp only [createOp_U, create_next, create_birth] at hy ⊢
    have hx' : x < s.U.next := by omega
    rw [upd_lt _ _ hx']
    by_cases hyo : y = s.U.next
    · subst hyo; rw [upd_same]; exact hI.birthLe x hx'
    · rw [upd_ne _ _ hyo]; exact hI.birthMono x y hxy (by omega)
  · -- creatorRoot
    simp only [createOp_U, create_creator]
    rw [upd_lt _ _ hI.nextPos]; exact hI.creatorRoot
  · -- msgs
    intro m hm
    have hm' := hI.msgs m hm
    cases m with
    | getOps i S =>
      intro x hx; exact (T hI.headLt).2 (hm' x hx)
    | ops i S =>
      intro x hx; exact (T hI.headLt).2 (hm' x hx)
    | cas i e d =>
      simp only [MsgOK, createOp_U, create_par, createOp_hub] at hm' ⊢
      rcases hm' with ⟨h, hh, hA⟩ | hA
      · by_cases hi : i = n
        · subst hi
          obtain ⟨h', hh', hA'⟩ := hHmono d h hh hA
          exact Or.inl ⟨h', by simpa using hh', hA'⟩
        · rw [createOp_node_ne hi]
          exact Or.inl ⟨h, hh, (T (hI.headsLt hh)).2 hA⟩
      · exact Or.inr ((T hI.headLt).2 hA)
    | head i k sq h => exact hm'
    | getHead => trivial
    | putOps => trivial
    | putObjs => trivial
    | getObjs => trivial
    | objs => trivial
    | stored => trivial

end createOp

/-! ## `UserOp` -/

/-- Characterization of `max(heads \ {p} ∪ {o})`. -/
theorem userOp_heads_iff {s : State} (hI : Inv N s) {n p : Nat} (hp : (s.node n).lops p)
    {y : Nat} :
    maxSet (upd s.U.par s.U.next [p])
        (fun y => ((s.node n).heads y ∧ y ≠ p) ∨ y = s.U.next) y ↔
      y = s.U.next ∨ ((s.node n).heads y ∧ y ≠ p ∧ ¬ Anc s.U.par y p) := by
  have hLlt : ∀ q ∈ [p], q < s.U.next := by
    intro q hq; simp at hq; subst hq; exact hI.lLt n q hp
  have hlt' := parLt_upd hI.parLt hLlt
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next [p]) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have Tnew : ∀ {a : Nat}, Anc (upd s.U.par s.U.next [p]) a s.U.next ↔
      a = s.U.next ∨ Anc s.U.par a p := by
    intro a; rw [anc_upd_new hI.parLt hLlt]; simp
  constructor
  · rintro ⟨hy, hmax⟩
    rcases hy with ⟨hh, hne⟩ | hy
    · right
      refine ⟨hh, hne, fun hA => ?_⟩
      have := hmax s.U.next (Or.inr rfl) (Tnew.2 (Or.inr hA))
      have := hI.headsLt hh
      omega
    · exact Or.inl hy
  · rintro (hy | ⟨hh, hne, hna⟩)
    · subst hy
      refine ⟨Or.inr rfl, fun z hz hA => ?_⟩
      rcases hz with ⟨hz, -⟩ | hz
      · have h1 := hA.le hlt'
        have h2 := hI.headsLt hz
        omega
      · exact hz.symm
    · refine ⟨Or.inl ⟨hh, hne⟩, fun z hz hA => ?_⟩
      rcases hz with ⟨hz, -⟩ | hz
      · exact hI.headsAnti n y z hh hz ((T (hI.headsLt hz)).1 hA)
      · subst hz
        rcases Tnew.1 hA with h | h
        · have := hI.headsLt hh; omega
        · exact absurd h hna

theorem inv_userOp {s : State} (hI : Inv N s) {n p : Nat} {O : List Nat} (hn : n < N)
    (hp : (s.node n).lops p) : Inv N (s.userOp n p O) := by
  have hLlt : ∀ q ∈ [p], q < s.U.next := by
    intro q hq; simp at hq; subst hq; exact hI.lLt n q hp
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next [p]) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have Tnew : ∀ {a : Nat}, Anc (upd s.U.par s.U.next [p]) a s.U.next ↔
      a = s.U.next ∨ Anc s.U.par a p := by
    intro a; rw [anc_upd_new hI.parLt hLlt]; simp
  have H := fun y => userOp_heads_iff (y := y) hI hp
  apply inv_createOp hI hn
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
  · intro h; cases h

/-! ## `Merge` -/

theorem inv_merge {s : State} (hI : Inv N s) {n : Nat} {L O : List Nat} (hn : n < N)
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    Inv N (s.mergeOp n L O) := by
  have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  apply inv_createOp hI hn
  · intro q hq; exact hI.headsLocal n q ((hL q).1 hq)
  · intro h; rw [h] at ha; simp at ha
  · rfl
  · intro y hy; exact Or.inr hy
  · intro x y hx hy _; rw [hx, hy]
  · intro x h hh hA
    refine ⟨s.U.next, rfl, ?_⟩
    rw [anc_upd_new hI.parLt hLlt]
    exact Or.inr ⟨h, (hL h).2 hh, hA⟩
  · intro _
    constructor
    · -- not both of `a`, `b` are accepted
      have key : ∀ p, p ∈ L → ¬ Anc s.U.par p s.hub.head →
          ∃ p ∈ L, s.U.creator p = some n ∧ ¬ Anc s.U.par p s.hub.head := by
        intro p hp hna
        exact ⟨p, hp, hI.ownOfUnacc (hI.headsLocal n p ((hL p).1 hp)) hna, hna⟩
      by_cases hA : Anc s.U.par a s.hub.head
      · by_cases hB : Anc s.U.par b s.hub.head
        · exact absurd (hI.accHeads n a b ((hL a).1 ha) ((hL b).1 hb) hA hB) hab
        · exact key b hb hB
      · exact key a ha hA
    · intro p hp hc
      rcases hI.locality n p (hI.headsLocal n p ((hL p).1 hp)) with h | h
      · exact absurd h hc
      · exact h

end Musubi

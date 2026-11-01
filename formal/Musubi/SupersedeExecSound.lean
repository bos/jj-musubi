/-
Soundness of the executable model with supersedes: every action `sexecStep` accepts, from a
state that keeps `SEOK` as every reachable one does (`sexec_ok`), is a step of `SRStep`
between the abstracted states, or leaves them as they were (`sexec_sound`); and
`sabs initSE = SState.init`. Hence every state reachable through `sexecStep` is `SRReachable`,
and every theorem of `Supersede.lean` applies to it, `SInv` and the superseded ids never coming
back among them. `smeasureE` and `sconvergedE` are `smeasure` and `SConverged`.
-/
import Musubi.SupersedeExec
import Musubi.ExecSound

namespace Musubi.Exec

open Musubi

/-! ## Lookups -/

theorem not_mem_of_not_contains {l : List Nat} {x : Nat} (h : (!l.contains x) = true) :
    x ∉ l := by
  intro hx; rw [List.contains_iff_mem.2 hx] at h; cases h

theorem assocF_cons {α : Type} (k : Nat) (v d : α) (l : List (Nat × α)) (i : Nat) :
    assocF ((k, v) :: l) i d = if i = k then v else assocF l i d := by
  unfold assocF
  rw [find?_cons_if]
  by_cases hi : i = k
  · subst hi; simp
  · have : ((k, v).1 == i) = false := by simp; omega
    simp [this, hi]

theorem assocF_filter_ne {α : Type} (l : List (Nat × α)) {n i : Nat} (d : α) (hi : i ≠ n) :
    assocF (l.filter (fun p => p.1 != n)) i d = assocF l i d := by
  unfold assocF
  congr 2
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.1 = n
    · have hne : (a.1 == i) = false := by simp; omega
      simp [ha, find?_cons_if, ih] at *
      simp [hne]
    · simp [ha, find?_cons_if, ih]

theorem assocF_set {α : Type} (l : List (Nat × α)) (n : Nat) (v d : α) (i : Nat) :
    assocF ((n, v) :: l.filter (fun p => p.1 != n)) i d = if i = n then v else assocF l i d := by
  rw [assocF_cons]
  by_cases hi : i = n
  · simp [hi]
  · simp only [hi, ↓reduceIte]; exact assocF_filter_ne l d hi

theorem nodeDF_setD (ses : SEState) (n : Nat) (D : List Nat) (i : Nat) :
    (ses.setD n D).nodeDF i = if i = n then D else ses.nodeDF i :=
  assocF_set _ _ _ _ _

theorem setP_union (l S : List Nat) : setP (union l S) = fun x => setP l x ∨ setP S x := by
  funext x; exact propext mem_union

theorem setP_nodeD_setD (ses : SEState) (n : Nat) (D : List Nat) :
    (fun i => setP ((ses.setD n D).nodeDF i)) = upd (fun i => setP (ses.nodeDF i)) n (setP D) := by
  funext i
  rw [nodeDF_setD]
  by_cases hi : i = n
  · subst hi; simp
  · simp [hi]

theorem recEq_flat : ∀ {A B : List Rec}, recEq A B = true → setP (flat A) = setP (flat B)
  | [], [], _ => rfl
  | a :: A, b :: B, h => by
    simp only [recEq, Bool.and_eq_true] at h
    have e1 := seteq_setP h.1
    have e2 := recEq_flat h.2
    funext x
    have h1 := congrFun e1 x
    have h2 := congrFun e2 x
    simp only [flat, List.flatten_cons, setP, List.mem_append] at h1 h2 ⊢
    rw [h1, h2]
  | [], _ :: _, h => by simp [recEq] at h
  | _ :: _, [], h => by simp [recEq] at h

theorem mem_newRec (ses : SEState) (Δ : List Nat) (x : Nat) :
    x ∈ newRec ses Δ ↔ x ∈ Δ ∧ x ∉ ses.hubDL := by
  unfold newRec
  rw [List.mem_filter]
  apply and_congr Iff.rfl
  constructor
  · exact not_mem_of_not_contains
  · intro h; cases hc : ses.hubDL.contains x
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) h

theorem mem_takeRecs (ses : SEState) (Δ : List Nat) (x : Nat) :
    x ∈ flat (ses.takeRecs Δ) ↔ x ∈ ses.hubDL ∨ x ∈ Δ := by
  unfold SEState.takeRecs
  split
  · rename_i h
    rw [List.isEmpty_iff] at h
    refine ⟨Or.inl, fun hx => hx.elim id fun hx => ?_⟩
    apply Classical.byContradiction
    intro hd
    have := (mem_newRec ses Δ x).2 ⟨hx, hd⟩
    rw [h] at this
    cases this
  · have e : flat (ses.recs ++ [newRec ses Δ]) = ses.hubDL ++ newRec ses Δ := by
      simp [flat, SEState.hubDL]
    rw [e, List.mem_append, mem_newRec]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hd : x ∈ ses.hubDL
        · exact Or.inl hd
        · exact Or.inr ⟨h, hd⟩

theorem mem_flat_take {R : List Rec} {k x : Nat} (h : x ∈ flat (R.take k)) : x ∈ flat R := by
  unfold flat at *
  rw [List.mem_flatten] at *
  obtain ⟨l, hl, hx⟩ := h
  exact ⟨l, List.mem_of_mem_take hl, hx⟩

theorem mem_flat_take_mono {R : List Rec} {a b : Nat} (hab : a ≤ b) {x : Nat}
    (h : x ∈ flat (R.take a)) : x ∈ flat (R.take b) := by
  have e : R.take a = (R.take b).take a := by rw [List.take_take, Nat.min_eq_left hab]
  rw [e] at h; exact mem_flat_take h

/-- An operation not among the records the hub remembers, it doesn't remember dropping. -/
theorem not_remembered {ses : SEState} {x : Nat} (h : x ∉ ses.remDL) :
    ¬ (x ∈ ses.hubDL ∧ x ∉ ses.hubPL) := by
  rintro ⟨hd, hf⟩
  apply h
  unfold SEState.hubDL at hd
  unfold SEState.remDL
  unfold SEState.hubPL at hf
  rw [← List.take_append_drop ses.pruned ses.recs] at hd
  simp only [flat, List.flatten_append, List.mem_append] at hd hf ⊢
  exact hd.resolve_left hf

theorem takeRecs_take (ses : SEState) (Δ : List Nat) (h : ses.pruned ≤ ses.recs.length) :
    (ses.takeRecs Δ).take ses.pruned = ses.recs.take ses.pruned := by
  unfold SEState.takeRecs
  split
  · rfl
  · exact List.take_append_of_le_length h

theorem length_takeRecs (ses : SEState) (Δ : List Nat) :
    ses.recs.length ≤ (ses.takeRecs Δ).length := by
  unfold SEState.takeRecs
  split
  · exact Nat.le_refl _
  · simp

/-- A value an association list gives is the default, or some entry's. -/
theorem assocF_cases {α : Type} (l : List (Nat × α)) (i : Nat) (d : α) :
    assocF l i d = d ∨ ∃ p ∈ l, p.2 = assocF l i d := by
  unfold assocF
  cases h : l.find? (fun p => p.1 == i) with
  | none => left; rfl
  | some p => right; exact ⟨p, List.mem_of_find?_eq_some h, rfl⟩

/-- Two states with the same fields are the same. -/
theorem sstate_ext {A B : SState} (h1 : A.s = B.s) (h2 : A.hubD = B.hubD)
    (h3 : A.hubDHist = B.hubDHist) (h4 : A.hubP = B.hubP) (h5 : A.hubPHist = B.hubPHist)
    (h6 : A.nodeD = B.nodeD) (h7 : A.sups = B.sups) (h8 : A.dmsgs = B.dmsgs) : A = B := by
  cases A; cases B
  simp only [SState.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## What executable states keep -/

/-- What every executable state reachable from `initSE` keeps, which soundness needs: a node
has dropped the operations of the records it took, and the hub has pruned no more records than
it has, as of any head. -/
structure SEOK (ses : SEState) : Prop where
  applied : ∀ n x, x ∈ flat (ses.appliedF n) → x ∈ ses.nodeDF n
  pruned : ses.pruned ≤ ses.recs.length
  hist : ∀ e ∈ ses.recHist, e.2.2 ≤ e.2.1.length

theorem SEOK.histF {ses : SEState} (hok : SEOK ses) (i : Nat) :
    ses.prunedHistF i ≤ (ses.recHistF i).length := by
  unfold SEState.prunedHistF SEState.recHistF
  rcases assocF_cases ses.recHist i ([], 0) with e | ⟨p, hp, e⟩
  · rw [e]; exact Nat.le_refl _
  · rw [← e]; exact hok.hist p hp

theorem appliedF_setD (ses : SEState) (n : Nat) (D : List Nat) (i : Nat) :
    (ses.setD n D).appliedF i = ses.appliedF i := rfl

theorem appliedF_adoptR (ses : SEState) (n : Nat) (R : List Rec) (i : Nat) :
    (ses.adoptR n R).appliedF i = if i = n then R else ses.appliedF i :=
  assocF_set _ _ _ _ _

/-- Records that are the hub's drop every operation it pruned. -/
theorem pruned_of_records {ses : SEState} {A : List Rec}
    (hr : setP (flat A) = setP (flat ses.recs)) {x : Nat} (hx : x ∈ ses.hubPL) :
    x ∈ flat A := by
  have e := congrFun hr x
  simp only [setP] at e
  rw [e]; exact mem_flat_take hx

/-! ## The guards are `HeadOK` and `HeadsOK` -/

theorem nodeAt_not_key (l : List (Nat × ENode)) {i : Nat} (hi : i ∉ l.map Prod.fst) :
    nodeAt l i = ENode.init := by
  unfold nodeAt
  have : l.find? (fun p => p.1 == i) = none := by
    rw [List.find?_eq_none]
    intro p hp
    simp only [beq_iff_eq]
    intro e
    exact hi (List.mem_map.2 ⟨p, hp, e⟩)
  rw [this]; rfl

theorem headOKB_ok {ses : SEState} {es' : EState}
    (h : headOKB ses es' = true) : HeadOK (sabs ses) (abs es') := by
  unfold headOKB at h
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
  rcases h with h | ⟨hr, hc⟩
  · exact Or.inl h
  · right
    refine ⟨not_remembered (not_mem_of_not_contains hr), ?_⟩
    rcases hc with h0 | hc
    · right
      intro x hx
      have hx' : x ∈ flat (ses.recs.take ses.pruned) := hx
      rw [h0, List.take_zero] at hx'
      simp [flat] at hx'
    · left
      obtain ⟨e, he, hm⟩ := List.any_eq_true.1 hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      exact ⟨e.1, setP (flat e.2.1), setP e.2.2.1, ⟨e, he, rfl, rfl, rfl, hm.1.symm⟩,
        fun x hx => pruned_of_records (recEq_flat hm.2) hx⟩

theorem headsOKB_ok {ses : SEState} {es' : EState} (h : headsOKB ses es' = true) :
    HeadsOK (sabs ses) (abs es') := by
  intro n x hx
  unfold headsOKB at h
  rw [List.all_eq_true] at h
  by_cases hk : n ∈ nodeKeys ses.es es'
  · have := h n hk
    rw [List.all_eq_true] at this
    have := this x hx
    simp only [Bool.or_eq_true, List.contains_iff_mem] at this
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (not_mem_of_not_contains h1)
  · simp only [nodeKeys, List.mem_append, not_or] at hk
    left
    show x ∈ (ses.es.nodeOf n).heads
    have e1 : es'.nodeOf n = ENode.init := nodeAt_not_key _ hk.2
    have e2 : ses.es.nodeOf n = ENode.init := nodeAt_not_key _ hk.1
    have hx' : x ∈ (es'.nodeOf n).heads := hx
    rw [e1] at hx'; rw [e2]; exact hx'

theorem sabs_withBase (ses : SEState) (es' : EState) :
    sabs (ses.withBase es') = (sabs ses).withBase (abs es') := by
  unfold SEState.withBase SState.withBase
  by_cases hq : es'.hub.seq = ses.es.hub.seq
  · have h1 : (abs es').hub.seq = (sabs ses).s.hub.seq := hq
    simp only [h1, ↓reduceIte]
    simp only [hq, beq_self_eq_true, ↓reduceIte]
    rfl
  · have h1 : ¬ (abs es').hub.seq = (sabs ses).s.hub.seq := hq
    simp only [h1, ↓reduceIte]
    have hq' : (es'.hub.seq == ses.es.hub.seq) = false := by simp [hq]
    simp only [hq', Bool.false_eq_true, ↓reduceIte]
    show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
    congr 1
    · funext i
      show setP (flat (assocF ((es'.hub.seq, ses.recs, ses.pruned) :: ses.recHist) i
        ([], 0)).1) = upd (fun i => setP (flat (ses.recHistF i))) es'.hub.seq (setP ses.hubDL) i
      rw [assocF_cons]
      by_cases hi : i = es'.hub.seq
      · subst hi; simp [upd, SEState.hubDL]
      · simp [upd, hi, SEState.recHistF]
    · funext i
      show setP (flat ((assocF ((es'.hub.seq, ses.recs, ses.pruned) :: ses.recHist) i
        ([], 0)).1.take (assocF ((es'.hub.seq, ses.recs, ses.pruned) :: ses.recHist) i
        ([], 0)).2)) =
        upd (fun i => setP (flat ((ses.recHistF i).take (ses.prunedHistF i)))) es'.hub.seq
          (setP ses.hubPL) i
      rw [assocF_cons]
      by_cases hi : i = es'.hub.seq
      · subst hi; simp [upd, SEState.hubPL]
      · simp [upd, hi, SEState.recHistF, SEState.prunedHistF]

/-! ## Soundness -/

theorem send_hub (es : EState) (m : EMsg) : (es.send m).hub = es.hub := by
  unfold EState.send; split <;> rfl

theorem execStep_hubPushAccept {N : Nat} {es es' : EState} {n : Nat} {S O : List Nat}
    {e d : Nat} (h : execStep N es (.hubPushAccept n S O e d) = .ok es') :
    es'.hub.seq = es.hub.seq + 1 ∧ es'.hub.head = d := by
  obtain ⟨-, h⟩ := req_ok h
  simp only [execCore] at h
  obtain ⟨-, h⟩ := req_ok h; obtain ⟨-, h⟩ := req_ok h; obtain ⟨-, h⟩ := req_ok h
  obtain ⟨-, h⟩ := req_ok h; obtain ⟨-, h⟩ := req_ok h
  cases h
  simp [send_hub, EState.hubAccept, EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]

theorem execStep_regress {N : Nat} {es es' : EState} {i : Nat}
    (h : execStep N es (.hubRegress i) = .ok es') : i ≤ es.hub.seq ∧ es' = es.regress i := by
  obtain ⟨-, h⟩ := req_ok h
  simp only [execCore] at h
  obtain ⟨hi, h⟩ := req_ok h
  cases h
  exact ⟨of_decide_eq_true hi, rfl⟩

theorem regressSeq_some {a : Action} {i : Nat} (h : a.regressSeq = some i) :
    a = .hubRegress i := by
  cases a <;> simp [Action.regressSeq] at h
  subst h; rfl

theorem regressSeq_none {a : Action} (h : a.regressSeq = none) : a.goesBack = false := by
  cases a <;> simp [Action.regressSeq, Action.goesBack] at h ⊢

/-- **Soundness of the executable model with supersedes**: every action `sexecStep` accepts,
from a state that keeps `SEOK`, is a step of `SRStep`, or no step. -/
theorem sexec_sound {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (h : sexecStep N ses a = .ok ses') :
    SRStep N (sabs ses) (sabs ses') ∨ sabs ses' = sabs ses := by
  obtain ⟨hwf, h⟩ := sreq_ok h
  have hlt := parOK_parLt hwf
  cases a with
  | base a =>
    simp only [sexecCore] at h
    cases hs : execStep N ses.es a with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      simp only at h
      cases hr : a.regressSeq with
      | some i =>
        rw [hr] at h
        cases h
        have ha := regressSeq_some hr
        subst ha
        obtain ⟨hi, rfl⟩ := execStep_regress hs
        left; right
        exact ⟨i, hi, rfl⟩
      | none =>
        rw [hr] at h
        simp only at h
        obtain ⟨hh, h⟩ := sreq_ok h
        obtain ⟨hn, h⟩ := sreq_ok h
        cases h
        left; left
        rw [sabs_withBase]
        exact SStep.base _ _ (exec_sound (regressSeq_none hr) hs) (headOKB_ok hh)
          (headsOKB_ok hn)
  | abandon n D =>
    simp only [sexecCore] at h
    obtain ⟨hn, h⟩ := sreq_ok h
    obtain ⟨hD, h⟩ := sreq_ok h
    obtain ⟨hhd, h⟩ := sreq_ok h
    obtain ⟨hr, h⟩ := sreq_ok h
    cases h
    left; left
    have e : sabs (ses.setD n (union (ses.nodeDF n) D)) =
        { sabs ses with
          nodeD := upd (sabs ses).nodeD n (fun x => (sabs ses).nodeD n x ∨ setP D x) } := by
      show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
      congr 1
      rw [setP_nodeD_setD, setP_union]; rfl
    rw [e]
    refine SStep.abandon _ n (setP D) (of_decide_eq_true hn) ?_ ?_ ?_
    · intro x hx
      rw [List.all_eq_true] at hD
      obtain ⟨g, hg, hA⟩ := List.any_eq_true.1 (hD x hx)
      exact ⟨g, hg, (ancB_iff hlt).1 hA⟩
    · intro g hg hgD
      rw [List.all_eq_true] at hhd
      exact not_mem_of_not_contains (hhd g hgD) hg
    · exact not_mem_of_not_contains hr
  | sendSup n d =>
    simp only [sexecCore] at h
    obtain ⟨hn, h⟩ := sreq_ok h
    obtain ⟨hd, h⟩ := sreq_ok h
    cases h
    left; left
    have e : sabs { ses with sups := ses.sups ++ [(n, ses.appliedF n, ses.nodeDF n, d)] } =
        (sabs ses).sendSupS n d (setP (flat (ses.appliedF n))) := by
      show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
      congr 1
      funext m T Δ g
      apply propext
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨e, he | rfl, h1, h2, h3, h4⟩
        · exact Or.inl ⟨e, he, h1, h2, h3, h4⟩
        · exact Or.inr ⟨h1.symm, h2, h3, h4⟩
      · rintro (⟨e, he, h1, h2, h3, h4⟩ | ⟨rfl, rfl, rfl, rfl⟩)
        · exact ⟨e, Or.inl he, h1, h2, h3, h4⟩
        · exact ⟨_, Or.inr rfl, rfl, rfl, rfl, rfl⟩
    rw [e]
    exact SStep.sendSup _ n d _ (of_decide_eq_true hn) (fun x hx => hok.applied n x hx)
      (not_mem_of_not_contains hd)
  | sendD n =>
    simp only [sexecCore] at h
    cases h
    left; left
    have e : sabs { ses with dmsgs := ses.dmsgs ++ [(n, ses.recs)] } =
        { sabs ses with
          dmsgs := fun m Δ => (sabs ses).dmsgs m Δ ∨ (m = n ∧ Δ = (sabs ses).hubD) } := by
      show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
      congr 1
      funext m Δ
      apply propext
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨e, he | rfl, h1, h2⟩
        · exact Or.inl ⟨e, he, h1, h2⟩
        · exact Or.inr ⟨h1.symm, h2⟩
      · rintro (⟨e, he, h1, h2⟩ | ⟨rfl, rfl⟩)
        · exact ⟨e, Or.inl he, h1, h2⟩
        · exact ⟨_, Or.inr rfl, rfl, rfl⟩
    rw [e]
    exact SStep.sendD _ n (sabs ses).hubD (fun _ h => h.1) (fun _ h => h)
  | adopt n R =>
    simp only [sexecCore] at h
    obtain ⟨hn, h⟩ := sreq_ok h
    obtain ⟨hm, h⟩ := sreq_ok h
    obtain ⟨hhd, h⟩ := sreq_ok h
    cases h
    left; left
    obtain ⟨em, hem, hmatch⟩ := List.any_eq_true.1 hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    have hR : setP (flat em.2) = setP (flat R) := recEq_flat hmatch.2
    have e : sabs (ses.adoptR n R) =
        { sabs ses with
          nodeD := upd (sabs ses).nodeD n
            (fun x => (sabs ses).nodeD n x ∨ setP (flat R) x) } := by
      show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
      congr 1
      have := setP_nodeD_setD ses n (union (ses.nodeDF n) (flat R))
      rw [setP_union] at this
      exact this
    rw [e]
    refine SStep.adopt _ n (setP (flat R)) (of_decide_eq_true hn)
      ⟨em, hem, hmatch.1, hR.symm⟩ ?_
    intro g hg hgR
    rw [List.all_eq_true] at hhd
    exact not_mem_of_not_contains (hhd g hg) hgR
  | hubSupAccept n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨hm, h⟩ := sreq_ok h
    obtain ⟨hA, h⟩ := sreq_ok h
    obtain ⟨hd, h⟩ := sreq_ok h
    cases hs : execStep N ses.es (.hubPushAccept n S O e d) with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      simp only at h
      obtain ⟨hn, h⟩ := sreq_ok h
      cases h
      left; left
      obtain ⟨hseq, hhead⟩ := execStep_hubPushAccept hs
      obtain ⟨sm, hsm, hmatch⟩ := List.any_eq_true.1 hm
      simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hmatch
      have hD : setP (flat (ses.takeRecs Δ)) = fun x => setP ses.hubDL x ∨ setP Δ x := by
        funext x; exact propext (mem_takeRecs ses Δ x)
      have hF : (ses.takeRecs Δ).take ses.pruned = ses.recs.take ses.pruned :=
        takeRecs_take ses Δ hok.pruned
      have e : sabs (ses.supAccept es' Δ) =
          { sabs ses with
            s := abs es'
            hubD := fun x => (sabs ses).hubD x ∨ setP Δ x
            hubDHist := upd (sabs ses).hubDHist (abs es').hub.seq
              (fun x => (sabs ses).hubD x ∨ setP Δ x)
            hubPHist := upd (sabs ses).hubPHist (abs es').hub.seq (sabs ses).hubP } := by
        refine sstate_ext rfl hD ?_ ?_ ?_ rfl rfl rfl
        · funext i
          show setP (flat (assocF ((es'.hub.seq, ses.takeRecs Δ, ses.pruned) :: ses.recHist) i
            ([], 0)).1) = _
          rw [assocF_cons]
          by_cases hi : i = es'.hub.seq
          · subst hi; simp only [↓reduceIte, upd]; rw [hD]; simp [abs, sabs]
          · have hi' : ¬ i = (abs es').hub.seq := hi
            simp only [hi, hi', ↓reduceIte, upd]; rfl
        · show setP (flat ((ses.takeRecs Δ).take ses.pruned)) =
            setP (flat (ses.recs.take ses.pruned))
          rw [hF]
        · funext i
          show setP (flat ((assocF ((es'.hub.seq, ses.takeRecs Δ, ses.pruned) :: ses.recHist) i
            ([], 0)).1.take (assocF ((es'.hub.seq, ses.takeRecs Δ, ses.pruned) :: ses.recHist) i
            ([], 0)).2)) = _
          rw [assocF_cons]
          by_cases hi : i = es'.hub.seq
          · subst hi; simp only [↓reduceIte, upd]; rw [hF]; simp [abs, sabs, SEState.hubPL]
          · have hi' : ¬ i = (abs es').hub.seq := hi
            simp only [hi, hi', ↓reduceIte, upd]; rfl
      rw [e]
      have hrecs : setP (flat sm.2.1) = setP (flat ses.recs) :=
        (recEq_flat h2).trans (recEq_flat hA)
      have hA' : setP (flat sm.2.1) = setP (flat A) := recEq_flat h2
      simp only [Bool.and_eq_true] at hd
      obtain ⟨hrem, hpend⟩ := hd
      refine SStep.sup _ _ n (setP (flat sm.2.1)) (setP Δ) (exec_sound rfl hs) hseq
        ⟨sm, hsm, h1, rfl, (seteq_setP h3).symm,
          by show es'.hub.head = _; rw [hhead]; exact h4.symm⟩
        (fun x hx => pruned_of_records hrecs hx) ?_ ?_ (headsOKB_ok hn)
      · show ¬ (es'.hub.head ∈ ses.hubDL ∧ es'.hub.head ∉ ses.hubPL)
        rw [hhead]; exact not_remembered (not_mem_of_not_contains hrem)
      · show ¬ (es'.hub.head ∈ Δ ∧ ¬ es'.hub.head ∈ flat sm.2.1)
        rw [hhead]
        rintro ⟨hdΔ, hdT⟩
        have hdA : d ∉ flat A := by
          have e := congrFun hA' d
          simp only [setP] at e
          rw [← e]; exact hdT
        apply not_mem_of_not_contains hpend
        unfold pendingOf
        rw [List.mem_filter]
        refine ⟨hdΔ, ?_⟩
        cases hc : (flat A).contains d
        · rfl
        · exact absurd (List.contains_iff_mem.1 hc) hdA
  | hubPushRefuse n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact Or.inr rfl
  | prune k =>
    simp only [sexecCore] at h
    obtain ⟨hk, h⟩ := sreq_ok h
    obtain ⟨hlen, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    cases h
    left; left
    have hk' : ses.pruned ≤ k := of_decide_eq_true hk
    have e : sabs (ses.pruneR k) =
        { sabs ses with
          hubP := fun x => (sabs ses).hubP x ∨ setP (flat (ses.recs.take k)) x
          hubPHist := upd (sabs ses).hubPHist (sabs ses).s.hub.seq
            (fun x => (sabs ses).hubP x ∨ setP (flat (ses.recs.take k)) x)
          hubDHist := upd (sabs ses).hubDHist (sabs ses).s.hub.seq (sabs ses).hubD } := by
      have hFk : setP (flat (ses.recs.take k)) =
          fun x => setP ses.hubPL x ∨ setP (flat (ses.recs.take k)) x := by
        funext x; apply propext
        exact ⟨Or.inr, fun h => h.elim (fun h => mem_flat_take_mono hk' h) id⟩
      refine sstate_ext rfl rfl ?_ hFk ?_ rfl rfl rfl
      · funext i
        show setP (flat (assocF ((ses.es.hub.seq, ses.recs, k) :: ses.recHist) i ([], 0)).1) = _
        rw [assocF_cons]
        by_cases hi : i = ses.es.hub.seq
        · subst hi; simp [upd, sabs, abs, SEState.hubDL]
        · have hi' : ¬ i = (sabs ses).s.hub.seq := hi
          simp only [hi, hi', ↓reduceIte, upd]; rfl
      · funext i
        show setP (flat ((assocF ((ses.es.hub.seq, ses.recs, k) :: ses.recHist) i
          ([], 0)).1.take (assocF ((ses.es.hub.seq, ses.recs, k) :: ses.recHist) i ([], 0)).2)) = _
        rw [assocF_cons]
        by_cases hi : i = ses.es.hub.seq
        · subst hi; simp only [↓reduceIte, upd]; rw [hFk]; simp [sabs, abs]
        · have hi' : ¬ i = (sabs ses).s.hub.seq := hi
          simp only [hi, hi', ↓reduceIte, upd]; rfl
    rw [e]
    exact SStep.prune _ (setP (flat (ses.recs.take k))) (fun x hx => mem_flat_take hx)

/-- The executable initial state abstracts to the relational one. -/
theorem sabs_initSE : sabs initSE = SState.init := by
  show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
  rw [show abs initSE.es = init from abs_initE]
  congr 1 <;> (try funext) <;> (try funext) <;> (try funext) <;>
    simp [initSE, SEState.hubDL, SEState.hubPL, SEState.recHistF, SEState.prunedHistF,
      SEState.nodeDF, assocF, flat, setP]

/-- States reachable through `sexecStep` from `initSE`. -/
inductive SExecReachable (N : Nat) : SEState → Prop
  | init : SExecReachable N initSE
  | step {ses ses' : SEState} (a : SAction) : SExecReachable N ses →
      sexecStep N ses a = .ok ses' → SExecReachable N ses'

theorem seok_init : SEOK initSE where
  applied := fun _ _ h => by simp [SEState.appliedF, initSE, assocF, flat] at h
  pruned := Nat.le_refl _
  hist := fun _ h => by simp [initSE] at h

/-- A node's dropped set that grows keeps what it had. -/
theorem seok_setD {ses : SEState} (hok : SEOK ses) (n : Nat) (D : List Nat)
    (hD : ∀ x, x ∈ ses.nodeDF n → x ∈ D) : SEOK (ses.setD n D) where
  applied := fun m x hx => by
    rw [nodeDF_setD]
    rw [appliedF_setD] at hx
    by_cases hm : m = n
    · subst hm; simp only [↓reduceIte]; exact hD x (hok.applied m x hx)
    · simp only [hm, ↓reduceIte]; exact hok.applied m x hx
  pruned := hok.pruned
  hist := hok.hist

/-- **Every action keeps `SEOK`.** -/
theorem sexec_ok {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (h : sexecStep N ses a = .ok ses') : SEOK ses' := by
  obtain ⟨-, h⟩ := sreq_ok h
  cases a with
  | base a =>
    simp only [sexecCore] at h
    cases hs : execStep N ses.es a with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      simp only at h
      cases hr : a.regressSeq with
      | some i =>
        rw [hr] at h
        cases h
        exact { hok with pruned := hok.histF i }
      | none =>
        rw [hr] at h
        simp only at h
        obtain ⟨-, h⟩ := sreq_ok h
        obtain ⟨-, h⟩ := sreq_ok h
        cases h
        refine { hok with hist := ?_ }
        unfold SEState.withBase
        split
        · exact hok.hist
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact hok.pruned
          · exact hok.hist e he
  | abandon n D =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact seok_setD hok n _ (fun x hx => mem_union.2 (Or.inl hx))
  | sendSup n d =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact ⟨hok.applied, hok.pruned, hok.hist⟩
  | sendD n =>
    simp only [sexecCore] at h
    cases h
    exact ⟨hok.applied, hok.pruned, hok.hist⟩
  | adopt n R =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    refine { hok with applied := ?_ }
    intro m x hx
    have e1 : (ses.adoptR n R).nodeDF m = (ses.setD n (union (ses.nodeDF n) (flat R))).nodeDF m :=
      rfl
    rw [e1, nodeDF_setD]
    rw [appliedF_adoptR] at hx
    by_cases hm : m = n
    · subst hm; simp only [↓reduceIte] at hx ⊢; exact mem_union.2 (Or.inr hx)
    · simp only [hm, ↓reduceIte] at hx ⊢; exact hok.applied m x hx
  | hubSupAccept n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases hs : execStep N ses.es (.hubPushAccept n S O e d) with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      simp only at h
      obtain ⟨-, h⟩ := sreq_ok h
      cases h
      refine { hok with pruned := Nat.le_trans hok.pruned (length_takeRecs ses Δ), hist := ?_ }
      intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact Nat.le_trans hok.pruned (length_takeRecs ses Δ)
      · exact hok.hist e he
  | hubPushRefuse n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact hok
  | prune k =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨hlen, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    cases h
    refine { hok with pruned := of_decide_eq_true hlen, hist := ?_ }
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact of_decide_eq_true hlen
    · exact hok.hist e he

/-- Every state reachable through `sexecStep` keeps `SEOK`. -/
theorem sexec_reachable_ok {N : Nat} {ses : SEState} (h : SExecReachable N ses) : SEOK ses := by
  induction h with
  | init => exact seok_init
  | step a _ hs ih => exact sexec_ok ih hs

/-- What every node of an executable state reachable from `initSE` has dropped: what the hub
has pruned, and had pruned as of any head, which the hub goes back to with it. -/
structure SEPruned (N : Nat) (ses : SEState) : Prop where
  now : ∀ n, n < N → ∀ x, x ∈ ses.hubPL → x ∈ ses.nodeDF n
  hist : ∀ e ∈ ses.recHist, ∀ n, n < N → ∀ x, x ∈ flat (e.2.1.take e.2.2) → x ∈ ses.nodeDF n

/-- A step that changes no records and only grows nodes' dropped sets keeps it. -/
theorem sepruned_mono {N : Nat} {ses ses' : SEState} (hp : SEPruned N ses)
    (hr : ses'.recs = ses.recs) (hk : ses'.pruned = ses.pruned) (hh : ses'.recHist = ses.recHist)
    (hD : ∀ n x, x ∈ ses.nodeDF n → x ∈ ses'.nodeDF n) : SEPruned N ses' where
  now := fun n hn x hx => by
    unfold SEState.hubPL at hx; rw [hr, hk] at hx
    exact hD n x (hp.now n hn x hx)
  hist := fun e he n hn x hx => by
    rw [hh] at he
    exact hD n x (hp.hist e he n hn x hx)

/-- A node's dropped set that grows in place, as `abandon` and `adopt` grow it. -/
theorem nodeDF_setD_union (ses : SEState) (n : Nat) (D : List Nat) (m x : Nat)
    (hx : x ∈ ses.nodeDF m) : x ∈ (ses.setD n (union (ses.nodeDF n) D)).nodeDF m := by
  rw [nodeDF_setD]
  by_cases hm : m = n
  · subst hm; simp only [↓reduceIte]; exact mem_union.2 (Or.inl hx)
  · simp only [hm, ↓reduceIte]; exact hx

theorem sepruned_init (N : Nat) : SEPruned N initSE where
  now := fun _ _ _ h => by simp [SEState.hubPL, initSE, flat] at h
  hist := fun _ h => by simp [initSE] at h

/-- **Every action keeps `SEPruned`**: the hub prunes only records every node has taken. -/
theorem sexec_pruned {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (hp : SEPruned N ses) (h : sexecStep N ses a = .ok ses') : SEPruned N ses' := by
  obtain ⟨-, h⟩ := sreq_ok h
  cases a with
  | base a =>
    simp only [sexecCore] at h
    cases hs : execStep N ses.es a with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      simp only at h
      cases hr : a.regressSeq with
      | some i =>
        rw [hr] at h
        cases h
        refine ⟨fun n hn x hx => ?_, hp.hist⟩
        have hx' : x ∈ flat ((ses.recHistF i).take (ses.prunedHistF i)) := hx
        unfold SEState.recHistF SEState.prunedHistF at hx'
        rcases assocF_cases ses.recHist i ([], 0) with e | ⟨q, hq, e⟩
        · rw [e] at hx'; simp [flat] at hx'
        · rw [← e] at hx'; exact hp.hist q hq n hn x hx'
      | none =>
        rw [hr] at h
        simp only at h
        obtain ⟨-, h⟩ := sreq_ok h
        obtain ⟨-, h⟩ := sreq_ok h
        cases h
        refine ⟨hp.now, ?_⟩
        unfold SEState.withBase
        split
        · exact hp.hist
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact hp.now
          · exact hp.hist e he
  | abandon n D =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact sepruned_mono hp rfl rfl rfl (fun m x hx => nodeDF_setD_union ses n D m x hx)
  | sendSup n d =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact sepruned_mono hp rfl rfl rfl (fun _ _ hx => hx)
  | sendD n =>
    simp only [sexecCore] at h
    cases h
    exact sepruned_mono hp rfl rfl rfl (fun _ _ hx => hx)
  | adopt n R =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact sepruned_mono hp rfl rfl rfl (fun m x hx => nodeDF_setD_union ses n (flat R) m x hx)
  | hubSupAccept n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases hs : execStep N ses.es (.hubPushAccept n S O e d) with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      simp only at h
      obtain ⟨-, h⟩ := sreq_ok h
      cases h
      have hF : (ses.takeRecs Δ).take ses.pruned = ses.recs.take ses.pruned :=
        takeRecs_take ses Δ hok.pruned
      refine ⟨fun n hn x hx => ?_, fun e he n hn x hx => ?_⟩
      · have hx' : x ∈ flat ((ses.takeRecs Δ).take ses.pruned) := hx
        rw [hF] at hx'; exact hp.now n hn x hx'
      · rcases List.mem_cons.1 he with rfl | he
        · have hx' : x ∈ flat ((ses.takeRecs Δ).take ses.pruned) := hx
          rw [hF] at hx'; exact hp.now n hn x hx'
        · exact hp.hist e he n hn x hx
  | hubPushRefuse n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h; obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact hp
  | prune k =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨hall, h⟩ := sreq_ok h
    cases h
    have taken : ∀ n, n < N → ∀ x, x ∈ flat (ses.recs.take k) → x ∈ ses.nodeDF n := by
      intro n hn x hx
      rw [List.all_eq_true] at hall
      have e2 := congrFun (recEq_flat (hall n (List.mem_range.2 hn))) x
      simp only [setP] at e2
      exact hok.applied n x (mem_flat_take (e2.mpr hx))
    refine ⟨taken, fun e he n hn x hx => ?_⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact taken n hn x hx
    · exact hp.hist e he n hn x hx

/-- Every state reachable through `sexecStep` keeps `SEPruned`. -/
theorem sexec_reachable_pruned {N : Nat} {ses : SEState} (h : SExecReachable N ses) :
    SEPruned N ses := by
  induction h with
  | init => exact sepruned_init N
  | step a hr hs ih => exact sexec_pruned (sexec_reachable_ok hr) ih hs

/-- **The executable hub prunes only what every node has dropped**: every state it reaches is
one where `eventually_convergesS` applies. -/
theorem sexec_allPruned {N : Nat} {ses : SEState} (h : SExecReachable N ses) :
    AllPruned N (sabs ses) :=
  fun n hn x hx => (sexec_reachable_pruned h).now n hn x hx

/-- Every state reachable through `sexecStep` is a state of the system with supersedes, so
every theorem of `Supersede.lean` applies to it. -/
theorem sexec_reachable {N : Nat} {ses : SEState} (h : SExecReachable N ses) :
    SRReachable N (sabs ses) := by
  induction h with
  | init => rw [sabs_initSE]; exact SRReachable.init
  | step a hr hs ih =>
    rcases sexec_sound (sexec_reachable_ok hr) hs with h | h
    · exact ih.step h
    · rw [h]; exact ih

/-- For example: no head is in its holder's dropped set, the root is in none, and every dropped
operation is below a head of a node that dropped it. -/
theorem sexec_inv {N : Nat} {ses : SEState} (h : SExecReachable N ses) : SInv N (sabs ses) :=
  sinv_reachable (sexec_reachable h)

/-! ## The liveness measure -/

theorem pendE_eq {N : Nat} (ses : SEState) : ses.pendE N = mPend N (sabs ses) := by
  unfold SEState.pendE mPend
  symm
  apply cnt_cntE
  intro x _
  simp [sabs, setP, List.any_eq_true, List.mem_range]

theorem lagE_eq {N : Nat} (ses : SEState) : ses.lagE N = mLag N (sabs ses) := by
  unfold SEState.lagE mLag
  apply sumN_congr
  intro n _
  symm
  apply cnt_cntE
  intro x _
  simp [sabs, setP]

/-- The executable measure is `smeasure`. -/
theorem smeasureE_eq {N : Nat} {ses : SEState} (hok : ses.es.parOK = true) :
    ses.smeasureE N = smeasure N (sabs ses) := by
  unfold SEState.smeasureE smeasure
  rw [pendE_eq, lagE_eq, rmeasureE_eq hok]
  rfl

/-- The executable convergence check is `SConverged`. -/
theorem sconvergedE_iff {N : Nat} {ses : SEState} :
    ses.sconvergedE N = true ↔ SConverged N (sabs ses) := by
  unfold SEState.sconvergedE SConverged
  rw [Bool.and_eq_true, convergedE_iff]
  apply and_congr Iff.rfl
  simp only [List.all_eq_true, List.mem_range]
  apply forall_congr'; intro n
  apply imp_congr Iff.rfl
  constructor
  · intro h x
    have := congrFun (seteq_setP h) x
    simp only [setP] at this
    simp [sabs, setP, this]
  · intro h
    unfold seteq
    simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

end Musubi.Exec

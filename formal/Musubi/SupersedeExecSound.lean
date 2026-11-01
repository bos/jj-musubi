/-
Soundness of the executable model with supersedes: every action `sexecStep` accepts is a step
of `SRStep` between the abstracted states, or leaves them as they were (`sexec_sound`); and
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

theorem headOKB_ok {ses : SEState} {es' : EState} (h : headOKB ses es' = true) :
    HeadOK (sabs ses) (abs es') := by
  unfold headOKB at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (not_mem_of_not_contains h)

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
    show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
    congr 1
    funext i
    show setP (flat (assocF ((es'.hub.seq, ses.recs) :: ses.recHist) i [])) =
      upd (fun i => setP (flat (ses.recHistF i))) es'.hub.seq (setP ses.hubDL) i
    rw [assocF_cons]
    by_cases hi : i = es'.hub.seq
    · subst hi; simp [upd, SEState.hubDL]
    · simp [upd, hi, SEState.recHistF]

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

/-- **Soundness of the executable model with supersedes**: every action `sexecStep` accepts
is a step of `SRStep`, or no step. -/
theorem sexec_sound {N : Nat} {ses ses' : SEState} {a : SAction}
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
      show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
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
  | sendSup n =>
    simp only [sexecCore] at h
    obtain ⟨hn, h⟩ := sreq_ok h
    cases h
    left; left
    have e : sabs { ses with sups := ses.sups ++ [(n, ses.appliedF n, ses.nodeDF n)] } =
        { sabs ses with
          sups := fun m Δ => (sabs ses).sups m Δ ∨ (m = n ∧ Δ = (sabs ses).nodeD n) } := by
      show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
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
    exact SStep.sendSup _ n (of_decide_eq_true hn)
  | sendD n =>
    simp only [sexecCore] at h
    cases h
    left; left
    have e : sabs { ses with dmsgs := ses.dmsgs ++ [(n, ses.recs)] } =
        { sabs ses with
          dmsgs := fun m Δ => (sabs ses).dmsgs m Δ ∨ (m = n ∧ Δ = (sabs ses).hubD) } := by
      show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
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
    exact SStep.sendD _ n
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
      show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
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
    obtain ⟨-, h⟩ := sreq_ok h
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
      simp only [Bool.and_eq_true] at hd
      have hD : setP (flat (ses.takeRecs Δ)) = fun x => setP ses.hubDL x ∨ setP Δ x := by
        funext x; exact propext (mem_takeRecs ses Δ x)
      have e : sabs (ses.supAccept es' Δ) =
          { sabs ses with
            s := abs es'
            hubD := fun x => (sabs ses).hubD x ∨ setP Δ x
            hubDHist := upd (sabs ses).hubDHist (abs es').hub.seq
              (fun x => (sabs ses).hubD x ∨ setP Δ x) } := by
        show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
        congr 1
        funext i
        show setP (flat (assocF ((es'.hub.seq, ses.takeRecs Δ) :: ses.recHist) i [])) = _
        rw [assocF_cons]
        by_cases hi : i = es'.hub.seq
        · subst hi; simp only [↓reduceIte, upd]; rw [hD]; simp [abs, sabs]
        · have hi' : ¬ i = (abs es').hub.seq := hi
          simp only [hi, hi', ↓reduceIte, upd]; rfl
      rw [e]
      refine SStep.sup _ _ n (setP Δ) (exec_sound rfl hs) hseq
        ⟨sm, hsm, hmatch.1.1, (seteq_setP hmatch.2).symm⟩ ⟨?_, ?_⟩ (headsOKB_ok hn)
      · show ¬ es'.hub.head ∈ ses.hubDL
        rw [hhead]; exact not_mem_of_not_contains hd.1
      · show ¬ es'.hub.head ∈ Δ
        rw [hhead]; exact not_mem_of_not_contains hd.2
  | hubPushRefuse n S O e d A Δ =>
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact Or.inr rfl

/-- The executable initial state abstracts to the relational one. -/
theorem sabs_initSE : sabs initSE = SState.init := by
  show SState.mk _ _ _ _ _ _ = SState.mk _ _ _ _ _ _
  rw [show abs initSE.es = init from abs_initE]
  congr 1 <;> (try funext) <;> (try funext) <;> simp [initSE, SEState.hubDL, SEState.recHistF,
    SEState.nodeDF, assocF, flat, setP]

/-- States reachable through `sexecStep` from `initSE`. -/
inductive SExecReachable (N : Nat) : SEState → Prop
  | init : SExecReachable N initSE
  | step {ses ses' : SEState} (a : SAction) : SExecReachable N ses →
      sexecStep N ses a = .ok ses' → SExecReachable N ses'

/-- Every state reachable through `sexecStep` is a state of the system with supersedes, so
every theorem of `Supersede.lean` applies to it. -/
theorem sexec_reachable {N : Nat} {ses : SEState} (h : SExecReachable N ses) :
    SRReachable N (sabs ses) := by
  induction h with
  | init => rw [sabs_initSE]; exact SRReachable.init
  | step a _ hs ih =>
    rcases sexec_sound hs with h | h
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

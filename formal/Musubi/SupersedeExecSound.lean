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

open Musubi Contract

/-! ## Lookups -/

theorem not_mem_of_not_contains {l : List Nat} {x : Nat} (h : (!l.contains x) = true) :
    x ∉ l := by
  intro hx; rw [List.contains_iff_mem.2 hx] at h; cases h

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

/-- The records at a sequence number are the default, or some entry's. -/
theorem logAt_cases (l : List HistEntry) (i : Nat) :
    logAt l i = ⟨[], 0⟩ ∨ ∃ e ∈ l, e.log = logAt l i := by
  unfold logAt
  cases h : l.find? (fun e => e.seq == i) with
  | none => left; rfl
  | some e => right; exact ⟨e, List.mem_of_find?_eq_some h, rfl⟩

theorem logAt_cons (e : HistEntry) (l : List HistEntry) (i : Nat) :
    logAt (e :: l) i = if i = e.seq then e.log else logAt l i := by
  unfold logAt
  rw [find?_cons_if]
  by_cases hi : i = e.seq
  · subst hi; simp
  · have : (e.seq == i) = false := by simp; omega
    simp [this, hi]

/-- Two states with the same fields are the same. -/
theorem sstate_ext {A B : SState} (h1 : A.s = B.s) (h2 : A.hubD = B.hubD)
    (h3 : A.hubDHist = B.hubDHist) (h4 : A.hubP = B.hubP) (h5 : A.hubPHist = B.hubPHist)
    (h6 : A.nodeD = B.nodeD) (h7 : A.sups = B.sups) (h8 : A.dmsgs = B.dmsgs) : A = B := by
  cases A; cases B
  simp only [SState.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-! ## What executable states keep -/

/-- What every executable state reachable from `initSE` keeps, which soundness needs: a node
has dropped the operations of the records it took, and of every list of records it took
before, and the hub has pruned no more records than it has, as of any head. -/
structure SEOK (ses : SEState) : Prop where
  applied : ∀ n x, x ∈ flat (ses.appliedF n) → x ∈ ses.nodeDF n
  pruned : ses.pruned ≤ ses.recs.length
  hist : ∀ e ∈ ses.recHist, e.log.pruned ≤ e.log.recs.length
  held : ∀ n L x, L ∈ ses.heldF n → x ∈ flat L → x ∈ ses.nodeDF n

theorem SEOK.histF {ses : SEState} (hok : SEOK ses) (i : Nat) :
    ses.prunedHistF i ≤ (ses.recHistF i).length := by
  unfold SEState.prunedHistF SEState.recHistF
  rcases logAt_cases ses.recHist i with e | ⟨p, hp, e⟩
  · rw [e]; exact Nat.le_refl _
  · rw [← e]; exact hok.hist p hp

theorem appliedF_setD (ses : SEState) (n : Nat) (D : List Nat) (i : Nat) :
    (ses.setD n D).appliedF i = ses.appliedF i := rfl

theorem appliedF_adoptR (ses : SEState) (n : Nat) (R : List Rec) (i : Nat) :
    (ses.adoptR n R).appliedF i = if i = n then R else ses.appliedF i :=
  assocF_set _ _ _ _ _

theorem heldF_setD (ses : SEState) (n : Nat) (D : List Nat) (i : Nat) :
    (ses.setD n D).heldF i = ses.heldF i := rfl

theorem heldF_adoptR (ses : SEState) (n : Nat) (R : List Rec) (i : Nat) :
    (ses.adoptR n R).heldF i = if i = n then R :: ses.heldF n else ses.heldF i :=
  assocF_set _ _ _ _ _

/-- What a node has held, it holds once it takes more. -/
theorem heldF_adoptR_mono (ses : SEState) (n : Nat) (R : List Rec) (i : Nat) {L : List Rec}
    (h : L ∈ ses.heldF i) : L ∈ (ses.adoptR n R).heldF i := by
  rw [heldF_adoptR]
  by_cases hi : i = n
  · subst hi; simp only [↓reduceIte]; exact List.mem_cons_of_mem _ h
  · simp only [hi, ↓reduceIte]; exact h

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
  unfold nodeAt assocF
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
      exact ⟨e.node, setP (flat e.applied), setP e.dropped, ⟨e, he, rfl, rfl, rfl, hm.1.symm⟩,
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
      show setP (flat (logAt (⟨es'.hub.seq, ⟨ses.recs, ses.pruned⟩⟩ :: ses.recHist) i).recs) = upd
          (fun i => setP (flat (ses.recHistF i))) es'.hub.seq (setP ses.hubDL) i
      rw [logAt_cons]
      by_cases hi : i = es'.hub.seq
      · subst hi; simp [upd, SEState.hubDL]
      · simp [upd, hi, SEState.recHistF]
    · funext i
      show setP (flat ((logAt (⟨es'.hub.seq, ⟨ses.recs, ses.pruned⟩⟩ :: ses.recHist) i).recs.take
          (logAt (⟨es'.hub.seq, ⟨ses.recs, ses.pruned⟩⟩ :: ses.recHist) i).pruned)) = upd (fun i =>
          setP (flat ((ses.recHistF i).take (ses.prunedHistF i)))) es'.hub.seq (setP ses.hubPL) i
      rw [logAt_cons]
      by_cases hi : i = es'.hub.seq
      · subst hi; simp [upd, SEState.hubPL]
      · simp [upd, hi, SEState.recHistF, SEState.prunedHistF]

/-! ## Soundness -/

theorem send_hub (es : EState) (m : EMsg) : (es.send m).hub = es.hub := by
  unfold EState.send; split <;> rfl

theorem execStep_hubPushAccept {N : Nat} {es es' : EState} {n : Nat} {S O : List Nat}
    {e d : Nat} (h : execStep N es (.hubPushAccept n S O e d) = .ok es') :
    es'.hub.seq = es.hub.seq + 1 ∧ es'.hub.head = d := by
  unstep [execStep, execCore] h with - - - - - -
  simp [send_hub, EState.hubAccept, EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]

theorem execStep_regress {N : Nat} {es es' : EState} {i : Nat}
    (h : execStep N es (.hubRegress i) = .ok es') : i ≤ es.hub.seq ∧ es' = es.regress i := by
  unstep [execStep, execCore] h with - hi
  exact ⟨of_decide_eq_true hi, rfl⟩

theorem regressSeq_some {a : Action} {i : Nat} (h : a.regressSeq = some i) :
    a = .hubRegress i := by
  cases a <;> simp [Action.regressSeq] at h
  subst h; rfl

theorem regressSeq_none {a : Action} (h : a.regressSeq = none) : a.goesBack = false := by
  cases a <;> simp [Action.regressSeq, Action.goesBack] at h ⊢

/-- What `baseCore` accepting says: `execStep` accepted the action, and either the hub went back
to its records as of that sequence number, or `HeadOK` and `HeadsOK` hold. -/
theorem baseCore_ok {N : Nat} {ses ses' : SEState} {a : Action}
    (h : baseCore N ses a = .ok ses') :
    (∃ i es', execStep N ses.es a = .ok es' ∧ a.regressSeq = some i ∧
      ses' = { ses with es := es', recs := ses.recHistF i, pruned := ses.prunedHistF i }) ∨
    (∃ es', execStep N ses.es a = .ok es' ∧ a.regressSeq = none ∧ headOKB ses es' = true ∧
      headsOKB ses es' = true ∧ ses' = ses.withBase es') := by
  simp only [baseCore] at h
  cases hs : execStep N ses.es a with
  | error e => rw [hs] at h; cases h
  | ok es' =>
    rw [hs] at h
    simp only at h
    cases hr : a.regressSeq with
    | some i => rw [hr] at h; cases h; exact Or.inl ⟨i, es', rfl, rfl, rfl⟩
    | none =>
      rw [hr] at h
      simp only at h
      peel h with hh hn
      cases h
      exact Or.inr ⟨es', rfl, rfl, hh, hn, rfl⟩

theorem droppedKnown_some {ses : SEState} {a : Action} {n : Nat}
    (h : ses.droppedKnown a = some n) :
    a = .advance n ∧ (ses.nodeDF n).contains (ses.es.nodeOf n).known.head = true := by
  cases a with
  | advance m =>
    simp only [SEState.droppedKnown] at h
    split at h
    · cases h; exact ⟨rfl, by assumption⟩
    · cases h
  | _ => simp [SEState.droppedKnown] at h

/-- What `sexecCore` accepting a base action says: an advance to what survives of a known head
the node dropped, or `baseCore` accepted it and its outcome checks held. -/
theorem sexecCore_base {N : Nat} {ses ses' : SEState} {a : Action}
    (h : sexecCore N ses (.base a) = .ok ses') :
    (∃ n, a = .advance n ∧ advanceB N ses n = true ∧ ses' = ses.advanceTo n (ses.nodeDF n)) ∨
    (baseOutcomeB ses a = true ∧ baseCore N ses a = .ok ses') := by
  simp only [sexecCore] at h
  cases hd : ses.droppedKnown a with
  | some n =>
    rw [hd] at h
    simp only at h
    peel h with hb
    cases h
    exact Or.inl ⟨n, (droppedKnown_some hd).1, hb, rfl⟩
  | none =>
    rw [hd] at h
    simp only at h
    cases hc : baseCore N ses a with
    | error e => rw [hc] at h; cases h
    | ok t =>
      rw [hc] at h
      simp only at h
      peel h with ho
      cases h
      exact Or.inr ⟨ho, rfl⟩

theorem bD_setP (D : List Nat) : bD (setP D) = D.contains := by
  funext x
  by_cases hx : x ∈ D <;> simp [bD, setP, hx]

theorem setP_snoc (l : List Nat) (k : Nat) : setP (l ++ [k]) = fun y => setP l y ∨ y = k := by
  funext y
  simp [setP]

/-- An advance to the frontier is the relational one. -/
theorem sabs_advanceTo {ses : SEState} (hlt : ParLt ses.es.parF) (n : Nat) (D : List Nat) :
    sabs (ses.advanceTo n D) = { sabs ses with s := (sabs ses).s.frontierTo n (bD (setP D)) } := by
  show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
  congr 1
  unfold SEState.advanceTo State.frontierTo
  rw [abs_setNode]
  congr 1
  change Node.mk _ _ _ _ _ _ = Node.mk _ _ _ _ _ _
  congr 1
  rw [setP_frontier hlt, bD_setP, setP_snoc]
  rfl

/-- Taking records `R` is the relational adoption. -/
theorem sabs_adoptR (ses : SEState) (n : Nat) (R : List Rec) :
    sabs (ses.adoptR n R) =
      { sabs ses with
        nodeD := upd (sabs ses).nodeD n (fun x => (sabs ses).nodeD n x ∨ setP (flat R) x) } := by
  show SState.mk _ _ _ _ _ _ _ _ = SState.mk _ _ _ _ _ _ _ _
  congr 1
  have := setP_nodeD_setD ses n (union (ses.nodeDF n) (flat R))
  rw [setP_union] at this
  exact this

/-- The hub accepting a push is the relational acceptance. -/
theorem abs_acceptPush (es : EState) (n : Nat) (S O : List Nat) (d : Nat) :
    abs (es.acceptPush n S O d) = ((abs es).hubStore (setP S) (setP O)).acceptHead n d := by
  unfold EState.acceptPush State.acceptHead
  rw [abs_send_notify, abs_send _ nb, abs_hubAccept, abs_hubStore]
  rfl

theorem acceptPush_hub (es : EState) (n : Nat) (S O : List Nat) (d : Nat) :
    (es.acceptPush n S O d).hub.seq = es.hub.seq + 1 ∧ (es.acceptPush n S O d).hub.head = d := by
  simp [EState.acceptPush, send_hub, EState.hubAccept, EState.hubStore, EState.hubStoreOps,
    EState.hubStoreObjs]

/-- The hub taking a supersede with a push it accepts is the relational one. -/
theorem sabs_supAccept {ses : SEState} (hok : SEOK ses) {es' : EState}
    (hseq : es'.hub.seq = ses.es.hub.seq + 1) (Δ : List Nat) :
    sabs (ses.supAccept es' Δ) = (sabs ses).supAt (abs es') (setP Δ) := by
  have hD : setP (flat (ses.takeRecs Δ)) = fun x => setP ses.hubDL x ∨ setP Δ x := by
    funext x; exact propext (mem_takeRecs ses Δ x)
  have hF : (ses.takeRecs Δ).take ses.pruned = ses.recs.take ses.pruned :=
    takeRecs_take ses Δ hok.pruned
  have hq : (sabs ses).s.hub.seq + 1 = es'.hub.seq := hseq.symm
  unfold SState.supAt
  rw [hq]
  refine sstate_ext rfl hD ?_ ?_ ?_ rfl rfl rfl
  · funext i
    show setP (flat (logAt (⟨es'.hub.seq, ⟨ses.takeRecs Δ, ses.pruned⟩⟩ :: ses.recHist) i).recs)
        = _
    rw [logAt_cons]
    by_cases hi : i = es'.hub.seq
    · subst hi; simp only [↓reduceIte, upd]; rw [hD]; simp [abs, sabs]
    · simp only [hi, ↓reduceIte, upd]; rfl
  · show setP (flat ((ses.takeRecs Δ).take ses.pruned)) =
      setP (flat (ses.recs.take ses.pruned))
    rw [hF]
  · funext i
    show setP (flat ((logAt (⟨es'.hub.seq, ⟨ses.takeRecs Δ, ses.pruned⟩⟩ :: ses.recHist)
        i).recs.take (logAt (⟨es'.hub.seq, ⟨ses.takeRecs Δ, ses.pruned⟩⟩ :: ses.recHist)
        i).pruned)) = _
    rw [logAt_cons]
    by_cases hi : i = es'.hub.seq
    · subst hi; simp only [↓reduceIte, upd]; rw [hF]; simp [abs, sabs, SEState.hubPL]
    · simp only [hi, ↓reduceIte, upd]; rfl

/-- The ledger entry a push's checks found: a supersede the relational state has in flight. -/
theorem ledger_sups {ses : SEState} {n d : Nat} {A : List Rec} {Δ : List Nat}
    (h : ledgerB ses n d A Δ = true) :
    ∃ sm ∈ ses.sups, recEq sm.applied A = true ∧
      (sabs ses).sups n (setP (flat sm.applied)) (setP Δ) d := by
  obtain ⟨sm, hsm, hmatch⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hmatch
  exact ⟨sm, hsm, h2, sm, hsm, h1, rfl, (seteq_setP h3).symm, h4.symm⟩

/-- The new head is neither one the hub remembers dropping nor one of the push's pending drops,
in the relational terms. -/
theorem head_not_dropped {ses : SEState} {d : Nat} {A : List Rec} {Δ : List Nat}
    {T : OSet} (hT : T = setP (flat A)) (hrem : (!ses.remDL.contains d) = true)
    (hpend : (!(pendingOf A Δ).contains d) = true) :
    ¬ Remembered (sabs ses) d ∧ ¬ (setP Δ d ∧ ¬ T d) := by
  refine ⟨not_remembered (not_mem_of_not_contains hrem), ?_⟩
  rintro ⟨hdΔ, hdT⟩
  rw [hT] at hdT
  apply not_mem_of_not_contains hpend
  unfold pendingOf
  rw [List.mem_filter]
  refine ⟨hdΔ, ?_⟩
  cases hc : (flat A).contains d
  · rfl
  · exact absurd (List.contains_iff_mem.1 hc) hdT

/-- **Soundness of the executable model with supersedes**: every action `sexecStep` accepts,
from a state that keeps `SEOK`, is a step of `SRStep`, or no step. -/
theorem sexec_sound {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (h : sexecStep N ses a = .ok ses') :
    SRStep N (sabs ses) (sabs ses') ∨ sabs ses' = sabs ses := by
  peel h with hwf
  have hlt := parOK_parLt hwf
  cases a with
  | base a =>
    rcases sexecCore_base h with ⟨n, rfl, hb, rfl⟩ | ⟨ho, hc⟩
    · left; left
      simp only [advanceB, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hb
      obtain ⟨⟨⟨hn, hne⟩, hl⟩, hna⟩ := hb
      rw [sabs_advanceTo hlt]
      refine SStep.advance _ n hn (fun x hx => ?_) ?_
      · have hx' : x ∈ frontier ses.es.parF (ses.nodeDF n).contains
            ((ses.es.nodeOf n).heads ++ [(ses.es.nodeOf n).known.head]) := by
          rw [mem_frontier hlt, setP_snoc, ← bD_setP]; exact hx
        exact List.contains_iff_mem.1 ((List.all_eq_true.1 hl) x hx')
      · rintro ⟨g, hg, hbel⟩
        have : belowB ses.es.parF (ses.nodeDF n).contains (ses.es.nodeOf n).known.head g =
            true := by
          rw [belowB_iff hlt]
          refine ⟨fun e => by simp [e] at hne, ?_⟩
          rw [← bD_setP]; exact hbel
        simp only [List.any_eq_false] at hna
        exact absurd this (by simpa using hna g hg)
    rcases baseCore_ok hc with ⟨i, es', hs, hr, rfl⟩ | ⟨es', hs, hr, hh, hn, rfl⟩
    · have ha := regressSeq_some hr
      subst ha
      obtain ⟨hi, rfl⟩ := execStep_regress hs
      left; right
      refine ⟨i, hi, ?_, rfl⟩
      exact (closedB_iff hlt).1 ho
    · left; left
      rw [sabs_withBase]
      exact SStep.base _ _ (exec_sound (regressSeq_none hr) hs) (headOKB_ok hh)
        (headsOKB_ok hn)
  | abandon n D =>
    unstep [sexecCore] h with hn hD hhd hr
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
    unstep [sexecCore] h with hn hd
    left; left
    have e : sabs { ses with sups := ses.sups ++ [⟨n, ses.appliedF n, ses.nodeDF n, d⟩] } =
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
    unstep [sexecCore] h with -
    left; left
    have e : sabs { ses with dmsgs := ses.dmsgs ++ [⟨n, ⟨ses.recs, ses.pruned⟩⟩] } =
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
    unstep [sexecCore] h with hn hm hhd
    left; left
    obtain ⟨em, hem, hmatch⟩ := List.any_eq_true.1 hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    obtain ⟨⟨hmn, hmR⟩, -⟩ := hmatch
    have hR : setP (flat em.log.recs) = setP (flat R) := recEq_flat hmR
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
      ⟨em, hem, hmn, hR.symm⟩ ?_
    intro g hg hgR
    rw [List.all_eq_true] at hhd
    exact not_mem_of_not_contains (hhd g hg) hgR
  | hubSupAccept n S O e d A Δ =>
    unstep [sexecCore] h with hg
    left; left
    simp only [acceptB, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hm, hA⟩, hrem⟩, hpend⟩, hnet⟩, hne⟩, he⟩, hbel⟩, hcl⟩ := hg
    obtain ⟨hseq, hhead⟩ := acceptPush_hub ses.es n S O d
    rw [sabs_supAccept hok hseq, abs_acceptPush]
    obtain ⟨sm, -, hsA, hsm⟩ := ledger_sups hm
    have hrecs : setP (flat sm.applied) = setP (flat ses.recs) :=
      (recEq_flat hsA).trans (recEq_flat hA)
    obtain ⟨hr, hp⟩ := head_not_dropped (recEq_flat hsA) hrem hpend
    have hc : ClosedAt ((abs ses.es).hubStore (setP S) (setP O)) d := by
      rw [← abs_hubStore]; exact (closedB_iff (es := ses.es.hubStore S O) hlt).1 hcl
    refine SStep.sup _ _ n e d _ (setP Δ) (Offer.push _ _ (inNet_net nb hnet)) hsm
      (fun x hx => pruned_of_records hrecs hx) hr hp hne he ?_ hc
    have hD : (bD fun x => (sabs ses).hubD x ∨ setP Δ x) = (acceptDrops ses Δ).contains := by
      rw [show (fun x => (sabs ses).hubD x ∨ setP Δ x) = setP (union ses.hubDL Δ) from
        (setP_union _ _).symm, bD_setP]
      rfl
    rw [hD]
    exact ((belowB_iff hlt).1 hbel).2
  | hubSupReject n S O e d A Δ =>
    simp only [sexecCore] at h
    peel h with -
    rcases baseCore_ok h with ⟨i, es', hs, hr, -⟩ | ⟨es', hs, hr, hh, hn, rfl⟩
    · simp [Action.regressSeq] at hr
    · left; left
      rw [sabs_withBase]
      exact SStep.base _ _ (exec_sound (regressSeq_none hr) hs) (headOKB_ok hh)
        (headsOKB_ok hn)
  | advancePrepared n R =>
    unstep [sexecCore] h with hg
    left; left
    simp only [preparedB, Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨⟨hn, hm⟩, -⟩, hl⟩ := hg
    obtain ⟨em, hem, hmatch⟩ := List.any_eq_true.1 hm
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    obtain ⟨⟨hmn, hmR⟩, -⟩ := hmatch
    have hR : setP (flat em.log.recs) = setP (flat R) := recEq_flat hmR
    unfold SEState.preparedAdvance
    rw [sabs_adoptR, sabs_advanceTo hlt]
    have hD : setP (union (ses.nodeDF n) (flat R)) =
        fun y => (sabs ses).nodeD n y ∨ setP (flat R) y := setP_union _ _
    rw [hD]
    refine SStep.adoptPrepared _ n (setP (flat R)) hn ⟨em, hem, hmn, hR.symm⟩ (fun x hx => ?_)
    have hx' : x ∈ frontier ses.es.parF (union (ses.nodeDF n) (flat R)).contains
        ((ses.es.nodeOf n).heads ++ [(ses.es.nodeOf n).known.head]) := by
      rw [mem_frontier hlt, setP_snoc, ← bD_setP, hD]; exact hx
    exact List.contains_iff_mem.1 ((List.all_eq_true.1 hl) x hx')
  | hubPushRefuse n S O e d A Δ =>
    unstep [sexecCore] h with - - -
    exact Or.inr rfl
  | prune k =>
    unstep [sexecCore] h with hk hlen -
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
        show setP (flat (logAt (⟨ses.es.hub.seq, ⟨ses.recs, k⟩⟩ :: ses.recHist) i).recs) = _
        rw [logAt_cons]
        by_cases hi : i = ses.es.hub.seq
        · subst hi; simp [upd, sabs, abs, SEState.hubDL]
        · have hi' : ¬ i = (sabs ses).s.hub.seq := hi
          simp only [hi, hi', ↓reduceIte, upd]; rfl
      · funext i
        show setP (flat ((logAt (⟨ses.es.hub.seq, ⟨ses.recs, k⟩⟩ :: ses.recHist) i).recs.take (logAt
            (⟨ses.es.hub.seq, ⟨ses.recs, k⟩⟩ :: ses.recHist) i).pruned)) = _
        rw [logAt_cons]
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
      SEState.nodeDF, assocF, logAt, flat, setP]

/-- States reachable through `sexecStep` from `initSE`. -/
inductive SExecReachable (N : Nat) : SEState → Prop
  | init : SExecReachable N initSE
  | step {ses ses' : SEState} (a : SAction) : SExecReachable N ses →
      sexecStep N ses a = .ok ses' → SExecReachable N ses'

theorem seok_init : SEOK initSE where
  applied := fun _ _ h => by simp [SEState.appliedF, initSE, assocF, flat] at h
  pruned := Nat.le_refl _
  hist := fun _ h => by simp [initSE] at h
  held := fun _ L _ hL h => by
    simp only [SEState.heldF, initSE, assocF, List.find?_nil, Option.map_none,
      Option.getD_none, List.mem_singleton] at hL
    subst hL; simp [flat] at h

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
  held := fun m L x hL hx => by
    rw [heldF_setD] at hL
    rw [nodeDF_setD]
    by_cases hm : m = n
    · subst hm; simp only [↓reduceIte]; exact hD x (hok.held m L x hL hx)
    · simp only [hm, ↓reduceIte]; exact hok.held m L x hL hx

/-- Taking records keeps `SEOK`. -/
theorem seok_adoptR {ses : SEState} (hok : SEOK ses) (n : Nat) (R : List Rec) :
    SEOK (ses.adoptR n R) := by
  have e1 : ∀ m, (ses.adoptR n R).nodeDF m =
      (ses.setD n (union (ses.nodeDF n) (flat R))).nodeDF m := fun _ => rfl
  refine { hok with applied := ?_, held := ?_ }
  · intro m x hx
    rw [e1, nodeDF_setD]
    rw [appliedF_adoptR] at hx
    by_cases hm : m = n
    · subst hm; simp only [↓reduceIte] at hx ⊢; exact mem_union.2 (Or.inr hx)
    · simp only [hm, ↓reduceIte] at hx ⊢; exact hok.applied m x hx
  · intro m L x hL hx
    rw [e1, nodeDF_setD]
    rw [heldF_adoptR] at hL
    by_cases hm : m = n
    · subst hm; simp only [↓reduceIte] at hL ⊢
      rcases List.mem_cons.1 hL with rfl | hL
      · exact mem_union.2 (Or.inr hx)
      · exact mem_union.2 (Or.inl (hok.held m L x hL hx))
    · simp only [hm, ↓reduceIte] at hL ⊢; exact hok.held m L x hL hx

/-- What `baseCore` reaches keeps `SEOK`. -/
theorem seok_baseCore {N : Nat} {ses ses' : SEState} {a : Action} (hok : SEOK ses)
    (h : baseCore N ses a = .ok ses') : SEOK ses' := by
  rcases baseCore_ok h with ⟨i, _, -, -, rfl⟩ | ⟨_, -, -, -, -, rfl⟩
  · exact { hok with pruned := hok.histF i }
  · refine { hok with hist := ?_ }
    unfold SEState.withBase
    split
    · exact hok.hist
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hok.pruned
      · exact hok.hist e he

/-- **Every action keeps `SEOK`.** -/
theorem sexec_ok {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (h : sexecStep N ses a = .ok ses') : SEOK ses' := by
  peel h with -
  cases a with
  | base a =>
    rcases sexecCore_base h with ⟨n, -, -, rfl⟩ | ⟨-, hc⟩
    · exact ⟨hok.applied, hok.pruned, hok.hist, hok.held⟩
    · exact seok_baseCore hok hc
  | abandon n D =>
    unstep [sexecCore] h with - - - -
    exact seok_setD hok n _ (fun x hx => mem_union.2 (Or.inl hx))
  | sendSup n d =>
    unstep [sexecCore] h with - -
    exact ⟨hok.applied, hok.pruned, hok.hist, hok.held⟩
  | sendD n =>
    unstep [sexecCore] h with -
    exact ⟨hok.applied, hok.pruned, hok.hist, hok.held⟩
  | adopt n R =>
    unstep [sexecCore] h with - - -
    exact seok_adoptR hok n R
  | hubSupAccept n S O e d A Δ =>
    unstep [sexecCore] h with -
    refine { hok with pruned := Nat.le_trans hok.pruned (length_takeRecs ses Δ), hist := ?_ }
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact Nat.le_trans hok.pruned (length_takeRecs ses Δ)
    · exact hok.hist e he
  | hubPushRefuse n S O e d A Δ =>
    unstep [sexecCore] h with - - -
    exact hok
  | hubSupReject n S O e d A Δ =>
    simp only [sexecCore] at h
    peel h with -
    exact seok_baseCore hok h
  | advancePrepared n R =>
    unstep [sexecCore] h with -
    unfold SEState.preparedAdvance
    exact seok_adoptR (ses := ses.advanceTo n _) ⟨hok.applied, hok.pruned, hok.hist, hok.held⟩
      n R
  | prune k =>
    unstep [sexecCore] h with - hlen -
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
  hist : ∀ e ∈ ses.recHist, ∀ n, n < N → ∀ x, x ∈ flat (e.log.recs.take e.log.pruned) →
    x ∈ ses.nodeDF n

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

/-- What `baseCore` reaches keeps `SEPruned`. -/
theorem sepruned_baseCore {N : Nat} {ses ses' : SEState} {a : Action} (hp : SEPruned N ses)
    (h : baseCore N ses a = .ok ses') : SEPruned N ses' := by
  rcases baseCore_ok h with ⟨i, _, -, -, rfl⟩ | ⟨_, -, -, -, -, rfl⟩
  · refine ⟨fun n hn x hx => ?_, hp.hist⟩
    have hx' : x ∈ flat ((ses.recHistF i).take (ses.prunedHistF i)) := hx
    unfold SEState.recHistF SEState.prunedHistF at hx'
    rcases logAt_cases ses.recHist i with e | ⟨q, hq, e⟩
    · rw [e] at hx'; simp [flat] at hx'
    · rw [← e] at hx'; exact hp.hist q hq n hn x hx'
  · refine ⟨hp.now, ?_⟩
    unfold SEState.withBase
    split
    · exact hp.hist
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hp.now
      · exact hp.hist e he

/-- **Every action keeps `SEPruned`**: the hub prunes only records every node has taken. -/
theorem sexec_pruned {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (hp : SEPruned N ses) (h : sexecStep N ses a = .ok ses') : SEPruned N ses' := by
  peel h with -
  cases a with
  | base a =>
    rcases sexecCore_base h with ⟨n, -, -, rfl⟩ | ⟨-, hc⟩
    · exact sepruned_mono hp rfl rfl rfl (fun _ _ hx => hx)
    · exact sepruned_baseCore hp hc
  | abandon n D =>
    unstep [sexecCore] h with - - - -
    exact sepruned_mono hp rfl rfl rfl (fun m x hx => nodeDF_setD_union ses n D m x hx)
  | sendSup n d =>
    unstep [sexecCore] h with - -
    exact sepruned_mono hp rfl rfl rfl (fun _ _ hx => hx)
  | sendD n =>
    unstep [sexecCore] h with -
    exact sepruned_mono hp rfl rfl rfl (fun _ _ hx => hx)
  | adopt n R =>
    unstep [sexecCore] h with - - -
    exact sepruned_mono hp rfl rfl rfl (fun m x hx => nodeDF_setD_union ses n (flat R) m x hx)
  | hubSupAccept n S O e d A Δ =>
    unstep [sexecCore] h with -
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
    unstep [sexecCore] h with - - -
    exact hp
  | hubSupReject n S O e d A Δ =>
    simp only [sexecCore] at h
    peel h with -
    exact sepruned_baseCore hp h
  | advancePrepared n R =>
    unstep [sexecCore] h with -
    exact sepruned_mono hp rfl rfl rfl
      (fun m x hx => nodeDF_setD_union ses n (flat R) m x hx)
  | prune k =>
    unstep [sexecCore] h with - - hall
    have taken : ∀ n, n < N → ∀ x, x ∈ flat (ses.recs.take k) → x ∈ ses.nodeDF n := by
      intro n hn x hx
      rw [List.all_eq_true] at hall
      obtain ⟨L, hL, heq⟩ := List.any_eq_true.1 (hall n (List.mem_range.2 hn))
      have e2 := congrFun (recEq_flat heq) x
      simp only [setP] at e2
      exact hok.held n L x hL (mem_flat_take (e2.mpr hx))
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

/-! ## Nodes keep what the hub pruned -/

/-- What every executable state reachable from `initSE` keeps: every node has held the hub's
records as far as the hub has pruned them, now and as of any head it can go back
to; and the node every announcement is for has held the announced records as far as they were
pruned. A node holds the records it took last. -/
structure SEHeld (N : Nat) (ses : SEState) : Prop where
  applied : ∀ n, ses.appliedF n ∈ ses.heldF n
  now : ∀ n, n < N → ses.heldPrefix n ses.recs ses.pruned = true
  hist : ∀ e ∈ ses.recHist, ∀ n, n < N → ses.heldPrefix n e.log.recs e.log.pruned = true
  msgs : ∀ e ∈ ses.dmsgs, ses.heldPrefix e.node e.log.recs e.log.pruned = true

/-- What a node has held, it holds in a state that keeps every list it held. -/
theorem heldPrefix_mono {ses ses' : SEState} {n : Nat} {R : List Rec} {p : Nat}
    (hH : ∀ L, L ∈ ses.heldF n → L ∈ ses'.heldF n) (h : ses.heldPrefix n R p = true) :
    ses'.heldPrefix n R p = true := by
  obtain ⟨L, hL, e⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨L, hH L hL, e⟩

/-- Every node has held the first zero records of anything. -/
theorem heldPrefix_zero {ses : SEState} (hH : SEHeld N ses) (n : Nat) (R : List Rec) :
    ses.heldPrefix n R 0 = true :=
  List.any_eq_true.2 ⟨_, hH.applied n, by simp [recEq]⟩

/-- A step that changes no records and no announcements, and only adds to what nodes held,
keeping what each took last among it, keeps it. -/
theorem seheld_mono {N : Nat} {ses ses' : SEState} (hH : SEHeld N ses)
    (hr : ses'.recs = ses.recs) (hk : ses'.pruned = ses.pruned) (hh : ses'.recHist = ses.recHist)
    (hd : ses'.dmsgs = ses.dmsgs) (hL : ∀ n L, L ∈ ses.heldF n → L ∈ ses'.heldF n)
    (ha : ∀ n, ses'.appliedF n ∈ ses'.heldF n) : SEHeld N ses' where
  applied := ha
  now := fun n hn => by rw [hr, hk]; exact heldPrefix_mono (hL n) (hH.now n hn)
  hist := fun e he n hn => by rw [hh] at he; exact heldPrefix_mono (hL n) (hH.hist e he n hn)
  msgs := fun e he => by rw [hd] at he; exact heldPrefix_mono (hL e.node) (hH.msgs e he)

theorem seheld_init (N : Nat) : SEHeld N initSE where
  applied := fun _ => by simp [SEState.appliedF, SEState.heldF, initSE, assocF]
  now := fun _ _ => by simp [SEState.heldPrefix, SEState.heldF, initSE, assocF, recEq]
  hist := fun _ h => by simp [initSE] at h
  msgs := fun _ h => by simp [initSE] at h

/-- What `baseCore` reaches keeps `SEHeld`. -/
theorem seheld_baseCore {N : Nat} {ses ses' : SEState} {a : Action} (hH : SEHeld N ses)
    (h : baseCore N ses a = .ok ses') : SEHeld N ses' := by
  rcases baseCore_ok h with ⟨i, _, -, -, rfl⟩ | ⟨_, -, -, -, -, rfl⟩
  · refine ⟨hH.applied, fun n hn => ?_, hH.hist, hH.msgs⟩
    show ses.heldPrefix n (ses.recHistF i) (ses.prunedHistF i) = true
    unfold SEState.recHistF SEState.prunedHistF
    rcases logAt_cases ses.recHist i with e | ⟨q, hq, e⟩
    · rw [e]; exact heldPrefix_zero hH n _
    · rw [← e]; exact hH.hist q hq n hn
  · refine ⟨hH.applied, hH.now, ?_, hH.msgs⟩
    unfold SEState.withBase
    split
    · exact hH.hist
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hH.now
      · exact hH.hist e he

/-- Taking records keeps `SEHeld`. -/
theorem seheld_adoptR {N : Nat} {ses : SEState} (hH : SEHeld N ses) (n : Nat) (R : List Rec) :
    SEHeld N (ses.adoptR n R) := by
  refine seheld_mono hH rfl rfl rfl rfl (fun m L hL => heldF_adoptR_mono ses n R m hL)
    (fun m => ?_)
  rw [appliedF_adoptR, heldF_adoptR]
  by_cases hm : m = n
  · subst hm; simp only [↓reduceIte]; exact List.mem_cons_self
  · simp only [hm, ↓reduceIte]; exact hH.applied m

/-- **Every action keeps `SEHeld`.** -/
theorem sexec_held {N : Nat} {ses ses' : SEState} {a : SAction} (hok : SEOK ses)
    (hH : SEHeld N ses) (h : sexecStep N ses a = .ok ses') : SEHeld N ses' := by
  peel h with -
  cases a with
  | base a =>
    rcases sexecCore_base h with ⟨n, -, -, rfl⟩ | ⟨-, hc⟩
    · exact seheld_mono hH rfl rfl rfl rfl (fun _ _ hL => hL) hH.applied
    · exact seheld_baseCore hH hc
  | abandon n D =>
    unstep [sexecCore] h with - - - -
    exact seheld_mono hH rfl rfl rfl rfl (fun _ _ hL => hL) hH.applied
  | sendSup n d =>
    unstep [sexecCore] h with - -
    exact seheld_mono hH rfl rfl rfl rfl (fun _ _ hL => hL) hH.applied
  | sendD n =>
    unstep [sexecCore] h with hn
    refine ⟨hH.applied, hH.now, hH.hist, fun e he => ?_⟩
    rcases List.mem_append.1 he with he | he
    · exact hH.msgs e he
    · rw [List.mem_singleton.1 he]; exact hH.now n (of_decide_eq_true hn)
  | adopt n R =>
    unstep [sexecCore] h with - - -
    exact seheld_adoptR hH n R
  | hubSupAccept n S O e d A Δ =>
    unstep [sexecCore] h with -
    have hF : (ses.takeRecs Δ).take ses.pruned = ses.recs.take ses.pruned :=
      takeRecs_take ses Δ hok.pruned
    have now : ∀ n, n < N → ses.heldPrefix n (ses.takeRecs Δ) ses.pruned = true := by
      intro n hn
      unfold SEState.heldPrefix
      rw [hF]; exact hH.now n hn
    refine ⟨hH.applied, now, fun e he n hn => ?_, hH.msgs⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact now n hn
    · exact hH.hist e he n hn
  | hubPushRefuse n S O e d A Δ =>
    unstep [sexecCore] h with - - -
    exact hH
  | hubSupReject n S O e d A Δ =>
    simp only [sexecCore] at h
    peel h with -
    exact seheld_baseCore hH h
  | advancePrepared n R =>
    unstep [sexecCore] h with -
    unfold SEState.preparedAdvance
    exact seheld_adoptR (ses := ses.advanceTo n _)
      (seheld_mono hH rfl rfl rfl rfl (fun _ _ hL => hL) hH.applied) n R
  | prune k =>
    unstep [sexecCore] h with - - hall
    rw [List.all_eq_true] at hall
    have now : ∀ n, n < N → ses.heldPrefix n ses.recs k = true :=
      fun n hn => hall n (List.mem_range.2 hn)
    refine ⟨hH.applied, now, fun e he n hn => ?_, hH.msgs⟩
    rcases List.mem_cons.1 he with rfl | he
    · exact now n hn
    · exact hH.hist e he n hn

/-- Every state reachable through `sexecStep` keeps `SEHeld`. -/
theorem sexec_reachable_held {N : Nat} {ses : SEState} (h : SExecReachable N ses) :
    SEHeld N ses := by
  induction h with
  | init => exact seheld_init N
  | step a hr hs ih => exact sexec_held (sexec_reachable_ok hr) ih hs

/-- **Every node the hub waits for has held the records it pruned**: every announcement,
however old, passes the check `adopt` makes of it, that its node has held the announced records
as far as they were pruned. So a node that took fewer records since, from an older
announcement, takes the hub's records all the same, as the implementation does from the count
and digest of the pruned ones; and every node has held the hub's records as far as it has
pruned them now. -/
theorem sexec_announced_held {N : Nat} {ses : SEState} (h : SExecReachable N ses) :
    (∀ e ∈ ses.dmsgs, ses.heldPrefix e.node e.log.recs e.log.pruned = true) ∧
      ∀ n, n < N → ses.heldPrefix n ses.recs ses.pruned = true :=
  ⟨(sexec_reachable_held h).msgs, (sexec_reachable_held h).now⟩

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

/-! ## The measure through surviving images -/

/-- After an advance to the frontier, every surviving image of the known head is covered. -/
theorem uncoveredImages_after_advance {par : Nat → List Nat} {D : Nat → Bool}
    {heads : List Nat} {known B : Nat} (hlt : ParLt par) (hb : ∀ h ∈ heads, h < B)
    (hk : known < B) : uncoveredImages par D (frontier par D (heads ++ [known])) known = 0 := by
  unfold uncoveredImages
  have hb' : ∀ g ∈ heads ++ [known], g < B := by
    intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hb g hg
    · exact (List.mem_singleton.1 hg) ▸ hk
  have hnil : (exp par D known).filter
      (fun p => !(frontier par D (heads ++ [known])).any (ancB par p)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨h, hh, ha⟩ := frontier_covers_image hlt hb' (by simp) hp
    have he : (frontier par D (heads ++ [known])).any (ancB par p) = true :=
      List.any_eq_true.2 ⟨h, hh, (ancB_iff hlt).2 ha⟩
    simp [he]
  rw [hnil]
  rfl

theorem uncoveredImages_singleton_zero {par : Nat → List Nat} {D : Nat → Bool} {h known : Nat}
    (hlt : ParLt par) : uncoveredImages par D [h] known = 0 ↔ Below par D known h := by
  simp [uncoveredImages, List.filter_eq_nil_iff, Below, ancB_iff hlt]

/-- Without dropped operations the measure equals `EState.rmeasureE` of `Exec.lean`. -/
theorem rmeasureCE_without_drops {ses : SEState} {N : Nat} (hlt : ParLt ses.es.parF)
    (hD : ∀ n x, (ses.nodeDF n).contains x = false) :
    ses.rmeasureCE N = ses.es.rmeasureE N := by
  have ha : ∀ n, ses.advCE n = ses.es.advE n := by
    intro n
    unfold SEState.advCE uncoveredImages
    rw [exp_eq hlt, hD]
    unfold EState.advE
    cases he : (ses.es.nodeOf n).heads.any (ancB ses.es.parF (ses.es.nodeOf n).known.head)
      <;> simp [he]
  have he : ∀ n x, exp ses.es.parF (ses.nodeDF n).contains x = [x] := by
    intro n x
    rw [exp_eq hlt, hD]
    rfl
  have hs : ∀ n, ses.settledCE n = ses.es.settledE n := by
    intro n
    unfold SEState.settledCE EState.settledE
    cases (ses.es.nodeOf n).heads <;>
      simp only [hD, he, Bool.not_false, Bool.true_or, Bool.and_true,
        List.all_cons, List.all_nil]
  have hadv : ses.advCE = ses.es.advE := funext ha
  simp only [SEState.rmeasureCE, EState.rmeasureE, hadv, hs]

end Musubi.Exec

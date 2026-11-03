/-
Entry to the rollback-free record suffix. The current head's survival is not a consequence
of SEOK alone: rollback must restore a head with the records saved at that same sequence.
This invariant keeps that fact for every saved slot, without requiring the old model's
original-ancestry history chain, which contracted acceptance does not preserve.
-/
import Musubi.PostCut

namespace Musubi.Exec

open Musubi

structure CutHistory (s : SEState) : Prop where
  cut : CutInv s
  atSeq : s.es.hub.histF s.es.hub.seq = s.es.hub.head
  savedHead : ∀ i, i ≤ s.es.hub.seq → s.es.hub.histF i ∉ flat (s.recHistF i)

theorem cutHistory_init : CutHistory initSE := by
  refine ⟨cutInv_init, rfl, ?_⟩
  intro i _
  simp [initSE, SEState.recHistF, assocF, flat]

/-- Apart from acceptance, the base actions leave the saved head history alone, including
rollback, which selects a slot rather than modifying one. -/
theorem execStep_hist_fixed {N : Nat} {es es' : EState} {a : Action}
    (h : execStep N es a = .ok es')
    (hc : ∀ n e d, a ≠ .casAccept n e d)
    (hp : ∀ n S O e d, a ≠ .hubPushAccept n S O e d) :
    es'.hub.hist = es.hub.hist := by
  obtain ⟨-, h⟩ := req_ok h
  cases a with
  | casAccept n e d => exact absurd rfl (hc n e d)
  | hubPushAccept n S O e d => exact absurd rfl (hp n S O e d)
  | _ =>
    simp only [execCore, req] at h
    repeat' split at h
    all_goals
      first
      | (simp at h; done)
      | (cases h; simp [send_hub, EState.userOp, EState.mergeOp, EState.createOp,
          EState.setNode, EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs,
          EState.forget, EState.regress])

theorem execStep_accept_hist {N : Nat} {es es' : EState} {n : Nat}
    {S O : List Nat} {e d : Nat}
    (h : execStep N es (.hubPushAccept n S O e d) = .ok es') :
    es'.hub.hist = (es.hub.seq + 1, d) :: es.hub.hist := by
  obtain ⟨-, h⟩ := req_ok h
  simp only [execCore] at h
  obtain ⟨-, h⟩ := req_ok h
  obtain ⟨-, h⟩ := req_ok h
  obtain ⟨-, h⟩ := req_ok h
  obtain ⟨-, h⟩ := req_ok h
  obtain ⟨-, h⟩ := req_ok h
  cases h
  simp [send_hub, EState.hubAccept, EState.hubStore,
    EState.hubStoreOps, EState.hubStoreObjs]

theorem histF_saved (hub : EHub) (k d i : Nat) :
    ({ hub with hist := (k, d) :: hub.hist }).histF i =
      if i = k then d else hub.histF i := by
  simp only [EHub.histF]
  by_cases hi : i = k
  · subst i; simp
  · simp [hi, Ne.symm hi]

theorem recHistF_saved (s : SEState) (k p i : Nat) (R : List Rec) :
    ({ s with recHist := (k, R, p) :: s.recHist }).recHistF i =
      if i = k then R else s.recHistF i := by
  simp only [SEState.recHistF, assocF_cons]
  split <;> rfl

/-- A non-rollback step either leaves both histories and the current pair alone, or saves
the current pair and records in one slot, leaving every other slot unchanged. -/
inductive HistoryUpdate (s t : SEState) : Prop
  | frame (hh : t.es.hub.head = s.es.hub.head) (hs : t.es.hub.seq = s.es.hub.seq)
      (hist : t.es.hub.histF = s.es.hub.histF) (recs : t.recHistF = s.recHistF)
  | save (bound : t.es.hub.seq ≤ s.es.hub.seq + 1)
      (atSeq : t.es.hub.histF t.es.hub.seq = t.es.hub.head)
      (current : t.recHistF t.es.hub.seq = t.recs)
      (other : ∀ i, i ≠ t.es.hub.seq →
        t.es.hub.histF i = s.es.hub.histF i ∧ t.recHistF i = s.recHistF i)

theorem withBase_history {s : SEState} {es : EState}
    (hh : es.hub.head = s.es.hub.head) (hs : es.hub.seq = s.es.hub.seq)
    (hist : es.hub.hist = s.es.hub.hist) : HistoryUpdate s (s.withBase es) := by
  apply HistoryUpdate.frame hh hs
  · funext i; simp [SEState.withBase, EHub.histF, hist]
  · funext i; simp [SEState.withBase, hs, SEState.recHistF]

theorem supAccept_history {s : SEState} {es : EState} {D : List Nat}
    (hs : es.hub.seq = s.es.hub.seq + 1)
    (hist : es.hub.hist = (es.hub.seq, es.hub.head) :: s.es.hub.hist) :
    HistoryUpdate s (s.supAccept es D) := by
  apply HistoryUpdate.save (by simp [SEState.supAccept, hs])
  · change es.hub.histF es.hub.seq = es.hub.head
    rw [show es.hub.histF =
      ({ s.es.hub with hist := (es.hub.seq, es.hub.head) :: s.es.hub.hist }).histF by
        funext i; simp [EHub.histF, hist]]
    simp [histF_saved]
  · exact (recHistF_saved s es.hub.seq s.pruned es.hub.seq (s.takeRecs D)).trans
      (by simp [SEState.supAccept])
  · intro i hi
    change i ≠ es.hub.seq at hi
    constructor
    · change es.hub.histF i = s.es.hub.histF i
      have h := histF_saved s.es.hub es.hub.seq es.hub.head i
      simpa [EHub.histF, hist, hi] using h
    · simp [SEState.supAccept, SEState.recHistF, assocF_cons, hi]

theorem prune_history {s : SEState} (hat : s.es.hub.histF s.es.hub.seq = s.es.hub.head)
    (k : Nat) : HistoryUpdate s (s.pruneR k) := by
  refine .save (by simp [SEState.pruneR]) (by exact hat) ?_ ?_
  · simp [SEState.pruneR, SEState.recHistF, assocF_cons]
  · intro i hi
    change i ≠ s.es.hub.seq at hi
    exact ⟨rfl, by simp [SEState.pruneR, SEState.recHistF, assocF_cons, hi]⟩

theorem base_history {N : Nat} {s t : SEState} {b : Action}
    (h : sexecStep N s (.base b) = .ok t)
    (hu : (CAction.old (.base b)).unledgeredAccept = false)
    (hr : b.goesBack = false) : HistoryUpdate s t := by
  obtain ⟨-, h⟩ := sreq_ok h
  simp only [sexecCore] at h
  split at h
  · cases h
  · rename_i es' hes
    split at h
    · rename_i i hi
      have := regressSeq_some hi
      subst this
      simp [Action.goesBack] at hr
    · obtain ⟨-, h⟩ := sreq_ok h
      obtain ⟨-, h⟩ := sreq_ok h
      cases h
      have hc : ∀ n e d, b ≠ .casAccept n e d := by
        intro n e d he; subst b; simp [CAction.unledgeredAccept] at hu
      have hp : ∀ n S O e d, b ≠ .hubPushAccept n S O e d := by
        intro n S O e d he; subst b; simp [CAction.unledgeredAccept] at hu
      obtain ⟨hh, hs⟩ := execStep_hub_fixed hes hc hp hr
      exact withBase_history hh hs (execStep_hist_fixed hes hc hp)

theorem sexec_history {N : Nat} {s t : SEState} {a : SAction}
    (hat : s.es.hub.histF s.es.hub.seq = s.es.hub.head)
    (h : sexecStep N s a = .ok t)
    (hu : (CAction.old a).unledgeredAccept = false) (hr : a.goesBack = false) :
    HistoryUpdate s t := by
  cases a with
  | base b => exact base_history h hu hr
  | hubSupAccept n S O e d A D =>
    obtain ⟨-, h⟩ := sreq_ok h
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    split at h
    · cases h
    · rename_i es' hes
      obtain ⟨-, h⟩ := sreq_ok h
      cases h
      obtain ⟨-, -, -, hh, hs⟩ := execStep_hubPushAccept_guards hes
      apply supAccept_history hs
      rw [execStep_accept_hist hes, hs, hh]
  | prune k =>
    obtain ⟨-, h⟩ := sreq_ok h
    simp only [sexecCore] at h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    obtain ⟨-, h⟩ := sreq_ok h
    cases h
    exact prune_history hat k
  | abandon n D | sendSup n D | sendD n | adopt n D | hubPushRefuse n S O e d A D =>
    obtain ⟨-, h⟩ := sreq_ok h
    simp only [sexecCore, sreq] at h
    repeat' split at h
    all_goals first | contradiction | (cases h; exact .frame rfl rfl rfl rfl)

theorem cexec_history {N : Nat} {s t : SEState} {a : SAction}
    (hat : s.es.hub.histF s.es.hub.seq = s.es.hub.head)
    (h : cexecStep N s a = .ok t)
    (hu : (CAction.old a).unledgeredAccept = false) (hr : a.goesBack = false) :
    HistoryUpdate s t := by
  unfold cexecStep at h
  cases hs : sexecStep N s a with
  | ok result =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h; exact sexec_history hat hs hu hr
    · contradiction
  | error error =>
    rw [hs] at h
    cases a with
    | base action =>
      cases action <;> simp only at h
      all_goals first | contradiction | skip
      split at h
      · cases h; exact .frame rfl rfl rfl rfl
      · contradiction
    | hubSupAccept n S O e d A D =>
      simp only at h
      split at h
      · cases h
        apply supAccept_history
        · simp [send_hub, EState.hubAccept,
            EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]
        · simp [send_hub, EState.hubAccept,
            EState.hubStore, EState.hubStoreOps, EState.hubStoreObjs]
      · contradiction
    | _ => contradiction

theorem cexecAction_history {N : Nat} {s t : SEState} {a : CAction}
    (hat : s.es.hub.histF s.es.hub.seq = s.es.hub.head)
    (h : cexecAction N s a = .ok t)
    (hu : a.unledgeredAccept = false) (hr : a.goesBack = false) : HistoryUpdate s t := by
  cases a with
  | old action => exact cexec_history hat h hu hr
  | advancePrepared n R =>
    simp only [cexecAction] at h
    split at h
    · cases h; exact .frame rfl rfl rfl rfl
    · contradiction
  | reject n S O e d A D =>
    simp only [cexecAction] at h
    split at h
    · exact base_history h rfl rfl
    · contradiction

theorem CutHistory.nonrollback {N : Nat} {s t : SEState} {a : CAction}
    (hi : CutHistory s) (h : cexecAction N s a = .ok t)
    (hu : a.unledgeredAccept = false) (hr : a.goesBack = false) : CutHistory t := by
  have hc := cutInv_step hi.cut h hu hr
  cases cexecAction_history hi.atSeq h hu hr with
  | frame hh hs hhist hrec =>
    refine ⟨hc, ?_, ?_⟩
    · rw [hhist, hs, hh]; exact hi.atSeq
    · intro i hle; rw [hhist, hrec]; exact hi.savedHead i (hs ▸ hle)
  | save bound atSeq current other =>
    refine ⟨hc, atSeq, fun i hle => ?_⟩
    by_cases he : i = t.es.hub.seq
    · subst i; rw [atSeq, current]; exact hc.head
    · obtain ⟨hh, hr⟩ := other i he
      rw [hh, hr]
      exact hi.savedHead i (by omega)

theorem CutHistory.rollback {N : Nat} {s t : SEState} {i : Nat}
    (hi : CutHistory s) (h : cexecAction N s (.old (.base (.hubRegress i))) = .ok t) :
    CutHistory t := by
  have hok := cexecAction_ok hi.cut.ok h
  simp only [cexecAction, cexecStep] at h
  cases hs : sexecStep N s (.base (.hubRegress i)) with
  | error error => simp [hs] at h
  | ok result =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h
      obtain ⟨-, hs⟩ := sreq_ok hs
      simp only [sexecCore] at hs
      split at hs
      · contradiction
      · rename_i es' he
        obtain ⟨hle, rfl⟩ := execStep_regress he
        simp only [Action.regressSeq] at hs
        cases hs
        refine ⟨⟨hok, hi.savedHead i hle, hi.cut.ledgerApplied, hi.cut.ledgerHead⟩,
          rfl, fun j hj => hi.savedHead j (by
            change j ≤ i at hj
            omega)⟩
    · contradiction

/-- Shipping runs never use the base model's unledgered acceptances. Rollbacks are allowed
throughout this prefix; each restored head still survives its restored record list. -/
theorem cutHistory_step {N : Nat} {s t : SEState} {a : CAction}
    (hi : CutHistory s) (h : cexecAction N s a = .ok t)
    (hu : a.unledgeredAccept = false) : CutHistory t := by
  cases hr : a.goesBack with
  | false => exact hi.nonrollback h hu hr
  | true =>
    cases a with
    | old action =>
      cases action with
      | base action =>
        cases action <;> simp [CAction.goesBack, SAction.goesBack, Action.goesBack] at hr
        exact hi.rollback h
      | _ => simp [CAction.goesBack, SAction.goesBack] at hr
    | _ => simp [CAction.goesBack] at hr

theorem cutHistory_run {N : Nat} (run : Nat → SEState) (actions : Nat → CAction)
    (h0 : CutHistory (run 0))
    (hs : ∀ i, cexecAction N (run i) (actions i) = .ok (run (i + 1)))
    (hu : ∀ i, (actions i).unledgeredAccept = false) : ∀ i, CutHistory (run i) := by
  intro i
  induction i with
  | zero => exact h0
  | succ i ih => exact cutHistory_step ih (hs i) (hu i)

end Musubi.Exec

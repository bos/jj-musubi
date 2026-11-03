/-
Record stabilization for the complete executable recovery relation. Survivor advancement,
prepared adoption and contracted acceptance must satisfy the same append/prune argument as
the older executable rules; a cut proved only for `sexecStep` does not cover those runs.
-/
import Musubi.ContractedExec
import Musubi.RecordStability

namespace Musubi.Exec

def CAction.goesBack : CAction → Bool
  | .old action => action.goesBack
  | _ => false

/-- Hub rollback can lose records, but does not make a node forget an abandonment. -/
theorem srstep_node_drop_mono {N : Nat} {s t : SState}
    (h : SRStep N s t) {n x : Nat} (hx : s.nodeD n x) : t.nodeD n x := by
  rcases h with step | ⟨i, _, rfl⟩
  · cases step with
    | base => exact hx
    | sup => exact hx
    | abandon m D _ _ _ _ | adopt m D _ _ _ =>
      change upd s.nodeD m (fun y => s.nodeD m y ∨ D y) n x
      by_cases hn : n = m
      · subst n; rw [upd_same]; exact Or.inl hx
      · rw [upd_ne _ _ hn]; exact hx
    | sendSup => exact hx
    | sendD => exact hx
    | prune => exact hx
  · exact hx

theorem contracted_step_node_drop_mono {N : Nat} {s t : SEState}
    (h : ContractedRStep N s t) {n x : Nat} (hx : x ∈ s.nodeDF n) :
    x ∈ t.nodeDF n := by
  cases h with
  | legacy t step =>
    change (sabs t).nodeD n x
    rcases step with step | same
    · exact srstep_node_drop_mono step hx
    · rw [same]; exact hx
  | advance => exact hx
  | accept => exact hx
  | prepared m R _ =>
    exact nodeDF_setD_union (s.preparedFrontier m R) m (flat R) n x hx

/-- Every rollback-free extended step either preserves records or appends their actual
nonempty difference, and never moves pruning backwards. This covers the executable union,
including recovery steps unavailable in the older relation. -/
theorem cexec_record_control {N : Nat} {s t : SEState} {a : SAction}
    (h : cexecStep N s a = .ok t) (hnr : a.goesBack = false) :
    (t.recs = s.recs ∨ ∃ D, t.recs = s.takeRecs D) ∧ s.pruned ≤ t.pruned := by
  unfold cexecStep at h
  cases hs : sexecStep N s a with
  | ok result =>
    rw [hs] at h
    simp only at h
    split at h
    · cases h; exact sexec_record_control hs hnr
    · contradiction
  | error error =>
    rw [hs] at h
    cases a with
    | base action =>
      cases action <;> simp only at h
      all_goals first | contradiction | skip
      split at h
      · cases h; exact ⟨Or.inl rfl, Nat.le_refl _⟩
      · contradiction
    | hubSupAccept n S O e d A D =>
      simp only at h
      split at h
      · cases h; exact ⟨Or.inr ⟨D, rfl⟩, Nat.le_refl _⟩
      · contradiction
    | _ => contradiction

theorem cexecAction_record_control {N : Nat} {s t : SEState} {a : CAction}
    (h : cexecAction N s a = .ok t) (hnr : a.goesBack = false) :
    (t.recs = s.recs ∨ ∃ D, t.recs = s.takeRecs D) ∧ s.pruned ≤ t.pruned := by
  cases a with
  | old action => exact cexec_record_control h hnr
  | advancePrepared n R =>
    simp only [cexecAction] at h
    split at h
    · cases h; exact ⟨Or.inl rfl, Nat.le_refl _⟩
    · contradiction
  | reject n S O e d A D =>
    simp only [cexecAction] at h
    split at h
    · exact sexec_record_control h rfl
    · contradiction

/-- The full ordered record list and pruning boundary stabilize for extended executions
without assuming head stabilization, node alignment, successful replies or rank descent.
Only bounded dropped originals and the end of rollback are trace assumptions. -/
theorem cexec_record_prefix_stabilizes (N B : Nat) (run : Nat → SEState)
    (actions : Nat → CAction) (hok : SEOK (run 0))
    (hs : ∀ i, cexecAction N (run i) (actions i) = .ok (run (i + 1)))
    (hnr : ∀ i, (actions i).goesBack = false)
    (hb : ∀ i x, x ∈ (run i).hubDL → x < B) :
    ∃ k, ∀ i, k ≤ i →
      ((run i).recs, (run i).pruned) = ((run k).recs, (run k).pruned) := by
  have hi : ∀ i, SEOK (run i) := by
    intro i
    induction i with
    | zero => exact hok
    | succ i ih => exact cexecAction_ok ih (hs i)
  exact record_prefix_eventually_stabilizes B run
    (fun i => (cexecAction_record_control (hs i) (hnr i)).1) hb
    (fun i => (cexecAction_record_control (hs i) (hnr i)).2) (fun i => (hi i).pruned)

/-- The ordered records, pruning boundary and all participants' dropped sets admit one
common cut for the actual executable recovery union. This does not assume that their
current record lists agree or that obsolete announcements have stopped arriving. -/
theorem cexec_record_and_drop_sets_stabilize (N B : Nat) (run : Nat → SEState)
    (actions : Nat → CAction) (hok : SEOK (run 0))
    (hs : ∀ i, cexecAction N (run i) (actions i) = .ok (run (i + 1)))
    (hnr : ∀ i, (actions i).goesBack = false)
    (hhub : ∀ i x, x ∈ (run i).hubDL → x < B)
    (hnode : ∀ i n, n < N → ∀ x, x ∈ (run i).nodeDF n → x < B) :
    ∃ k, ∀ i, k ≤ i →
      ((run i).recs, (run i).pruned) = ((run k).recs, (run k).pruned) ∧
      ∀ n, n < N → ∀ x, x ∈ (run i).nodeDF n ↔ x ∈ (run k).nodeDF n := by
  have hi : ∀ i, SEOK (run i) := by
    intro i
    induction i with
    | zero => exact hok
    | succ i ih => exact cexecAction_ok ih (hs i)
  exact record_and_drop_sets_stabilize N B run
    (fun i => (cexecAction_record_control (hs i) (hnr i)).1)
    (fun i => (cexecAction_record_control (hs i) (hnr i)).2)
    (fun i => (hi i).pruned)
    (fun i _ _ _ hx =>
      contracted_step_node_drop_mono (cexecAction_sound (hi i) (hs i)) hx) hhub hnode

end Musubi.Exec

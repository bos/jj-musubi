/-
Compose the record/node-drop cut with finite stale acceptance. The conclusion is about a
ledger witness of an accepted head, not production request identity: that distinction is
retained until the request-control refinement couples the complete packet fields.
-/
import Musubi.PostCut

namespace Musubi.Exec

/-- After a finite prefix, every hub movement has an aligned ledger witness from a participant
whose dropped set agrees with the hub's forever after that cut. The conclusion does not
assume that the hub stops moving or that all participants have reconciled. -/
theorem eventual_aligned_acceptance_witnesses (N B : Nat) (run : Nat → SEState)
    (actions : Nat → CAction) (h0 : CutInv (run 0))
    (hs : ∀ i, cexecAction N (run i) (actions i) = .ok (run (i + 1)))
    (hu : ∀ i, (actions i).unledgeredAccept = false)
    (hr : ∀ i, (actions i).goesBack = false)
    (hhub : ∀ i x, x ∈ (run i).hubDL → x < B)
    (hnode : ∀ i n, n < N → ∀ x, x ∈ (run i).nodeDF n → x < B) :
    ∃ k, ∀ i, k ≤ i →
      (run (i + 1)).es.hub.head ≠ (run i).es.hub.head →
      ∃ p ∈ (run i).sups, p.1 < N ∧ p.2.2.2 = (run (i + 1)).es.hub.head ∧
        ∀ j, k ≤ j → ∀ x, x ∈ (run j).nodeDF p.1 ↔ x ∈ (run j).hubDL := by
  obtain ⟨k, hcut⟩ := cexec_record_and_drop_sets_stabilize N B run actions h0.ok hs hr hhub hnode
  have hrec : ∀ i, k ≤ i → (run i).recs = (run k).recs :=
    fun i hi => congrArg Prod.fst (hcut i hi).1
  obtain ⟨later, hkl, hstale⟩ := stale_accepts_stop run actions h0 hs hu hr k hrec
  refine ⟨later, fun i hi hmove => ?_⟩
  obtain ⟨p, hp, hn, hhead, _, _, halign⟩ :=
    fresh_accept_aligned run actions h0 hs hu hr k hrec i (by omega) hmove
      (hstale i hi hmove)
  have hat : ∀ x, x ∈ (run k).nodeDF p.1 ↔ x ∈ (run k).hubDL :=
    halign (fun j hj x => (hcut j hj).2 p.1 hn x)
  refine ⟨p, hp, hn, hhead, fun j hj x => ?_⟩
  have hnodes := (hcut j (show k ≤ j by omega)).2 p.1 hn x
  have hhubs : x ∈ (run j).hubDL ↔ x ∈ (run k).hubDL := by
    simp only [SEState.hubDL, hrec j (by omega)]
  exact hnodes.trans ((hat x).trans hhubs.symm)

end Musubi.Exec

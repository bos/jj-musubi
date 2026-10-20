/-
The implementation's merged requests (`protocol.md`, "Hub"): `Push` uploads and `Cas`es in one
critical section, and `Fetch` returns the hub's head together with everything accepted since
a base. The policy steps of `Liveness.lean` exchange the fine-grained messages. Here each
merged exchange is shown to be a run of the asynchronous model that ends in a state agreeing
with the corresponding policy step's on everything the measure and convergence depend on:
all but the network and what nodes have staged. So the liveness theorems carry over to a
node that uses the merged requests.
-/
import Musubi.Liveness

namespace Musubi

variable {N : Nat}

/-- Two states agree on everything but the network and what nodes have staged. -/
def AgreeUpToStaging (s t : State) : Prop :=
  s.U = t.U ∧ s.hub = t.hub ∧ ∀ n, (s.node n).lops = (t.node n).lops ∧
    (s.node n).lobj = (t.node n).lobj ∧ (s.node n).heads = (t.node n).heads ∧
    (s.node n).known = (t.node n).known

theorem measure_agree {s t : State} (h : AgreeUpToStaging s t) : measure N s = measure N t := by
  obtain ⟨hU, hhub, hn⟩ := h
  unfold measure mDirty mStale mMiss mAdv mMulti
  have e1 : cnt N (dirty s) = cnt N (dirty t) := by
    apply cnt_congr; intro i _; unfold dirty; rw [hU, hhub, (hn i).2.2.1]
  have e2 : sumN N (fun i => s.hub.seq - (s.node i).known.1) =
      sumN N (fun i => t.hub.seq - (t.node i).known.1) := by
    apply sumN_congr; intro i _; rw [hhub, (hn i).2.2.2]
  have e3 : sumN N (mMiss s) = sumN N (mMiss t) := by
    apply sumN_congr; intro i _; unfold mMiss; rw [hU, hhub, (hn i).1]
  have e4 : sumN N (mAdv s) = sumN N (mAdv t) := by
    apply sumN_congr; intro i _; unfold mAdv; rw [hU, (hn i).2.2.1, (hn i).2.2.2]
  have e5 : sumN N (mMulti s) = sumN N (mMulti t) := by
    apply sumN_congr; intro i _; unfold mMulti; rw [(hn i).2.2.1]
  unfold mMiss at e3; unfold mAdv at e4; unfold mMulti at e5
  rw [e1, e2, e3, e4, e5]

theorem converged_agree {s t : State} (h : AgreeUpToStaging s t) :
    Converged N s ↔ Converged N t := by
  obtain ⟨_, hhub, hn⟩ := h
  unfold Converged
  simp only [hhub, (hn _).2.2.1, (hn _).2.2.2]

/-! ## `Push` -/

/-- A `push` of what `Upload` would send, accepted, then `Accepted` learned: the effect of
`PStep.pushAccept`. -/
theorem pushAccept_merged {s : State} (h : Reachable N s) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd) (hne : hd ≠ (s.node n).known.2)
    (hk : Anc s.U.par (s.node n).known.2 hd) (hacc : s.hub.head = (s.node n).known.2) :
    ∃ s', Reachable N s' ∧ AgreeUpToStaging s' (s.pPushAccept n hd) := by
  have hI := inv_reachable h
  have hl := hI.headsLocal n hd ((hh hd).2 rfl)
  have r1 := h.step (Or.inr (SyncStep.pushAll s n (s.upOps n hd) (s.upObjs n hd)
    (s.node n).known.2 hd hn (fun x hx => hI.lopsAnc hl hx.1)
    (fun o ho => by
      obtain ⟨⟨y, hy, hoy⟩, -⟩ := ho
      exact hI.lObjs n y o (hI.lopsAnc hl hy) hoy) hl))
  have r2 := r1.step (Or.inr (SyncStep.hubPushAccept _ n (s.upOps n hd) (s.upObjs n hd)
    (s.node n).known.2 hd (Or.inr rfl)
    (fun e => hne ((show s.hub.head = hd from e).symm.trans hacc)) hacc hk
    (pUpload_closed hI)))
  have r3 := r2.step (Or.inr (SyncStep.learn _ n .accepted (s.hub.seq + 1) hd hn
    (Or.inl (Or.inr rfl)) (Nat.lt_succ_of_le (hI.known n).1)))
  exact ⟨_, r3, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The effect of `PStep.pushIdem`. -/
theorem pushIdem_merged {s : State} (h : Reachable N s) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd) (hne : hd ≠ (s.node n).known.2)
    (hidem : s.hub.head = hd) :
    ∃ s', Reachable N s' ∧ AgreeUpToStaging s' (s.pPushIdem n hd) := by
  have hI := inv_reachable h
  have hl := hI.headsLocal n hd ((hh hd).2 rfl)
  have hlt : (s.node n).known.1 < s.hub.seq := by
    rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
    · exact h1
    · exfalso; apply hne; rw [← hidem, ← hI.histHead, ← h1, (hI.known n).2]
  have r1 := h.step (Or.inr (SyncStep.pushAll s n (s.upOps n hd) (s.upObjs n hd)
    (s.node n).known.2 hd hn (fun x hx => hI.lopsAnc hl hx.1)
    (fun o ho => by
      obtain ⟨⟨y, hy, hoy⟩, -⟩ := ho
      exact hI.lObjs n y o (hI.lopsAnc hl hy) hoy) hl))
  have r2 := r1.step (Or.inr (SyncStep.hubPushIdem _ n (s.upOps n hd) (s.upObjs n hd)
    (s.node n).known.2 hd (Or.inr rfl) hidem))
  have r3 := r2.step (Or.inr (SyncStep.learn _ n .accepted s.hub.seq s.hub.head hn
    (Or.inr rfl) hlt))
  exact ⟨_, r3, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The effect of `PStep.pushReject`. -/
theorem pushReject_merged {s : State} (h : Reachable N s) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd) (hrej : s.hub.head ≠ (s.node n).known.2)
    (hrej' : s.hub.head ≠ hd) :
    ∃ s', Reachable N s' ∧ AgreeUpToStaging s' (s.pPushReject n hd) := by
  have hI := inv_reachable h
  have hl := hI.headsLocal n hd ((hh hd).2 rfl)
  have hlt : (s.node n).known.1 < s.hub.seq := by
    rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
    · exact h1
    · exfalso; apply hrej; rw [← hI.histHead, ← h1, (hI.known n).2]
  have r1 := h.step (Or.inr (SyncStep.pushAll s n (s.upOps n hd) (s.upObjs n hd)
    (s.node n).known.2 hd hn (fun x hx => hI.lopsAnc hl hx.1)
    (fun o ho => by
      obtain ⟨⟨y, hy, hoy⟩, -⟩ := ho
      exact hI.lObjs n y o (hI.lopsAnc hl hy) hoy) hl))
  have r2 := r1.step (Or.inr (SyncStep.hubPushReject _ n (s.upOps n hd) (s.upObjs n hd)
    (s.node n).known.2 hd (Or.inr rfl) hrej' (fun ⟨e, _, _⟩ => hrej e)))
  have r3 := r2.step (Or.inr (SyncStep.learn _ n .rejected s.hub.seq s.hub.head hn
    (Or.inr rfl) hlt))
  exact ⟨_, r3, rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-! ## `Fetch` -/

/-- A `fetch` from a local base `b`, with haves the node has, answered and taken in: the
effect of `PStep.learn`, and afterwards every operation the node lacks below the head it
learned is staged with its objects at hand, so that `Realize` can take each in turn. -/
theorem fetch_merged {s : State} (h : Reachable N s) {n b : Nat} {H : OSet} (hn : n < N)
    (hs : (s.node n).known.1 < s.hub.seq) (hb : (s.node n).lops b)
    (hH : ∀ o, H o → (s.node n).lobj o) :
    ∃ s', Reachable N s' ∧ AgreeUpToStaging s' (s.pLearn n) ∧
      ∀ x, Anc s.U.par x s.hub.head → ¬ (s.node n).lops x →
        (s'.node n).sops x ∧ ∀ o ∈ s.U.objs x, (s'.node n).lobj o ∨ (s'.node n).sobj o := by
  have hI := inv_reachable h
  have r1 := h.step (Or.inr (SyncStep.fetchAll s n b H hn))
  have r2 := r1.step (Or.inr (SyncStep.hubFetch _ n b H (Or.inr rfl)))
  have r3 := r2.step (Or.inr (SyncStep.learn _ n .head s.hub.seq s.hub.head hn
    (Or.inl (Or.inl (Or.inr rfl))) hs))
  have r4 := r3.step (Or.inr (SyncStep.recvOps _ n (s.sinceOps b) hn (Or.inl (Or.inr rfl))))
  have r5 := r4.step (Or.inr (SyncStep.recvObjs _ n (s.sinceObjs b H) hn (Or.inr rfl)))
  refine ⟨_, r5, ⟨rfl, rfl, fun i => ?_⟩, fun x hx hnl => ?_⟩
  · by_cases hi : i = n
    · subst hi
      simp [State.recvObjs, State.recvOps, State.learn, State.pLearn, State.setNode,
        State.send]
    · simp [State.recvObjs, State.recvOps, State.learn, State.pLearn, State.setNode,
        State.send, upd, hi]
  · have hxb : ¬ Anc s.U.par x b := fun hxb => hnl (hI.lopsAnc hb hxb)
    have hsince : s.sinceOps b x := ⟨hx, hxb, (hI.hubClosed x hx).1⟩
    refine ⟨?_, fun o ho => ?_⟩
    · simp [State.recvObjs, State.recvOps, State.learn, State.setNode, State.send, hsince]
    · by_cases hoH : H o
      · left
        simp [State.recvObjs, State.recvOps, State.learn, State.setNode, State.send]
        exact hH o hoH
      · right
        have : s.sinceObjs b H o := ⟨⟨x, hsince, ho⟩, hoH, (hI.hubClosed x hx).2 o ho⟩
        simp [State.recvObjs, State.recvOps, State.learn, State.setNode, State.send, this]

/-- Realizing a staged operation has the effect of `PStep.realize`, which fetches it first. -/
theorem realize_agree {s : State} {n x : Nat} :
    AgreeUpToStaging (s.realize n x) (s.pRealize n x) := by
  refine ⟨rfl, rfl, fun i => ?_⟩
  by_cases hi : i = n
  · subst hi
    simp [State.realize, State.pRealize, State.recvObjs, State.recvOps, State.setNode,
      State.send]
  · simp [State.realize, State.pRealize, State.recvObjs, State.recvOps, State.setNode,
      State.send, upd, hi]

end Musubi

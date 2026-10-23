/-
Liveness. After environment `UserOp`s stop, nodes follow the policy with atomic, reliable
request/reply exchanges (`PStep`). Every `PStep` is a sequence of steps of the asynchronous
model, so all safety invariants hold along policy runs. We prove:

* progress: every reachable state that is not converged has an enabled policy step;
* termination: a lexicographic measure strictly decreases on every policy step, so there is
  no infinite policy run, under any scheduling of nodes and actions;
* hence every maximal policy run ends in a converged state, where every node has
  `heads = {hub.head}` and `known = (hub.seq, hub.head)` and every created operation is in
  `anc*(hub.head)`; and converged states enable no policy step (no feedback).
-/
import Musubi.Safety

namespace Musubi

variable {N : Nat}

/-! ## Atomic policy exchanges -/

namespace State

/-- `GetHead` → `Head(seq, head)` → `Learn`. -/
def pLearn (s : State) (n : Nat) : State :=
  ((s.send (.getHead n)).send (.head n .head s.hub.seq s.hub.head)).learn n s.hub.seq
    s.hub.head

/-- Fetch one operation `x` and its objects from the hub, then realize it. -/
def pRealize (s : State) (n x : Nat) : State :=
  ((((((s.send (.getOps n (· = x))).send (.ops n (fun y => y = x ∧ s.hub.ops y))).recvOps n
    (fun y => y = x ∧ s.hub.ops y)).send (.getObjs n (· ∈ s.U.objs x))).send
    (.objs n (fun o => o ∈ s.U.objs x ∧ s.hub.objs o))).recvObjs n
    (fun o => o ∈ s.U.objs x ∧ s.hub.objs o)).realize n x

/-- Operations uploaded before pushing `h`: `anc*(h) \ anc*(known.head)`. -/
def upOps (s : State) (n h : Nat) : OSet :=
  fun y => Anc s.U.par y h ∧ ¬ Anc s.U.par y (s.node n).known.2

/-- Objects uploaded before pushing `h`: objects of `closure(h) \ closure(known.head)`. -/
def upObjs (s : State) (n h : Nat) : OSet :=
  fun o => (∃ y, Anc s.U.par y h ∧ o ∈ s.U.objs y) ∧
    ¬ ∃ z, Anc s.U.par z (s.node n).known.2 ∧ o ∈ s.U.objs z

/-- `Upload` (both `PutOps` and `PutObjects` exchanges), then send `Cas(known.head, h)`. -/
def pUpload (s : State) (n h : Nat) : State :=
  ((((((s.send (.putOps n (s.upOps n h))).hubStoreOps (s.upOps n h)).send (.stored n)).send
    (.putObjs n (s.upObjs n h))).hubStoreObjs (s.upObjs n h)).send (.stored n)).send
    (.cas n (s.node n).known.2 h)

/-- Upload, `Cas` accepted, node learns `Accepted`. -/
def pPushAccept (s : State) (n h : Nat) : State :=
  ((((s.pUpload n h).hubAccept h).send (.head n .accepted (s.hub.seq + 1) h)).notifyAll
    (s.hub.seq + 1) h).learn n (s.hub.seq + 1) h

/-- Upload, `Cas` finds `new = head` already, node learns `Accepted(seq, head)`. -/
def pPushIdem (s : State) (n h : Nat) : State :=
  ((s.pUpload n h).send (.head n .accepted s.hub.seq s.hub.head)).learn n s.hub.seq s.hub.head

/-- Upload, `Cas` rejected, node learns `Rejected(seq, head)`. -/
def pPushReject (s : State) (n h : Nat) : State :=
  ((s.pUpload n h).send (.head n .rejected s.hub.seq s.hub.head)).learn n s.hub.seq s.hub.head

end State

/-- Reliable policy steps. Each is enabled exactly when the corresponding policy action of
`protocol.md` would do something; the order in which nodes and actions are scheduled is
arbitrary (the policy's priority order is one particular schedule). There is no `UserOp`:
environment activity has stopped. `Merge` is a policy action (musubi triggers jj's merge). -/
inductive PStep (N : Nat) : State → State → Prop
  | learn (s : State) (n : Nat) (hn : n < N) (hs : (s.node n).known.1 < s.hub.seq) :
      PStep N s (s.pLearn n)
  | realize (s : State) (n x : Nat) (hn : n < N) (hx : Anc s.U.par x (s.node n).known.2)
      (hnl : ¬ (s.node n).lops x) (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) :
      PStep N s (s.pRealize n x)
  | advance (s : State) (n : Nat) (hn : n < N) (hk : (s.node n).lops (s.node n).known.2)
      (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
      PStep N s (s.advance n)
  | merge (s : State) (n : Nat) (L O : List Nat) (hn : n < N)
      (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
      PStep N s (s.mergeOp n L O)
  | pushAccept (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.2) (hk : Anc s.U.par (s.node n).known.2 h)
      (hacc : s.hub.head = (s.node n).known.2) : PStep N s (s.pPushAccept n h)
  | pushIdem (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.2) (hk : Anc s.U.par (s.node n).known.2 h)
      (hidem : s.hub.head = h) : PStep N s (s.pPushIdem n h)
  | pushReject (s : State) (n h : Nat) (hn : n < N) (hh : ∀ y, (s.node n).heads y ↔ y = h)
      (hne : h ≠ (s.node n).known.2) (hk : Anc s.U.par (s.node n).known.2 h)
      (hrej : s.hub.head ≠ (s.node n).known.2) (hrej' : s.hub.head ≠ h) :
      PStep N s (s.pPushReject n h)

/-- Reflexive-transitive closure of `PStep`. -/
inductive PSteps (N : Nat) : State → State → Prop
  | refl (s : State) : PSteps N s s
  | tail {s t u : State} : PSteps N s t → PStep N t u → PSteps N s u

/-- Converged: every node's heads are exactly `{hub.head}` and it knows the current head. -/
def Converged (N : Nat) (s : State) : Prop :=
  ∀ n, n < N → (∀ y, (s.node n).heads y ↔ y = s.hub.head) ∧
    (s.node n).known = (s.hub.seq, s.hub.head)

/-! ## Policy steps are runs of the asynchronous model -/

/-- Uploading what `h` adds to `known.head` closes `h` at the hub, when the hub holds
`closure(known.head)`. -/
theorem pUpload_closed_of {s : State} {n h : Nat} (hc : ClosedAt s s.hub.head)
    (hk : Anc s.U.par (s.node n).known.2 s.hub.head) : ClosedAt (s.pUpload n h) h := by
  intro y hy
  have hy' : Anc s.U.par y h := hy
  constructor
  · show (s.hub.ops y ∨ s.upOps n h y)
    by_cases hyk : Anc s.U.par y (s.node n).known.2
    · exact Or.inl (hc y (hyk.trans hk)).1
    · exact Or.inr ⟨hy', hyk⟩
  · intro o ho
    show s.hub.objs o ∨ s.upObjs n h o
    by_cases hz : ∃ z, Anc s.U.par z (s.node n).known.2 ∧ o ∈ s.U.objs z
    · obtain ⟨z, hz, hoz⟩ := hz
      exact Or.inl ((hc z (hz.trans hk)).2 o hoz)
    · exact Or.inr ⟨⟨y, hy', ho⟩, hz⟩

theorem pUpload_closed {s : State} (hI : Inv N s) {n h : Nat} :
    ClosedAt (s.pUpload n h) h :=
  pUpload_closed_of hI.hubClosed (hI.knownAnc n)

/-- `pUpload` is a run of sync steps, in any set of states that sync steps keep, from a state
where node `n`'s operations are closed under parents and have their objects. -/
theorem pUpload_run {P : State → Prop} (hP : ∀ {s s'}, P s → SyncStep N s s' → P s')
    {s : State} (h : P s) {n hd : Nat} (hn : n < N)
    (hpar : ∀ x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p)
    (hobj : ∀ x o, (s.node n).lops x → o ∈ s.U.objs x → (s.node n).lobj o)
    (hl : (s.node n).lops hd) : P (s.pUpload n hd) := by
  have lopsAnc : ∀ {a}, Anc s.U.par a hd → (s.node n).lops a := fun ha =>
    Anc.closed (S := (s.node n).lops) (fun y p hy hp => hpar y p hy hp) ha hl
  have r1 := hP h (SyncStep.uploadOps s n (s.upOps n hd) hn (fun x hx => lopsAnc hx.1))
  have r2 := hP r1 (SyncStep.hubPutOps _ n (s.upOps n hd) (Or.inr rfl))
  have r3 := hP r2 (SyncStep.uploadObjs _ n (s.upObjs n hd) hn
    (fun o ho => by
      obtain ⟨⟨y, hy, hoy⟩, -⟩ := ho
      exact hobj y o (lopsAnc hy) hoy))
  have r4 := hP r3 (SyncStep.hubPutObjs _ n (s.upObjs n hd) (Or.inr rfl))
  exact hP r4 (SyncStep.push _ n (s.node n).known.2 hd hn hl)

/-- `pRealize` is a run of sync steps, in any set of states that sync steps keep, when the
hub holds `x` and its objects and node `n` has its parents. -/
theorem pRealize_run {P : State → Prop} (hP : ∀ {s s'}, P s → SyncStep N s s' → P s')
    {s : State} (h : P s) {n x : Nat} (hn : n < N) (hx : Anc s.U.par x (s.node n).known.2)
    (hc : HubHas s x) (hp : ∀ p ∈ s.U.par x, (s.node n).lops p) : P (s.pRealize n x) := by
  have r1 := hP h (SyncStep.fetchOps s n (· = x) hn (fun y hy => hy ▸ hx))
  have r2 := hP r1 (SyncStep.hubGetOps _ n (· = x) (Or.inr rfl))
  have r3 := hP r2 (SyncStep.recvOps _ n (fun y => y = x ∧ s.hub.ops y) hn (Or.inr rfl))
  have r4 := hP r3 (SyncStep.fetchObjs _ n (· ∈ s.U.objs x) hn)
  have r5 := hP r4 (SyncStep.hubGetObjs _ n (· ∈ s.U.objs x) (Or.inr rfl))
  have r6 := hP r5 (SyncStep.recvObjs _ n
    (fun o => o ∈ s.U.objs x ∧ s.hub.objs o) hn (Or.inr rfl))
  refine hP r6 (SyncStep.realize _ n x hn ?_ ?_ ?_)
  · simp [State.recvObjs, State.recvOps, State.setNode, State.send, hc.1]
  · simpa [State.recvObjs, State.recvOps, State.setNode, State.send] using hp
  · intro o ho
    have ho' : o ∈ s.U.objs x := ho
    simp [State.recvObjs, State.recvOps, State.setNode, State.send, ho', hc.2 o ho']

theorem pUpload_reachable {s : State} (h : Reachable N s) {n hd : Nat} (hn : n < N)
    (hh : (s.node n).heads hd) : Reachable N (s.pUpload n hd) := by
  have hI := inv_reachable h
  exact pUpload_run (fun h st => h.step (Or.inr st)) h hn (hI.lParents n) (hI.lObjs n)
    (hI.headsLocal n hd hh)

theorem pstep_reachable {s s' : State} (h : Reachable N s) (hp : PStep N s s') :
    Reachable N s' := by
  have hI := inv_reachable h
  cases hp with
  | learn n hn hs =>
    have r1 := h.step (Or.inr (SyncStep.getHead s n hn))
    have r2 := r1.step (Or.inr (SyncStep.hubGetHead _ n (Or.inr rfl)))
    exact r2.step (Or.inr (SyncStep.learn _ n .head s.hub.seq s.hub.head hn (Or.inr rfl) hs))
  | realize n x hn hx hnl hp =>
    exact pRealize_run (fun h st => h.step (Or.inr st)) h hn hx
      (hI.hubClosed x (hx.trans (hI.knownAnc n))) hp
  | advance n hn hk hna => exact h.step (Or.inr (SyncStep.advance s n hn hk hna))
  | merge n L O hn hL h2 => exact h.step (Or.inl (EnvStep.merge s n L O hn hL h2))
  | pushAccept n hd hn hh hne hk hacc =>
    have r := pUpload_reachable h hn ((hh hd).2 rfl)
    have r' := r.step (Or.inr (SyncStep.casAccept _ n (s.node n).known.2 hd (Or.inr rfl)
      (fun e => hne ((show s.hub.head = hd from e).symm.trans hacc)) hacc hk
      (pUpload_closed hI)))
    exact r'.step (Or.inr (SyncStep.learn _ n .accepted (s.hub.seq + 1) hd hn
      (Or.inl (Or.inr rfl)) (Nat.lt_succ_of_le (hI.known n).1)))
  | pushIdem n hd hn hh hne hk hidem =>
    have hlt : (s.node n).known.1 < s.hub.seq := by
      rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
      · exact h1
      · exfalso; apply hne; rw [← hidem, ← hI.histHead, ← h1, (hI.known n).2]
    have r := pUpload_reachable h hn ((hh hd).2 rfl)
    have r' := r.step (Or.inr (SyncStep.casIdem _ n (s.node n).known.2 hd (Or.inr rfl) hidem))
    exact r'.step (Or.inr (SyncStep.learn _ n .accepted s.hub.seq s.hub.head hn
      (Or.inr rfl) hlt))
  | pushReject n hd hn hh hne hk hrej hrej' =>
    have hlt : (s.node n).known.1 < s.hub.seq := by
      rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
      · exact h1
      · exfalso; apply hrej; rw [← hI.histHead, ← h1, (hI.known n).2]
    have r := pUpload_reachable h hn ((hh hd).2 rfl)
    have r' := r.step (Or.inr (SyncStep.casReject _ n (s.node n).known.2 hd (Or.inr rfl)
      hrej' (fun ⟨e, _, _⟩ => hrej e)))
    exact r'.step (Or.inr (SyncStep.learn _ n .rejected s.hub.seq s.hub.head hn
      (Or.inr rfl) hlt))

theorem psteps_reachable {s s' : State} (h : Reachable N s) (hp : PSteps N s s') :
    Reachable N s' := by
  induction hp with
  | refl => exact h
  | tail _ hst ih => exact pstep_reachable ih hst

/-! ## The measure -/

/-- A node is dirty when one of its heads is not accepted. -/
def dirty (s : State) (n : Nat) : Prop := ∃ h, (s.node n).heads h ∧ ¬ Anc s.U.par h s.hub.head

noncomputable def mDirty (N : Nat) (s : State) : Nat := cnt N (dirty s)

def mStale (s : State) (n : Nat) : Nat := s.hub.seq - (s.node n).known.1

noncomputable def mMiss (s : State) (n : Nat) : Nat :=
  cnt (s.hub.head + 1) (fun x => Anc s.U.par x s.hub.head ∧ ¬ (s.node n).lops x)

open Classical in
noncomputable def mAdv (s : State) (n : Nat) : Nat :=
  if ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h then 0 else 1

open Classical in
noncomputable def mMulti (s : State) (n : Nat) : Nat :=
  if ∃ a b, (s.node n).heads a ∧ (s.node n).heads b ∧ a ≠ b then 1 else 0

/-- The lexicographic measure: (dirty nodes, staleness, missing operations, pending
advances, pending merges). -/
noncomputable def measure (N : Nat) (s : State) : Nat × Nat × Nat × Nat × Nat :=
  (mDirty N s, sumN N (mStale s), sumN N (mMiss s), sumN N (mAdv s), sumN N (mMulti s))

def Lex5 : Nat × Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat × Nat → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))

theorem lex5_wf : WellFounded Lex5 :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel
    (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)))).wf

theorem lex5_of {a b c d e a' b' c' d' e' : Nat}
    (h : a' < a ∨ (a' = a ∧ (b' < b ∨ (b' = b ∧ (c' < c ∨ (c' = c ∧
      (d' < d ∨ (d' = d ∧ e' < e)))))))) :
    Lex5 (a', b', c', d', e') (a, b, c, d, e) := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h | ⟨rfl, h | ⟨rfl, h⟩⟩⟩⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ h))
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ h)))
  · exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ h)))

theorem ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) {a b : Nat} :
    (if P then a else b) = (if Q then a else b) := by
  by_cases hp : P
  · have hq := h.1 hp
    simp only [hp, hq, ↓reduceIte]
  · have hq : ¬ Q := fun hq => hp (h.2 hq)
    simp only [hp, hq, ↓reduceIte]

/-! ### Framing: steps that touch only node `n` and keep the universe and hub head/seq -/

/-- `s'` differs from `s` at most in node `n`, the network, and hub stores. -/
structure Frame (s s' : State) (n : Nat) : Prop where
  U : s'.U = s.U
  head : s'.hub.head = s.hub.head
  seq : s'.hub.seq = s.hub.seq
  other : ∀ i, i ≠ n → s'.node i = s.node i

namespace Frame

variable {s s' : State} {n : Nat}

theorem dirty_ne (f : Frame s s' n) {i : Nat} (hi : i ≠ n) : dirty s' i ↔ dirty s i := by
  unfold dirty; rw [f.U, f.head, f.other i hi]

theorem dirty_eq (f : Frame s s' n) (hh : (s'.node n).heads = (s.node n).heads) :
    mDirty N s' = mDirty N s := by
  apply cnt_congr
  intro i _
  by_cases hi : i = n
  · subst hi; unfold dirty; rw [f.U, f.head, hh]
  · exact f.dirty_ne hi

theorem stale_ne (f : Frame s s' n) {i : Nat} (hi : i ≠ n) : mStale s' i = mStale s i := by
  unfold mStale; rw [f.seq, f.other i hi]

theorem miss_ne (f : Frame s s' n) {i : Nat} (hi : i ≠ n) : mMiss s' i = mMiss s i := by
  unfold mMiss; rw [f.U, f.head, f.other i hi]

theorem adv_ne (f : Frame s s' n) {i : Nat} (hi : i ≠ n) : mAdv s' i = mAdv s i := by
  unfold mAdv; rw [f.U, f.other i hi]

theorem multi_ne (f : Frame s s' n) {i : Nat} (hi : i ≠ n) : mMulti s' i = mMulti s i := by
  unfold mMulti; rw [f.other i hi]

theorem sum_eq (_f : Frame s s' n) {g : State → Nat → Nat}
    (hne : ∀ i, i ≠ n → g s' i = g s i) (hn : g s' n = g s n) :
    sumN N (g s') = sumN N (g s) := by
  apply sumN_congr
  intro i _
  by_cases hi : i = n
  · subst hi; exact hn
  · exact hne i hi

theorem sum_lt (_f : Frame s s' n) {g : State → Nat → Nat} (hN : n < N)
    (hne : ∀ i, i ≠ n → g s' i = g s i) (hn : g s' n < g s n) :
    sumN N (g s') < sumN N (g s) :=
  sumN_lt hN hn (fun i _ hi => hne i hi)

end Frame

/-! ### Each policy step decreases the measure -/

theorem measure_learn {s : State} {n : Nat} (hn : n < N)
    (hs : (s.node n).known.1 < s.hub.seq) : Lex5 (measure N (s.pLearn n)) (measure N s) := by
  have f : Frame s (s.pLearn n) n :=
    ⟨rfl, rfl, rfl, fun i hi => by simp [State.pLearn, State.learn, setNode_ne hi]⟩
  have hnode : (s.pLearn n).node n = { s.node n with known := (s.hub.seq, s.hub.head) } := by
    simp [State.pLearn, State.learn]
  apply lex5_of
  right; refine ⟨f.dirty_eq (by rw [hnode]), Or.inl ?_⟩
  apply f.sum_lt hn (fun i hi => f.stale_ne hi)
  unfold mStale; rw [hnode, f.seq]; simp; omega

theorem measure_realize {s : State} (hI : Inv N s) {n x : Nat} (hn : n < N)
    (hx : Anc s.U.par x (s.node n).known.2) (hnl : ¬ (s.node n).lops x) :
    Lex5 (measure N (s.pRealize n x)) (measure N s) := by
  have f : Frame s (s.pRealize n x) n :=
    ⟨rfl, rfl, rfl, fun i hi => by
      simp [State.pRealize, State.realize, State.recvObjs, State.recvOps, setNode_ne hi]⟩
  have hnode : ((s.pRealize n x).node n).heads = (s.node n).heads ∧
      ((s.pRealize n x).node n).known = (s.node n).known ∧
      ((s.pRealize n x).node n).lops = fun y => (s.node n).lops y ∨ y = x := by
    simp [State.pRealize, State.realize, State.recvObjs, State.recvOps]
  have hxa : Anc s.U.par x s.hub.head := hx.trans (hI.knownAnc n)
  apply lex5_of
  right; refine ⟨f.dirty_eq hnode.1, Or.inr ⟨?_, Or.inl ?_⟩⟩
  · apply f.sum_eq (fun i hi => f.stale_ne hi)
    unfold mStale; rw [hnode.2.1, f.seq]
  · apply f.sum_lt hn (fun i hi => f.miss_ne hi)
    unfold mMiss; rw [hnode.2.2, f.U, f.head]
    apply cnt_lt
    · intro y _ ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
    · exact ⟨x, Nat.lt_succ_of_le (hxa.le hI.parLt), ⟨hxa, hnl⟩, fun ⟨_, h⟩ => h (Or.inr rfl)⟩

theorem measure_advance {s : State} (hI : Inv N s) {n : Nat} (hn : n < N)
    (hna : ¬ ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h) :
    Lex5 (measure N (s.advance n)) (measure N s) := by
  have f : Frame s (s.advance n) n :=
    ⟨rfl, rfl, rfl, fun i hi => by simp [State.advance, setNode_ne hi]⟩
  have H := fun y => advance_heads_iff (y := y) hI hna
  have hheads : ((s.advance n).node n).heads =
      maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) := by
    simp [State.advance]
  have hknown : ((s.advance n).node n).known = (s.node n).known := by simp [State.advance]
  have hlops : ((s.advance n).node n).lops = (s.node n).lops := by simp [State.advance]
  have hka := hI.knownAnc n
  apply lex5_of
  right
  refine ⟨?_, Or.inr ⟨?_, Or.inr ⟨?_, Or.inl ?_⟩⟩⟩
  · apply cnt_congr
    intro i _
    by_cases hi : i = n
    · subst hi
      unfold dirty; rw [hheads, f.U, f.head]
      constructor
      · rintro ⟨h, hh, hna'⟩
        rcases (H h).1 hh with rfl | ⟨hh', -⟩
        · exact absurd hka hna'
        · exact ⟨h, hh', hna'⟩
      · rintro ⟨h, hh, hna'⟩
        refine ⟨h, (H h).2 (Or.inr ⟨hh, fun hk => hna' (hk.trans hka)⟩), hna'⟩
    · exact f.dirty_ne hi
  · apply f.sum_eq (fun i hi => f.stale_ne hi)
    unfold mStale; rw [hknown, f.seq]
  · apply f.sum_eq (fun i hi => f.miss_ne hi)
    unfold mMiss; rw [hlops, f.U, f.head]
  · apply f.sum_lt hn (fun i hi => f.adv_ne hi)
    unfold mAdv; rw [hheads, hknown, f.U]
    have h1 : ∃ h, maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) h ∧
        Anc s.U.par (s.node n).known.2 h := ⟨_, (H _).2 (Or.inl rfl), Anc.refl⟩
    simp only [h1, hna, ↓reduceIte]
    omega

open Classical in
/-- What a merge does to the last three components of the measure, which `measure` and
`rmeasure` share: no operation goes missing, no advance becomes pending, and node `n` has no
merge left to do. -/
theorem merge_tail {s : State} {n : Nat} {L O : List Nat} (hn : n < N)
    (hlt : ParLt s.U.par) (hhead : s.hub.head < s.U.next)
    (hheadsLt : ∀ i x, (s.node i).heads x → x < s.U.next)
    (hk : ∀ i, (s.node i).known.2 < s.U.next)
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    sumN N (mMiss (s.mergeOp n L O)) = sumN N (mMiss s) ∧
      sumN N (mAdv (s.mergeOp n L O)) = sumN N (mAdv s) ∧
      sumN N (mMulti (s.mergeOp n L O)) < sumN N (mMulti s) := by
  have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hheadsLt n q ((hL q).1 hq)
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next L) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hlt hLlt hx
  have Tnew : ∀ {a : Nat}, Anc (upd s.U.par s.U.next L) a s.U.next ↔
      a = s.U.next ∨ ∃ p ∈ L, Anc s.U.par a p := anc_upd_new hlt hLlt
  have hpar : (s.mergeOp n L O).U.par = upd s.U.par s.U.next L := rfl
  have hhub : (s.mergeOp n L O).hub = s.hub := rfl
  have hother : ∀ i, i ≠ n → (s.mergeOp n L O).node i = s.node i :=
    fun i hi => createOp_node_ne hi
  have hheads : ((s.mergeOp n L O).node n).heads = (· = s.U.next) := createOp_heads
  have hknown : ((s.mergeOp n L O).node n).known = (s.node n).known := createOp_known
  have hlops : ((s.mergeOp n L O).node n).lops = fun y => (s.node n).lops y ∨ y = s.U.next :=
    createOp_lops
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · apply sumN_congr; intro i _
    unfold mMiss; rw [hhub, hpar]
    apply cnt_congr; intro x hx
    have hxl : x < s.U.next := by have := hhead; omega
    by_cases hi : i = n
    · subst hi; rw [hlops, T hhead]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h.elim h2 (fun e => by omega)⟩
    · rw [hother i hi, T hhead]
  · apply sumN_congr; intro i _
    unfold mAdv; rw [hpar]
    by_cases hi : i = n
    · subst hi
      rw [hheads, hknown]
      have : (∃ h, h = s.U.next ∧ Anc (upd s.U.par s.U.next L) (s.node i).known.2 h) ↔
          (∃ h, (s.node i).heads h ∧ Anc s.U.par (s.node i).known.2 h) := by
        constructor
        · rintro ⟨h, rfl, hA⟩
          rcases Tnew.1 hA with e | ⟨p, hp, hA'⟩
          · have := hk i; omega
          · exact ⟨p, (hL p).1 hp, hA'⟩
        · rintro ⟨h, hh, hA⟩
          exact ⟨s.U.next, rfl, Tnew.2 (Or.inr ⟨h, (hL h).2 hh, hA⟩)⟩
      exact ite_iff this
    · rw [hother i hi]
      have : (∃ h, (s.node i).heads h ∧ Anc (upd s.U.par s.U.next L) (s.node i).known.2 h) ↔
          (∃ h, (s.node i).heads h ∧ Anc s.U.par (s.node i).known.2 h) := by
        constructor
        · rintro ⟨h, hh, hA⟩; exact ⟨h, hh, (T (hheadsLt _ _ hh)).1 hA⟩
        · rintro ⟨h, hh, hA⟩; exact ⟨h, hh, (T (hheadsLt _ _ hh)).2 hA⟩
      exact ite_iff this
  · apply sumN_lt hn
    · unfold mMulti; rw [hheads]
      have h1 : ¬ ∃ a b, a = s.U.next ∧ b = s.U.next ∧ a ≠ b := by
        rintro ⟨a, b, rfl, rfl, h⟩; exact h rfl
      have h2 : ∃ a b, (s.node n).heads a ∧ (s.node n).heads b ∧ a ≠ b :=
        ⟨a, b, (hL a).1 ha, (hL b).1 hb, hab⟩
      simp only [h1, h2, ↓reduceIte]
      omega
    · intro i _ hi
      unfold mMulti; rw [hother i hi]

open Classical in
theorem measure_merge {s : State} (hI : Inv N s) {n : Nat} {L O : List Nat} (hn : n < N)
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    Lex5 (measure N (s.mergeOp n L O)) (measure N s) := by
  have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
  have T : ∀ {a x : Nat}, x < s.U.next →
      (Anc (upd s.U.par s.U.next L) a x ↔ Anc s.U.par a x) :=
    fun hx => anc_upd_iff hI.parLt hLlt hx
  have hpar : (s.mergeOp n L O).U.par = upd s.U.par s.U.next L := rfl
  have hhub : (s.mergeOp n L O).hub = s.hub := rfl
  have hother : ∀ i, i ≠ n → (s.mergeOp n L O).node i = s.node i :=
    fun i hi => createOp_node_ne hi
  have hheads : ((s.mergeOp n L O).node n).heads = (· = s.U.next) := createOp_heads
  have hknown : ((s.mergeOp n L O).node n).known = (s.node n).known := createOp_known
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  -- dirtiness is unchanged
  have hdirty : ∀ i, dirty (s.mergeOp n L O) i ↔ dirty s i := by
    intro i
    unfold dirty
    rw [hpar, hhub]
    by_cases hi : i = n
    · subst hi
      rw [hheads]
      constructor
      · intro _
        by_cases hA : Anc s.U.par a s.hub.head
        · by_cases hB : Anc s.U.par b s.hub.head
          · exact absurd (hI.accHeads i a b ((hL a).1 ha) ((hL b).1 hb) hA hB) hab
          · exact ⟨b, (hL b).1 hb, hB⟩
        · exact ⟨a, (hL a).1 ha, hA⟩
      · intro _
        refine ⟨s.U.next, rfl, fun h => ?_⟩
        have := (h.le (parLt_upd hI.parLt hLlt))
        have := hI.headLt
        omega
    · rw [hother i hi]
      constructor
      · rintro ⟨h, hh, hna⟩; exact ⟨h, hh, fun hA => hna ((T hI.headLt).2 hA)⟩
      · rintro ⟨h, hh, hna⟩; exact ⟨h, hh, fun hA => hna ((T hI.headLt).1 hA)⟩
  have hk : ∀ i, (s.node i).known.2 < s.U.next := fun i => hI.knownLt i
  apply lex5_of
  right
  obtain ⟨t1, t2, t3⟩ := merge_tail (O := O) hn hI.parLt hI.headLt (fun _ _ h => hI.headsLt h)
    hk hL ⟨a, b, ha, hb, hab⟩
  refine ⟨cnt_congr (fun i _ => hdirty i), Or.inr ⟨?_, Or.inr ⟨t1, Or.inr ⟨t2, t3⟩⟩⟩⟩
  · apply sumN_congr; intro i _
    unfold mStale; rw [hhub]
    by_cases hi : i = n
    · subst hi; rw [hknown]
    · rw [hother i hi]

@[simp] theorem pUpload_node {s : State} {n h : Nat} : (s.pUpload n h).node = s.node := rfl
@[simp] theorem pUpload_U {s : State} {n h : Nat} : (s.pUpload n h).U = s.U := rfl
@[simp] theorem pUpload_head {s : State} {n h : Nat} : (s.pUpload n h).hub.head = s.hub.head :=
  rfl
@[simp] theorem pUpload_seq {s : State} {n h : Nat} : (s.pUpload n h).hub.seq = s.hub.seq := rfl

/-- Facts about the state after `pUpload`. -/
theorem pUpload_frame {s : State} {n h : Nat} :
    (s.pUpload n h).U = s.U ∧ (s.pUpload n h).hub.head = s.hub.head ∧
    (s.pUpload n h).hub.seq = s.hub.seq ∧ (s.pUpload n h).node = s.node :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem measure_pushAccept {s : State} (hI : Inv N s) {n hd : Nat} (hn : n < N)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd) (hne : hd ≠ (s.node n).known.2)
    (hk : Anc s.U.par (s.node n).known.2 hd) (hacc : s.hub.head = (s.node n).known.2) :
    Lex5 (measure N (s.pPushAccept n hd)) (measure N s) := by
  have hU : (s.pPushAccept n hd).U = s.U := rfl
  have hhead : (s.pPushAccept n hd).hub.head = hd := rfl
  have hheads : ∀ i, ((s.pPushAccept n hd).node i).heads = (s.node i).heads := by
    intro i
    by_cases hi : i = n
    · subst hi; simp [State.pPushAccept, State.learn]
    · simp [State.pPushAccept, State.learn, setNode_ne hi]
  have hed : Anc s.U.par s.hub.head hd := hacc ▸ hk
  apply lex5_of
  left
  apply cnt_lt
  · intro i _ ⟨g, hg, hna⟩
    rw [hheads, hU, hhead] at *
    exact ⟨g, hg, fun hA => hna (hA.trans hed)⟩
  · refine ⟨n, hn, ⟨hd, (hh hd).2 rfl, fun hA => ?_⟩, ?_⟩
    · rw [hacc] at hA
      exact hne (Anc.antisymm hI.parLt hA hk)
    · rintro ⟨g, hg, hna⟩
      rw [hheads, hU, hhead] at *
      rw [(hh g).1 hg] at hna
      exact hna Anc.refl

/-- `Idem` and `Reject` both just teach node `n` the current head. -/
theorem measure_pushLearn {s : State} {n : Nat} (hn : n < N) {s' : State}
    (f : Frame s s' n) (hheads : (s'.node n).heads = (s.node n).heads)
    (hknown : (s'.node n).known = (s.hub.seq, s.hub.head))
    (hs : (s.node n).known.1 < s.hub.seq) : Lex5 (measure N s') (measure N s) := by
  apply lex5_of
  right; refine ⟨f.dirty_eq hheads, Or.inl ?_⟩
  apply f.sum_lt hn (fun i hi => f.stale_ne hi)
  unfold mStale; rw [hknown, f.seq]; simp; omega

theorem measure_decreases {s s' : State} (h : Reachable N s) (hp : PStep N s s') :
    Lex5 (measure N s') (measure N s) := by
  have hI := inv_reachable h
  cases hp with
  | learn n hn hs => exact measure_learn hn hs
  | realize n x hn hx hnl hp => exact measure_realize hI hn hx hnl
  | advance n hn hk hna => exact measure_advance hI hn hna
  | merge n L O hn hL h2 => exact measure_merge hI hn hL h2
  | pushAccept n hd hn hh hne hk hacc => exact measure_pushAccept hI hn hh hne hk hacc
  | pushIdem n hd hn hh hne hk hidem =>
    have hlt : (s.node n).known.1 < s.hub.seq := by
      rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
      · exact h1
      · exfalso; apply hne; rw [← hidem, ← hI.histHead, ← h1, (hI.known n).2]
    refine measure_pushLearn hn ⟨rfl, rfl, rfl, fun i hi => ?_⟩ ?_ ?_ hlt
    · simp [State.pPushIdem, State.learn, setNode_ne hi]
    · simp [State.pPushIdem, State.learn]
    · simp [State.pPushIdem, State.learn]
  | pushReject n hd hn hh hne hk hrej hrej' =>
    have hlt : (s.node n).known.1 < s.hub.seq := by
      rcases Nat.lt_or_eq_of_le (hI.known n).1 with h1 | h1
      · exact h1
      · exfalso; apply hrej; rw [← hI.histHead, ← h1, (hI.known n).2]
    refine measure_pushLearn hn ⟨rfl, rfl, rfl, fun i hi => ?_⟩ ?_ ?_ hlt
    · simp [State.pPushReject, State.learn, setNode_ne hi]
    · simp [State.pPushReject, State.learn]
    · simp [State.pPushReject, State.learn]

/-! ## Termination -/

/-- Policy steps from reachable states are well-founded: there is no infinite policy run. -/
theorem pstep_wf : WellFounded (fun s' s => Reachable N s ∧ PStep N s s') :=
  Subrelation.wf (fun ⟨h, hp⟩ => measure_decreases h hp) (InvImage.wf (measure N) lex5_wf)

theorem no_infinite_run_aux {r : State → State → Prop} {a : State} (ha : Acc r a) :
    ∀ f : Nat → State, f 0 = a → ¬ ∀ i, r (f (i + 1)) (f i) := by
  induction ha with
  | intro a _ ih =>
    intro f hf hall
    exact ih (f 1) (hf ▸ hall 0) (fun i => f (i + 1)) rfl (fun i => hall (i + 1))

/-- **Termination**: no infinite sequence of policy steps starts from a reachable state,
whatever the scheduling (in particular despite contention for the hub). -/
theorem no_infinite_policy_run {s : State} (h : Reachable N s) :
    ¬ ∃ f : Nat → State, f 0 = s ∧ ∀ i, PStep N (f i) (f (i + 1)) := by
  rintro ⟨f, hf0, hf⟩
  have hreach : ∀ i, Reachable N (f i) := by
    intro i
    induction i with
    | zero => exact hf0 ▸ h
    | succ i ih => exact pstep_reachable ih (hf i)
  exact no_infinite_run_aux (pstep_wf.apply s) f hf0 (fun i => ⟨hreach i, hf i⟩)

/-! ## Progress -/

open Classical in
/-- The list of heads of node `n` (used to build the merge's parent list). -/
noncomputable def headsList (s : State) (n : Nat) : List Nat :=
  (List.range s.U.next).filter (fun x => decide ((s.node n).heads x))

theorem mem_headsList_of {s : State} {n x : Nat}
    (hlt : ∀ y, (s.node n).heads y → y < s.U.next) :
    x ∈ headsList s n ↔ (s.node n).heads x := by
  unfold headsList
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hlt x h, h⟩⟩

theorem mem_headsList {s : State} (hI : Inv N s) {n x : Nat} :
    x ∈ headsList s n ↔ (s.node n).heads x :=
  mem_headsList_of (fun _ h => hI.headsLt h)

/-- **Progress**: in every reachable state that is not converged, some policy step is
enabled. -/
theorem progress {s : State} (h : Reachable N s) (hc : ¬ Converged N s) :
    ∃ s', PStep N s s' := by
  have hI := inv_reachable h
  unfold Converged at hc
  rw [Classical.not_forall] at hc
  obtain ⟨n, hc⟩ := hc
  rw [Classical.not_imp] at hc
  obtain ⟨hn, hc⟩ := hc
  -- 1. merge
  by_cases hmulti : ∃ a b, (s.node n).heads a ∧ (s.node n).heads b ∧ a ≠ b
  · obtain ⟨a, b, ha, hb, hab⟩ := hmulti
    exact ⟨_, PStep.merge s n (headsList s n) [] hn (fun x => mem_headsList hI)
      ⟨a, b, (mem_headsList hI).2 ha, (mem_headsList hI).2 hb, hab⟩⟩
  -- 2. learn
  by_cases hstale : (s.node n).known.1 < s.hub.seq
  · exact ⟨_, PStep.learn s n hn hstale⟩
  have hk1 : (s.node n).known.1 = s.hub.seq := by have := (hI.known n).1; omega
  have hk2 : (s.node n).known.2 = s.hub.head := by
    rw [← (hI.known n).2, hk1, hI.histHead]
  -- 3. fetch and realize
  by_cases hnloc : ¬ (s.node n).lops (s.node n).known.2
  · have hloc := hnloc
    obtain ⟨x, ⟨hxa, hxl⟩, hmin⟩ := exists_min
      (fun x => Anc s.U.par x (s.node n).known.2 ∧ ¬ (s.node n).lops x)
      (a := (s.node n).known.2) ⟨Anc.refl, hloc⟩
    refine ⟨_, PStep.realize s n x hn hxa hxl (fun p hp => ?_)⟩
    refine Classical.byContradiction fun hpl => ?_
    exact hmin p (hI.parLt x p hp) ⟨(Anc.parent hp).trans hxa, hpl⟩
  have hloc := Classical.not_not.1 hnloc
  -- 4. advance
  by_cases hnadv : ¬ ∃ g, (s.node n).heads g ∧ Anc s.U.par (s.node n).known.2 g
  · exact ⟨_, PStep.advance s n hn hloc hnadv⟩
  have hadv := Classical.not_not.1 hnadv
  -- 5. push
  obtain ⟨g, hg, hkg⟩ := hadv
  have hsingle : ∀ y, (s.node n).heads y ↔ y = g := by
    intro y
    constructor
    · intro hy
      refine Classical.byContradiction fun hne => ?_
      exact hmulti ⟨y, g, hy, hg, hne⟩
    · rintro rfl; exact hg
  have hne : g ≠ (s.node n).known.2 := by
    intro e
    apply hc
    refine ⟨fun y => ?_, ?_⟩
    · rw [hsingle y, e, hk2]
    · rw [← hk2, ← hk1]
  exact ⟨_, PStep.pushAccept s n g hn hsingle hne hkg (hk2.symm)⟩

/-! ## Convergence -/

/-! What a converged node cannot do: the guards of every policy step but `learn` fail. Shared
with `converged_quiescentR`. -/

namespace Converged

variable {s : State} (hc : Converged N s) {n : Nat} (hn : n < N)
include hc hn

/-- Everything below `known.head` is local, so there is nothing to realize. -/
theorem lops_below {x : Nat}
    (hpar : ∀ x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p)
    (hhl : ∀ x, (s.node n).heads x → (s.node n).lops x)
    (hx : Anc s.U.par x (s.node n).known.2) : (s.node n).lops x := by
  rw [(hc n hn).2] at hx
  exact Anc.closed (S := (s.node n).lops) (fun y p hy hp => hpar y p hy hp) hx
    (hhl _ (((hc n hn).1 _).2 rfl))

/-- `known.head` is a head, so there is nothing to advance to. -/
theorem known_in_heads : ∃ h, (s.node n).heads h ∧ Anc s.U.par (s.node n).known.2 h := by
  rw [(hc n hn).2]; exact ⟨_, ((hc n hn).1 _).2 rfl, Anc.refl⟩

/-- There is one head, so nothing to merge. -/
theorem heads_eq {a b : Nat} (ha : (s.node n).heads a) (hb : (s.node n).heads b) : a = b :=
  (((hc n hn).1 a).1 ha).trans (((hc n hn).1 b).1 hb).symm

/-- The one head is `known.head`, so there is nothing to push. -/
theorem head_known {h : Nat} (hh : ∀ y, (s.node n).heads y ↔ y = h) :
    h = (s.node n).known.2 := by
  rw [(hc n hn).2]; exact ((hc n hn).1 h).1 ((hh h).2 rfl)

end Converged

/-- Converged states enable no policy step: once converged, the nodes are quiescent apart
from polls (no feedback loop). -/
theorem converged_quiescent {s : State} (h : Reachable N s) (hc : Converged N s)
    {s' : State} : ¬ PStep N s s' := by
  have hI := inv_reachable h
  intro hp
  cases hp with
  | learn n hn hs => rw [((hc n hn).2)] at hs; exact Nat.lt_irrefl _ hs
  | realize n x hn hx hnl hp =>
    exact hnl (hc.lops_below hn (hI.lParents n) (hI.headsLocal n) hx)
  | advance n hn hk hna => exact hna (hc.known_in_heads hn)
  | merge n L O hn hL h2 =>
    obtain ⟨a, b, ha, hb, hab⟩ := h2
    exact hab (hc.heads_eq hn ((hL a).1 ha) ((hL b).1 hb))
  | pushAccept n hd hn hh hne => exact hne (hc.head_known hn hh)
  | pushIdem n hd hn hh hne => exact hne (hc.head_known hn hh)
  | pushReject n hd hn hh hne => exact hne (hc.head_known hn hh)

/-- A state with no enabled policy step is converged, and conversely. -/
theorem terminal_iff_converged {s : State} (h : Reachable N s) :
    (∀ s', ¬ PStep N s s') ↔ Converged N s := by
  constructor
  · intro ht
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨s', hs'⟩ := progress h hc
    exact ht s' hs'
  · intro hc s'
    exact converged_quiescent h hc

/-- In a converged state every operation any node created is in `anc*(hub.head)`. -/
theorem converged_all_accepted {s : State} (h : Reachable N s) (hc : Converged N s)
    {x : Nat} (hx : x < s.U.next) : Anc s.U.par x s.hub.head := by
  have hI := inv_reachable h
  by_cases hx0 : x = 0
  · subst hx0; exact hI.rootAnc _ hI.headLt
  · obtain ⟨n, hn, hcr⟩ := hI.creatorSome x (by omega) hx
    obtain ⟨g, hg, hA⟩ := hI.ownInHeads n x hx hcr
    rw [((hc n hn).1 g).1 hg] at hA
    exact hA

theorem PSteps.head {s t u : State} (h1 : PStep N s t) (h2 : PSteps N t u) :
    PSteps N s u := by
  induction h2 with
  | refl => exact PSteps.tail (PSteps.refl _) h1
  | tail _ hst ih => exact PSteps.tail ih hst

/-- **Liveness**: from every reachable state, policy steps reach a converged state. -/
theorem eventually_converges {s : State} (h : Reachable N s) :
    ∃ s', PSteps N s s' ∧ Converged N s' := by
  refine WellFounded.induction (C := fun s => Reachable N s → ∃ s', PSteps N s s' ∧
    Converged N s') (pstep_wf (N := N)) s (fun s ih h => ?_) h
  by_cases hc : Converged N s
  · exact ⟨s, PSteps.refl s, hc⟩
  · obtain ⟨s', hs'⟩ := progress h hc
    obtain ⟨u, hu, huc⟩ := ih s' ⟨h, hs'⟩ (pstep_reachable h hs')
    exact ⟨u, PSteps.head hs' hu, huc⟩

/-- **Liveness**, maximal-run form: every policy run from a reachable state that cannot be
extended ends in a converged state (and, by `no_infinite_policy_run`, every run is finite). -/
theorem maximal_run_converges {s s' : State} (h : Reachable N s) (hr : PSteps N s s')
    (hmax : ∀ s'', ¬ PStep N s' s'') : Converged N s' :=
  (terminal_iff_converged (psteps_reachable h hr)).1 hmax

end Musubi

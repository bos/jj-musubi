/-
Progress at the asynchronous boundaries hidden by the atomic policy exchanges. These lemmas
do not yet prove the retry bridge: fix-up creation and stale ordered-record adoption need a
separate stabilization argument before the record-aware policy theorem can apply.
-/
import Musubi.RecordLiveness

namespace Musubi

variable {N : Nat}

/-- An honest delayed reply can improve a consistent node without naming the hub's latest
head. The reply must belong to the current history; recovery from an obsolete history is
outside this lemma. Network, staging and hub stores are deliberately unconstrained. -/
theorem measureR_delayed_learn {s t : State} {n sq hd : Nat}
    (hn : n < N) (hc : Consistent s n) (hsq : sq ≤ s.hub.seq)
    (hhist : s.hub.hist sq = hd) (hlt : (s.node n).known.1 < sq)
    (f : RFrame s t n) (hheads : (t.node n).heads = (s.node n).heads)
    (hknown : (t.node n).known = (sq, hd)) :
    Lex6 (rmeasure N t) (rmeasure N s) := by
  have hc' : Consistent t n := by
    unfold Consistent
    rw [hknown, f.seq, f.hist]
    exact ⟨hsq, hhist⟩
  have hset := settled_congr f.U f.head f.seq f.hist hheads
  have hg : ∀ i, Good t i ↔ Good s i := by
    intro i
    by_cases hi : i = n
    · subst i
      exact ⟨fun h => ⟨hc, hset.1 h.2⟩, fun h => ⟨hc', hset.2 h.2⟩⟩
    · exact f.good_ne hi
  have hcons : ∀ i, Consistent t i ↔ Consistent s i := by
    intro i
    by_cases hi : i = n
    · subst i; exact ⟨fun _ => hc, fun _ => hc'⟩
    · exact f.consistent_ne hi
  have e1 : mBad N t = mBad N s := cnt_congr fun i _ => not_congr (hg i)
  have e2 : mIncons N t = mIncons N s := cnt_congr fun i _ => not_congr (hcons i)
  unfold rmeasure
  rw [e1, e2]
  apply Prod.Lex.right
  apply Prod.Lex.right
  apply Prod.Lex.left
  apply sumN_lt hn
  · unfold mStaleR
    simp only [hc, hc', ↓reduceIte, hknown, f.seq]
    omega
  · intro i _ hi; exact f.staleR_ne hi

/-- Acceptance makes the pusher good before it receives the acknowledgement. This is the
hub-only effect, so a lost reply does not erase the decrease. It relies on the pusher still
having the single head it sent, and its old knowledge belonging to the current history. -/
theorem bad_accept_before_reply {s : State} (hI : InvR N s) {n hd : Nat}
    (hn : n < N) (hc : Consistent s n)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd)
    (hne : hd ≠ s.hub.head) (hdesc : Anc s.U.par s.hub.head hd) :
    mBad N (s.hubAccept hd) < mBad N s := by
  have histOld : ∀ {i}, i ≤ s.hub.seq →
      upd s.hub.hist (s.hub.seq + 1) hd i = s.hub.hist i :=
    fun hi => upd_ne _ _ (by omega)
  have hbad : ¬ Good s n := by
    rintro ⟨_, x, hx, hxa, _⟩
    have he : x = hd := ((hx hd).1 ((hh hd).2 rfl)).symm
    subst x
    exact hne (Anc.antisymm hI.parLt hxa hdesc)
  have hgood : Good (s.hubAccept hd) n := by
    refine ⟨?_, hd, hh, Anc.refl, ?_⟩
    · exact ⟨Nat.le_succ_of_le hc.1, (histOld hc.1).trans hc.2⟩
    · intro i hi
      change i ≤ s.hub.seq + 1 at hi
      change Anc s.U.par hd (upd s.hub.hist (s.hub.seq + 1) hd i) ∨
        Anc s.U.par (upd s.hub.hist (s.hub.seq + 1) hd i) hd
      by_cases he : i = s.hub.seq + 1
      · subst i; exact Or.inl (by simp [Anc.refl])
      · rw [histOld (by omega)]
        exact Or.inr ((hI.histAnc (by omega)).trans hdesc)
  apply cnt_lt
  · intro i _ hng hg
    apply hng
    obtain ⟨hci, x, hx, hxa, hcmp⟩ := hg
    refine ⟨?_, x, hx, hxa.trans hdesc, ?_⟩
    · exact ⟨Nat.le_succ_of_le hci.1, (histOld hci.1).trans hci.2⟩
    · intro j hj
      change j ≤ s.hub.seq + 1 at hj
      change Anc s.U.par x (upd s.hub.hist (s.hub.seq + 1) hd j) ∨
        Anc s.U.par (upd s.hub.hist (s.hub.seq + 1) hd j) x
      by_cases he : j = s.hub.seq + 1
      · subst j; exact Or.inl (by simpa using hxa.trans hdesc)
      · rw [histOld (by omega)]; exact hcmp j (by omega)
  · exact ⟨n, hn, hbad, fun h => h hgood⟩

theorem measureR_accept_before_reply {s : State} (hI : InvR N s) {n hd : Nat}
    (hn : n < N) (hc : Consistent s n)
    (hh : ∀ y, (s.node n).heads y ↔ y = hd)
    (hne : hd ≠ s.hub.head) (hdesc : Anc s.U.par s.hub.head hd) :
    Lex6 (rmeasure N (s.hubAccept hd)) (rmeasure N s) :=
  Prod.Lex.left _ _ (bad_accept_before_reply hI hn hc hh hne hdesc)

/-- Stores, staging and message bookkeeping do not affect whether a node is good. -/
structure HeadAgreement (s t : State) : Prop where
  U : s.U = t.U
  head : s.hub.head = t.hub.head
  seq : s.hub.seq = t.hub.seq
  hist : s.hub.hist = t.hub.hist
  heads : ∀ n, (s.node n).heads = (t.node n).heads
  known : ∀ n, (s.node n).known = (t.node n).known

theorem HeadAgreement.bad_eq {s t : State} (h : HeadAgreement s t) :
    mBad N s = mBad N t :=
  cnt_congr fun i _ => not_congr
    (good_congr h.U h.head h.seq h.hist (h.heads i) (h.known i))

theorem lex6_first_le {a b : Nat × Nat × Nat × Nat × Nat × Nat} (h : Lex6 a b) :
    a.1 ≤ b.1 := by
  cases h with
  | left _ _ h => exact Nat.le_of_lt h
  | right => exact Nat.le_refl _

/-- The nonincreasing first component after operation-creating disturbances stop. Local
merges remain allowed: they cannot make a good node bad. A real advance/merge is two steps.
The relation deliberately excludes fix-up creation, hub regression, and obsolete-history
recovery; proving that a concrete run eventually has this form is a separate obligation. -/
inductive SettlingStep (N : Nat) : State → State → Prop
  | policy {s t : State} (hp : PStepR N s t)
      (hh : t.hub.head = s.hub.head) (hs : t.hub.seq = s.hub.seq) : SettlingStep N s t
  | delayed {s t : State} {n sq hd : Nat} (hn : n < N)
      (hc : Consistent s n) (hsq : sq ≤ s.hub.seq) (hhist : s.hub.hist sq = hd)
      (hlt : (s.node n).known.1 < sq) (f : RFrame s t n)
      (hheads : (t.node n).heads = (s.node n).heads)
      (hknown : (t.node n).known = (sq, hd)) : SettlingStep N s t
  | accept {s t : State} {n hd : Nat} (hn : n < N) (hc : Consistent s n)
      (hh : ∀ y, (s.node n).heads y ↔ y = hd)
      (hne : hd ≠ s.hub.head) (hdesc : Anc s.U.par s.hub.head hd)
      (ha : HeadAgreement t (s.hubAccept hd)) : SettlingStep N s t
  | bookkeeping {s t : State} (ha : HeadAgreement t s) : SettlingStep N s t

/-- Acceptance is the only hub-head change in this suffix, and pays for it immediately. -/
theorem settling_decreases {s t : State} (hr : RReachable N s) (hs : SettlingStep N s t) :
    mBad N t ≤ mBad N s ∧
      ((t.hub.seq, t.hub.head) ≠ (s.hub.seq, s.hub.head) → mBad N t < mBad N s) := by
  cases hs with
  | policy hp hh hseq =>
    exact ⟨lex6_first_le (measureR_decreases hr hp), fun h => False.elim (h (by rw [hh, hseq]))⟩
  | delayed hn hc hsq hh hlt f hheads hknown =>
    exact ⟨lex6_first_le (measureR_delayed_learn hn hc hsq hh hlt f hheads hknown),
      fun h => False.elim (h (by rw [f.head, f.seq]))⟩
  | accept hn hc hh hne hdesc ha =>
    have hlt := bad_accept_before_reply (invR_reachable hr) hn hc hh hne hdesc
    rw [ha.bad_eq]
    exact ⟨Nat.le_of_lt hlt, fun _ => hlt⟩
  | bookkeeping ha =>
    rw [ha.bad_eq]
    exact ⟨Nat.le_refl _, fun h => False.elim (h (by rw [ha.seq, ha.head]))⟩

/-- A natural-valued nonincreasing trace eventually has its least attained value. This
does not require a bound on the time between changes. -/
theorem nat_trace_stabilizes (f : Nat → Nat) (hf : ∀ i, f (i + 1) ≤ f i) :
    ∃ k, ∀ i, k ≤ i → f i = f k := by
  suffices h : ∀ b, ∀ g : Nat → Nat, g 0 = b → (∀ i, g (i + 1) ≤ g i) →
      ∃ k, ∀ i, k ≤ i → g i = g k from h (f 0) f rfl hf
  intro b
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro g h0 hg
    by_cases hsm : ∃ j, g j < b
    · obtain ⟨j, hj⟩ := hsm
      obtain ⟨k, hk⟩ := ih (g j) hj (fun i => g (j + i)) (by simp)
        (fun i => by simpa [Nat.add_assoc] using hg (j + i))
      refine ⟨j + k, fun i hi => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show j ≤ i by omega)
      exact hk d (by omega)
    · refine ⟨0, fun i _ => ?_⟩
      have hle : ∀ i, g i ≤ b := by
        intro i
        induction i with
        | zero => omega
        | succ i ih => exact Nat.le_trans (hg i) ih
      have hnot : ¬ g i < b := fun h => hsm ⟨i, h⟩
      have := hle i
      omega

/-- On a suffix with no fix-up creation or obsolete-history recovery, hub acceptance
cannot continue forever. This proves hub stabilization from the primitive acceptance
effect, rather than assuming the hub stops accepting. Establishing such a suffix for the
implementation still requires the finite-fix-up/record and transport arguments. -/
theorem settling_hub_stabilizes (run : Nat → State)
    (hr : ∀ i, RReachable N (run i))
    (hs : ∀ i, SettlingStep N (run i) (run (i + 1))) :
    ∃ k, ∀ i, k ≤ i →
      ((run i).hub.seq, (run i).hub.head) = ((run k).hub.seq, (run k).hub.head) := by
  obtain ⟨k, hk⟩ := nat_trace_stabilizes (fun i => mBad N (run i))
    (fun i => (settling_decreases (hr i) (hs i)).1)
  refine ⟨k, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => simp
  | succ d ih =>
    let i := k + d
    have he : ((run (i + 1)).hub.seq, (run (i + 1)).hub.head) =
        ((run i).hub.seq, (run i).hub.head) := by
      apply Classical.byContradiction
      intro hne
      have hlt := (settling_decreases (hr i) (hs i)).2 hne
      rw [hk i (by omega), hk (i + 1) (by omega)] at hlt
      exact Nat.lt_irrefl _ hlt
    exact he.trans (ih (by omega))

end Musubi

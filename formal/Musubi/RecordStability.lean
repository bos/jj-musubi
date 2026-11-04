/-
Hub record stabilization is independent of original-head ancestry. After regressions stop,
`takeRecs` appends only a nonempty difference. If all original drops are below a finite cut,
each changed record list spends an unseen original; pruning then spends a bounded prefix.
This does not assume that the hub stops accepting heads, or that nodes have reconciled yet.
-/
import Musubi.RetryControl
import Musubi.ContractOrder

namespace Musubi.Exec

noncomputable def unseenDrops (B : Nat) (s : SEState) : Nat :=
  cnt B (fun x => x ∉ s.hubDL)

/-- The rollback-free executable record rules append a difference or keep the list, and
never move the pruned prefix backwards. No head-ancestry invariant is used here. -/
theorem sexec_record_control {N : Nat} {s t : SEState} {a : SAction}
    (h : sexecStep N s a = .ok t) (hnr : a.goesBack = false) :
    (t.recs = s.recs ∨ ∃ D, t.recs = s.takeRecs D) ∧ s.pruned ≤ t.pruned := by
  simp only [sexecStep] at h
  obtain ⟨_, h⟩ := sreq_ok h
  cases a with
  | base b =>
    cases hs : execStep N s.es b with
    | error e => simp [sexecCore, hs] at h
    | ok es' =>
      cases hr : b.regressSeq with
      | some i =>
        have hb := regressSeq_some hr
        subst b
        simp [SAction.goesBack, Action.goesBack] at hnr
      | none =>
        simp only [sexecCore, hs, hr] at h
        obtain ⟨_, h⟩ := sreq_ok h
        obtain ⟨_, h⟩ := sreq_ok h
        cases h
        exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | abandon n D =>
    simp only [sexecCore] at h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    cases h
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | sendSup n d =>
    simp only [sexecCore] at h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    cases h
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | sendD n =>
    simp only [sexecCore] at h
    obtain ⟨_, h⟩ := sreq_ok h
    cases h
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | adopt n R =>
    simp only [sexecCore] at h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    cases h
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | hubSupAccept n S O e d A D =>
    simp only [sexecCore] at h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    cases hs : execStep N s.es (.hubPushAccept n S O e d) with
    | error e => rw [hs] at h; cases h
    | ok es' =>
      rw [hs] at h
      obtain ⟨_, h⟩ := sreq_ok h
      cases h
      exact ⟨Or.inr ⟨D, rfl⟩, Nat.le_refl _⟩
  | hubPushRefuse n S O e d A D =>
    simp only [sexecCore] at h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    cases h
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | prune k =>
    simp only [sexecCore] at h
    obtain ⟨hp, h⟩ := sreq_ok h
    obtain ⟨_, h⟩ := sreq_ok h; obtain ⟨_, h⟩ := sreq_ok h
    cases h
    exact ⟨Or.inl rfl, of_decide_eq_true hp⟩

theorem takeRecs_grows (s : SEState) (D : List Nat) {x : Nat}
    (hx : x ∈ s.hubDL) : x ∈ flat (s.takeRecs D) :=
  (mem_takeRecs s D x).2 (Or.inl hx)

theorem takeRecs_changes {s : SEState} {D : List Nat}
    (he : s.takeRecs D ≠ s.recs) :
    ∃ x, x ∈ flat (s.takeRecs D) ∧ x ∉ s.hubDL := by
  have hn : newRec s D ≠ [] := by
    intro hz
    exact he (by simp [SEState.takeRecs, hz])
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (newRec s D) hn
  have hm := (mem_newRec s D x).1 hx
  exact ⟨x, (mem_takeRecs s D x).2 (Or.inr hm.1), hm.2⟩

/-- Once the record list is fixed, any accepted payload contains only already known
original drops. A delayed or repeated acceptance cannot evade this by changing order. -/
theorem takeRecs_eq_iff (s : SEState) (D : List Nat) :
    s.takeRecs D = s.recs ↔ ∀ x ∈ D, x ∈ s.hubDL := by
  constructor
  · intro he x hx
    have hm := (mem_takeRecs s D x).2 (Or.inr hx)
    simpa [he, SEState.hubDL] using hm
  · intro hsub
    have hn : newRec s D = [] := by
      apply Classical.byContradiction
      intro hne
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil (newRec s D) hne
      have hm := (mem_newRec s D x).1 hx
      exact hm.2 (hsub x hm.1)
    simp [SEState.takeRecs, hn]

/-- Every record-changing acceptance spends a previously unseen original. This uses the
actual record constructor, without the old model's original-ancestry acceptance guard. -/
theorem unseenDrops_step {B : Nat} {s t : SEState}
    (hs : t.recs = s.recs ∨ ∃ D, t.recs = s.takeRecs D)
    (hb : ∀ x ∈ t.hubDL, x < B) :
    unseenDrops B t ≤ unseenDrops B s ∧
      (t.recs ≠ s.recs → unseenDrops B t < unseenDrops B s) := by
  rcases hs with he | ⟨D, he⟩
  · have hsame : t.hubDL = s.hubDL := by simp [SEState.hubDL, he]
    simp [unseenDrops, hsame, he]
  · have hg : ∀ x, x ∈ s.hubDL → x ∈ t.hubDL := by
      intro x hx
      simpa [SEState.hubDL, he] using takeRecs_grows s D hx
    constructor
    · exact cnt_le (fun x _ hnt hx => hnt (hg x hx))
    · intro hne
      have hchange : s.takeRecs D ≠ s.recs := by simpa [he] using hne
      obtain ⟨x, hxt, hxs⟩ := takeRecs_changes hchange
      have hxt' : x ∈ t.hubDL := by simpa [SEState.hubDL, he] using hxt
      exact cnt_lt (fun y _ hnt hy => hnt (hg y hy))
        ⟨x, hb x hxt', hxs, fun h => h hxt'⟩

/-- With no record rollback and only bounded original drops, the full ordered record list
eventually stops changing, even if head acceptances and duplicate requests continue. -/
theorem records_eventually_stabilize (B : Nat) (run : Nat → SEState)
    (hs : ∀ i, (run (i + 1)).recs = (run i).recs ∨
      ∃ D, (run (i + 1)).recs = (run i).takeRecs D)
    (hb : ∀ i x, x ∈ (run i).hubDL → x < B) :
    ∃ k, ∀ i, k ≤ i → (run i).recs = (run k).recs := by
  obtain ⟨k, hk⟩ := Musubi.nat_trace_stabilizes (fun i => unseenDrops B (run i))
    (fun i => (unseenDrops_step (hs i) (hb (i + 1))).1)
  refine ⟨k, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction d with
  | zero => simp
  | succ d ih =>
    have he : (run (k + d + 1)).recs = (run (k + d)).recs := by
      apply Classical.byContradiction
      intro hne
      have hlt := (unseenDrops_step (hs (k + d)) (hb (k + d + 1))).2 hne
      rw [hk (k + d) (by omega), hk (k + d + 1) (by omega)] at hlt
      exact Nat.lt_irrefl _ hlt
    simpa [Nat.add_assoc] using he.trans (ih (by omega))

/-- Record stabilization gives an original-ancestry epoch even when earlier accepted heads
do not form such a chain. `par` is the immutable birth-parent graph of the whole run; the
step premise is the contracted comparison under the resulting hub drops, not the old
original-ancestry guard. Its physical-store projection is a separate obligation. -/
theorem eventual_original_chain (B : Nat) (run : Nat → SEState)
    (hlt : ParLt par)
    (hs : ∀ i, (run (i + 1)).recs = (run i).recs ∨
      ∃ D, (run (i + 1)).recs = (run i).takeRecs D)
    (hb : ∀ i x, x ∈ (run i).hubDL → x < B)
    (halive : ∀ i, ((run i).hubDL.contains (run i).es.hub.head) = false)
    (hstep : ∀ i, Contract.Below par (fun x => (run (i + 1)).hubDL.contains x)
      (run i).es.hub.head (run (i + 1)).es.hub.head) :
    ∃ k, ∀ i j, k ≤ i → i ≤ j →
      Anc par (run i).es.hub.head (run j).es.hub.head := by
  obtain ⟨k, hk⟩ := records_eventually_stabilize B run hs hb
  let D := fun x => (run k).hubDL.contains x
  have hd : ∀ i, k ≤ i → (fun x => (run i).hubDL.contains x) = D := by
    intro i hi
    simp [SEState.hubDL, hk i hi, D]
  have ha : ∀ i, D (run (k + i)).es.hub.head = false := by
    intro i
    have h := halive (k + i)
    change (fun x => (run (k + i)).hubDL.contains x) (run (k + i)).es.hub.head = false at h
    rwa [hd (k + i) (by omega)] at h
  have hs' : ∀ i, Contract.Below par D
      (run (k + i)).es.hub.head (run (k + (i + 1))).es.hub.head := by
    intro i
    have h := hstep (k + i)
    rw [hd (k + i + 1) (by omega)] at h
    simpa [Nat.add_assoc] using h
  have hc := Contract.stable_suffix_chain hlt
    (fun i => (run (k + i)).es.hub.head) D ha hs'
  refine ⟨k, fun i j hi hij => ?_⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hi
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ j by omega)
  exact hc a b (by omega)

/-- Pruning can continue after the last append, but only through the finite record prefix.
The full modeled record list and its pruned-prefix count therefore eventually stabilize. -/
theorem record_prefix_eventually_stabilizes (B : Nat) (run : Nat → SEState)
    (hs : ∀ i, (run (i + 1)).recs = (run i).recs ∨
      ∃ D, (run (i + 1)).recs = (run i).takeRecs D)
    (hb : ∀ i x, x ∈ (run i).hubDL → x < B)
    (hp : ∀ i, (run i).pruned ≤ (run (i + 1)).pruned)
    (hl : ∀ i, (run i).pruned ≤ (run i).recs.length) :
    ∃ k, ∀ i, k ≤ i →
      ((run i).recs, (run i).pruned) = ((run k).recs, (run k).pruned) := by
  obtain ⟨k, hk⟩ := records_eventually_stabilize B run hs hb
  let debt := fun i => (run k).recs.length - (run (k + i)).pruned
  have hd : ∀ i, debt (i + 1) ≤ debt i := by
    intro i
    have hm : (run (k + i)).pruned ≤ (run (k + (i + 1))).pruned := by
      simpa only [Nat.add_assoc] using hp (k + i)
    dsimp [debt]
    omega
  obtain ⟨j, hj⟩ := Musubi.nat_trace_stabilizes debt hd
  refine ⟨k + j, fun i hi => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show k ≤ i by omega)
  have he := hj d (by omega)
  have hbi := hl (k + d)
  have hbj := hl (k + j)
  rw [hk (k + d) (by omega)] at hbi
  rw [hk (k + j) (by omega)] at hbj
  have hp' : (run (k + d)).pruned = (run (k + j)).pruned := by
    dsimp [debt] at he
    omega
  exact Prod.ext ((hk (k + d) (by omega)).trans (hk (k + j) (by omega)).symm) hp'

/-- The executable rules discharge the record-step and pruning premises. Only the finite
original-drop bound and cessation of rollback remain as trace assumptions. -/
theorem sexec_record_prefix_stabilizes (N B : Nat) (run : Nat → SEState)
    (actions : Nat → SAction) (hok : SEOK (run 0))
    (hs : ∀ i, sexecStep N (run i) (actions i) = .ok (run (i + 1)))
    (hnr : ∀ i, (actions i).goesBack = false)
    (hb : ∀ i x, x ∈ (run i).hubDL → x < B) :
    ∃ k, ∀ i, k ≤ i →
      ((run i).recs, (run i).pruned) = ((run k).recs, (run k).pruned) := by
  have hi : ∀ i, SEOK (run i) := by
    intro i
    induction i with
    | zero => exact hok
    | succ i ih => exact sexec_ok ih (hs i)
  exact record_prefix_eventually_stabilizes B run
    (fun i => (sexec_record_control (hs i) (hnr i)).1) hb
    (fun i => (sexec_record_control (hs i) (hnr i)).2) (fun i => (hi i).pruned)

/-- Pending is a difference in immutable original-operation names. -/
theorem mem_pendingOf (R : List Rec) (D : List Nat) (x : Nat) :
    x ∈ pendingOf R D ↔ x ∈ D ∧ x ∉ flat R := by
  simp [pendingOf]

/-- Once a node has aligned to the current record epoch, adopting an extension cannot
introduce a pending original. This derives the retry budget's shrink premise from adoptR,
rather than imposing a test on the resulting progress rank. -/
theorem adopt_pending_subset (s : SEState) (n : Nat) (R : List Rec)
    (he : ∀ x, x ∈ flat (s.appliedF n) → x ∈ flat R) :
    ∀ x, x ∈ pendingOf R ((s.adoptR n R).nodeDF n) →
      x ∈ pendingOf (s.appliedF n) (s.nodeDF n) := by
  intro x hx
  have hD : (s.adoptR n R).nodeDF n = union (s.nodeDF n) (flat R) := by
    change (s.setD n (union (s.nodeDF n) (flat R))).nodeDF n = _
    simp [nodeDF_setD]
  have hm := (mem_pendingOf R _ x).1 hx
  rw [hD] at hm
  have ho : x ∈ s.nodeDF n := (mem_union.1 hm.1).resolve_right hm.2
  exact (mem_pendingOf _ _ x).2 ⟨ho, fun h => hm.2 (he x h)⟩

/-- The existing cache epoch accepts every such adoption, for either cache flag. The
first adoption of a different epoch remains unrestricted by that model. -/
theorem retry_adopt_of_extension (s : SEState) (n : Nat) (R : List Rec)
    (cache : Musubi.Retry.Fixup)
    (hc : cache.pending = pendingOf (s.appliedF n) (s.nodeDF n))
    (he : ∀ x, x ∈ flat (s.appliedF n) → x ∈ flat R) :
    ∃ next, cache.adopt (pendingOf R ((s.adoptR n R).nodeDF n)) = some next := by
  have ha : (pendingOf R ((s.adoptR n R).nodeDF n)).all cache.pending.contains = true := by
    apply List.all_eq_true.2
    intro x hx
    exact List.contains_iff_mem.2 (hc ▸ adopt_pending_subset s n R he x hx)
  unfold Musubi.Retry.Fixup.adopt
  simp [ha]

/-- A monotone set of bounded original-operation identities eventually stops growing.
The list can still change order or duplicate entries; those do not change its set. -/
theorem bounded_drop_set_stabilizes (B : Nat) (run : Nat → List Nat)
    (hm : ∀ i x, x ∈ run i → x ∈ run (i + 1))
    (hb : ∀ i x, x ∈ run i → x < B) :
    ∃ k, ∀ i, k ≤ i → ∀ x, x ∈ run i ↔ x ∈ run k := by
  have mono {i j : Nat} (hij : i ≤ j) : ∀ x, x ∈ run i → x ∈ run j := by
    induction hij with
    | refl => exact fun _ hx => hx
    | step _ ih => exact fun x hx => hm _ x (ih x hx)
  let unseen := fun i => cnt B (fun x => x ∉ run i)
  obtain ⟨k, hk⟩ := Musubi.nat_trace_stabilizes unseen
    (fun i => cnt_le (fun x _ hn hx => hn (hm i x hx)))
  refine ⟨k, fun i hi x => ⟨fun hx => ?_, mono hi x⟩⟩
  apply Classical.byContradiction
  intro hn
  have hlt : unseen i < unseen k :=
    cnt_lt (fun y _ hnt hy => hnt (mono hi y hy))
      ⟨x, hb i x hx, hn, fun h => h hx⟩
  rw [hk i hi] at hlt
  exact Nat.lt_irrefl _ hlt

/-- A finite set of participating nodes has a common cut after which none learns a new
original drop. This is independent of their applied record boundaries and cache flags. -/
theorem node_drop_sets_eventually_stabilize (N B : Nat) (run : Nat → SEState)
    (hm : ∀ i n, n < N → ∀ x, x ∈ (run i).nodeDF n → x ∈ (run (i + 1)).nodeDF n)
    (hb : ∀ i n, n < N → ∀ x, x ∈ (run i).nodeDF n → x < B) :
    ∃ k, ∀ i, k ≤ i → ∀ n, n < N → ∀ x,
      x ∈ (run i).nodeDF n ↔ x ∈ (run k).nodeDF n := by
  induction N with
  | zero => exact ⟨0, fun _ _ _ hn => by omega⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih
      (fun i n hn => hm i n (by omega)) (fun i n hn => hb i n (by omega))
    obtain ⟨j, hj⟩ := bounded_drop_set_stabilizes B (fun i => (run i).nodeDF N)
      (fun i x hx => hm i N (by omega) x hx) (fun i x hx => hb i N (by omega) x hx)
    refine ⟨max k j, fun i hi n hn x => ?_⟩
    by_cases hnN : n = N
    · subst n
      exact (hj i (by omega) x).trans (hj (max k j) (by omega) x).symm
    · exact (hk i (by omega) n (by omega) x).trans
        (hk (max k j) (by omega) n (by omega) x).symm

/-- The record and original-drop cut needs only their own field effects. Local raw
realization may contract parents, so it need not simulate an original-history `cexecAction`
to use this cut. An implementation supplies record append/prune effects and persistent
original-drop custody independently of how its raw repository operations are represented. -/
theorem record_and_drop_sets_stabilize (N B : Nat) (run : Nat → SEState)
    (hs : ∀ i, (run (i + 1)).recs = (run i).recs ∨
      ∃ D, (run (i + 1)).recs = (run i).takeRecs D)
    (hp : ∀ i, (run i).pruned ≤ (run (i + 1)).pruned)
    (hl : ∀ i, (run i).pruned ≤ (run i).recs.length)
    (hm : ∀ i n, n < N → ∀ x, x ∈ (run i).nodeDF n → x ∈ (run (i + 1)).nodeDF n)
    (hhub : ∀ i x, x ∈ (run i).hubDL → x < B)
    (hnode : ∀ i n, n < N → ∀ x, x ∈ (run i).nodeDF n → x < B) :
    ∃ k, ∀ i, k ≤ i →
      ((run i).recs, (run i).pruned) = ((run k).recs, (run k).pruned) ∧
      ∀ n, n < N → ∀ x, x ∈ (run i).nodeDF n ↔ x ∈ (run k).nodeDF n := by
  obtain ⟨r, hr⟩ := record_prefix_eventually_stabilizes B run hs hhub hp hl
  obtain ⟨d, hd⟩ := node_drop_sets_eventually_stabilize N B run hm hnode
  refine ⟨max r d, fun i hi => ?_⟩
  constructor
  · exact (hr i (by omega)).trans (hr (max r d) (by omega)).symm
  · intro n hn x
    exact (hd i (by omega) n hn x).trans (hd (max r d) (by omega) n hn x).symm

end Musubi.Exec

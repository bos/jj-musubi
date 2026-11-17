/-
Stabilization of the hub's record list, which does not depend on ancestry between original
heads. Once rollbacks stop, `takeRecs` appends only a nonempty difference. If every original
drop is below a finite bound `B`, each change of the record list spends an original drop not
yet seen, so the list stops changing; pruning then spends a bounded prefix. The hub may keep
accepting heads, and nodes need not have reconciled.

The convergence proof uses this file except `sexec_record_prefix_stabilizes`,
`adopt_pending_subset` and their helpers, which are not used by the assembly and stand alone.
-/
import Musubi.RetryControl
import Musubi.ContractOrder

namespace Musubi.Exec

/-- The number of original drops below `B` that the hub has not yet seen. -/
noncomputable def unseenDrops (B : Nat) (s : SEState) : Nat :=
  cnt B (fun x => x ∉ s.hubDL)

/-- A step that is not a rollback either keeps the record list or replaces it by `takeRecs`
(an append of the difference), and never moves the pruned prefix backwards. -/
theorem sexec_record_control {N : Nat} {s t : SEState} {a : SAction}
    (h : sexecStep N s a = .ok t) (hnr : a.goesBack = false) :
    (t.recs = s.recs ∨ ∃ D, t.recs = s.takeRecs D) ∧ s.pruned ≤ t.pruned := by
  simp only [sexecStep] at h
  peel h with _
  have core : ∀ {b : Action} {t : SEState}, b.goesBack = false → baseCore N s b = .ok t →
      t.recs = s.recs ∧ t.pruned = s.pruned := by
    intro b t hb hc
    rcases baseCore_ok hc with ⟨i, -, -, hr, -⟩ | ⟨_, -, -, -, -, rfl⟩
    · have := regressSeq_some hr
      subst b
      simp [Action.goesBack] at hb
    · exact ⟨rfl, rfl⟩
  cases a with
  | base b =>
    rcases sexecCore_base h with ⟨n, -, -, rfl⟩ | ⟨-, hc⟩
    · exact ⟨Or.inl rfl, Nat.le_refl _⟩
    · obtain ⟨hr, hp⟩ := core (by simpa [SAction.goesBack] using hnr) hc
      exact ⟨Or.inl hr, hp ▸ Nat.le_refl _⟩
  | abandon n D =>
    unstep [sexecCore] h with _ _ _ _
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | sendSup n d =>
    unstep [sexecCore] h with _ _
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | sendD n =>
    unstep [sexecCore] h with _
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | adopt n R =>
    unstep [sexecCore] h with _ _ _
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | hubSupAccept n S O e d A D =>
    unstep [sexecCore] h with _
    exact ⟨Or.inr ⟨D, rfl⟩, Nat.le_refl _⟩
  | hubPushRefuse n S O e d A D =>
    unstep [sexecCore] h with _ _ _
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | hubSupReject n S O e d A D =>
    simp only [sexecCore] at h
    peel h with _
    obtain ⟨hr, hp⟩ := core rfl h
    exact ⟨Or.inl hr, hp ▸ Nat.le_refl _⟩
  | advancePrepared n R =>
    unstep [sexecCore] h with _
    exact ⟨Or.inl rfl, Nat.le_refl _⟩
  | prune k =>
    unstep [sexecCore] h with hp _ _
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

/-- `takeRecs D` leaves the record list unchanged exactly when every original drop in `D` is
already in the hub's drops. Order does not matter. -/
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

/-- Every acceptance that changes the record list adds an original drop not previously seen;
no step removes one. This follows from the record constructor `takeRecs` alone. -/
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

/-- With no record rollback and original drops bounded by `B`, the ordered record list
eventually stops changing, though head acceptances and duplicate requests may continue. -/
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

/-- Record stabilization gives a point from which the hub's heads form an ancestry chain in
`par`, even if earlier accepted heads do not. `par` is the immutable birth-parent graph of the
whole run. The step premise `hstep` is the contracted comparison (`Contract.Below`) under the
hub's drops. Projecting this onto the physical stores is not covered here. -/
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

/-- Pruning can continue after the last append, but only through the finite record prefix. So
the record list and its pruned-prefix count both eventually stop changing. -/
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

/-- The executable rules give the record-step and pruning premises of the previous theorem.
The remaining assumptions on the trace are that original drops are bounded by `B` and that no
step is a rollback. -/
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

/-- Pending is the difference of the original-operation names `D` and those in the records
`R`. -/
theorem mem_pendingOf (R : List Rec) (D : List Nat) (x : Nat) :
    x ∈ pendingOf R D ↔ x ∈ D ∧ x ∉ flat R := by
  simp [pendingOf]

/-- Once a node has aligned to the current record epoch, adopting an extension `R` of its
applied records introduces no new pending original. This gives the retry budget's shrink
premise (`Fixup.adopt`) from `adoptR`. -/
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

/-- Within the current cache epoch, `Fixup.adopt` accepts every such adoption, whatever the
cache flags. The first adoption of a different epoch is unrestricted in the `Fixup` model. -/
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

/-- The record list, pruned prefix and every node's original-drop set eventually stop changing
together. Only the field effects are assumed: record append and prune, and nodes keeping the
original drops they have learned. Local raw operations may contract parents, so they need not
simulate an executable step for this theorem to apply. -/
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

/-- A node's dropped set only grows, whatever the step, the hub going back included. -/
theorem sexec_node_drop_mono {N : Nat} {s t : SEState} {a : SAction} (hok : SEOK s)
    (h : sexecStep N s a = .ok t) {n x : Nat} (hx : x ∈ s.nodeDF n) : x ∈ t.nodeDF n := by
  rcases sexec_sound hok h with h' | e
  · exact nodeD_grows h' (n := n) (x := x) hx
  · have : (sabs t).nodeD n x := by rw [e]; exact hx
    exact this

/-- The ordered records, pruning boundary and all participants' dropped sets admit one common
cut for every executable run without rollback. This does not assume that the nodes' record
lists agree or that obsolete announcements have stopped arriving. -/
theorem sexec_record_and_drop_sets_stabilize (N B : Nat) (run : Nat → SEState)
    (actions : Nat → SAction) (hok : SEOK (run 0))
    (hs : ∀ i, sexecStep N (run i) (actions i) = .ok (run (i + 1)))
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
    | succ i ih => exact sexec_ok ih (hs i)
  exact record_and_drop_sets_stabilize N B run
    (fun i => (sexec_record_control (hs i) (hnr i)).1)
    (fun i => (sexec_record_control (hs i) (hnr i)).2)
    (fun i => (hi i).pruned)
    (fun i _ _ _ hx => sexec_node_drop_mono (hi i) (hs i) hx) hhub hnode

end Musubi.Exec

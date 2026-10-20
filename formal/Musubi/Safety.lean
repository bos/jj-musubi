/-
The safety properties of `protocol.md`, stated over every reachable state of the full
asynchronous model, and the no-feedback property.
-/
import Musubi.PreserveSync

namespace Musubi

variable {N : Nat}

/-! ## HubClosed -/

/-- **HubClosed**: `closure(head) ⊆ ops ∪ objects`. -/
theorem hubClosed {s : State} (h : Reachable N s) :
    ∀ y, Anc s.U.par y s.hub.head → s.hub.ops y ∧ ∀ o ∈ s.U.objs y, s.hub.objs o :=
  (inv_reachable h).hubClosed

/-! ## HubMonotone -/

/-- **HubMonotone**: on every step, the old hub head is in `anc*` of the new hub head. -/
theorem hubMonotone {s s' : State} (h : Reachable N s) (hs : Step N s s') :
    Anc s'.U.par s.hub.head s'.hub.head := by
  have hI := inv_reachable h
  rcases hs with hs | hs
  · cases hs <;> exact Anc.refl
  · cases hs with
    | casAccept n e d hm hne he ha hc => exact he ▸ ha
    | _ => exact Anc.refl

/-- The ghost history only grows: entries up to the old `seq` are unchanged, `seq` never
decreases, and the newest entry is the current head. -/
theorem histStable {s s' : State} (h : Reachable N s) (hs : Step N s s') :
    s.hub.seq ≤ s'.hub.seq ∧ (∀ i, i ≤ s.hub.seq → s'.hub.hist i = s.hub.hist i) ∧
      s'.hub.hist s'.hub.seq = s'.hub.head := by
  have hI' := inv_step (inv_reachable h) hs
  refine ⟨?_, ?_, hI'.histHead⟩
  · rcases hs with hs | hs
    · cases hs <;> exact Nat.le_refl _
    · cases hs with
      | casAccept => exact Nat.le_succ _
      | _ => exact Nat.le_refl _
  · intro i hi
    rcases hs with hs | hs
    · cases hs <;> rfl
    · cases hs with
      | casAccept => exact upd_ne _ _ (by omega)
      | _ => rfl

/-- Consequence of HubMonotone: an operation that is ever in `anc*(head)` stays there. -/
theorem acceptedStays {s s' : State} (h : Reachable N s) (hs : Step N s s') {x : Nat}
    (hx : Anc s.U.par x s.hub.head) : Anc s'.U.par x s'.hub.head := by
  have hI := inv_reachable h
  have hm := hubMonotone h hs
  rcases hs with hs | hs
  · cases hs with
    | userOp n p O hn hp =>
      have hLlt : ∀ q ∈ [p], q < s.U.next := by
        intro q hq; simp at hq; subst hq; exact hI.lLt n q hp
      exact (anc_upd_iff hI.parLt hLlt hI.headLt).2 hx
    | merge n L O hn hL h2 =>
      have hLlt : ∀ q ∈ L, q < s.U.next := fun q hq => hI.headsLt ((hL q).1 hq)
      exact (anc_upd_iff hI.parLt hLlt hI.headLt).2 hx
  · have hU : s'.U = s.U := by cases hs <;> rfl
    rw [hU] at hm ⊢
    exact hx.trans hm

/-! ## NodeClosed -/

/-- **NodeClosed**: `local` is closed under parents, its operations' objects are present,
`heads ⊆ local`, and `heads` is a (nonempty) antichain. -/
theorem nodeClosed {s : State} (h : Reachable N s) (n : Nat) :
    (∀ x p, (s.node n).lops x → p ∈ s.U.par x → (s.node n).lops p) ∧
    (∀ x o, (s.node n).lops x → o ∈ s.U.objs x → (s.node n).lobj o) ∧
    (∀ x, (s.node n).heads x → (s.node n).lops x) ∧
    (∀ x y, (s.node n).heads x → (s.node n).heads y → Anc s.U.par x y → x = y) ∧
    (∃ x, (s.node n).heads x) :=
  have hI := inv_reachable h
  ⟨hI.lParents n, hI.lObjs n, hI.headsLocal n, hI.headsAnti n, hI.headsNonempty n⟩

/-! ## KnownIsHubHistory -/

/-- **KnownIsHubHistory**: `known.head` is the head the hub accepted at `known.seq`.
(`hist` is the ghost history of accepted heads; see `histStable` and `hubHistory`.) -/
theorem knownIsHubHistory {s : State} (h : Reachable N s) (n : Nat) :
    (s.node n).known.1 ≤ s.hub.seq ∧ s.hub.hist (s.node n).known.1 = (s.node n).known.2 :=
  (inv_reachable h).known n

/-- The ghost history is a chain of strictly increasing heads starting at the root. -/
theorem hubHistory {s : State} (h : Reachable N s) :
    s.hub.hist 0 = root ∧ s.hub.hist s.hub.seq = s.hub.head ∧
    ∀ i, i < s.hub.seq →
      Anc s.U.par (s.hub.hist i) (s.hub.hist (i + 1)) ∧ s.hub.hist i ≠ s.hub.hist (i + 1) :=
  have hI := inv_reachable h
  ⟨hI.hist0, hI.histHead, hI.histStep⟩

/-- Every head-carrying message in the network (a `Head`, `Accepted`, or `Rejected` reply, or
a notification) carries a true `(seq, head)` pair from the hub's history. -/
theorem headMsgsTruthful {s : State} (h : Reachable N s) {n : Nat} {k : HeadKind}
    {sq hd : Nat} (hm : s.net (.head n k sq hd)) : sq ≤ s.hub.seq ∧ s.hub.hist sq = hd :=
  (inv_reachable h).msgs _ hm

/-! ## Locality -/

/-- **Locality**: every operation on node `n` was created by `n` or is accepted. -/
theorem locality {s : State} (h : Reachable N s) {n x : Nat} (hx : (s.node n).lops x) :
    s.U.creator x = some n ∨ Anc s.U.par x s.hub.head :=
  (inv_reachable h).locality n x hx

/-! ## MergeOwnership -/

/-- **MergeOwnership**, at the moment of the merge: whenever `Merge` is enabled on node `n`
(the list `L` enumerates its `≥ 2` heads), one of the merge's parents was created by `n` and
is not accepted by the hub. -/
theorem mergeOwnership {s : State} (h : Reachable N s) {n : Nat} {L : List Nat}
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b) :
    ∃ p ∈ L, s.U.creator p = some n ∧ ¬ Anc s.U.par p s.hub.head := by
  have hI := inv_reachable h
  obtain ⟨a, b, ha, hb, hab⟩ := h2
  have key : ∀ p, p ∈ L → ¬ Anc s.U.par p s.hub.head →
      ∃ p ∈ L, s.U.creator p = some n ∧ ¬ Anc s.U.par p s.hub.head :=
    fun p hp hna => ⟨p, hp, hI.ownOfUnacc (hI.headsLocal n p ((hL p).1 hp)) hna, hna⟩
  by_cases hA : Anc s.U.par a s.hub.head
  · by_cases hB : Anc s.U.par b s.hub.head
    · exact absurd (hI.accHeads n a b ((hL a).1 ha) ((hL b).1 hb) hA hB) hab
    · exact key b hb hB
  · exact key a ha hA

/-- **MergeOwnership**, as a persistent ghost record: every merge `m` ever created has a
parent with the same creator that was not accepted when `m` was created (`hist (birth m)` is
the hub head at that moment). -/
theorem mergeOwnershipGhost {s : State} (h : Reachable N s) {m : Nat} (hm : m < s.U.next)
    (hmg : s.U.isMerge m = true) :
    ∃ p ∈ s.U.par m, s.U.creator p = s.U.creator m ∧
      ¬ Anc s.U.par p (s.hub.hist (s.U.birth m)) :=
  (inv_reachable h).mergeOwn m hm hmg

/-- The ghost `birth` really records the hub head at creation: an environment step that
creates `m` sets `birth m` to the current `seq`. -/
theorem birth_at_creation {s s' : State} (hs : EnvStep N s s') :
    s'.U.birth s.U.next = s.hub.seq ∧ s'.U.next = s.U.next + 1 ∧ s'.hub = s.hub := by
  cases hs <;> exact ⟨upd_same _ _ _, rfl, rfl⟩

/-- Hence two different nodes never create merges with the same set of parents. -/
theorem noDuplicateMerge {s : State} (h : Reachable N s) {m1 m2 : Nat}
    (h1 : m1 < s.U.next) (h2 : m2 < s.U.next)
    (g1 : s.U.isMerge m1 = true) (g2 : s.U.isMerge m2 = true)
    (hc : s.U.creator m1 ≠ s.U.creator m2) :
    ¬ ∀ x, x ∈ s.U.par m1 ↔ x ∈ s.U.par m2 := by
  have hI := inv_reachable h
  intro hpar
  -- the merge created later has an own unaccepted parent that the earlier one had accepted
  have later : ∀ a b, a < s.U.next → b < s.U.next → s.U.isMerge a = true →
      s.U.isMerge b = true → s.U.creator a ≠ s.U.creator b →
      (∀ x, x ∈ s.U.par b → x ∈ s.U.par a) → a ≤ b → False := by
    intro a b ha hb ga gb hcab hba hab
    obtain ⟨q, hq, hcq, hna⟩ := hI.mergeOwn b hb gb
    have hqa := hba q hq
    have hcq' : s.U.creator q ≠ s.U.creator a := by rw [hcq]; exact Ne.symm hcab
    have hacc := hI.mergeForeign a ha ga q hqa hcq'
    have hbirth : s.U.birth a ≤ s.U.birth b := by
      rcases Nat.lt_or_eq_of_le hab with hlt | heq
      · exact hI.birthMono a b hlt hb
      · rw [heq]; exact Nat.le_refl _
    exact hna (hacc.trans (hI.chain hbirth (hI.birthLe b hb)))
  rcases Nat.le_total m1 m2 with h12 | h21
  · exact later m1 m2 h1 h2 g1 g2 hc (fun x hx => (hpar x).2 hx) h12
  · exact later m2 m1 h2 h1 g2 g1 (Ne.symm hc) (fun x hx => (hpar x).1 hx) h21

/-- Stronger form: a merge never repeats the parent set of any earlier merge, whoever
created it (so no merge, and none of the commits it rebases, is ever performed twice). -/
theorem mergeNeverRepeats {s : State} (h : Reachable N s) {n : Nat} {L : List Nat}
    (hL : ∀ x, x ∈ L ↔ (s.node n).heads x) (h2 : ∃ a b, a ∈ L ∧ b ∈ L ∧ a ≠ b)
    {m : Nat} (hm : m < s.U.next) (hmg : s.U.isMerge m = true) :
    ¬ ∀ x, x ∈ s.U.par m ↔ x ∈ L := by
  have hI := inv_reachable h
  intro hpar
  by_cases hc : s.U.creator m = some n
  · -- an earlier merge by `n` is below one of `n`'s heads, which is one of its own parents
    obtain ⟨g, hg, hA⟩ := hI.ownInHeads n m hm hc
    have hgm : g ∈ s.U.par m := (hpar g).2 ((hL g).2 hg)
    have h1 := hI.parLt m g hgm
    have h2 := hA.le hI.parLt
    omega
  · -- the new merge's own unaccepted parent would have been accepted already
    obtain ⟨p, hpL, hcp, hna⟩ := mergeOwnership h hL h2
    have hpm : p ∈ s.U.par m := (hpar p).2 hpL
    have hcp' : s.U.creator p ≠ s.U.creator m := by rw [hcp]; exact fun e => hc e.symm
    exact hna ((hI.mergeForeign m hm hmg p hpm hcp').trans (hI.histAnc (hI.birthLe m hm)))

/-! ## Policy claims -/

/-- `protocol.md`, policy step 3: after `Advance`, `|heads| ≥ 2` or `heads = {known.head}`. -/
theorem advance_result {s : State} (h : Reachable N s) {n : Nat}
    (hna : ¬ ∃ g, (s.node n).heads g ∧ Anc s.U.par (s.node n).known.2 g) :
    (∀ y, ((s.advance n).node n).heads y ↔ y = (s.node n).known.2) ∨
      ∃ a b, ((s.advance n).node n).heads a ∧ ((s.advance n).node n).heads b ∧ a ≠ b := by
  have hI := inv_reachable h
  have H := fun y => advance_heads_iff (y := y) hI hna
  have hh : ((s.advance n).node n).heads =
      maxSet s.U.par (fun y => (s.node n).heads y ∨ y = (s.node n).known.2) := by
    simp [State.advance]
  rw [hh]
  by_cases hex : ∃ g, (s.node n).heads g ∧ ¬ Anc s.U.par g (s.node n).known.2
  · obtain ⟨g, hg, hng⟩ := hex
    refine Or.inr ⟨g, _, (H g).2 (Or.inr ⟨hg, hng⟩), (H _).2 (Or.inl rfl), ?_⟩
    rintro rfl; exact hng Anc.refl
  · left
    intro y
    rw [H y]
    constructor
    · rintro (h | ⟨hy, hny⟩)
      · exact h
      · exact absurd ⟨y, hy, hny⟩ hex
    · exact Or.inl

/-! ## No feedback -/

/-- **No feedback**: sync actions (including realization, hub request handling, and crashes)
never create canonical operations; the universe of operations is unchanged. -/
theorem noFeedback {s s' : State} (hs : SyncStep N s s') : s'.U = s.U := by
  cases hs <;> rfl

/-- Only environment actions create operations, and each creates exactly one. -/
theorem envCreatesOne {s s' : State} (hs : EnvStep N s s') : s'.U.next = s.U.next + 1 := by
  cases hs <;> rfl

end Musubi

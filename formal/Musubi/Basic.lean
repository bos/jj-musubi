/-
Basic utilities: sets as predicates, point updates of functions, and finite counting
over `Nat` ranges (used by the liveness measure), termination of runs, and traces that stop
changing: nonincreasing ones of naturals, and ones of lexicographic ranks.
-/

namespace Musubi

/-- What a node knows of the hub: the sequence number and the head accepted at it. -/
@[ext] structure Known where
  seq : Nat
  head : Nat
  deriving DecidableEq, Repr

/-- Sets of identifiers (operation ids, object ids) are predicates. -/
abbrev OSet := Nat → Prop

/-- Point update of a function on `Nat`. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (a : α) : Nat → α :=
  fun j => if j = i then a else f j

@[simp] theorem upd_same {α : Type} (f : Nat → α) (i : Nat) (a : α) : upd f i a i = a := by
  simp [upd]

@[simp] theorem upd_ne {α : Type} (f : Nat → α) {i j : Nat} (a : α) (h : j ≠ i) :
    upd f i a j = f j := by
  simp [upd, h]

theorem upd_lt {α : Type} (f : Nat → α) {i j : Nat} (a : α) (h : j < i) :
    upd f i a j = f j := upd_ne f a (Nat.ne_of_lt h)

/-! ## Indicators -/

noncomputable def ind (P : Prop) : Nat := @ite _ P (Classical.propDecidable P) 1 0

theorem ind_pos {P : Prop} (h : P) : ind P = 1 := by
  unfold ind; split
  · rfl
  · contradiction

theorem ind_neg {P : Prop} (h : ¬ P) : ind P = 0 := by
  unfold ind; split
  · contradiction
  · rfl

theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases hp : P
  · rw [ind_pos hp, ind_pos (h hp)]; exact Nat.le_refl _
  · rw [ind_neg hp]; exact Nat.zero_le _

theorem ind_congr {P Q : Prop} (h : P ↔ Q) : ind P = ind Q := by
  rw [propext h]

/-! ## Counting -/

open Classical in
/-- `cnt B P` is the number of `x < B` satisfying `P`. -/
noncomputable def cnt : Nat → (Nat → Prop) → Nat
  | 0, _ => 0
  | B + 1, P => cnt B P + (if P B then 1 else 0)

theorem cnt_congr {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → (P x ↔ Q x)) :
    cnt B P = cnt B Q := by
  induction B with
  | zero => rfl
  | succ B ih =>
    simp only [cnt]
    rw [ih (fun x hx => h x (Nat.lt_succ_of_lt hx)), h B (Nat.lt_succ_self B)]

theorem cnt_le {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x) :
    cnt B Q ≤ cnt B P := by
  induction B with
  | zero => exact Nat.le_refl _
  | succ B ih =>
    simp only [cnt]
    have ih' := ih (fun x hx => h x (Nat.lt_succ_of_lt hx))
    have hB := h B (Nat.lt_succ_self B)
    grind only

theorem cnt_lt {B : Nat} {P Q : Nat → Prop} (h : ∀ x, x < B → Q x → P x)
    (w : ∃ x, x < B ∧ P x ∧ ¬ Q x) : cnt B Q < cnt B P := by
  induction B with
  | zero => obtain ⟨x, hx, -⟩ := w; omega
  | succ B ih =>
    simp only [cnt]
    have hle := cnt_le (B := B) (P := P) (Q := Q) (fun x hx => h x (Nat.lt_succ_of_lt hx))
    obtain ⟨x, hx, hPx, hQx⟩ := w
    by_cases hxB : x = B
    · subst hxB
      simp [hPx, hQx]; omega
    · have hlt : x < B := by omega
      have ih' := ih (fun y hy => h y (Nat.lt_succ_of_lt hy)) ⟨x, hlt, hPx, hQx⟩
      have hB := h B (Nat.lt_succ_self B)
      grind only

/-! ## Sums over `n < N` -/

/-- `sumN N f = f 0 + ... + f (N-1)`. -/
def sumN : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | N + 1, f => sumN N f + f N

theorem sumN_congr {N : Nat} {f g : Nat → Nat} (h : ∀ n, n < N → f n = g n) :
    sumN N f = sumN N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    simp only [sumN]
    rw [ih (fun n hn => h n (Nat.lt_succ_of_lt hn)), h N (Nat.lt_succ_self N)]

theorem sumN_lt {N : Nat} {f g : Nat → Nat} {i : Nat} (hi : i < N)
    (hlt : f i < g i) (heq : ∀ n, n < N → n ≠ i → f n = g n) : sumN N f < sumN N g := by
  induction N with
  | zero => omega
  | succ N ih =>
    simp only [sumN]
    by_cases h : i = N
    · subst h
      have := sumN_congr (N := i) (f := f) (g := g)
        (fun n hn => heq n (Nat.lt_succ_of_lt hn) (Nat.ne_of_lt hn))
      omega
    · have := ih (by omega) (fun n hn hne => heq n (Nat.lt_succ_of_lt hn) hne)
      have := heq N (Nat.lt_succ_self N) (Ne.symm h)
      omega

/-! ## Runs -/

/-- An accessible state cannot start an infinite descending chain. -/
theorem acc_no_infinite_chain {α : Sort u} {r : α → α → Prop} {a : α} (ha : Acc r a) :
    ∀ f : Nat → α, f 0 = a → ¬ ∀ i, r (f (i + 1)) (f i) := by
  induction ha with
  | intro a _ ih =>
    intro f hf hall
    exact ih (f 1) (hf ▸ hall 0) (fun i => f (i + 1)) rfl (fun i => hall (i + 1))

/-- A well-founded step relation on an invariant admits no infinite run from that invariant.
The relation is reversed in `wf` because each forward step descends. -/
theorem no_infinite_run_of_invariant {α : Sort u} {step : α → α → Prop} {inv : α → Prop}
    (wf : WellFounded (fun t s => inv s ∧ step s t))
    (preserve : ∀ {s t}, inv s → step s t → inv t) {s : α} (hs : inv s) :
    ¬ ∃ f : Nat → α, f 0 = s ∧ ∀ i, step (f i) (f (i + 1)) := by
  rintro ⟨f, hf0, hf⟩
  have hinv : ∀ i, inv (f i) := by
    intro i
    induction i with
    | zero => exact hf0 ▸ hs
    | succ i ih => exact preserve ih (hf i)
  exact acc_no_infinite_chain (wf.apply s) f hf0 (fun i => ⟨hinv i, hf i⟩)

/-- Progress and quiescence characterize terminal states. -/
theorem terminal_iff_of_progress {α : Sort u} {step : α → α → Prop} {s : α} {done : Prop}
    (progress : ¬ done → ∃ t, step s t) (quiescent : done → ∀ t, ¬ step s t) :
    (∀ t, ¬ step s t) ↔ done := by
  constructor
  · intro ht
    refine Classical.byContradiction fun hd => ?_
    obtain ⟨t, hst⟩ := progress hd
    exact ht t hst
  · exact quiescent

/-- A run of zero or more steps of `step`. -/
inductive Steps {α : Sort u} (step : α → α → Prop) : α → α → Prop
  | refl (s : α) : Steps step s s
  | tail {s t u : α} : Steps step s t → step t u → Steps step s u

/-- A run can also start with its first step. -/
theorem Steps.head {α : Sort u} {step : α → α → Prop} {s t u : α} (h1 : step s t)
    (h2 : Steps step t u) : Steps step s u := by
  induction h2 with
  | refl => exact .tail (.refl _) h1
  | tail _ hst ih => exact .tail ih hst

/-- An invariant that every step preserves holds all along a run. -/
theorem Steps.invariant {α : Sort u} {step : α → α → Prop} {inv : α → Prop}
    (preserve : ∀ {s t}, inv s → step s t → inv t) {s t : α} (hs : inv s)
    (h : Steps step s t) : inv t := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => exact preserve ih hst

/-- A well-founded step relation on an invariant, with progress at every state of the
invariant that is not `done`, reaches `done` from every state of the invariant. -/
theorem eventually_done_of_progress {α : Sort u} {step : α → α → Prop} {inv done : α → Prop}
    (wf : WellFounded (fun t s => inv s ∧ step s t))
    (preserve : ∀ {s t}, inv s → step s t → inv t)
    (progress : ∀ {s}, inv s → ¬ done s → ∃ t, step s t) {s : α} (hs : inv s) :
    ∃ t, Steps step s t ∧ done t := by
  refine WellFounded.induction (C := fun s => inv s → ∃ t, Steps step s t ∧ done t) wf s
    (fun s ih hs => ?_) hs
  by_cases hd : done s
  · exact ⟨s, .refl s, hd⟩
  · obtain ⟨t, hst⟩ := progress hs hd
    obtain ⟨u, hu, hdu⟩ := ih t ⟨hs, hst⟩ (preserve hs hst)
    exact ⟨u, .head hst hu, hdu⟩

/-- On an invariant that has progress, a run that cannot be extended ends in a `done` state. -/
theorem done_of_maximal_run {α : Sort u} {step : α → α → Prop} {inv done : α → Prop}
    (preserve : ∀ {s t}, inv s → step s t → inv t)
    (progress : ∀ {s}, inv s → ¬ done s → ∃ t, step s t) {s s' : α} (hs : inv s)
    (hr : Steps step s s') (hmax : ∀ t, ¬ step s' t) : done s' :=
  Classical.byContradiction fun hd =>
    let ⟨t, ht⟩ := progress (Steps.invariant (step := step) (inv := inv) preserve hs hr) hd
    hmax t ht

/-! ## Minimal elements -/

theorem exists_min (P : Nat → Prop) {a : Nat} (ha : P a) :
    ∃ x, P x ∧ ∀ y, y < x → ¬ P y := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases h : ∃ y, y < a ∧ P y
    · obtain ⟨y, hy, hPy⟩ := h
      exact ih y hy hPy
    · exact ⟨a, ha, fun y hy hPy => h ⟨y, hy, hPy⟩⟩

/-- The first index satisfying `P`, if any does. -/
theorem exists_first {P : Nat → Prop} (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, m < n → ¬ P m :=
  let ⟨_, ha⟩ := h
  exists_min P ha

/-- A predicate that holds somewhere, and only at numbers up to `x`, holds at a largest one. -/
theorem exists_max_le {Q : Nat → Prop} {x a : Nat} (ha : Q a) (hle : ∀ m, Q m → m ≤ x) :
    ∃ m, Q m ∧ ∀ m', Q m' → m' ≤ m := by
  have hP : x - a ≤ x ∧ Q (x - (x - a)) :=
    ⟨Nat.sub_le x a, by rw [Nat.sub_sub_self (hle a ha)]; exact ha⟩
  obtain ⟨d, ⟨hd, hQd⟩, hmin⟩ := exists_min (fun d => d ≤ x ∧ Q (x - d)) hP
  refine ⟨x - d, hQd, fun m' hm' => ?_⟩
  have hm'x := hle m' hm'
  apply Classical.byContradiction
  intro hgt
  have hlt : x - m' < d := by omega
  exact hmin (x - m') hlt ⟨Nat.sub_le x m', by rw [Nat.sub_sub_self hm'x]; exact hm'⟩

/-- Finitely many indices each have a cut after which `P` holds; one cut serves them all. -/
theorem finite_common_cut (N : Nat) (P : Nat → Nat → Prop)
    (he : ∀ n, n < N → ∃ k, ∀ i, k ≤ i → P n i) :
    ∃ k, ∀ i, k ≤ i → ∀ n, n < N → P n i := by
  induction N with
  | zero => exact ⟨0, fun _ _ _ hn => by omega⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih (fun n hn => he n (by omega))
    obtain ⟨j, hj⟩ := he N (by omega)
    refine ⟨max k j, fun i hi n hn => ?_⟩
    by_cases heq : n = N
    · subst n; exact hj i (by omega)
    · exact hk i (by omega) n (by omega)

/-! ## Traces that stop changing -/

/-- A nonincreasing trace of naturals is eventually constant, at its least value. No bound on
the time between changes is needed. -/
theorem nat_trace_stabilizes (f : Nat → Nat) (hf : ∀ i, f (i + 1) ≤ f i) :
    ∃ k, ∀ i, k ≤ i → f i = f k := by
  obtain ⟨v, ⟨k, rfl⟩, hmin⟩ := exists_min (fun v => ∃ k, f k = v) ⟨0, rfl⟩
  refine ⟨k, fun i hi => ?_⟩
  have hle : f i ≤ f k := by
    induction hi with
    | refl => exact Nat.le_refl _
    | step _ ih => exact Nat.le_trans (hf _) ih
  have hnot : ¬ f i < f k := fun h => hmin (f i) h ⟨i, rfl⟩
  omega

/-- Strictly below, first difference first, for lists of one length. -/
def LexLt : List Nat → List Nat → Prop
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLt as bs)
  | _, _ => False

def LexLe (x y : List Nat) : Prop := LexLt x y ∨ x = y

theorem lexLt_irrefl : ∀ x : List Nat, ¬ LexLt x x
  | [] => fun h => False.elim h
  | _ :: as => fun h => by
    rcases h with h | ⟨_, h⟩
    · exact Nat.lt_irrefl _ h
    · exact lexLt_irrefl as h

theorem lt_hd {a b : Nat} {as bs : List Nat} (h : a < b) : LexLt (a :: as) (b :: bs) :=
  Or.inl h

theorem lt_cons {a b : Nat} {as bs : List Nat} (h : a ≤ b) (t : a = b → LexLt as bs) :
    LexLt (a :: as) (b :: bs) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, t h⟩

theorem le_cons {a b : Nat} {as bs : List Nat} (h : a ≤ b) (t : a = b → LexLe as bs) :
    LexLe (a :: as) (b :: bs) := by
  rcases Nat.lt_or_eq_of_le h with h | h
  · exact Or.inl (Or.inl h)
  · rcases t h with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · subst h; subst h'; exact Or.inr rfl

theorem LexLt.le {x y : List Nat} (h : LexLt x y) : LexLe x y := Or.inl h

theorem lexLe_head {a b : Nat} {as bs : List Nat} (h : LexLe (a :: as) (b :: bs)) : a ≤ b := by
  rcases h with h | h
  · rcases h with h | ⟨h, -⟩
    · exact Nat.le_of_lt h
    · exact Nat.le_of_eq h
  · injection h with h1; exact Nat.le_of_eq h1

theorem lexLe_tail {a : Nat} {as bs : List Nat} (h : LexLe (a :: as) (a :: bs)) :
    LexLe as bs := by
  rcases h with h | h
  · rcases h with h | ⟨-, h⟩
    · exact absurd h (Nat.lt_irrefl _)
    · exact Or.inl h
  · injection h with _ h2; exact Or.inr h2

/-- A run of ranks of one length that never rises stops changing. -/
theorem lex_stabilizes : ∀ (L : Nat) (f : Nat → List Nat), (∀ i, (f i).length = L) →
    (∀ i, LexLe (f (i + 1)) (f i)) → ∃ k, ∀ i, k ≤ i → f i = f k := by
  intro L
  induction L with
  | zero =>
    intro f hl _
    exact ⟨0, fun i _ => by
      rw [List.eq_nil_of_length_eq_zero (hl i), List.eq_nil_of_length_eq_zero (hl 0)]⟩
  | succ L ih =>
    intro f hl hf
    have hcons : ∀ i, f i = (f i).headD 0 :: (f i).tail := by
      intro i
      have := hl i
      revert this
      cases f i with
      | nil => intro h; simp at h
      | cons a as => intro _; rfl
    have hhd : ∀ i, (f (i + 1)).headD 0 ≤ (f i).headD 0 := by
      intro i
      have := hf i
      rw [hcons (i + 1), hcons i] at this
      exact lexLe_head this
    obtain ⟨k1, hk1⟩ := nat_trace_stabilizes (fun i => (f i).headD 0) hhd
    have hh : ∀ i, k1 ≤ i → (f i).headD 0 = (f k1).headD 0 := fun i hi => hk1 i hi
    have htl : ∀ j, LexLe (f (k1 + j + 1)).tail (f (k1 + j)).tail := by
      intro j
      have := hf (k1 + j)
      rw [hcons (k1 + j + 1), hcons (k1 + j), hh (k1 + j + 1) (by omega),
        hh (k1 + j) (by omega)] at this
      exact lexLe_tail this
    obtain ⟨k2, hk2⟩ := ih (fun j => (f (k1 + j)).tail)
      (fun j => by simp [hl]) htl
    refine ⟨k1 + k2, fun i hi => ?_⟩
    rw [hcons i, hcons (k1 + k2), hh i (by omega), hh (k1 + k2) (by omega)]
    have e : (f (k1 + (i - k1))).tail = (f (k1 + k2)).tail := hk2 (i - k1) (by omega)
    rw [show k1 + (i - k1) = i by omega] at e
    rw [e]

end Musubi

/-
Contracting operations out of a history, as a replicated `jj op abandon` does
(docs/internals/design.md, "Abandoning operations").

A history is a parent function `par` whose parents have smaller ids (`ParLt`), and a set `D`
of operations to drop. Each surviving operation's parents become the expansion of its parent
list: a dropped parent is replaced, in place, by the expansion of its own parents, and then
duplicates are removed, keeping each one's first occurrence (`cpar`). An operation's id hashes
its immutable content and its parents' ids, so a survivor whose parents change gets a new id,
and so does every operation after it. Ids are modeled as terms (`IdTerm`, with content of any
type), which makes the hash injective: `cid content par D x` is the id `x` has once `D` is
dropped.

- `cpar_union`, `cid_union`: dropping `D₁` and then, from what is left, `D₂`, gives the same
  parents and ids as dropping `D₁ ∪ D₂` at once. So abandons compose in any order and grouping
  (`cid_comm`): two machines that drop sets concurrently, or a machine that drops a set again
  on a hub that lost it, reach the same ids.
- `cid_eq`, with injective immutable content: a survivor's id under one dropped set equals one
  under another only if they are the same operation and the two sets agree on its proper
  ancestors. `idTerm_cpar_eq` proves it for content of any type, which may depend on the set.
- `superseded_ne`: hence, once a machine's dropped set has grown to include an operation or
  one of its ancestors, no id the operation had before equals any id the machine holds.
- `anc_cpar_iff`: among survivors, contraction keeps ancestry exactly.

jj's own `op_walk::reparent_range` doesn't compose: it moves every operation outside the
abandoned range whose parent lies anywhere in `::abandon_heads` onto the range's root, which
reparents concurrent branches as well, and two such abandons give different ids in different
orders. So the canonical history uses contraction, whatever jj did locally.
-/
import Musubi.Dag

namespace Musubi.Contract

/-! ## Removing duplicates -/

/-- The elements of `l` not in `seen`, each at its first occurrence. -/
def ddAux : List Nat → List Nat → List Nat
  | _, [] => []
  | seen, a :: l => if a ∈ seen then ddAux seen l else a :: ddAux (a :: seen) l

/-- `l` without duplicates, keeping each element's first occurrence. -/
def dd (l : List Nat) : List Nat := ddAux [] l

theorem ddAux_congr {s₁ s₂ : List Nat} (h : ∀ a, a ∈ s₁ ↔ a ∈ s₂) (l : List Nat) :
    ddAux s₁ l = ddAux s₂ l := by
  induction l generalizing s₁ s₂ with
  | nil => rfl
  | cons a l ih =>
    simp only [ddAux]
    by_cases ha : a ∈ s₁
    · have : a ∈ s₂ := (h a).1 ha
      simp [ha, this, ih h]
    · have : a ∉ s₂ := fun h₂ => ha ((h a).2 h₂)
      simp only [ha, this, ite_false]
      congr 1
      exact ih (fun b => by simp [h b])

theorem mem_ddAux {s l : List Nat} {a : Nat} : a ∈ ddAux s l ↔ a ∈ l ∧ a ∉ s := by
  induction l generalizing s with
  | nil => simp [ddAux]
  | cons b l ih =>
    simp only [ddAux]
    by_cases hb : b ∈ s
    · simp only [hb, ite_true, ih, List.mem_cons]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact absurd hb h2
        · exact ⟨h1, h2⟩
    · simp only [hb, ite_false, List.mem_cons, ih]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · subst h; exact ⟨Or.inl rfl, hb⟩
        · exact ⟨Or.inr h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact Or.inl h1
        · by_cases hab : a = b
          · exact Or.inl hab
          · exact Or.inr ⟨h1, fun h => h.elim hab h2⟩

theorem mem_dd {l : List Nat} {a : Nat} : a ∈ dd l ↔ a ∈ l := by
  simp [dd, mem_ddAux]

theorem ddAux_append (s l k : List Nat) :
    ddAux s (l ++ k) = ddAux s l ++ ddAux (l ++ s) k := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    simp only [List.cons_append, ddAux]
    by_cases ha : a ∈ s
    · simp only [ha, ite_true, ih]
      congr 1
      exact ddAux_congr (fun b => by simp only [List.mem_append, List.mem_cons]; grind) k
    · simp only [ha, ite_false, ih, List.cons_append]
      congr 2
      exact ddAux_congr (fun b => by simp only [List.mem_append, List.mem_cons]; grind) k

theorem ddAux_seen {s l : List Nat} (h : ∀ a ∈ l, a ∈ s) : ddAux s l = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [ddAux, h a (List.mem_cons_self), ite_true]
    exact ih (fun b hb => h b (List.mem_cons_of_mem a hb))

/-- Where no element repeats and none is already seen, nothing is removed. -/
theorem ddAux_eq_of_nodup {s l : List Nat} (hl : l.Nodup)
    (hs : ∀ a ∈ l, a ∉ s) : ddAux s l = l := by
  induction l generalizing s with
  | nil => rfl
  | cons a l ih =>
    have ha : a ∉ s := hs a List.mem_cons_self
    simp only [ddAux, ha, ite_false, List.cons.injEq, true_and]
    obtain ⟨hal, hl'⟩ := List.nodup_cons.1 hl
    apply ih hl'
    intro b hb hbs
    rcases List.mem_cons.1 hbs with rfl | hbs
    · exact hal hb
    · exact hs b (List.mem_cons_of_mem a hb) hbs

theorem ddAux_ddAux (s t l : List Nat) : ddAux s (ddAux t l) = ddAux (s ++ t) l := by
  induction l generalizing s t with
  | nil => rfl
  | cons a l ih =>
    simp only [ddAux]
    by_cases hat : a ∈ t
    · have : a ∈ s ++ t := List.mem_append.2 (Or.inr hat)
      simp only [hat, this, ite_true, ih]
    · simp only [hat, ite_false, ddAux]
      by_cases has : a ∈ s
      · have : a ∈ s ++ t := List.mem_append.2 (Or.inl has)
        simp only [has, this, ite_true, ih]
        exact ddAux_congr (fun b => by simp only [List.mem_append, List.mem_cons]; grind) l
      · have : a ∉ s ++ t := by simp [has, hat]
        simp only [has, this, ite_false, ih]
        congr 1
        exact ddAux_congr (fun b => by simp only [List.mem_append, List.mem_cons]; grind) l

/-! ## Lists equal once duplicates are removed -/

/-- `l` and `m` are equal once duplicates are removed, whatever is seen before them. -/
def Eqv (l m : List Nat) : Prop := ∀ s, ddAux s l = ddAux s m

namespace Eqv

theorem refl (l : List Nat) : Eqv l l := fun _ => rfl

theorem symm {l m : List Nat} (h : Eqv l m) : Eqv m l := fun s => (h s).symm

theorem trans {l m k : List Nat} (h₁ : Eqv l m) (h₂ : Eqv m k) : Eqv l k :=
  fun s => (h₁ s).trans (h₂ s)

theorem mem {l m : List Nat} (h : Eqv l m) {a : Nat} : a ∈ l ↔ a ∈ m := by
  have := h []
  constructor
  · intro ha
    have : a ∈ ddAux [] m := by rw [← this]; exact mem_ddAux.2 ⟨ha, by simp⟩
    exact (mem_ddAux.1 this).1
  · intro ha
    have : a ∈ ddAux [] l := by rw [this]; exact mem_ddAux.2 ⟨ha, by simp⟩
    exact (mem_ddAux.1 this).1

theorem append_left {l m : List Nat} (k : List Nat) (h : Eqv l m) : Eqv (k ++ l) (k ++ m) := by
  intro s
  rw [ddAux_append, ddAux_append, h]

theorem append_right {l m : List Nat} (k : List Nat) (h : Eqv l m) :
    Eqv (l ++ k) (m ++ k) := by
  intro s
  rw [ddAux_append, ddAux_append, h s]
  congr 1
  exact ddAux_congr (fun b => by simp [h.mem]) k

theorem append {l m l' m' : List Nat} (h : Eqv l m) (h' : Eqv l' m') :
    Eqv (l ++ l') (m ++ m') := (h.append_right l').trans (h'.append_left m)

theorem flatMap {l : List Nat} {f g : Nat → List Nat} (h : ∀ a ∈ l, Eqv (f a) (g a)) :
    Eqv (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => exact refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append
      (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem dd (l : List Nat) : Eqv (Contract.dd l) l := by
  intro s
  simp only [Contract.dd, ddAux_ddAux, List.append_nil]

end Eqv

/-- Mapping over a list with duplicates removed: what an element seen earlier adds is all seen
already. -/
theorem flatMap_ddAux (f : Nat → List Nat) (t l : List Nat) :
    Eqv (t.flatMap f ++ l.flatMap f) (t.flatMap f ++ (ddAux t l).flatMap f) := by
  induction l generalizing t with
  | nil => simp [ddAux]; exact Eqv.refl _
  | cons a l ih =>
    simp only [ddAux]
    by_cases hat : a ∈ t
    · simp only [hat, ite_true]
      refine Eqv.trans ?_ (ih t)
      intro s
      simp only [List.flatMap_cons]
      rw [ddAux_append, ddAux_append, ddAux_append]
      congr 1
      rw [ddAux_seen (s := t.flatMap f ++ s) (l := f a)]
      · rw [List.nil_append]
        exact ddAux_congr (fun b => by simp only [List.mem_append]; grind) _
      · intro b hb
        exact List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨a, hat, hb⟩))
    · simp only [hat, ite_false, List.flatMap_cons]
      have e₁ := ih (t ++ [a])
      have hc : ddAux (a :: t) l = ddAux (t ++ [a]) l :=
        ddAux_congr (fun b => by simp [or_comm]) l
      rw [hc]
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.append_assoc] at e₁
      exact e₁

theorem flatMap_dd (f : Nat → List Nat) (l : List Nat) :
    Eqv ((dd l).flatMap f) (l.flatMap f) := by
  have := flatMap_ddAux f [] l
  simp only [List.flatMap_nil, List.nil_append] at this
  exact this.symm

theorem flatMap_congr_mem {l : List Nat} {f g : Nat → List Nat} (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons, h a List.mem_cons_self,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-! ## Contraction -/

variable (par : Nat → List Nat) (D : Nat → Bool)

/-- The expansion of `p` with fuel: `[p]` if it survives, otherwise its parents' expansions. -/
def expF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, p => if D p then (par p).flatMap (expF f) else [p]

/-- The expansion of `p`: `[p]` if `p` survives, and otherwise what its parents expand to. -/
def exp (p : Nat) : List Nat := expF par D (p + 1) p

/-- The parents of `x` once `D` is dropped: its parent list expanded, without duplicates. -/
def cpar (x : Nat) : List Nat := dd ((par x).flatMap (exp par D))

variable {par D}

theorem expF_fuel (hlt : ParLt par) {f g p : Nat} (hf : p < f) (hg : p < g) :
    expF par D f p = expF par D g p := by
  induction f generalizing g p with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [expF]
      split
      · apply flatMap_congr_mem
        intro q hq
        have := hlt p q hq
        exact ih (by omega) (by omega)
      · rfl

theorem exp_eq (hlt : ParLt par) (p : Nat) :
    exp par D p = if D p then (par p).flatMap (exp par D) else [p] := by
  simp only [exp, expF]
  split
  · apply flatMap_congr_mem
    intro q hq
    have := hlt p q hq
    exact expF_fuel hlt (by omega) (by omega)
  · rfl

/-- What `p` expands to survives, and is `p` or one of its ancestors. -/
theorem mem_exp (hlt : ParLt par) {p q : Nat} (h : q ∈ exp par D p) :
    D q = false ∧ Anc par q p := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    rw [exp_eq hlt] at h
    split at h
    · obtain ⟨r, hr, hq⟩ := List.mem_flatMap.1 h
      obtain ⟨hD, hA⟩ := ih r (hlt p r hr) hq
      exact ⟨hD, Anc.step hr hA⟩
    · simp at h
      subst h
      rename_i hD
      exact ⟨by simpa using hD, Anc.refl⟩

/-- A survivor that is `p` or an ancestor of `p` is reached from what `p` expands to. -/
theorem exp_covers (hlt : ParLt par) {a p : Nat} (hA : Anc par a p) (ha : D a = false) :
    ∃ q ∈ exp par D p, Anc par a q := by
  induction hA with
  | refl => exact ⟨a, by rw [exp_eq hlt]; simp [ha], Anc.refl⟩
  | @step r x hr hA ih =>
    rw [exp_eq hlt]
    by_cases hx : D x
    · obtain ⟨q, hq, hAq⟩ := ih
      exact ⟨q, by simp only [hx, ite_true]; exact List.mem_flatMap.2 ⟨r, hr, hq⟩, hAq⟩
    · exact ⟨x, by simp [hx], Anc.step hr hA⟩

theorem mem_cpar (hlt : ParLt par) {x q : Nat} (h : q ∈ cpar par D x) :
    D q = false ∧ Anc par q x ∧ q ≠ x := by
  obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 (mem_dd.1 h)
  obtain ⟨hD, hA⟩ := mem_exp hlt hq
  have hlt' : q < x := Nat.lt_of_le_of_lt (hA.le hlt) (hlt x p hp)
  exact ⟨hD, Anc.step hp hA, Nat.ne_of_lt hlt'⟩

/-- A surviving proper ancestor of `x` is reached from `x`'s contracted parents. -/
theorem cpar_covers (hlt : ParLt par) {a x : Nat} (hA : Anc par a x) (hne : a ≠ x)
    (ha : D a = false) : ∃ q ∈ cpar par D x, Anc par a q := by
  cases hA with
  | refl => exact absurd rfl hne
  | @step p _ hp hA =>
    obtain ⟨q, hq, hAq⟩ := exp_covers hlt hA ha
    exact ⟨q, mem_dd.2 (List.mem_flatMap.2 ⟨p, hp, hq⟩), hAq⟩

theorem parLt_cpar (hlt : ParLt par) : ParLt (cpar par D) := by
  intro y q hq
  obtain ⟨-, hA, hne⟩ := mem_cpar hlt hq
  exact Anc.lt_of_ne hlt hA hne

/-- The whole contracted closure of a survivor contains only survivors. This includes its
head, unlike the fact that each contracted parent survives. -/
theorem anc_cpar_survives (hlt : ParLt par) {x y : Nat} (hx : D x = false)
    (ha : Anc (cpar par D) y x) : D y = false := by
  induction ha with
  | refl => exact hx
  | step hp _ ih => exact ih (mem_cpar hlt hp).1

/-- Among survivors, contraction keeps ancestry exactly. -/
theorem anc_cpar_iff (hlt : ParLt par) {a x : Nat} (ha : D a = false) :
    Anc (cpar par D) a x ↔ Anc par a x := by
  constructor
  · intro h
    induction h with
    | refl => exact Anc.refl
    | step hq _ ih => exact ih.trans (mem_cpar hlt hq).2.1
  · intro h
    induction x using Nat.strongRecOn with
    | ind x ih =>
      by_cases hax : a = x
      · subst hax; exact Anc.refl
      · obtain ⟨q, hq, hAq⟩ := cpar_covers hlt h hax ha
        have hlt' := (parLt_cpar hlt) x q hq
        exact Anc.step hq (ih q hlt' hAq)

/-! ## The frontier -/

/-- The frontier of heads `H` once `D` is dropped: the maximal surviving images of the heads. A
head that survives is its own image, so with nothing dropped this is `max(H)`. A node advances
to it, adopts records that drop a head through it, and publishes a merge of it. -/
def frontierSet (par : Nat → List Nat) (D : Nat → Bool) (H : OSet) : OSet :=
  maxSet par (fun x => ∃ h, H h ∧ x ∈ exp par D h)

theorem frontierSet_survives (hlt : ParLt par) {H : OSet} {x : Nat}
    (hx : frontierSet par D H x) : D x = false :=
  let ⟨_, _, hm⟩ := hx.1
  (mem_exp hlt hm).1

/-- **Every surviving operation below a head is below the frontier.** -/
theorem frontierSet_covers (hlt : ParLt par) {H : OSet} {B : Nat} (hB : ∀ h, H h → h < B)
    {a h : Nat} (hh : H h) (ha : Anc par a h) (hD : D a = false) :
    ∃ y, frontierSet par D H y ∧ Anc par a y := by
  obtain ⟨q, hq, haq⟩ := exp_covers hlt ha hD
  have hbound : ∀ y, (∃ g, H g ∧ y ∈ exp par D g) → y < B := fun y ⟨g, hg, hy⟩ =>
    Nat.lt_of_le_of_lt ((mem_exp hlt hy).2.le hlt) (hB g hg)
  obtain ⟨y, hy, hqy⟩ := maxSet_covers hlt hbound ⟨h, hh, hq⟩
  exact ⟨y, hy, haq.trans hqy⟩

/-! ## Dropping in two steps -/

/-- Dropping both sets at once. -/
def union (D₁ D₂ : Nat → Bool) : Nat → Bool := fun x => D₁ x || D₂ x

/-- Adding a subset does not change the dropped set. -/
theorem union_absorbs_subset {larger smaller : Nat → Bool}
    (hsub : ∀ x, smaller x = true → larger x = true) : union larger smaller = larger := by
  funext x
  cases hl : larger x <;> cases hs : smaller x <;> simp_all [union]

/-- Each operation's expansion under `D₁`, expanded again under `D₂` in what `D₁` left, is
its expansion under both at once, up to duplicates. -/
theorem exp_union (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (r : Nat) :
    Eqv ((exp par D₁ r).flatMap (exp (cpar par D₁) D₂)) (exp par (union D₁ D₂) r) := by
  have hlt₁ := parLt_cpar (D := D₁) hlt
  induction r using Nat.strongRecOn with
  | ind r ih =>
    have ihp : ∀ p ∈ par r,
        Eqv ((exp par D₁ p).flatMap (exp (cpar par D₁) D₂)) (exp par (union D₁ D₂) p) :=
      fun p hp => ih p (hlt r p hp)
    rw [exp_eq hlt (D := union D₁ D₂), exp_eq hlt (D := D₁)]
    cases h₁ : D₁ r
    · simp only [union, h₁, Bool.false_or, Bool.false_eq_true, ite_false,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [exp_eq hlt₁]
      cases h₂ : D₂ r
      · exact Eqv.refl _
      · simp only [ite_true, cpar]
        refine (flatMap_dd _ _).trans ?_
        rw [List.flatMap_assoc]
        exact Eqv.flatMap ihp
    · simp only [union, h₁, Bool.true_or, ite_true, List.flatMap_assoc]
      exact Eqv.flatMap ihp

/-- Dropping `D₁`, then `D₂` from what is left, gives the parents that dropping both at once
gives. -/
theorem cpar_union (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    cpar (cpar par D₁) D₂ x = cpar par (union D₁ D₂) x := by
  have e : Eqv ((cpar par D₁ x).flatMap (exp (cpar par D₁) D₂))
      ((par x).flatMap (exp par (union D₁ D₂))) := by
    refine (flatMap_dd _ _).trans ?_
    rw [List.flatMap_assoc]
    exact Eqv.flatMap (fun p _ => exp_union hlt D₁ D₂ p)
  simp only [cpar, dd]
  exact e []

/-- A history already contracted by a larger set keeps its parents when a subset is dropped
again. This does not compare the two contractions of the original, uncontracted history. -/
theorem cpar_absorbs_subset (hlt : ParLt par) {larger smaller : Nat → Bool}
    (hsub : ∀ x, smaller x = true → larger x = true) (x : Nat) :
    cpar (cpar par larger) smaller x = cpar par larger x := by
  rw [cpar_union hlt, union_absorbs_subset hsub]

/-! ## Comparing through surviving images -/

/-- Every surviving image of `a` is below `b`. The image's nonemptiness is a separate
guard, as on the shipping hub; the relational lemmas do not assume rooted histories. -/
def Below (par : Nat → List Nat) (D : Nat → Bool) (a b : Nat) : Prop :=
  ∀ p ∈ exp par D a, Anc par p b

theorem below_refl (hlt : ParLt par) (D : Nat → Bool) (a : Nat) :
    Below par D a a :=
  fun _ hp => (mem_exp hlt hp).2

theorem below_survivor_iff (hlt : ParLt par) (ha : D a = false) :
    Below par D a b ↔ Anc par a b := by
  simp [Below, exp_eq hlt, ha]

/-- The images survive, so their ancestry can equivalently be checked in the contracted
graph, as the hub does with current canonical ids. -/
theorem below_contracted_iff (hlt : ParLt par) :
    Below par D a b ↔ ∀ p ∈ exp par D a, Anc (cpar par D) p b := by
  constructor
  · intro h p hp
    exact (anc_cpar_iff hlt (mem_exp hlt hp).1).2 (h p hp)
  · intro h p hp
    exact (anc_cpar_iff hlt (mem_exp hlt hp).1).1 (h p hp)

/-- Expanding a current head under a new pending drop set is the same comparison as
contracting the original history by both sets. -/
theorem below_two_step (hlt : ParLt par) (ha : D a = false) :
    Below (cpar par D) E a b ↔ Below par (union D E) a b := by
  have himages : ∀ p, p ∈ exp (cpar par D) E a ↔ p ∈ exp par (union D E) a := by
    intro p
    have he := (exp_union hlt D E a).mem (a := p)
    simpa [exp_eq hlt, ha] using he
  have hsurvives : ∀ p, p ∈ exp par (union D E) a → D p = false := by
    intro p hp
    have h := (mem_exp hlt hp).1
    have hh : D p = false ∧ E p = false := by simpa [union] using h
    exact hh.1
  constructor
  · intro h p hp
    exact (anc_cpar_iff hlt (hsurvives p hp)).1 (h p ((himages p).2 hp))
  · intro h p hp
    have hm := (himages p).1 hp
    exact (anc_cpar_iff hlt (hsurvives p hm)).2 (h p hm)

/-- Contracting more operations preserves every comparison already made. -/
theorem below_mono (hlt : ParLt par) (hDE : ∀ x, D x = true → E x = true)
    (h : Below par D a b) : Below par E a b := by
  intro p hp
  obtain ⟨hpE, hpa⟩ := mem_exp hlt hp
  have hpD : D p = false := by
    cases hd : D p
    · rfl
    · have := hDE p hd
      simp_all
  obtain ⟨q, hq, hpq⟩ := exp_covers hlt hpa hpD
  exact hpq.trans (h q hq)

theorem below_trans (hlt : ParLt par) (hab : Below par D a b)
    (hbc : Below par D b c) : Below par D a c := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := exp_covers hlt (hab p hp) (mem_exp hlt hp).1
  exact hpq.trans (hbc q hq)

/-- Fresh operations do not change the images of an older head. -/
theorem exp_upd (hlt : ParLt par) (hL : ∀ p ∈ L, p < o) (hx : x < o) :
    exp (upd par o L) D x = exp par D x := by
  have hlt' := parLt_upd hlt hL
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [exp_eq hlt', exp_eq hlt, upd_ne _ _ (Nat.ne_of_lt hx)]
    split
    · apply flatMap_congr_mem
      intro p hp
      exact ih p (hlt x p hp) (by have := hlt x p hp; omega)
    · rfl

/-- `anc*` between operations older than a fresh one is as it was, and so is every comparison
of their images. -/
theorem below_upd (hlt : ParLt par) {L : List Nat} {o a b : Nat} (hL : ∀ p ∈ L, p < o)
    (ha : a < o) (hb : b < o) : Below (upd par o L) D a b ↔ Below par D a b := by
  unfold Below
  rw [exp_upd hlt hL ha]
  constructor <;> intro h p hp
  · exact (anc_upd_iff hlt hL hb).1 (h p hp)
  · exact (anc_upd_iff hlt hL hb).2 (h p hp)

/-- Every surviving image of `a` is below `b` if `a` is. -/
theorem below_of_anc (hlt : ParLt par) {a b : Nat} (h : Anc par a b) : Below par D a b :=
  fun _ hp => (mem_exp hlt hp).2.trans h

/-! ## Ids -/

/-- An operation id: a hash of the operation's content, which `α` stands for, and its parents'
ids. As a term it is injective, as a hash is taken to be. -/
inductive IdTerm (α : Type)
  | mk (content : α) (parents : List (IdTerm α))

/-- The content an id hashes. -/
def IdTerm.content {α : Type} : IdTerm α → α
  | .mk c _ => c

/-- Lists whose images are equal are equal, where equal images have equal sources. -/
theorem map_eq_of_first {α β : Type} {f g : α → β} (hfg : ∀ a b, f a = g b → a = b) :
    ∀ {l l' : List α}, l.map f = l'.map g → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hfg a b h.1, map_eq_of_first hfg h.2]

section Ids

variable {α : Type} {P : Nat → List Nat}

/-- Ids with fuel, in a history with parents `P`, for arbitrary content. -/
def idTermF (content : Nat → α) (P : Nat → List Nat) : Nat → Nat → IdTerm α
  | 0, x => .mk (content x) []
  | f + 1, x => .mk (content x) ((P x).map (idTermF content P f))

/-- The id of `x` in a history with parents `P`, its content `content x`. -/
def idTerm (content : Nat → α) (P : Nat → List Nat) (x : Nat) : IdTerm α :=
  idTermF content P (x + 1) x

theorem idTermF_fuel {content : Nat → α} (hlt : ParLt P) {f g x : Nat} (hf : x < f)
    (hg : x < g) : idTermF content P f x = idTermF content P g x := by
  induction f generalizing g x with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [idTermF, IdTerm.mk.injEq, true_and]
      apply List.map_congr_left
      intro q hq
      have := hlt x q hq
      exact ih (by omega) (by omega)

theorem idTerm_eq_mk {content : Nat → α} (hlt : ParLt P) (x : Nat) :
    idTerm content P x = .mk (content x) ((P x).map (idTerm content P)) := by
  simp only [idTerm, idTermF, IdTerm.mk.injEq, true_and]
  apply List.map_congr_left
  intro q hq
  have := hlt x q hq
  exact idTermF_fuel hlt (by omega) (by omega)

@[simp] theorem content_idTerm {content : Nat → α} (x : Nat) :
    (idTerm content P x).content = content x := by
  simp [idTerm]
  cases x <;> simp [idTermF, IdTerm.content]

/-- Equal ids are of the same operation, `x = y`, given that the contents name the operations
(`hfirst`) and each history's parents have smaller ids (`ParLt`). -/
theorem idTerm_first {P' : Nat → List Nat} {c c' : Nat → α} (hlt : ParLt P) (hlt' : ParLt P')
    (hfirst : ∀ x y, c x = c' y → x = y) {x y : Nat} (h : idTerm c P x = idTerm c' P' y) :
    x = y := by
  rw [idTerm_eq_mk hlt, idTerm_eq_mk hlt'] at h
  simp only [IdTerm.mk.injEq] at h
  exact hfirst x y h.1

variable {par : Nat → List Nat}

/-- Two survivors' ids, each in a history contracted from `par` by its own dropped set, are
equal only for the same operation, where the sets agree on its proper ancestors. The contents
may depend on the sets, as long as they name the operation (`hfirst`). -/
theorem idTerm_cpar_eq (hlt : ParLt par) {c c' : Nat → α} (hfirst : ∀ x y, c x = c' y → x = y)
    {D D' : Nat → Bool} {x y : Nat}
    (h : idTerm c (cpar par D) x = idTerm c' (cpar par D') y) :
    x = y ∧ ∀ a, Anc par a x → a ≠ x → D a = D' a := by
  have hlt₁ := parLt_cpar (D := D) hlt
  have hlt₂ := parLt_cpar (D := D') hlt
  have hxy : x = y := idTerm_first hlt₁ hlt₂ hfirst h
  subst hxy
  refine ⟨rfl, ?_⟩
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [idTerm_eq_mk hlt₁, idTerm_eq_mk hlt₂] at h
    simp only [IdTerm.mk.injEq] at h
    obtain ⟨-, h⟩ := h
    have hl : cpar par D x = cpar par D' x :=
      map_eq_of_first (fun q r hqr => idTerm_first hlt₁ hlt₂ hfirst hqr) h
    rw [← hl] at h
    have hq : ∀ q ∈ cpar par D x, idTerm c (cpar par D) q = idTerm c' (cpar par D') q :=
      List.map_inj_left.1 h
    -- One side drops `a` and the other doesn't: the other reaches it from a parent both
    -- share, whose ids then differ.
    have key : ∀ (E E' : Nat → Bool), cpar par E x = cpar par E' x →
        (∀ q ∈ cpar par E x, ∀ a, Anc par a q → a ≠ q → E a = E' a) →
        ∀ a, Anc par a x → a ≠ x → E a = true → E' a = false → False := by
      intro E E' hl' ih' a hA hne hE hE'
      obtain ⟨q, hqm, hAq⟩ := cpar_covers (D := E') hlt hA hne hE'
      rw [← hl'] at hqm
      have hqE := (mem_cpar hlt hqm).1
      by_cases haq : a = q
      · subst haq; rw [hqE] at hE; exact Bool.false_ne_true hE
      · have := ih' q hqm a hAq haq
        rw [hE, hE'] at this
        exact Bool.noConfusion this
    have ihD : ∀ q ∈ cpar par D x, ∀ a, Anc par a q → a ≠ q → D a = D' a :=
      fun q hqm => ih q ((parLt_cpar hlt) x q hqm) (hq q hqm)
    have ihD' : ∀ q ∈ cpar par D' x, ∀ a, Anc par a q → a ≠ q → D' a = D a := by
      intro q hqm a hAq hne
      rw [← hl] at hqm
      exact (ihD q hqm a hAq hne).symm
    intro a hA hne
    cases hDa : D a <;> cases hD'a : D' a
    · rfl
    · exact (key D' D hl.symm ihD' a hA hne hD'a hDa).elim
    · exact (key D D' hl ihD a hA hne hDa hD'a).elim
    · rfl

/-- Once what is dropped has grown from `D'` to include `x` or one of its proper ancestors, the
id `x` had under `D'` is no id of any operation that survives, as in `idTerm_cpar_eq`. -/
theorem idTerm_superseded_ne (hlt : ParLt par) {c c' : Nat → α}
    (hfirst : ∀ x y, c' x = c y → x = y) {D D' : Nat → Bool} {x : Nat}
    (hsup : D x = true ∨ ∃ a, Anc par a x ∧ a ≠ x ∧ D a = true ∧ D' a = false)
    {y : Nat} (hy : D y = false) : idTerm c' (cpar par D') x ≠ idTerm c (cpar par D) y := by
  intro h
  obtain ⟨rfl, hagree⟩ := idTerm_cpar_eq hlt hfirst h
  rcases hsup with hx | ⟨a, hA, hne, hDa, hD'a⟩
  · rw [hx] at hy; exact Bool.noConfusion hy
  · have := hagree a hA hne
    rw [hDa, hD'a] at this
    exact Bool.noConfusion this

end Ids

/-- An operation id with natural-number content. -/
abbrev CId := IdTerm Nat

variable {content : Nat → Nat}

/-- The id of `x` once `D` is dropped. -/
def cid (content : Nat → Nat) (par : Nat → List Nat) (D : Nat → Bool) (x : Nat) : CId :=
  idTerm content (cpar par D) x

/-- Without an immutable discriminator, removing 1 in a chain can recreate its old id at 2.
This is identical content, not a hash collision. -/
theorem equal_content_recreates_id :
    let par := fun n => if n = 0 then [] else [n - 1]
    cid (fun _ => 0) par (fun n => n == 1) 2 =
      cid (fun _ => 0) par (fun _ => false) 1 := by rfl

theorem cid_eq_mk (hlt : ParLt par) (x : Nat) :
    cid content par D x = .mk (content x) ((cpar par D x).map (cid content par D)) :=
  idTerm_eq_mk (parLt_cpar hlt) x

@[simp] theorem content_cid (x : Nat) : (cid content par D x).content = content x :=
  content_idTerm x

/-- Dropping `D₁` and then `D₂` gives the ids that dropping both at once gives. -/
theorem cid_union (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    cid content (cpar par D₁) D₂ x = cid content par (union D₁ D₂) x := by
  have hlt₁ := parLt_cpar (D := D₁) hlt
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [cid_eq_mk hlt₁, cid_eq_mk hlt, cpar_union hlt]
    simp only [IdTerm.mk.injEq, true_and]
    apply List.map_congr_left
    intro q hq
    exact ih q ((parLt_cpar hlt) x q hq)

/-- A body written under a larger dropped set keeps its canonical id when a subset is dropped
again. Native correspondence must supply this body construction, not an incomplete lookup's
fallback to the input id. -/
theorem cid_absorbs_subset (hlt : ParLt par) {larger smaller : Nat → Bool}
    (hsub : ∀ x, smaller x = true → larger x = true) (x : Nat) :
    cid content (cpar par larger) smaller x = cid content par larger x := by
  rw [cid_union hlt, union_absorbs_subset hsub]

/-- The complete images a contraction writes, in their canonical ids. This is a body
construction; an incomplete lookup that returns its input is not such an image. -/
def image (content : Nat → Nat) (par : Nat → List Nat) (D : Nat → Bool) (x : Nat) :
    List CId := (dd (exp par D x)).map (cid content par D)

/-- A surviving body already written under a larger dropped set is a fixed point when a
subset is contracted again. Survival is essential: unchanged parents alone do not prevent
the head itself from being dropped. -/
theorem image_absorbs_subset (hlt : ParLt par) {larger smaller : Nat → Bool}
    (hsub : ∀ y, smaller y = true → larger y = true) {x : Nat} (hx : larger x = false) :
    image content (cpar par larger) smaller x = [cid content par larger x] := by
  have hs : smaller x = false := by
    cases h : smaller x
    · rfl
    · exact False.elim (Bool.noConfusion (hx.symm.trans (hsub x h)))
  rw [image, exp_eq (parLt_cpar hlt), hs]
  simp only [Bool.false_eq_true, ite_false, dd, ddAux, List.not_mem_nil, ite_false,
    List.map_cons, List.map_nil]
  rw [cid_absorbs_subset hlt hsub]

/-- When drops name originals, every image has a surviving original. No global injectivity
of immutable content is needed: different raw versions may have the same original. -/
theorem image_original_survives (hlt : ParLt par) (dropped : Nat → Bool) {x : Nat} {id : CId}
    (hi : id ∈ image content par (fun y => dropped (content y)) x) :
    dropped id.content = false := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hi
  simpa only [content_cid] using (mem_exp hlt (mem_dd.1 hy)).1

/-- An image cannot be any historical version of a dropped original. This compares
originals, rather than assuming a raw name occurs in only one history. -/
theorem image_ne_dropped_original (hlt : ParLt par) (dropped : Nat → Bool)
    {x : Nat} {id old : CId}
    (hi : id ∈ image content par (fun y => dropped (content y)) x)
    (hold : dropped old.content = true) : id ≠ old := by
  intro he
  have hs := image_original_survives hlt dropped hi
  rw [he, hold] at hs
  cases hs

/-- Hence the order of two drops doesn't matter. -/
theorem cid_comm (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    cid content (cpar par D₁) D₂ x = cid content (cpar par D₂) D₁ x := by
  rw [cid_union hlt, cid_union hlt]
  congr 1
  funext y
  simp [union, Bool.or_comm]

/-- Requires injective immutable content; collision-free hashing alone is insufficient.
Two survivors' ids under two dropped sets are equal only for the same operation, where the
sets agree on its proper ancestors. -/
theorem cid_eq (hlt : ParLt par) (hinj : Function.Injective content) {D' : Nat → Bool}
    {x y : Nat} (h : cid content par D x = cid content par D' y) :
    x = y ∧ ∀ a, Anc par a x → a ≠ x → D a = D' a :=
  idTerm_cpar_eq hlt (fun _ _ e => hinj e) h

/-- Once a machine's dropped set `D` has grown from `D'` to include `x` or one of its proper
ancestors, the id `x` had under `D'` is no id of any operation that survives `D`. -/
theorem superseded_ne (hlt : ParLt par) (hinj : Function.Injective content)
    {D' : Nat → Bool} {x : Nat}
    (hsup : D x = true ∨ ∃ a, Anc par a x ∧ a ≠ x ∧ D a = true ∧ D' a = false)
    {y : Nat} (hy : D y = false) : cid content par D' x ≠ cid content par D y :=
  idTerm_superseded_ne hlt (fun _ _ e => hinj e) hsup hy

/-! ## Ids depend only on what is below -/

/-- `anc*(x)` depends only on the parents of `x` and what is below it. -/
theorem anc_congr {par par' : Nat → List Nat} (hlt : ParLt par) {x : Nat}
    (h : ∀ y, y ≤ x → par y = par' y) {a : Nat} : Anc par a x ↔ Anc par' a x := by
  have hlt' : ∀ y p, y ≤ x → p ∈ par' y → p < y := by
    intro y p hy hp; rw [← h y hy] at hp; exact hlt y p hp
  constructor
  · intro hA
    have : ∀ z, Anc par a z → z ≤ x → Anc par' a z := by
      intro z hz
      induction hz with
      | refl => intro _; exact Anc.refl
      | @step p z hp _ ih =>
        intro hzx
        have hpz := hlt z p hp
        exact Anc.step (by rw [← h z hzx]; exact hp) (ih (by omega))
    exact this x hA (Nat.le_refl _)
  · intro hA
    have : ∀ z, Anc par' a z → z ≤ x → Anc par a z := by
      intro z hz
      induction hz with
      | refl => intro _; exact Anc.refl
      | @step p z hp _ ih =>
        intro hzx
        have hpz := hlt' z p hzx hp
        exact Anc.step (by rw [h z hzx]; exact hp) (ih (by omega))
    exact this x hA (Nat.le_refl _)

/-- The id of `x` depends only on the parents of `x` and what is below it. -/
theorem cid_congr {par par' : Nat → List Nat} (hlt : ParLt par) (hlt' : ParLt par')
    {x : Nat} (h : ∀ y, y ≤ x → par y = par' y) : cid content par D x = cid content par' D x := by
  have hexp : ∀ p, p ≤ x → exp par D p = exp par' D p := by
    intro p
    induction p using Nat.strongRecOn with
    | ind p ih =>
      intro hp
      rw [exp_eq hlt, exp_eq hlt', h p hp]
      split
      · apply flatMap_congr_mem
        intro q hq
        have := hlt' p q hq
        exact ih q this (by omega)
      · rfl
  have hcpar : ∀ z, z ≤ x → cpar par D z = cpar par' D z := by
    intro z hz
    simp only [cpar, h z hz]
    congr 1
    apply flatMap_congr_mem
    intro q hq
    have := hlt' z q hq
    exact hexp q (by omega)
  have : ∀ z, z ≤ x → cid content par D z = cid content par' D z := by
    intro z
    induction z using Nat.strongRecOn with
    | ind z ih =>
      intro hz
      rw [cid_eq_mk hlt, cid_eq_mk hlt', hcpar z hz]
      simp only [IdTerm.mk.injEq, true_and]
      apply List.map_congr_left
      intro q hq
      have := (parLt_cpar hlt') z q hq
      exact ih q this (by omega)
  exact this x (Nat.le_refl _)

end Musubi.Contract

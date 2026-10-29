/-
The local names of workspaces (design.md, "Which workspaces are this machine's own").

A canonical view keys each workspace by its machine, `<key>/<workspace>`, and each machine shows
a view with its own workspaces under their names and every other machine's as
`<prefix>/<workspace>`. Canonicalizing reads the local names back as keys, so naming must be
injective on a view's keys.

Each machine, this one among them, takes the first of its candidate prefixes that is free
(`assign`; `workspaces::display_names`), as the hub, which names every machine, does too; this
machine shows only the others'. The candidates are its name, if no other machine has it; its name
and the start of its key's suffix, `laptop-1a2b`; its name and the whole suffix; then that with
ever more `-`. A prefix is free if no machine before it took it, and no name of this machine's own
starts with it and `/`. The last candidates make one free: one longer than every prefix taken and
every name of this machine's own (`choose_free`).

- Naming is injective on a view's keys (`localName_injective`), whatever the machines and the
  names of this machine's own.

Keys are modeled as their name and suffix, and names as lists of characters. A machine's name
and suffix have no `/`, as `workspaces::sanitize` and the random suffix make them; this
machine's own names may have any.
-/

namespace Musubi.Names

abbrev Str := List Char

/-- A machine key, `name#suffix`. -/
structure Key where
  name : Str
  suffix : Str
deriving DecidableEq, Repr

/-- Whether a name of this machine's own starts with `p/`. -/
def taken (own : List Str) (p : Str) : Bool := own.any fun w => (p ++ ['/']).isPrefixOf w

/-- A prefix nothing before has taken. -/
def free (own used : List Str) (p : Str) : Bool := !used.contains p && !taken own p

/-- The machine's name and its whole suffix. -/
def full (k : Key) : Str := k.name ++ '-' :: k.suffix

/-- The length of the longest of `ss`. -/
def maxLen : List Str → Nat
  | [] => 0
  | s :: ss => max s.length (maxLen ss)

theorem le_maxLen {s : Str} : ∀ {ss : List Str}, s ∈ ss → s.length ≤ maxLen ss
  | _ :: _, .head _ => Nat.le_max_left _ _
  | _ :: _, .tail _ h => Nat.le_trans (le_maxLen h) (Nat.le_max_right _ _)

/-- `k`'s candidate prefixes, in order: its name if `plain`, its name and the start of its
suffix, its name and its whole suffix, then that with `1` to `bound + 1` dashes. -/
def candidates (plain : Bool) (k : Key) (bound : Nat) : List Str :=
  (if plain then [k.name] else []) ++ [k.name ++ '-' :: k.suffix.take 4, full k] ++
    (List.range (bound + 1)).map fun i => full k ++ List.replicate (i + 1) '-'

/-- The first free candidate. The bound makes the last one free. -/
def choose (own used : List Str) (plain : Bool) (k : Key) : Str :=
  ((candidates plain k (maxLen (used ++ own))).find? (free own used)).getD (full k)

theorem isPrefixOf_length {l₁ l₂ : Str} (h : l₁.isPrefixOf l₂ = true) :
    l₁.length ≤ l₂.length :=
  (List.isPrefixOf_iff_prefix.mp h).length_le

/-- A candidate longer than every prefix taken and every name of this machine's own is free. -/
theorem free_of_long {own used : List Str} {p : Str} (h : maxLen (used ++ own) < p.length) :
    free own used p = true := by
  simp only [free, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · apply Bool.eq_false_iff.mpr
    intro hc
    have := le_maxLen (List.mem_append_left own (List.contains_iff_mem.mp hc))
    omega
  · apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨w, hw, hp⟩ := List.any_eq_true.mp ht
    have h₁ := isPrefixOf_length hp
    have h₂ := le_maxLen (List.mem_append_right used hw)
    simp only [List.length_append, List.length_singleton] at h₁
    omega

theorem choose_free (own used : List Str) (plain : Bool) (k : Key) :
    free own used (choose own used plain k) = true := by
  have hlast : full k ++ List.replicate (maxLen (used ++ own) + 1) '-' ∈
      candidates plain k (maxLen (used ++ own)) := by
    simp only [candidates, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨_, Nat.lt_succ_self _, rfl⟩
  have hfree : free own used (full k ++ List.replicate (maxLen (used ++ own) + 1) '-') = true :=
    free_of_long (by simp only [List.length_append, List.length_replicate]; omega)
  unfold choose
  cases hp : (candidates plain k (maxLen (used ++ own))).find? (free own used) with
  | none => exact absurd (List.find?_isSome.mpr ⟨_, hlast, hfree⟩) (by simp [hp])
  | some p => exact List.find?_some hp

/-- Every candidate is free of `/` when the name and suffix are. -/
theorem choose_no_slash (own used : List Str) (plain : Bool) {k : Key}
    (hn : '/' ∉ k.name) (hs : '/' ∉ k.suffix) : '/' ∉ choose own used plain k := by
  have hfull : '/' ∉ full k := by
    simp only [full, List.mem_append, List.mem_cons, not_or]
    exact ⟨hn, by decide, hs⟩
  unfold choose
  cases h : (candidates plain k (maxLen (used ++ own))).find? (free own used) with
  | none => exact hfull
  | some p =>
    simp only [Option.getD_some]
    have hm := List.mem_of_find?_eq_some h
    simp only [candidates, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.mem_nil_iff, or_false] at hm
    rcases hm with (hm | rfl | rfl) | ⟨i, -, rfl⟩
    · split at hm
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm; exact hm ▸ hn
      · simp at hm
    · simp only [List.mem_append, List.mem_cons, not_or]
      exact ⟨hn, by decide, fun m => hs (List.mem_of_mem_take m)⟩
    · exact hfull
    · simp only [List.mem_append, List.mem_replicate, not_or, not_and]
      exact ⟨hfull, fun _ => by decide⟩

/-- Whether no other machine has `k`'s name. -/
def plainOk (machines : List Key) (k : Key) : Bool :=
  (machines.filter (·.name == k.name)).length == 1

/-- `display_names`: each machine's prefix, in order, each choosing among the prefixes those
before it left free. -/
def assignFrom (machines : List Key) (own : List Str) :
    List (Key × Str) → List Key → List (Key × Str)
  | acc, [] => acc
  | acc, k :: ks =>
    assignFrom machines own (acc ++ [(k, choose own (acc.map (·.2)) (plainOk machines k) k)]) ks

def assign (machines : List Key) (own : List Str) : List (Key × Str) :=
  assignFrom machines own [] machines

/-- What `assign` keeps true of the prefixes chosen so far. -/
def Good (own : List Str) (acc : List (Key × Str)) : Prop :=
  (acc.map (·.2)).Nodup ∧ ∀ p ∈ acc.map (·.2), taken own p = false

theorem assignFrom_spec (machines : List Key) (own : List Str)
    (hslash : ∀ k ∈ machines, '/' ∉ k.name ∧ '/' ∉ k.suffix) :
    ∀ (ks : List Key) (acc : List (Key × Str)), (∀ k ∈ ks, k ∈ machines) → Good own acc →
      (∀ e ∈ acc, '/' ∉ e.2) →
      Good own (assignFrom machines own acc ks) ∧
        (assignFrom machines own acc ks).map (·.1) = acc.map (·.1) ++ ks ∧
        ∀ e ∈ assignFrom machines own acc ks, '/' ∉ e.2
  | [], acc, _, hg, hs => ⟨hg, by simp [assignFrom], hs⟩
  | k :: ks, acc, hks, ⟨hnd, htk⟩, hs => by
    let p := choose own (acc.map (·.2)) (plainOk machines k) k
    have hf := choose_free own (acc.map (·.2)) (plainOk machines k) k
    simp only [free, Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hg : Good own (acc ++ [(k, p)]) := by
      refine ⟨?_, ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.mpr ⟨hnd, by simp, ?_⟩
        intro q hq r hr hqr
        simp only [List.mem_singleton] at hr
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
        have hc : (acc.map (·.2)).contains p = true := List.contains_iff_mem.mpr
          (by rw [← hr, ← hqr]; exact List.mem_map_of_mem he)
        rw [hf.1] at hc
        exact Bool.noConfusion hc
      · intro q hq
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton] at hq
        rcases hq with hq | rfl
        · exact htk q hq
        · exact hf.2
    have hs' : ∀ e ∈ acc ++ [(k, p)], '/' ∉ e.2 := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hs e he
      · have := hslash k (hks k List.mem_cons_self)
        exact choose_no_slash _ _ _ this.1 this.2
    have ih := assignFrom_spec machines own hslash ks (acc ++ [(k, p)])
      (fun k' hk' => hks k' (List.mem_cons_of_mem _ hk')) hg hs'
    refine ⟨ih.1, ?_, ih.2.2⟩
    rw [show assignFrom machines own acc (k :: ks) =
      assignFrom machines own (acc ++ [(k, p)]) ks from rfl, ih.2.1]
    simp

/-- Two entries of a list that `f` takes to the same value are the same, if `f` takes the
list's entries to distinct values. -/
theorem eq_of_map_nodup {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b}, a ∈ l → b ∈ l → f a = f b → a = b
  | x :: xs, hnd, a, b, ha, hb, h => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hnd.1 (by rw [h]; exact List.mem_map_of_mem hb')).elim
    · exact (hnd.1 (by rw [← h]; exact List.mem_map_of_mem ha')).elim
    · exact eq_of_map_nodup hnd.2 ha' hb' h

/-- The prefix `assign` gave machine `k`. -/
def prefixOf (a : List (Key × Str)) (k : Key) : Str :=
  ((a.find? (·.1 == k)).map (·.2)).getD []

theorem prefixOf_mem {a : List (Key × Str)} {k : Key} (hk : k ∈ a.map (·.1)) :
    (k, prefixOf a k) ∈ a := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
  cases hx : a.find? (·.1 == e.1) with
  | none =>
    have := List.find?_eq_none.mp hx e he
    simp at this
  | some x =>
    have hb : (x.1 == e.1) = true := List.find?_some (p := fun y : Key × Str => y.1 == e.1) hx
    have hxk : x.1 = e.1 := beq_iff_eq.mp hb
    simp only [prefixOf, hx, Option.map_some, Option.getD_some]
    rw [← hxk]
    exact List.mem_of_find?_eq_some hx

/-- `local_names`: the name here of workspace `w` of machine `k`, on machine `me`. -/
def localName (me : Key) (a : List (Key × Str)) (k : Key) (w : Str) : Str :=
  if k = me then w else prefixOf a k ++ '/' :: w

/-- Splitting at the first `/` is unique. -/
theorem split_slash {p₁ p₂ w₁ w₂ : Str} (h₁ : '/' ∉ p₁) (h₂ : '/' ∉ p₂)
    (h : p₁ ++ '/' :: w₁ = p₂ ++ '/' :: w₂) : p₁ = p₂ ∧ w₁ = w₂ := by
  induction p₁ generalizing p₂ with
  | nil =>
    cases p₂ with
    | nil => simpa using h
    | cons c p₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h₂
  | cons c p₁ ih =>
    cases p₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self) h₁
    | cons d p₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      have := ih (fun m => h₁ (List.mem_cons_of_mem _ m))
        (fun m => h₂ (List.mem_cons_of_mem _ m)) h
      exact ⟨congrArg _ this.1, this.2⟩

/-- Naming is injective on a view's keys: this machine's workspaces, whose names are among
`own`, and the other machines', whose keys are among `machines`, which may have this
machine's too. -/
theorem localName_injective {me : Key} {machines : List Key} {own : List Str}
    (hslash : ∀ k ∈ machines, '/' ∉ k.name ∧ '/' ∉ k.suffix)
    {k₁ k₂ : Key} {w₁ w₂ : Str}
    (hk₁ : k₁ = me ∧ w₁ ∈ own ∨ k₁ ≠ me ∧ k₁ ∈ machines)
    (hk₂ : k₂ = me ∧ w₂ ∈ own ∨ k₂ ≠ me ∧ k₂ ∈ machines)
    (h : localName me (assign machines own) k₁ w₁ = localName me (assign machines own) k₂ w₂) :
    k₁ = k₂ ∧ w₁ = w₂ := by
  let a := assign machines own
  obtain ⟨⟨hpnd, htk⟩, hkeys, hsl⟩ :=
    assignFrom_spec machines own hslash machines [] (fun _ h => h) ⟨List.nodup_nil, by simp⟩
      (by simp)
  simp only [List.map_nil, List.nil_append] at hkeys
  have mem : ∀ {k}, k ∈ machines → (k, prefixOf a k) ∈ a :=
    fun hk => prefixOf_mem (by simpa [a, assign, hkeys] using hk)
  -- A name of this machine's own isn't another machine's prefix and `/`.
  have apart : ∀ {w k v}, w ∈ own → k ∈ machines → w ≠ prefixOf a k ++ '/' :: v := by
    intro w k v hw hk e
    have := htk _ (List.mem_map_of_mem (f := (·.2)) (mem hk))
    simp only [taken, List.any_eq_false, Bool.not_eq_true] at this
    have hpre : (prefixOf a k ++ ['/']).isPrefixOf (prefixOf a k ++ '/' :: v) = true :=
      List.isPrefixOf_iff_prefix.mpr ⟨v, by simp⟩
    have := this w hw
    rw [e, hpre] at this
    exact Bool.noConfusion this
  have mine : ∀ {k w}, k = me ∧ w ∈ own ∨ k ≠ me ∧ k ∈ machines → k = me → w ∈ own :=
    fun hk e => (hk.resolve_right fun h => h.1 e).2
  have other : ∀ {k w}, k = me ∧ w ∈ own ∨ k ≠ me ∧ k ∈ machines → k ≠ me → k ∈ machines :=
    fun hk e => (hk.resolve_left fun h => e h.1).2
  unfold localName at h
  by_cases e₁ : k₁ = me <;> by_cases e₂ : k₂ = me <;> simp only [e₁, e₂, ite_true, ite_false] at h
  · exact ⟨e₁.trans e₂.symm, h⟩
  · exact absurd h (apart (mine hk₁ e₁) (other hk₂ e₂))
  · exact absurd h.symm (apart (mine hk₂ e₂) (other hk₁ e₁))
  · have m₁ := mem (other hk₁ e₁)
    have m₂ := mem (other hk₂ e₂)
    have ⟨hp, hw⟩ := split_slash (hsl _ m₁) (hsl _ m₂) h
    exact ⟨congrArg Prod.fst (eq_of_map_nodup hpnd m₁ m₂ hp), hw⟩

/-! Cases where the rule before this one gave two workspaces one name, now apart. -/

/-- The names here of each machine's `default`, and of this machine's own `own`. -/
def namesOf (machines : List Key) (own : List Str) : List Str :=
  let me : Key := ⟨"me".toList, "00000000".toList⟩
  own.map (localName me (assign machines own) me) ++
    machines.map fun k => localName me (assign machines own) k "default".toList

-- Two machines named alike whose suffixes start alike.
#guard (namesOf [⟨"mac".toList, "aaaa1111".toList⟩, ⟨"mac".toList, "aaaa2222".toList⟩] []).map
    String.ofList == ["mac-aaaa/default", "mac-aaaa2222/default"]

-- A machine whose name was the longer prefix of another.
#guard (namesOf [⟨"mac".toList, "aaaa0000".toList⟩, ⟨"mac".toList, "bbbb0000".toList⟩,
    ⟨"mac-aaaa".toList, "12345678".toList⟩] []).map String.ofList ==
  ["mac-aaaa/default", "mac-bbbb/default", "mac-aaaa-1234/default"]

-- A name of this machine's own that started with the longer prefix another forced.
#guard (namesOf [⟨"beta".toList, "1a2b3c4d".toList⟩] ["beta/x".toList,
    "beta-1a2b/default".toList]).map String.ofList ==
  ["beta/x", "beta-1a2b/default", "beta-1a2b3c4d/default"]

end Musubi.Names

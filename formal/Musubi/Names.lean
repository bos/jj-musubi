/-
The local names of workspaces (design.md, "Which workspaces are this machine's own").

A canonical view keys each workspace by its machine, `<key>/<workspace>`, and each machine shows
a view with its own workspaces under their names and every other machine's as
`<prefix>/<workspace>`. Canonicalizing reads the local names back as keys, so naming must be
injective on a view's keys.

A machine's prefix is the first of its candidates that is free. The candidates are its name, if
it may take it plain; its name and the start of its key's suffix, `laptop-1a2b`; its name and the
whole suffix; then that with ever more `-`. A prefix is free if no machine before it took it, and
no name of this machine's own starts with it and `/`. The last candidates make one free: one
longer than every prefix taken and every name of this machine's own (`choose_free`), and none has
a `/` (`choose_no_slash`). Which machines are named, in which order, and which may take their
names plain is `Identity.lean`'s (`Identity.Naming.assign`, `workspaces::display_names`), which
proves the names injective on a view's keys (`Identity.Naming.localName_injective`).

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

end Musubi.Names

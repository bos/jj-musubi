/-
The decisions musubi makes when it moves jj operation heads that it read earlier
(`docs/internals/design.md`, "Moving op heads"; `crates/musubi-jj/src/node/heads.rs`), as pure
functions of the heads, the watch and what was read, for the oracle
(`docs/internals/conformance.md`, "Moving op heads"), with the theorems the Rust code relies on.

An operation is a `Nat`, `Graph` has what musubi reads of one (its parents, its fingerprint, and
whether the translation cache knows it), and `r` rewrites `h` when they have one fingerprint and
two ids. The look takes an op head for a rewrite of a replaced head: an op head that is none of
musubi's, unknown to its cache, with the replaced head's fingerprint. It doesn't look below the op
heads, where the operation a replaced head was rewritten from has that fingerprint too
(`OvertakenBelow` is what the walk found). `Replaced` is one entry of the watch: an op head musubi
took out, with what it rewrote to (`images`) and what it put in its place (`put`).

* `lookPlan` is `plan::look` in `heads/plan.rs` (`retiring` in `heads.rs` calls it): from the
  heads and the watch, what to take out, what to put back and what to keep watching, or nothing.
* `entries` is `plan::entries` (once `replaced_by`), `compose` is `plan::compose`
  (`Records::watch_replaced` calls it), `same` is `plan::same`, the check that the op heads are
  those musubi read.

The theorems are about `lookPlan`: that it finds exactly the op heads beside a rewrite of what
musubi replaced (`rewritten_empty_iff`), what it takes out is only what musubi put in
(`retire_out_put`) and leaves a head beside (`retire_stay`), what a merge or realization it takes
out was on is put back (`retire_back_covers`), and that taking out again and again ends
(`settle_nothing`). `OpHeadsRace.lean` puts them among jj's commands.
-/

namespace Musubi.OpHeads

/-- What musubi reads of operations. -/
structure Graph where
  parents : Nat → List Nat
  fp : Nat → Nat
  known : Nat → Bool

/-- `g` with operation `n`. -/
def Graph.add (g : Graph) (n : Nat) (ps : List Nat) (fp : Nat) (kn : Bool) : Graph where
  parents i := if i = n then ps else g.parents i
  fp i := if i = n then fp else g.fp i
  known i := if i = n then kn else g.known i

/-- Every operation's parents come before it, as ids go in the oracle and in the model. -/
def Graph.Dag (g : Graph) : Prop := ∀ x p, p ∈ g.parents x → p < x

/-- One op head musubi took out. -/
structure Replaced where
  head : Nat
  fp : Nat
  images : List Nat
  put : List Nat
deriving DecidableEq, Repr

/-- Whether `a` and `b` are the same op heads, in any order: the check before a move, and
after it. -/
def same (a b : List Nat) : Bool := a.all (b.contains ·) && b.all (a.contains ·)

theorem same_iff {a b : List Nat} : same a b = true ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [same, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨h1 x, h2 x⟩
  · intro h
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

/-! ## The history below an op head, which musubi no longer walks -/

/-- A path of operations below an op head that are none of what musubi put in or its cache
knows. musubi once looked for the rewrite of a replaced head along such a path, and took what
the head was rewritten *from* for a rewrite made since (`OvertakenBelow`); it now looks only at
the op heads themselves ([design.md, "Moving op heads"](../../docs/internals/design.md)). -/
inductive Down (g : Graph) (put : List Nat) : Nat → Nat → Prop
  | here {x : Nat} : x ∉ put → g.known x = false → Down g put x x
  | step {x p y : Nat} : x ∉ put → g.known x = false → p ∈ g.parents x →
      Down g put p y → Down g put x y

/-! ## What the watch finds -/

/-- The watch entries with something that replaced them still an op head. -/
def liveOf (heads : List Nat) (W : List Replaced) : List Replaced :=
  W.filter fun r => r.put.any (heads.contains ·)

/-- What musubi put in place of what it watches. -/
def putOf (W : List Replaced) : List Nat := W.flatMap (·.put)

/-- The op heads that are none of what musubi put in. -/
def besideOf (heads put : List Nat) : List Nat := heads.filter fun h => !put.contains h

/-- The watched op heads that jj rewrote: for which an op head beside musubi's, that the cache
doesn't know, has the head's fingerprint and another id. -/
def rewritten (g : Graph) (W : List Replaced) (beside : List Nat) : List Nat :=
  (W.filter fun r => beside.any fun x => !g.known x && g.fp x == r.fp && x != r.head).map (·.head)

/-- Musubi's replacement of some op head sits beside a rewrite of what it replaced: an op head
that is none of what musubi put in, unknown to its cache, with the replaced head's fingerprint
and another id. -/
def Overtaken (g : Graph) (heads : List Nat) (W : List Replaced) : Prop :=
  ∃ w ∈ liveOf heads W, ∃ x ∈ besideOf heads (putOf (liveOf heads W)),
    g.known x = false ∧ g.fp x = w.fp ∧ x ≠ w.head

instance (g : Graph) (heads : List Nat) (W : List Replaced) : Decidable (Overtaken g heads W) := by
  unfold Overtaken; infer_instance

/-- What musubi's look found before, by walking below the op heads beside its replacement: the
operation it found may be below one. -/
def OvertakenBelow (g : Graph) (heads : List Nat) (W : List Replaced) : Prop :=
  ∃ w ∈ liveOf heads W, ∃ x ∈ besideOf heads (putOf (liveOf heads W)),
    ∃ y, Down g (putOf (liveOf heads W)) x y ∧ g.fp y = w.fp ∧ y ≠ w.head

/-- What `Overtaken` finds, the walk finds too: it is the walk that stops at the op head. -/
theorem overtaken_below {g : Graph} {heads : List Nat} {W : List Replaced}
    (h : Overtaken g heads W) : OvertakenBelow g heads W := by
  obtain ⟨w, hw, x, hx, hk, hfp, hne⟩ := h
  have hx' := List.mem_filter.1 hx
  exact ⟨w, hw, x, hx, x, .here (by simpa using hx'.2) hk, hfp, hne⟩

theorem rewritten_empty_iff {g : Graph} {heads : List Nat} (W : List Replaced) :
    rewritten g (liveOf heads W) (besideOf heads (putOf (liveOf heads W))) = [] ↔
      ¬ Overtaken g heads W := by
  unfold rewritten Overtaken
  simp only [List.map_eq_nil_iff, List.filter_eq_nil_iff, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · intro h ⟨w, hw, x, hx, hk, hfp, hne⟩
    exact h w hw ⟨x, hx, ⟨by simpa using hk, hfp⟩, hne⟩
  · intro h w hw ⟨x, hx, ⟨hk, hfp⟩, hne⟩
    exact h ⟨w, hw, x, hx, by simpa using hk, hfp, hne⟩

/-! ## What to take out and what to put back -/

/-- What musubi does about the op heads beside which a rewrite sits. -/
inductive Look
  /-- Nothing; what it watches is `kept`. -/
  | nothing (kept : List Replaced)
  /-- Take `out` out, put `back` in, and watch `kept`; `rewritten` heads were rewritten. -/
  | retire (out back : List Nat) (kept : List Replaced) (rewritten : Nat)
deriving DecidableEq, Repr

/-- What a merge or realization taken out was on, that goes back: its parents that are none of
what is replaced and not on a rewrite. -/
def backOf (g : Graph) (heads staleImages staleBy outs : List Nat) : List Nat :=
  outs.foldl (fun back op =>
    (g.parents op).foldl (fun back p =>
      if staleImages.contains p || staleBy.contains p || heads.contains p || back.contains p then
        back
      else if (g.parents p).all fun q => !staleImages.contains q then back ++ [p]
      else back) back) []

/-- What to take out of `heads` and put back, once some of `watched` are `found` rewritten. -/
def retirePlan (g : Graph) (heads : List Nat) (watched : List Replaced) (found : List Nat) :
    Look :=
  let stale := watched.filter fun r => found.contains r.head
  let kept0 := watched.filter fun r => !found.contains r.head
  let staleImages := stale.flatMap (·.images)
  let staleBy := stale.flatMap (·.put)
  let out := heads.filter (staleBy.contains ·)
  let back := backOf g heads staleImages staleBy (out.filter fun o => !staleImages.contains o)
  let kept := kept0.map fun r =>
    { r with put := r.put.filter (fun o => !out.contains o) ++ back.filter (r.images.contains ·) }
  .retire out back kept stale.length

/-- `plan::look` in `heads/plan.rs`. -/
def lookPlan (g : Graph) (heads : List Nat) (W : List Replaced) : Look :=
  let watched := liveOf heads W
  let put := putOf watched
  let found := rewritten g watched (besideOf heads put)
  if found.isEmpty then .nothing watched else retirePlan g heads watched found

/-- The op heads once `out` is taken out and `back` put in. -/
def after (heads out back : List Nat) : List Nat := heads.filter (fun h => !out.contains h) ++ back

/-- The watched heads and the ones found, which `lookPlan` retires. -/
theorem lookPlan_retire {g : Graph} {heads : List Nat} {W : List Replaced}
    {l : Look} (h : lookPlan g heads W = l) (hl : ∀ k, l ≠ .nothing k) :
    let watched := liveOf heads W
    let found := rewritten g watched (besideOf heads (putOf watched))
    found ≠ [] ∧ l = retirePlan g heads watched found := by
  unfold lookPlan at h
  simp only at h
  split at h
  · exact absurd h.symm (hl _)
  · rename_i hne
    refine ⟨by simpa using hne, h.symm⟩

section Retire

/-- The step `backOf` takes for one parent `p` of an operation. -/
def backStep (g : Graph) (heads staleImages staleBy : List Nat) (back : List Nat) (p : Nat) :
    List Nat :=
  if staleImages.contains p || staleBy.contains p || heads.contains p || back.contains p then back
  else if (g.parents p).all fun q => !staleImages.contains q then back ++ [p]
  else back

theorem backOf_eq (g : Graph) (heads staleImages staleBy outs : List Nat) :
    backOf g heads staleImages staleBy outs =
      outs.foldl (fun back op => (g.parents op).foldl (backStep g heads staleImages staleBy) back)
        [] := rfl

theorem backStep_mono (g : Graph) (heads si sb : List Nat) (back : List Nat) (p : Nat) :
    ∀ b ∈ back, b ∈ backStep g heads si sb back p := by
  intro b hb
  unfold backStep
  split
  · exact hb
  · split
    · exact List.mem_append.2 (Or.inl hb)
    · exact hb

theorem backStep_sub (g : Graph) (heads si sb : List Nat) (back : List Nat) (p : Nat) :
    ∀ b ∈ backStep g heads si sb back p, b ∈ back ∨ (b = p ∧ p ∉ heads) := by
  intro b hb
  unfold backStep at hb
  split at hb
  · exact Or.inl hb
  · next hc =>
    split at hb
    · rcases List.mem_append.1 hb with hb | hb
      · exact Or.inl hb
      · have : b = p := by simpa using hb
        subst this
        refine Or.inr ⟨rfl, fun hp => hc ?_⟩
        have : heads.contains b = true := List.contains_iff_mem.2 hp
        simp only [Bool.or_eq_true]
        exact Or.inl (Or.inr this)
    · exact Or.inl hb

theorem foldl_step_mono (g : Graph) (heads si sb : List Nat) :
    ∀ (ps : List Nat) (acc : List Nat), ∀ b ∈ acc, b ∈ ps.foldl (backStep g heads si sb) acc := by
  intro ps
  induction ps with
  | nil => intro acc b hb; exact hb
  | cons p ps ih => intro acc b hb; exact ih _ b (backStep_mono g heads si sb acc p b hb)

theorem backStep_cases (g : Graph) (heads si sb : List Nat) (back : List Nat) (p : Nat) :
    p ∈ si ∨ p ∈ sb ∨ p ∈ heads ∨ p ∈ backStep g heads si sb back p ∨
      ∃ q ∈ g.parents p, q ∈ si := by
  unfold backStep
  split
  · rename_i h
    simp only [Bool.or_eq_true, List.contains_iff_mem] at h
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · split
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_append.2 (Or.inr (by simp))))))
    · rename_i h1 h2
      have : ∃ q ∈ g.parents p, q ∈ si := by
        refine Classical.byContradiction fun hno => ?_
        apply h2
        simp only [List.all_eq_true]
        intro q hq
        have hq' : q ∉ si := fun hqs => hno ⟨q, hq, hqs⟩
        simp [hq']
      exact Or.inr (Or.inr (Or.inr (Or.inr this)))

/-- Every parent of an operation `backOf` looks at is on a rewrite, among what is replaced, an op
head, put back, or built on a rewrite. -/
theorem backOf_covers (g : Graph) (heads si sb outs : List Nat) :
    ∀ op ∈ outs, ∀ p ∈ g.parents op,
      p ∈ si ∨ p ∈ sb ∨ p ∈ heads ∨ p ∈ backOf g heads si sb outs ∨ ∃ q ∈ g.parents p, q ∈ si := by
  rw [backOf_eq]
  have key : ∀ (outs acc : List Nat) (op : Nat), op ∈ outs → ∀ p ∈ g.parents op,
      p ∈ si ∨ p ∈ sb ∨ p ∈ heads ∨
        p ∈ outs.foldl (fun back op => (g.parents op).foldl (backStep g heads si sb) back) acc ∨
        ∃ q ∈ g.parents p, q ∈ si := by
    intro outs
    induction outs with
    | nil => intro acc op h; simp at h
    | cons o outs ih =>
      intro acc op hop p hp
      simp only [List.foldl_cons]
      -- either `op` is `o`, handled now, or one of `outs`, handled by `ih`
      rcases List.mem_cons.1 hop with rfl | hop
      · have inner : ∀ (ps : List Nat) (acc : List Nat), p ∈ ps →
            p ∈ si ∨ p ∈ sb ∨ p ∈ heads ∨ p ∈ ps.foldl (backStep g heads si sb) acc ∨
              ∃ q ∈ g.parents p, q ∈ si := by
          intro ps
          induction ps with
          | nil => intro acc h; simp at h
          | cons p' ps ih2 =>
            intro acc hp'
            simp only [List.foldl_cons]
            rcases List.mem_cons.1 hp' with rfl | hp'
            · rcases backStep_cases g heads si sb acc p with h | h | h | h | h
              · exact Or.inl h
              · exact Or.inr (Or.inl h)
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inr (Or.inl (foldl_step_mono g heads si sb ps _ p h))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
            · exact ih2 _ hp'
        have := inner (g.parents op) acc hp
        rcases this with h | h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · -- later operations only add
          have mono : ∀ (outs acc : List Nat), ∀ b ∈ acc,
              b ∈ outs.foldl (fun back op =>
                (g.parents op).foldl (backStep g heads si sb) back) acc := by
            intro outs
            induction outs with
            | nil => intro acc b hb; exact hb
            | cons o' outs ih3 =>
              intro acc b hb
              simp only [List.foldl_cons]
              exact ih3 _ b (foldl_step_mono g heads si sb _ _ b hb)
          exact Or.inr (Or.inr (Or.inr (Or.inl (mono outs _ p h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · exact ih _ op hop p hp
  intro op hop p hp
  exact key outs [] op hop p hp

/-- What `retirePlan` retires, put out in the terms of its definition. -/
theorem retirePlan_eq {g : Graph} {heads : List Nat} {watched : List Replaced} {found : List Nat}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : retirePlan g heads watched found = .retire out back kept n) :
    out = heads.filter (fun o =>
      ((watched.filter fun r => found.contains r.head).flatMap (·.put)).contains o) ∧
    back = backOf g heads ((watched.filter fun r => found.contains r.head).flatMap (·.images))
      ((watched.filter fun r => found.contains r.head).flatMap (·.put))
      (out.filter fun o =>
        !((watched.filter fun r => found.contains r.head).flatMap (·.images)).contains o) ∧
    kept = (watched.filter fun r => !found.contains r.head).map (fun r =>
        { r with put := r.put.filter (fun o => !out.contains o) ++
            back.filter (r.images.contains ·) }) ∧
    n = (watched.filter fun r => found.contains r.head).length := by
  unfold retirePlan at h
  simp only [Look.retire.injEq] at h
  obtain ⟨ho, hb, hk, hn⟩ := h
  exact ⟨ho.symm, by rw [← hb, ← ho], by rw [← hk, ← ho, ← hb], hn.symm⟩

/-- What `lookPlan` retiring says of the entries it retires: `stale`. -/
theorem retire_unpack {g : Graph} {heads : List Nat} {W : List Replaced}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : lookPlan g heads W = .retire out back kept n) :
    ∃ stale : List Replaced,
      (∀ r ∈ stale, r ∈ liveOf heads W) ∧ stale ≠ [] ∧ stale.length = n ∧
      kept.length + stale.length = (liveOf heads W).length ∧
      out = heads.filter (fun o => (stale.flatMap (·.put)).contains o) ∧
      back = backOf g heads (stale.flatMap (·.images)) (stale.flatMap (·.put))
        (out.filter fun o => !(stale.flatMap (·.images)).contains o) ∧
      (∀ w ∈ stale, ∃ r ∈ liveOf heads W, r.head = w.head ∧
        ∃ x ∈ besideOf heads (putOf (liveOf heads W)),
          g.known x = false ∧ g.fp x = r.fp ∧ x ≠ r.head) := by
  obtain ⟨hne, hl⟩ := lookPlan_retire h (by intro k hk; cases hk)
  obtain ⟨ho, hb, hk, hn⟩ := retirePlan_eq hl.symm
  have hfound : ∀ x, x ∈ rewritten g (liveOf heads W)
      (besideOf heads (putOf (liveOf heads W))) ↔ ∃ r ∈ liveOf heads W,
        r.head = x ∧ (besideOf heads (putOf (liveOf heads W))).any
            (fun y => !g.known y && g.fp y == r.fp && y != r.head) = true := by
    intro x
    simp only [rewritten, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨r, ⟨hr, hy⟩, rfl⟩; exact ⟨r, hr, rfl, hy⟩
    · rintro ⟨r, hr, rfl, hy⟩; exact ⟨r, ⟨hr, hy⟩, rfl⟩
  generalize hw : liveOf heads W = watched at *
  generalize hf : rewritten g watched (besideOf heads (putOf watched)) = found
    at *
  have hfound' : ∀ x, x ∈ found ↔ ∃ r ∈ watched, r.head = x ∧
      (besideOf heads (putOf watched)).any
        (fun y => !g.known y && g.fp y == r.fp && y != r.head) = true := by
    exact hfound
  refine ⟨watched.filter fun r => found.contains r.head, ?_, ?_, hn.symm, ?_, ho, hb, ?_⟩
  · intro r hr; exact (List.mem_filter.1 hr).1
  · intro hnil
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨r, hr, rfl, -⟩ := (hfound' x).1 hx
    have : r ∈ watched.filter (fun r' => found.contains r'.head) :=
      List.mem_filter.2 ⟨hr, List.contains_iff_mem.2 hx⟩
    rw [hnil] at this
    simp at this
  · rw [hk]
    simp only [List.length_map]
    have := List.length_eq_countP_add_countP (fun r : Replaced => found.contains r.head)
      (l := watched)
    simp only [List.countP_eq_length_filter] at this
    have e : (watched.filter fun r => !found.contains r.head) =
        watched.filter (fun a => decide ¬found.contains a.head = true) :=
      List.filter_congr (fun a _ => by simp)
    rw [e]
    omega
  · intro w hw
    obtain ⟨hwm, hwf⟩ := List.mem_filter.1 hw
    obtain ⟨r, hr, hrh, hany⟩ := (hfound' w.head).1 (List.contains_iff_mem.1 hwf)
    simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne,
      ne_eq] at hany
    obtain ⟨x, hx, ⟨hk, hfp⟩, hne⟩ := hany
    exact ⟨r, hr, hrh, x, hx, by simpa using hk, hfp, hne⟩

/-- Only op heads that musubi put in place of what it replaced are taken out. -/
theorem retire_out_put {g : Graph} {heads : List Nat} {W : List Replaced}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : lookPlan g heads W = .retire out back kept n) :
    ∀ o ∈ out, o ∈ heads ∧ o ∈ putOf (liveOf heads W) := by
  obtain ⟨stale, hs, -, -, -, ho, -⟩ := retire_unpack h
  intro o hmem
  rw [ho] at hmem
  obtain ⟨hh, hc⟩ := List.mem_filter.1 hmem
  obtain ⟨w, hw, hp⟩ := List.mem_flatMap.1 (List.contains_iff_mem.1 hc)
  exact ⟨hh, List.mem_flatMap.2 ⟨w, hs w hw, hp⟩⟩

/-- An op head stays beside what is taken out, so taking it out leaves an op head. -/
theorem retire_stay {g : Graph} {heads : List Nat} {W : List Replaced}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : lookPlan g heads W = .retire out back kept n) :
    ∃ s ∈ heads, s ∉ out ∧ s ∉ putOf (liveOf heads W) := by
  obtain ⟨stale, hs, hne, -, -, ho, -, hw⟩ := retire_unpack h
  obtain ⟨w, hw'⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨r, hr, -, x, hx, -⟩ := hw w hw'
  obtain ⟨hxh, hxp⟩ := List.mem_filter.1 hx
  have hxp' : x ∉ putOf (liveOf heads W) := by simpa using hxp
  refine ⟨x, hxh, fun hxo => hxp' ((retire_out_put h x hxo).2), hxp'⟩

/-- What is put back is not an op head. -/
theorem retire_back_new {g : Graph} {heads : List Nat} {W : List Replaced}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : lookPlan g heads W = .retire out back kept n) :
    ∀ b ∈ back, b ∉ heads := by
  obtain ⟨stale, -, -, -, -, ho, hb, -⟩ := retire_unpack h
  rw [hb]
  unfold backOf
  intro b hmem
  -- every element is added by a step that has checked `heads.contains`
  have step : ∀ (ps : List Nat) (acc : List Nat) (si sb : List Nat), (∀ b ∈ acc, b ∉ heads) →
      ∀ b ∈ ps.foldl (backStep g heads si sb) acc, b ∉ heads := by
    intro ps
    induction ps with
    | nil => intro acc si sb ha b hb; exact ha b hb
    | cons p ps ih =>
      intro acc si sb ha
      apply ih
      intro b hb
      rcases backStep_sub g heads si sb acc p b hb with hb | ⟨rfl, hp⟩
      · exact ha b hb
      · exact hp
  have outer : ∀ (outs acc : List Nat) (si sb : List Nat), (∀ b ∈ acc, b ∉ heads) →
      ∀ b ∈ outs.foldl (fun back op => (g.parents op).foldl (backStep g heads si sb) back) acc,
        b ∉ heads := by
    intro outs
    induction outs with
    | nil => intro acc si sb ha b hb; exact ha b hb
    | cons o outs ih =>
      intro acc si sb ha
      exact ih _ si sb (step _ acc si sb ha)
  exact outer _ [] _ _ (by simp) b hmem

/-- A merge or realization taken out, that wasn't on a rewrite, has each of its parents among
what is replaced, put back or still an op head, or on a rewrite itself. -/
theorem retire_back_covers {g : Graph} {heads : List Nat} {W : List Replaced}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : lookPlan g heads W = .retire out back kept n) :
    ∃ stale : List Replaced, (∀ r ∈ stale, r ∈ liveOf heads W) ∧
      ∀ o ∈ out, o ∉ stale.flatMap (·.images) → ∀ p ∈ g.parents o,
        p ∈ stale.flatMap (·.images) ∨ p ∈ stale.flatMap (·.put) ∨ p ∈ after heads out back ∨
          ∃ q ∈ g.parents p, q ∈ stale.flatMap (·.images) := by
  obtain ⟨stale, hs, -, -, -, ho, hb, -⟩ := retire_unpack h
  refine ⟨stale, hs, fun o hout hnimg p hp => ?_⟩
  have hcov := backOf_covers g heads (stale.flatMap (·.images)) (stale.flatMap (·.put))
    (out.filter fun o => !(stale.flatMap (·.images)).contains o) o
    (List.mem_filter.2 ⟨hout, by simpa using hnimg⟩) p hp
  rw [← hb] at hcov
  rcases hcov with h1 | h2 | h3 | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · -- an op head: still one, or one of those taken out, which are the replaced
    by_cases hpo : p ∈ out
    · exact Or.inr (Or.inl (by
        have := (List.mem_filter.1 (ho ▸ hpo)).2
        exact List.contains_iff_mem.1 this))
    · exact Or.inr (Or.inr (Or.inl (List.mem_append.2 (Or.inl (List.mem_filter.2
        ⟨h3, by simpa using hpo⟩)))))
  · exact Or.inr (Or.inr (Or.inl (List.mem_append.2 (Or.inr h4))))
  · exact Or.inr (Or.inr (Or.inr h5))

/-- What musubi watches after taking out is fewer than before: each look that retires
shrinks it. -/
theorem retire_shrinks {g : Graph} {heads : List Nat} {W : List Replaced}
    {out back : List Nat} {kept : List Replaced} {n : Nat}
    (h : lookPlan g heads W = .retire out back kept n) : kept.length < W.length := by
  obtain ⟨stale, hs, hne, -, hlen, -⟩ := retire_unpack h
  have : (liveOf heads W).length ≤ W.length := List.length_filter_le _ _
  have : 0 < stale.length := List.length_pos_iff.2 hne
  omega

/-- Nothing to do: what is watched is the live part, and nothing sits beside a rewrite. -/
theorem lookPlan_nothing_iff {g : Graph} {heads : List Nat} (W : List Replaced) :
    (∃ k, lookPlan g heads W = .nothing k) ↔ ¬ Overtaken g heads W := by
  rw [← rewritten_empty_iff W]
  unfold lookPlan
  simp only
  split
  · rename_i hemp
    simp only [List.isEmpty_iff] at hemp
    exact ⟨fun _ => hemp, fun _ => ⟨_, rfl⟩⟩
  · rename_i hne
    simp only [List.isEmpty_iff] at hne
    constructor
    · rintro ⟨k, hk⟩
      unfold retirePlan at hk
      cases hk
    · intro hemp; exact absurd hemp hne

/-- **Not below the op heads.** Whether a rewrite sits beside musubi's replacement depends on
the op heads' own fingerprints and whether the cache knows them, and on nothing below them: two
graphs that agree there agree whether there is one. -/
theorem overtaken_congr {g g' : Graph} {heads : List Nat} {W : List Replaced}
    (hk : ∀ x ∈ heads, g'.known x = g.known x) (hf : ∀ x ∈ heads, g'.fp x = g.fp x) :
    Overtaken g' heads W ↔ Overtaken g heads W := by
  have one : ∀ {g g' : Graph}, (∀ x ∈ heads, g'.known x = g.known x) →
      (∀ x ∈ heads, g'.fp x = g.fp x) → Overtaken g' heads W → Overtaken g heads W := by
    intro g g' hk hf ⟨w, hw, x, hx, hkn, hfp, hne⟩
    have hxh := (List.mem_filter.1 hx).1
    exact ⟨w, hw, x, hx, by rw [← hk x hxh]; exact hkn, by rw [← hf x hxh]; exact hfp, hne⟩
  exact ⟨one hk hf, one (fun x hx => (hk x hx).symm) (fun x hx => (hf x hx).symm)⟩

/-- So the decision to take something out (`lookPlan` answering something other than nothing)
is the same on two graphs that agree on the op heads. -/
theorem lookPlan_nothing_congr {g g' : Graph} {heads : List Nat} (W : List Replaced)
    (hk : ∀ x ∈ heads, g'.known x = g.known x) (hf : ∀ x ∈ heads, g'.fp x = g.fp x) :
    (∃ k, lookPlan g' heads W = .nothing k) ↔ ∃ k, lookPlan g heads W = .nothing k := by
  rw [lookPlan_nothing_iff, lookPlan_nothing_iff]
  exact not_congr (overtaken_congr hk hf)

/-- What is watched when nothing is to do. -/
theorem lookPlan_nothing {g : Graph} {heads : List Nat} {W : List Replaced}
    {k : List Replaced} (h : lookPlan g heads W = .nothing k) : k = liveOf heads W := by
  unfold lookPlan at h
  simp only at h
  split at h
  · cases h; rfl
  · unfold retirePlan at h; cases h

/-! ## Taking out until nothing is left -/

/-- A look that retires, as often as it does, from `heads` and the watch, at most `n` times. -/
def settle (g : Graph) : Nat → List Nat → List Replaced → List Nat × List Replaced
  | 0, heads, W => (heads, W)
  | n + 1, heads, W =>
    match lookPlan g heads W with
    | .nothing k => (heads, k)
    | .retire out back kept _ => settle g n (after heads out back) kept

theorem liveOf_liveOf (heads : List Nat) (W : List Replaced) :
    liveOf heads (liveOf heads W) = liveOf heads W := by
  unfold liveOf
  rw [List.filter_filter]
  exact List.filter_congr (fun a _ => by simp)

theorem lookPlan_live (g : Graph) (heads : List Nat) (W : List Replaced) :
    lookPlan g heads (liveOf heads W) = lookPlan g heads W := by
  unfold lookPlan
  simp only [liveOf_liveOf]

/-- Taking out until nothing is to do ends, in as many looks as there are entries. -/
theorem settle_nothing (g : Graph) :
    ∀ n heads W, W.length < n →
      ∃ k, lookPlan g (settle g n heads W).1 (settle g n heads W).2 = .nothing k := by
  intro n
  induction n with
  | zero => intro heads W h; omega
  | succ n ih =>
    intro heads W hlen
    simp only [settle]
    cases hl : lookPlan g heads W with
    | nothing k =>
      simp only
      have hk := lookPlan_nothing hl
      refine ⟨k, ?_⟩
      rw [hk, lookPlan_live, hl, hk]
    | retire out back kept m =>
      simp only
      apply ih
      have := retire_shrinks hl
      omega

end Retire

/-! ## What musubi remembers of a move -/

/-- The op heads of `read` that a move to `new` takes out. -/
def oldOf (read new : List Nat) : List Nat := read.filter fun h => !new.contains h

/-- `plan::entries`: for each op head taken out, what `new` puts in its place:
its images among `new`, and what else of `new` is on them. Only operations of `new` that
weren't read, which musubi made, count. `from_` says what each head became. -/
def entries (g : Graph) (read new : List Nat) (from_ : List (Nat × List Nat)) : List Replaced :=
  let fresh := (new.filter fun o => !read.contains o).eraseDups
  (oldOf read new).filterMap fun h =>
    let images := (from_.lookup h).getD []
    let put := fresh.filter fun op => images.contains op || (g.parents op).any (images.contains ·)
    if put.isEmpty then none else some { head := h, fp := g.fp h, images, put }

theorem entries_put {g : Graph} {read new : List Nat} {from_ : List (Nat × List Nat)} :
    ∀ w ∈ entries g read new from_, w.head ∈ read ∧ w.head ∉ new ∧
      ∀ o ∈ w.put, o ∈ new ∧ o ∉ read := by
  intro w hw
  unfold entries at hw
  obtain ⟨h, hh, hw⟩ := List.mem_filterMap.1 hw
  have hh' := List.mem_filter.1 hh
  simp only at hw
  split at hw
  · cases hw
  · cases hw
    refine ⟨hh'.1, by simpa using hh'.2, fun o ho => ?_⟩
    simp only [List.mem_filter, List.mem_eraseDups] at ho
    obtain ⟨⟨hn, hr⟩, -⟩ := ho
    exact ⟨hn, by simpa using hr⟩

/-- Of an op head taken out again, its entry with those that replaced it. -/
def swapIn (ops : List Nat) (now : Replaced) (with_ : List Nat) : List Nat :=
  if ops.contains now.head then (ops.filter (· != now.head) ++ with_).eraseDups else ops

def composeOne (e now : Replaced) : Replaced :=
  { e with images := swapIn e.images now now.images, put := swapIn e.put now now.put }

/-- `plan::compose`, for `Records::watch_replaced`: watches `E`, which musubi has just taken out; where one is itself
what musubi put in place of one it watches already, what replaced it takes its place there too. -/
def compose (W E : List Replaced) : List Replaced :=
  if E.isEmpty then W else W.map (fun e => E.foldl composeOne e) ++ E

theorem swapIn_sub {P : Nat → Prop} {ops with_ : List Nat} {now : Replaced}
    (h1 : ∀ o ∈ ops, P o) (h2 : ∀ o ∈ with_, P o) : ∀ o ∈ swapIn ops now with_, P o := by
  intro o ho
  unfold swapIn at ho
  split at ho
  · have := (List.mem_eraseDups).1 ho
    rcases List.mem_append.1 this with h | h
    · exact h1 o (List.mem_filter.1 h).1
    · exact h2 o h
  · exact h1 o ho

/-- Entries made of operations that satisfy `P`, composed with more, are too. -/
theorem compose_put {P : Nat → Prop} {W E : List Replaced}
    (hW : ∀ w ∈ W, (∀ o ∈ w.put, P o) ∧ (∀ o ∈ w.images, P o))
    (hE : ∀ w ∈ E, (∀ o ∈ w.put, P o) ∧ (∀ o ∈ w.images, P o)) :
    ∀ w ∈ compose W E, (∀ o ∈ w.put, P o) ∧ (∀ o ∈ w.images, P o) := by
  intro w hw
  unfold compose at hw
  split at hw
  · exact hW w hw
  · rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hw
      have key : ∀ (E : List Replaced), (∀ w ∈ E, (∀ o ∈ w.put, P o) ∧ (∀ o ∈ w.images, P o)) →
          ∀ e : Replaced, ((∀ o ∈ e.put, P o) ∧ (∀ o ∈ e.images, P o)) →
          (∀ o ∈ (E.foldl composeOne e).put, P o) ∧ (∀ o ∈ (E.foldl composeOne e).images, P o) := by
        intro E
        induction E with
        | nil => intro _ e he; exact he
        | cons now E ih =>
          intro hE e he
          apply ih (fun w hw => hE w (List.mem_cons_of_mem _ hw))
          obtain ⟨hnow1, hnow2⟩ := hE now List.mem_cons_self
          exact ⟨swapIn_sub he.1 hnow1, swapIn_sub he.2 hnow2⟩
      exact key E hE e (hW e he)
    · exact hE w hw

end Musubi.OpHeads

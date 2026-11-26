/-
A copy's display name apart from its key (design.md, "Which workspaces are this machine's own";
`workspaces.rs`).

A copy's key is `name#suffix`, and stays the copy's for good: leaving and joining again keeps
it, and only `--fresh`, which drops the history the key worked in, takes a new one. The name
inside the key is only the copy's initial name. A daemon records the copy's name as `musubi.name` on an operation that is the copy's
work (`musubi.work = <key>`), whenever the machine's `musubi.machine-name` differs from the
name the copy has; and an operation names only the copies present there, by their names as of
that operation.

1. **Name records** (`NHist`). An operation that is a copy's work may record its name. A
   copy's name at `x` is the greatest name its latest records in `anc*(x)` give, or its initial
   name (the one its key embeds) where it has recorded none (`NameIs`). Forgets don't touch
   names. Proved: every machine agrees (`nameIs_unique`, `nameIs_exists`, `nameIs_local`);
   merging the same records in any order or grouping gives the same name (`nameIs_congr`); a
   record names its copy so from there on, until a later record (`rename_sticks`); and a
   rename is work, so it makes its copy present (`rename_present`).

2. **Naming among present copies** (`assign`, `localName`). `Names.lean`'s candidates, over
   copies given as identities with a name and a suffix each, rather than as `name#suffix`
   keys: two copies may share both a name and a suffix once one renames, and still differ.
   Where present copies share a name, the one present under it longest keeps it plain
   (`wins`): by the generation of its latest mark, the later of its latest name record and its
   latest return (`SinceIs`), then by key. Generations respect ancestry, so a claim made after
   another's mark always loses to it; concurrent claims fall back to key order where their
   generations are equal, and to generation otherwise, since ancestry alone orders claims only
   partly. Proved: naming is injective on a view's keys (`localName_injective`); every machine
   agrees on the labels at an operation, a function of its history alone (`sinceIs_local`,
   `naming_local`, with `Presence.present_local` and `nameIs_local`); and a copy that stays
   present under an unchanged name keeps its label across another copy's rename, leave or
   return (`keeps_label`, from `winner_label`, `later_mark` and `since_stable`). Nothing
   remembers a forgotten copy, nor a name a copy had before. The examples at the end show a
   name freed by a rename and taken by another copy, and why a name in a view `jj undo` brings
   back must be read by the naming of the operation that view came from (`resolve_at_origin`),
   not by today's.

3. **Leaving and joining again under one key** (`Rejoin`). `Presence.leave_sticks` assumes
   that the key does no later work. With one key for good it becomes
   `leave_sticks_until_rejoin`: the copy is absent from the leave's forget on until work it
   pushes after joining again, which brings it back (`rejoin_returns`). A command that started
   before the leave and ended after it is that copy's work too, and needs no forgetting
   (`late_work_same_key`). `Copies.Detach` models the files leaving and joining again write.

`PresenceExec.lean` computes names and how long each copy has held its name on a finite
history, for the oracle, and `crates/musubi-jj/src/presence.rs` keeps them as presence does.
Names in part 1 are numbers ordered as the names they stand for; the tie-break needs only some
total order on names that every machine shares.
-/
import Musubi.Presence
import Musubi.Names

namespace Musubi.Identity

open Musubi.Presence

/-! ## 1. Name records -/

/-- A hive's history, with the names copies record for themselves: `named x k = some n` says
operation `x` records `n` as copy `k`'s name. -/
structure NHist extends Hist where
  named : Nat → Nat → Option Nat

namespace NHist

variable (h : NHist)

/-- Recording a name is work by the copy named: `musubi.work = <key>` and `musubi.name`. -/
def RecordsAreWork : Prop := ∀ x k, (h.named x k).isSome → h.work x k

/-- `m` is a latest record of `k`'s name in `anc*(x)`: no other record of it there follows. -/
def LatestRec (x k m : Nat) : Prop :=
  Anc h.par m x ∧ (h.named m k).isSome ∧
    ∀ m', Anc h.par m' x → (h.named m' k).isSome → Anc h.par m m' → m' = m

/-- `k`'s name at `x` is `n`: the greatest name among its latest records there, or, where it has
recorded none, its initial name, the name its key embeds (`init`). Forgets play no part: a
forgotten copy that comes back keeps its name. -/
def NameIs (init : Nat → Nat) (x k n : Nat) : Prop :=
  (∃ m, h.LatestRec x k m ∧ h.named m k = some n ∧
      ∀ m' n', h.LatestRec x k m' → h.named m' k = some n' → n' ≤ n) ∨
    ((∀ m, Anc h.par m x → h.named m k = none) ∧ n = init k)

theorem isSome_of_eq {o : Option Nat} {n : Nat} (e : o = some n) : o.isSome := by
  rw [e]; rfl

/-- Every machine that has `x` gives `k` one name there. -/
theorem nameIs_unique {init : Nat → Nat} {x k n n' : Nat} (h₁ : h.NameIs init x k n)
    (h₂ : h.NameIs init x k n') : n = n' := by
  rcases h₁ with ⟨m, hm, hn, hmax⟩ | ⟨hnone, rfl⟩ <;>
    rcases h₂ with ⟨m', hm', hn', hmax'⟩ | ⟨hnone', rfl⟩
  · exact Nat.le_antisymm (hmax' m n hm hn) (hmax m' n' hm' hn')
  · have := hnone' m hm.1; rw [hn] at this; exact absurd this (by simp)
  · have := hnone m' hm'.1; rw [hn'] at this; exact absurd this (by simp)
  · rfl

/-- The largest of `f 0, …, f b`. -/
def maxUpTo (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | b + 1 => max (maxUpTo f b) (f (b + 1))

theorem le_maxUpTo (f : Nat → Nat) : ∀ {b m : Nat}, m ≤ b → f m ≤ maxUpTo f b
  | 0, m, hm => by
    have : m = 0 := by omega
    subst this; exact Nat.le_refl _
  | b + 1, m, hm => by
    by_cases e : m = b + 1
    · subst e; exact Nat.le_max_right _ _
    · exact Nat.le_trans (le_maxUpTo f (b := b) (by omega)) (Nat.le_max_left _ _)

/-- A record of `k` latest by its id is a latest record. -/
theorem latest_of_max (hlt : ParLt h.par) {x k m : Nat} (hm : Anc h.par m x)
    (hr : (h.named m k).isSome) (hmax : ∀ m', Anc h.par m' x → (h.named m' k).isSome → m' ≤ m) :
    h.LatestRec x k m :=
  ⟨hm, hr, fun m' hm'x hr' hmm' => Nat.le_antisymm (hmax m' hm'x hr') (hmm'.le hlt)⟩

/-- Every operation gives every copy a name. -/
theorem nameIs_exists (hlt : ParLt h.par) (init : Nat → Nat) (x k : Nat) :
    ∃ n, h.NameIs init x k n := by
  by_cases hany : ∃ m, Anc h.par m x ∧ (h.named m k).isSome
  · -- Some latest record exists; among the latest records, take one naming the greatest name.
    obtain ⟨a, ha, har⟩ := hany
    obtain ⟨m₀, ⟨hm₀x, hm₀r⟩, hmax₀⟩ := Musubi.exists_max_le
      (Q := fun m => Anc h.par m x ∧ (h.named m k).isSome) ⟨ha, har⟩ (fun m hm => hm.1.le hlt)
    have hl₀ := h.latest_of_max hlt hm₀x hm₀r (fun m' h₁ h₂ => hmax₀ m' ⟨h₁, h₂⟩)
    let f : Nat → Nat := fun m => (h.named m k).getD 0
    have hbound : ∀ n, (∃ m, h.LatestRec x k m ∧ h.named m k = some n) → n ≤ maxUpTo f x := by
      rintro n ⟨m, hm, hmn⟩
      have := le_maxUpTo f (hm.1.le hlt)
      simp only [f, hmn, Option.getD_some] at this
      exact this
    obtain ⟨n₀, hn₀⟩ : ∃ n, h.named m₀ k = some n := Option.isSome_iff_exists.mp hm₀r
    obtain ⟨n, ⟨m, hm, hmn⟩, hnmax⟩ := Musubi.exists_max_le
      (Q := fun n => ∃ m, h.LatestRec x k m ∧ h.named m k = some n) ⟨m₀, hl₀, hn₀⟩ hbound
    exact ⟨n, Or.inl ⟨m, hm, hmn, fun m' n' hm' hn' => hnmax n' ⟨m', hm', hn'⟩⟩⟩
  · refine ⟨init k, Or.inr ⟨fun m hm => ?_, rfl⟩⟩
    cases e : h.named m k with
    | none => rfl
    | some _ => exact absurd ⟨m, hm, by rw [e]; rfl⟩ hany

/-- Operations whose histories hold the same records of `k`'s name agree on it: merges of the
same heads, in any order or grouping. -/
theorem nameIs_congr {init : Nat → Nat} {x y k n : Nat}
    (hxy : ∀ a, (h.named a k).isSome → (Anc h.par a x ↔ Anc h.par a y)) :
    h.NameIs init x k n ↔ h.NameIs init y k n := by
  have hl : ∀ m, h.LatestRec x k m ↔ h.LatestRec y k m := fun m =>
    ⟨fun ⟨hm, hr, hmax⟩ =>
      ⟨(hxy m hr).1 hm, hr, fun m' hm' hr' => hmax m' ((hxy m' hr').2 hm') hr'⟩,
     fun ⟨hm, hr, hmax⟩ =>
      ⟨(hxy m hr).2 hm, hr, fun m' hm' hr' => hmax m' ((hxy m' hr').1 hm') hr'⟩⟩
  have hnone : (∀ m, Anc h.par m x → h.named m k = none) ↔
      (∀ m, Anc h.par m y → h.named m k = none) := by
    constructor
    · intro hn m hm
      cases e : h.named m k with
      | none => rfl
      | some _ =>
        have := hn m ((hxy m (isSome_of_eq e)).2 hm)
        rw [e] at this; exact absurd this (by simp)
    · intro hn m hm
      cases e : h.named m k with
      | none => rfl
      | some _ =>
        have := hn m ((hxy m (isSome_of_eq e)).1 hm)
        rw [e] at this; exact absurd this (by simp)
  unfold NameIs
  rw [hnone]
  constructor
  · rintro (⟨m, hm, hn, hmax⟩ | hb)
    · exact Or.inl ⟨m, (hl m).1 hm, hn, fun m' n' hm' hn' => hmax m' n' ((hl m').2 hm') hn'⟩
    · exact Or.inr hb
  · rintro (⟨m, hm, hn, hmax⟩ | hb)
    · exact Or.inl ⟨m, (hl m).2 hm, hn, fun m' n' hm' hn' => hmax m' n' ((hl m').1 hm') hn'⟩
    · exact Or.inr hb

/-- A copy's name at `x` depends only on `x`'s history: two histories that agree there, as every
machine that has `x` does, agree on it. -/
theorem nameIs_local (h₁ h₂ : NHist) {init : Nat → Nat} {x k n : Nat}
    (hpar : ∀ b, Anc h₁.par b x → h₁.par b = h₂.par b)
    (hrec : ∀ b, Anc h₁.par b x → h₁.named b k = h₂.named b k) :
    h₁.NameIs init x k n ↔ h₂.NameIs init x k n := by
  have hanc : ∀ a, Anc h₁.par a x ↔ Anc h₂.par a x := fun _ => anc_local hpar
  have hanc' : ∀ f, Anc h₁.par f x → ∀ a, (Anc h₁.par a f ↔ Anc h₂.par a f) :=
    fun f hfx _ => anc_local (fun b hb => hpar b (Anc.trans hb hfx))
  have hl : ∀ m, h₁.LatestRec x k m ↔ h₂.LatestRec x k m := by
    intro m
    constructor
    · rintro ⟨hm, hr, hmax⟩
      refine ⟨(hanc m).1 hm, by rw [← hrec m hm]; exact hr, fun m' hm' hr' hmm' => ?_⟩
      have hm'₁ := (hanc m').2 hm'
      exact hmax m' hm'₁ (by rw [hrec m' hm'₁]; exact hr') ((hanc' m' hm'₁ m).2 hmm')
    · rintro ⟨hm, hr, hmax⟩
      have hm₁ := (hanc m).2 hm
      refine ⟨hm₁, by rw [hrec m hm₁]; exact hr, fun m' hm' hr' hmm' => ?_⟩
      exact hmax m' ((hanc m').1 hm') (by rw [← hrec m' hm']; exact hr') ((hanc' m' hm' m).1 hmm')
  have hrecl : ∀ m n, h₁.LatestRec x k m → (h₁.named m k = some n ↔ h₂.named m k = some n) :=
    fun m n hm => by rw [hrec m hm.1]
  unfold NameIs
  constructor
  · rintro (⟨m, hm, hn, hmax⟩ | ⟨hnone, hi⟩)
    · refine Or.inl ⟨m, (hl m).1 hm, (hrecl m n hm).1 hn, fun m' n' hm' hn' => ?_⟩
      have hm'₁ := (hl m').2 hm'
      exact hmax m' n' hm'₁ ((hrecl m' n' hm'₁).2 hn')
    · refine Or.inr ⟨fun m hm => ?_, hi⟩
      have hm₁ := (hanc m).2 hm
      rw [← hrec m hm₁]; exact hnone m hm₁
  · rintro (⟨m, hm, hn, hmax⟩ | ⟨hnone, hi⟩)
    · have hm₁ := (hl m).2 hm
      refine Or.inl ⟨m, hm₁, (hrecl m n hm₁).2 hn, fun m' n' hm' hn' => ?_⟩
      exact hmax m' n' ((hl m').1 hm') ((hrecl m' n' hm').1 hn')
    · refine Or.inr ⟨fun m hm => ?_, hi⟩
      rw [hrec m hm]; exact hnone m ((hanc m).1 hm)

/-- A record names its copy so wherever it is in the history with no record of the copy's name
after it: in particular at the record itself, and on a machine that was offline across it, once
it has it. -/
theorem rename_sticks (hlt : ParLt h.par) {init : Nat → Nat} {r x k n : Nat}
    (hr : h.named r k = some n) (hrx : Anc h.par r x)
    (hlast : ∀ m, Anc h.par m x → (h.named m k).isSome → Anc h.par m r) :
    h.NameIs init x k n := by
  have hl : h.LatestRec x k r :=
    ⟨hrx, isSome_of_eq hr, fun m' hm' hr' hrm' => Anc.antisymm hlt (hlast m' hm' hr') hrm'⟩
  refine Or.inl ⟨r, hl, hr, fun m' n' hm' hn' => ?_⟩
  have : m' = r := Eq.symm <| hm'.2.2 r hrx (isSome_of_eq hr) (hlast m' hm'.1 hm'.2.1)
  subst this
  rw [hr] at hn'
  exact Nat.le_of_eq (Option.some.inj hn').symm

theorem record_names (hlt : ParLt h.par) {init : Nat → Nat} {r k n : Nat}
    (hr : h.named r k = some n) : h.NameIs init r k n :=
  h.rename_sticks hlt hr Anc.refl (fun _ hm _ => hm)

/-- Renaming is the copy's work, so it shows the copy again if the hive had forgotten it, as
recording its `forget-after` does. -/
theorem rename_present (hlt : ParLt h.par) (hwf : h.WellFormed) (hrw : h.RecordsAreWork)
    {r k n : Nat} (hr : h.named r k = some n) : h.Present r k :=
  h.work_present hlt hwf (hrw r k (isSome_of_eq hr))

/-! ### How long a copy has been present under its name -/

/-- `e` is a return of `k`: its work, made where `k` was absent just before: its join, or its
first work after a forget that saw all its work before. -/
def Return (e k : Nat) : Prop := h.work e k ∧ ¬ h.PresentIn (h.Below e) k

/-- `e` marks when `k` came to be present under its name: a record of its name, or a return. -/
def Mark (e k : Nat) : Prop := (h.named e k).isSome ∨ h.Return e k

/-- Generation numbers, as the implementation keeps them: above every ancestor's. -/
def GenMono (gen : Nat → Nat) : Prop := ∀ a x, Anc h.par a x → a ≠ x → gen a < gen x

/-- `k` has been present under its name at `x` since generation `s`: the latest of its marks
there, the later of its latest name record and its latest return. -/
def SinceIs (gen : Nat → Nat) (x k s : Nat) : Prop :=
  ∃ e, Anc h.par e x ∧ h.Mark e k ∧ gen e = s ∧
    ∀ e', Anc h.par e' x → h.Mark e' k → gen e' ≤ s

theorem sinceIs_unique {gen : Nat → Nat} {x k s s' : Nat} (h₁ : h.SinceIs gen x k s)
    (h₂ : h.SinceIs gen x k s') : s = s' := by
  obtain ⟨e, he, hm, rfl, hmax⟩ := h₁
  obtain ⟨e', he', hm', rfl, hmax'⟩ := h₂
  exact Nat.le_antisymm (hmax' e he hm) (hmax e' he' hm')

theorem sinceIs_exists (hlt : ParLt h.par) (gen : Nat → Nat) {x k : Nat}
    (hm : ∃ e, Anc h.par e x ∧ h.Mark e k) : ∃ s, h.SinceIs gen x k s := by
  obtain ⟨e₀, he₀, hm₀⟩ := hm
  obtain ⟨s, ⟨e, he, hme, rfl⟩, hmax⟩ := Musubi.exists_max_le
    (Q := fun s => ∃ e, Anc h.par e x ∧ h.Mark e k ∧ gen e = s) ⟨e₀, he₀, hm₀, rfl⟩
    (fun _ ⟨e, he, _, hs⟩ => hs ▸ le_maxUpTo gen (he.le hlt))
  exact ⟨gen e, e, he, hme, rfl, fun e' he' hm' => hmax _ ⟨e', he', hm', rfl⟩⟩

/-- A copy present at `x` has a mark there: its earliest work in `x`'s history returned it. -/
theorem mark_of_present (hlt : ParLt h.par) {x k : Nat} (hp : h.Present x k) :
    ∃ e, Anc h.par e x ∧ h.Mark e k := by
  obtain ⟨w, hw, hW, _⟩ := hp
  obtain ⟨m, ⟨hm, hmW⟩, hmin⟩ :=
    Musubi.exists_min (fun m => Anc h.par m x ∧ h.work m k) ⟨hw, hW⟩
  refine ⟨m, hm, Or.inr ⟨hmW, fun ⟨w', hb, hW', _⟩ => ?_⟩⟩
  obtain ⟨p, hp, hw'p⟩ := hb
  have hlt' : w' < m := Nat.lt_of_le_of_lt (hw'p.le hlt) (hlt m p hp)
  exact hmin w' hlt' ⟨Anc.trans (h.below_anc ⟨p, hp, hw'p⟩) hm, hW'⟩

/-- A copy that neither recorded a name nor returned between `y` and `x` has been present under
its name since the same generation at both. -/
theorem since_stable {gen : Nat → Nat} {y x k s : Nat} (hyx : Anc h.par y x)
    (hnew : ∀ e, Anc h.par e x → h.Mark e k → Anc h.par e y) :
    h.SinceIs gen y k s ↔ h.SinceIs gen x k s := by
  constructor
  · rintro ⟨e, he, hm, hs, hmax⟩
    exact ⟨e, Anc.trans he hyx, hm, hs, fun e' he' hm' => hmax e' (hnew e' he' hm') hm'⟩
  · rintro ⟨e, he, hm, hs, hmax⟩
    exact ⟨e, hnew e he hm, hm, hs, fun e' he' hm' => hmax e' (Anc.trans he' hyx) hm'⟩

/-- A copy that came to its name, by a rename or a return, after another copy's mark `o` has
been present under it for less time. -/
theorem later_mark {gen : Nat → Nat} (hg : h.GenMono gen) {x b o e sb : Nat}
    (he : Anc h.par e x) (hm : h.Mark e b) (hoe : Anc h.par o e) (hne : o ≠ e)
    (hsb : h.SinceIs gen x b sb) : gen o < sb := by
  obtain ⟨_, _, _, rfl, hmax⟩ := hsb
  exact Nat.lt_of_lt_of_le (hg o e hoe hne) (hmax e he hm)

end NHist

/-- `PresentIn (Below e)` depends only on `e`'s history. -/
theorem presentIn_below_local (h₁ h₂ : Hist) {e k : Nat}
    (hpar : ∀ b, Anc h₁.par b e → h₁.par b = h₂.par b)
    (hw : ∀ b, Anc h₁.par b e → (h₁.work b k ↔ h₂.work b k))
    (hfg : ∀ b, Anc h₁.par b e → (h₁.forget b k ↔ h₂.forget b k)) :
    h₁.PresentIn (h₁.Below e) k ↔ h₂.PresentIn (h₂.Below e) k := by
  have hparE : h₁.par e = h₂.par e := hpar e Anc.refl
  have hbelow : ∀ a, h₁.Below e a ↔ h₂.Below e a := by
    intro a
    constructor
    · rintro ⟨p, hp, hA⟩
      refine ⟨p, hparE ▸ hp, (anc_local (fun b hb => hpar b (Anc.trans hb (Anc.parent hp)))).1 hA⟩
    · rintro ⟨p, hp, hA⟩
      have hp₁ : p ∈ h₁.par e := hparE ▸ hp
      exact ⟨p, hp₁, (anc_local (fun b hb => hpar b (Anc.trans hb (Anc.parent hp₁)))).2 hA⟩
  have hanc' : ∀ f, h₁.Below e f → ∀ a, (Anc h₁.par a f ↔ Anc h₂.par a f) :=
    fun f hf _ => anc_local (fun b hb => hpar b (Anc.trans hb (h₁.below_anc hf)))
  constructor
  · rintro ⟨w, hb, hW, hn⟩
    refine ⟨w, (hbelow w).1 hb, (hw w (h₁.below_anc hb)).1 hW, ?_⟩
    rintro ⟨f, hf, hF, hA⟩
    have hf₁ := (hbelow f).2 hf
    exact hn ⟨f, hf₁, (hfg f (h₁.below_anc hf₁)).2 hF, (hanc' f hf₁ w).2 hA⟩
  · rintro ⟨w, hb, hW, hn⟩
    have hb₁ := (hbelow w).2 hb
    refine ⟨w, hb₁, (hw w (h₁.below_anc hb₁)).2 hW, ?_⟩
    rintro ⟨f, hf, hF, hA⟩
    exact hn ⟨f, (hbelow f).1 hf, (hfg f (h₁.below_anc hf)).1 hF, (hanc' f hf w).1 hA⟩

/-- How long a copy has held its name at `x` depends only on `x`'s history. -/
theorem sinceIs_local (h₁ h₂ : NHist) {gen : Nat → Nat} {x k s : Nat}
    (hpar : ∀ b, Anc h₁.par b x → h₁.par b = h₂.par b)
    (hw : ∀ b, Anc h₁.par b x → (h₁.work b k ↔ h₂.work b k))
    (hfg : ∀ b, Anc h₁.par b x → (h₁.forget b k ↔ h₂.forget b k))
    (hrec : ∀ b, Anc h₁.par b x → h₁.named b k = h₂.named b k) :
    h₁.SinceIs gen x k s ↔ h₂.SinceIs gen x k s := by
  have hanc : ∀ a, Anc h₁.par a x ↔ Anc h₂.par a x := fun _ => anc_local hpar
  have hmark : ∀ e, Anc h₁.par e x → (h₁.Mark e k ↔ h₂.Mark e k) := by
    intro e he
    have hb := presentIn_below_local h₁.toHist h₂.toHist (e := e) (k := k)
      (fun b hb => hpar b (Anc.trans hb he)) (fun b hb => hw b (Anc.trans hb he))
      (fun b hb => hfg b (Anc.trans hb he))
    unfold NHist.Mark NHist.Return
    rw [hrec e he, hw e he]
    exact or_congr Iff.rfl (and_congr Iff.rfl (not_congr hb))
  constructor
  · rintro ⟨e, he, hm, hs, hmax⟩
    refine ⟨e, (hanc e).1 he, (hmark e he).1 hm, hs, fun e' he' hm' => ?_⟩
    have he'₁ := (hanc e').2 he'
    exact hmax e' he'₁ ((hmark e' he'₁).2 hm')
  · rintro ⟨e, he, hm, hs, hmax⟩
    have he₁ := (hanc e).2 he
    refine ⟨e, he₁, (hmark e he₁).2 hm, hs, fun e' he' hm' => ?_⟩
    exact hmax e' ((hanc e').1 he') ((hmark e' he').1 hm')

/-! ## 2. Naming among present copies

`Names.lean`'s choice, over copies of any type `α`, each with its name now (`nm`), its key's
suffix (`sfx`), and its priority (`pri`): how long it has been present under its name, then its
key. `Names.lean` takes a copy to be its `name#suffix` key, so that two copies differ in name
or suffix; once names change, two copies can share both (`a#1a2b3c4d` and `b#1a2b3c4d` both
renamed `x`), and naming must still tell them apart.

Among copies that share a name, the one present under it longest keeps the plain name
(`wins`): the earliest by `SinceIs`, then by key. Copies that keep their plain names are named
first, then the rest, each taking the first of `Names.candidates` that is free, as today. -/

namespace Naming

open Names (Str)

variable {α : Type} [DecidableEq α]

/-- What `Names.candidates` sees of copy `a`: its name now, and its key's suffix. -/
def keyOf (nm sfx : α → Str) (a : α) : Names.Key := ⟨nm a, sfx a⟩

/-- Lexicographic order on priorities: generation since, then key. -/
def lexLt (p q : Nat × Nat) : Bool := p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)

theorem lexLt_asymm {p q : Nat × Nat} (h₁ : lexLt p q = true) (h₂ : lexLt q p = true) :
    False := by
  simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h₁ h₂
  omega

/-- Copy `a` keeps its plain name: every other copy named alike came to the name after it, or
as long ago with a later key. -/
def wins (nm : α → Str) (pri : α → Nat × Nat) (ms : List α) (a : α) : Bool :=
  ms.all fun b => b == a || nm b != nm a || lexLt (pri a) (pri b)

/-- Copies that keep their plain names first, then the rest. -/
def order (nm : α → Str) (pri : α → Nat × Nat) (ms : List α) : List α :=
  ms.filter (wins nm pri ms) ++ ms.filter (fun a => !wins nm pri ms a)

theorem mem_order {nm : α → Str} {pri : α → Nat × Nat} {ms : List α} {a : α} (ha : a ∈ ms) :
    a ∈ order nm pri ms := by
  unfold order
  cases hw : wins nm pri ms a
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨ha, by simp [hw]⟩)
  · exact List.mem_append_left _ (List.mem_filter.mpr ⟨ha, hw⟩)

/-- `display_names`, as `Names.assignFrom`, with whether each copy may take its plain name
given (`plain`). -/
def assignFrom (nm sfx : α → Str) (plain : α → Bool) (own : List Str) :
    List (α × Str) → List α → List (α × Str)
  | acc, [] => acc
  | acc, a :: as =>
    assignFrom nm sfx plain own
      (acc ++ [(a, Names.choose own (acc.map (·.2)) (plain a) (keyOf nm sfx a))]) as

def assign (nm sfx : α → Str) (pri : α → Nat × Nat) (ms : List α) (own : List Str) :
    List (α × Str) :=
  assignFrom nm sfx (wins nm pri ms) own [] (order nm pri ms)

def Good (own : List Str) (acc : List (α × Str)) : Prop :=
  (acc.map (·.2)).Nodup ∧ ∀ p ∈ acc.map (·.2), Names.taken own p = false

omit [DecidableEq α] in
theorem assignFrom_append (nm sfx : α → Str) (plain : α → Bool) (own : List Str) :
    ∀ (as bs : List α) (acc : List (α × Str)),
      assignFrom nm sfx plain own acc (as ++ bs) =
        assignFrom nm sfx plain own (assignFrom nm sfx plain own acc as) bs
  | [], _, _ => rfl
  | _ :: as, bs, _ => assignFrom_append nm sfx plain own as bs _

omit [DecidableEq α] in
theorem assignFrom_extends (nm sfx : α → Str) (plain : α → Bool) (own : List Str) :
    ∀ (as : List α) (acc : List (α × Str)),
      ∃ rest, assignFrom nm sfx plain own acc as = acc ++ rest
  | [], acc => ⟨[], by simp [assignFrom]⟩
  | a :: as, acc => by
    obtain ⟨rest, h⟩ := assignFrom_extends nm sfx plain own as (acc ++ [(a, Names.choose own
      (acc.map (·.2)) (plain a) (keyOf nm sfx a))])
    refine ⟨(a, Names.choose own (acc.map (·.2)) (plain a) (keyOf nm sfx a)) :: rest, ?_⟩
    rw [show assignFrom nm sfx plain own acc (a :: as) = assignFrom nm sfx plain own
      (acc ++ [(a, Names.choose own (acc.map (·.2)) (plain a) (keyOf nm sfx a))]) as from rfl, h]
    simp

omit [DecidableEq α] in
theorem assignFrom_map_fst (nm sfx : α → Str) (plain : α → Bool) (own : List Str) :
    ∀ (as : List α) (acc : List (α × Str)),
      (assignFrom nm sfx plain own acc as).map (·.1) = acc.map (·.1) ++ as
  | [], acc => by simp [assignFrom]
  | a :: as, acc => by
    rw [show assignFrom nm sfx plain own acc (a :: as) = assignFrom nm sfx plain own
      (acc ++ [(a, Names.choose own (acc.map (·.2)) (plain a) (keyOf nm sfx a))]) as from rfl,
      assignFrom_map_fst nm sfx plain own as]
    simp

omit [DecidableEq α] in
theorem assignFrom_spec (nm sfx : α → Str) (plain : α → Bool) (ms : List α) (own : List Str)
    (hslash : ∀ a ∈ ms, '/' ∉ nm a ∧ '/' ∉ sfx a) :
    ∀ (as : List α) (acc : List (α × Str)), (∀ a ∈ as, a ∈ ms) → Good own acc →
      (∀ e ∈ acc, '/' ∉ e.2) →
      Good own (assignFrom nm sfx plain own acc as) ∧
        (assignFrom nm sfx plain own acc as).map (·.1) = acc.map (·.1) ++ as ∧
        ∀ e ∈ assignFrom nm sfx plain own acc as, '/' ∉ e.2
  | [], acc, _, hg, hs => ⟨hg, by simp [assignFrom], hs⟩
  | a :: as, acc, has, ⟨hnd, htk⟩, hs => by
    let p := Names.choose own (acc.map (·.2)) (plain a) (keyOf nm sfx a)
    have hf := Names.choose_free own (acc.map (·.2)) (plain a) (keyOf nm sfx a)
    simp only [Names.free, Bool.and_eq_true, Bool.not_eq_true'] at hf
    have hg : Good own (acc ++ [(a, p)]) := by
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
    have hs' : ∀ e ∈ acc ++ [(a, p)], '/' ∉ e.2 := by
      intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hs e he
      · have := hslash a (has a List.mem_cons_self)
        exact Names.choose_no_slash (k := keyOf nm sfx a) _ _ _ this.1 this.2
    have ih := assignFrom_spec nm sfx plain ms own hslash as (acc ++ [(a, p)])
      (fun a' ha' => has a' (List.mem_cons_of_mem _ ha')) hg hs'
    refine ⟨ih.1, ?_, ih.2.2⟩
    rw [show assignFrom nm sfx plain own acc (a :: as) =
      assignFrom nm sfx plain own (acc ++ [(a, p)]) as from rfl, ih.2.1]
    simp

/-- The prefix `assign` gave copy `a`. -/
def prefixOf (asg : List (α × Str)) (a : α) : Str :=
  ((asg.find? (·.1 == a)).map (·.2)).getD []

theorem prefixOf_mem {asg : List (α × Str)} {a : α} (ha : a ∈ asg.map (·.1)) :
    (a, prefixOf asg a) ∈ asg := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  cases hx : asg.find? (·.1 == e.1) with
  | none =>
    have := List.find?_eq_none.mp hx e he
    simp at this
  | some x =>
    have hb : (x.1 == e.1) = true := List.find?_some (p := fun y : α × Str => y.1 == e.1) hx
    have hxk : x.1 = e.1 := beq_iff_eq.mp hb
    simp only [prefixOf, hx, Option.map_some, Option.getD_some]
    rw [← hxk]
    exact List.mem_of_find?_eq_some hx

/-- `local_names`: the name here of workspace `w` of copy `a`, on copy `me`. -/
def localName (me : α) (asg : List (α × Str)) (a : α) (w : Str) : Str :=
  if a = me then w else prefixOf asg a ++ '/' :: w

/-- Naming is injective on a view's keys: this copy's workspaces, named among `own`, and those of
the copies named, `ms`, by their names now, whatever their priorities. Nothing here needs the
copies named, or their names, to be those of any other operation. -/
theorem localName_injective {nm sfx : α → Str} {pri : α → Nat × Nat} {me : α} {ms : List α}
    {own : List Str} (hslash : ∀ a ∈ ms, '/' ∉ nm a ∧ '/' ∉ sfx a)
    {k₁ k₂ : α} {w₁ w₂ : Str}
    (hk₁ : k₁ = me ∧ w₁ ∈ own ∨ k₁ ≠ me ∧ k₁ ∈ ms)
    (hk₂ : k₂ = me ∧ w₂ ∈ own ∨ k₂ ≠ me ∧ k₂ ∈ ms)
    (h : localName me (assign nm sfx pri ms own) k₁ w₁ =
      localName me (assign nm sfx pri ms own) k₂ w₂) :
    k₁ = k₂ ∧ w₁ = w₂ := by
  let asg := assign nm sfx pri ms own
  have hord : ∀ a ∈ order nm pri ms, a ∈ ms := by
    intro a ha
    simp only [order, List.mem_append, List.mem_filter] at ha
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
  obtain ⟨⟨hpnd, htk⟩, hkeys, hsl⟩ :=
    assignFrom_spec nm sfx (wins nm pri ms) ms own hslash (order nm pri ms) [] hord
      ⟨List.nodup_nil, by simp⟩ (by simp)
  simp only [List.map_nil, List.nil_append] at hkeys
  have mem : ∀ {k}, k ∈ ms → (k, prefixOf asg k) ∈ asg := fun {k} hk =>
    prefixOf_mem (by
      show k ∈ (assign nm sfx pri ms own).map (·.1)
      rw [assign, hkeys]; exact mem_order hk)
  have apart : ∀ {w k v}, w ∈ own → k ∈ ms → w ≠ prefixOf asg k ++ '/' :: v := by
    intro w k v hw hk e
    have := htk _ (List.mem_map_of_mem (f := (·.2)) (mem hk))
    simp only [Names.taken, List.any_eq_false, Bool.not_eq_true] at this
    have hpre : (prefixOf asg k ++ ['/']).isPrefixOf (prefixOf asg k ++ '/' :: v) = true :=
      List.isPrefixOf_iff_prefix.mpr ⟨v, by simp⟩
    have := this w hw
    rw [e, hpre] at this
    exact Bool.noConfusion this
  have mine : ∀ {k w}, k = me ∧ w ∈ own ∨ k ≠ me ∧ k ∈ ms → k = me → w ∈ own :=
    fun hk e => (hk.resolve_right fun h => h.1 e).2
  have other : ∀ {k w}, k = me ∧ w ∈ own ∨ k ≠ me ∧ k ∈ ms → k ≠ me → k ∈ ms :=
    fun hk e => (hk.resolve_left fun h => e h.1).2
  unfold localName at h
  by_cases e₁ : k₁ = me <;> by_cases e₂ : k₂ = me <;> simp only [e₁, e₂, ite_true, ite_false] at h
  · exact ⟨e₁.trans e₂.symm, h⟩
  · exact absurd h (apart (mine hk₁ e₁) (other hk₂ e₂))
  · exact absurd h.symm (apart (mine hk₂ e₂) (other hk₁ e₁))
  · have m₁ := mem (other hk₁ e₁)
    have m₂ := mem (other hk₂ e₂)
    have ⟨hp, hw⟩ := Names.split_slash (hsl _ m₁) (hsl _ m₂) h
    exact ⟨congrArg Prod.fst (Names.eq_of_map_nodup hpnd m₁ m₂ hp), hw⟩

/-- Naming depends only on the copies named, their names now, and their priorities: not on any
copy forgotten, nor on a name any copy had before. -/
theorem assign_congr {nm₁ nm₂ sfx : α → Str} {pri₁ pri₂ : α → Nat × Nat} {ms : List α}
    {own : List Str} (hnm : ∀ a ∈ ms, nm₁ a = nm₂ a) (hpri : ∀ a ∈ ms, pri₁ a = pri₂ a) :
    assign nm₁ sfx pri₁ ms own = assign nm₂ sfx pri₂ ms own := by
  have hwins : ∀ a ∈ ms, wins nm₁ pri₁ ms a = wins nm₂ pri₂ ms a := by
    intro a ha
    unfold wins
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor <;> intro h b hb <;> have := h b hb <;>
      simp only [hnm b hb, hnm a ha, hpri b hb, hpri a ha] at this ⊢ <;> exact this
  have hord : order nm₁ pri₁ ms = order nm₂ pri₂ ms := by
    unfold order
    rw [List.filter_congr (p := wins nm₁ pri₁ ms) (q := wins nm₂ pri₂ ms) hwins,
      List.filter_congr (p := fun a => !wins nm₁ pri₁ ms a) (q := fun a => !wins nm₂ pri₂ ms a)
        (fun a ha => by rw [hwins a ha])]
  have key : ∀ (as : List α) (acc : List (α × Str)), (∀ a ∈ as, a ∈ ms) →
      assignFrom nm₁ sfx (wins nm₁ pri₁ ms) own acc as =
        assignFrom nm₂ sfx (wins nm₂ pri₂ ms) own acc as := by
    intro as
    induction as with
    | nil => intro acc _; rfl
    | cons a as ih =>
      intro acc has
      have ha := has a List.mem_cons_self
      simp only [assignFrom, keyOf, hwins a ha, hnm a ha]
      exact ih _ (fun a' ha' => has a' (List.mem_cons_of_mem _ ha'))
  unfold assign
  rw [← hord]
  exact key _ [] (fun a ha => by
    simp only [order, List.mem_append, List.mem_filter] at ha
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h)

/-- So every machine agrees on the labels at an operation, a function of its history alone:
given the copies present there (`Presence.present_local`), each copy's name there (`NameIs`,
decoded by `dec`) and how long it has held it (`SinceIs`) agree, and so does the naming. -/
theorem naming_local (h₁ h₂ : NHist) {init gen : Nat → Nat} {x : Nat}
    (hpar : ∀ b, Anc h₁.par b x → h₁.par b = h₂.par b)
    (hw : ∀ b k, Anc h₁.par b x → (h₁.work b k ↔ h₂.work b k))
    (hfg : ∀ b k, Anc h₁.par b x → (h₁.forget b k ↔ h₂.forget b k))
    (hrec : ∀ b k, Anc h₁.par b x → h₁.named b k = h₂.named b k)
    {ms : List Nat} {own : List Str} {sfx : Nat → Str} (dec : Nat → Str)
    {c₁ c₂ s₁ s₂ : Nat → Nat}
    (hc₁ : ∀ a ∈ ms, h₁.NameIs init x a (c₁ a)) (hc₂ : ∀ a ∈ ms, h₂.NameIs init x a (c₂ a))
    (hs₁ : ∀ a ∈ ms, h₁.SinceIs gen x a (s₁ a)) (hs₂ : ∀ a ∈ ms, h₂.SinceIs gen x a (s₂ a)) :
    assign (dec ∘ c₁) sfx (fun a => (s₁ a, a)) ms own =
      assign (dec ∘ c₂) sfx (fun a => (s₂ a, a)) ms own := by
  apply assign_congr
  · intro a ha
    have h₂' := (NHist.nameIs_local h₁ h₂ hpar (fun b hb => hrec b a hb)).2 (hc₂ a ha)
    simp only [Function.comp, h₁.nameIs_unique (hc₁ a ha) h₂']
  · intro a ha
    have h₂' := (sinceIs_local h₁ h₂ hpar (fun b hb => hw b a hb) (fun b hb => hfg b a hb)
      (fun b hb => hrec b a hb)).2 (hs₂ a ha)
    simp only [h₁.sinceIs_unique (hs₁ a ha) h₂']

/-- A name in a view brought back by `jj undo` or `jj op restore` stands for at most one
workspace when read by the naming of the operation the view came from (`y`): whatever names
copies have since, and whichever copies are present now. -/
theorem resolve_at_origin {nm sfx : α → Str} {pri : α → Nat × Nat} {me : α} {ms : List α}
    {own : List Str} (hslash : ∀ a ∈ ms, '/' ∉ nm a ∧ '/' ∉ sfx a) {k₁ k₂ : α} {w₁ w₂ : Str}
    (hk₁ : k₁ ≠ me ∧ k₁ ∈ ms) (hk₂ : k₂ ≠ me ∧ k₂ ∈ ms)
    (h : localName me (assign nm sfx pri ms own) k₁ w₁ =
      localName me (assign nm sfx pri ms own) k₂ w₂) :
    k₁ = k₂ ∧ w₁ = w₂ :=
  localName_injective hslash (Or.inr hk₁) (Or.inr hk₂) h

/-! ### Who keeps the plain name -/

/-- Two copies that both keep their plain names have different names. -/
theorem winners_apart {nm : α → Str} {pri : α → Nat × Nat} {ms : List α} {a b : α}
    (ha : a ∈ ms) (hb : b ∈ ms) (hwa : wins nm pri ms a = true) (hwb : wins nm pri ms b = true)
    (hn : nm a = nm b) : a = b := by
  apply Classical.byContradiction
  intro hne
  have h₁ := List.all_eq_true.mp hwa b hb
  have h₂ := List.all_eq_true.mp hwb a ha
  have e₁ : (b == a) = false := by simpa using fun h => hne h.symm
  have e₂ : (a == b) = false := by simpa using hne
  have n₁ : (nm b != nm a) = false := by simp [hn]
  have n₂ : (nm a != nm b) = false := by simp [hn]
  simp only [e₁, n₁, e₂, n₂, Bool.false_or] at h₁ h₂
  exact lexLt_asymm h₁ h₂

theorem choose_plain {own used : List Str} {k : Names.Key}
    (hf : Names.free own used k.name = true) : Names.choose own used true k = k.name := by
  simp [Names.choose, Names.candidates, hf]

/-- Naming the copies that keep their plain names first gives each its name, if no name of
this machine's own starts with one of theirs and `/`. -/
theorem pass_one (nm sfx : α → Str) (pri : α → Nat × Nat) (ms : List α) (own : List Str)
    (hown : ∀ b ∈ ms, wins nm pri ms b = true → Names.taken own (nm b) = false) :
    ∀ (W : List α) (acc : List (α × Str)),
      (∀ c ∈ W, c ∈ ms ∧ wins nm pri ms c = true) →
      (∀ e ∈ acc, e.1 ∈ ms ∧ wins nm pri ms e.1 = true ∧ e.2 = nm e.1) →
      (acc.map (·.1) ++ W).Nodup →
      ∀ e ∈ assignFrom nm sfx (wins nm pri ms) own acc W, e.2 = nm e.1
  | [], acc, _, hacc, _ => fun e he => (hacc e he).2.2
  | c :: W, acc, hW, hacc, hnd => by
    have ⟨hcm, hcw⟩ := hW c List.mem_cons_self
    have hfree : Names.free own (acc.map (·.2)) (nm c) = true := by
      simp only [Names.free, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨?_, hown c hcm hcw⟩
      apply Bool.eq_false_iff.mpr
      intro hc
      obtain ⟨e, he, hec⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
      have ⟨hem, hew, hen⟩ := hacc e he
      have := winners_apart hem hcm hew hcw (hen ▸ hec)
      have hin : c ∈ acc.map (·.1) := List.mem_map.mpr ⟨e, he, this⟩
      exact (List.nodup_append.mp hnd).2.2 c hin c List.mem_cons_self rfl
    have hch : Names.choose own (acc.map (·.2)) (wins nm pri ms c) (keyOf nm sfx c) = nm c := by
      rw [hcw]; exact choose_plain hfree
    show ∀ e ∈ assignFrom nm sfx (wins nm pri ms) own (acc ++ [(c, Names.choose own
      (acc.map (·.2)) (wins nm pri ms c) (keyOf nm sfx c))]) W, e.2 = nm e.1
    rw [hch]
    apply pass_one nm sfx pri ms own hown W
    · exact fun c' hc' => hW c' (List.mem_cons_of_mem _ hc')
    · intro e he
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · exact hacc e he
      · exact ⟨hcm, hcw, rfl⟩
    · simpa using hnd

/-- A copy that keeps its plain name is shown under it. -/
theorem winner_label {nm sfx : α → Str} {pri : α → Nat × Nat} {ms : List α} {own : List Str}
    {a : α} (hnd : ms.Nodup) (ha : a ∈ ms) (hw : wins nm pri ms a = true)
    (hown : ∀ b ∈ ms, wins nm pri ms b = true → Names.taken own (nm b) = false) :
    prefixOf (assign nm sfx pri ms own) a = nm a := by
  let W := ms.filter (wins nm pri ms)
  have hP := pass_one nm sfx pri ms own hown W []
    (fun c hc => ⟨(List.mem_filter.mp hc).1, (List.mem_filter.mp hc).2⟩) (by simp)
    (by simp only [List.map_nil, List.nil_append]; exact List.Pairwise.filter _ hnd)
  obtain ⟨rest, hrest⟩ := assignFrom_extends nm sfx (wins nm pri ms) own
    (ms.filter fun a => !wins nm pri ms a) (assignFrom nm sfx (wins nm pri ms) own [] W)
  have hfst : (assignFrom nm sfx (wins nm pri ms) own [] W).map (·.1) = W := by
    simpa using assignFrom_map_fst nm sfx (wins nm pri ms) own W []
  have haW : a ∈ (assignFrom nm sfx (wins nm pri ms) own [] W).map (·.1) := by
    rw [hfst]; exact List.mem_filter.mpr ⟨ha, hw⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp haW
  unfold assign order
  rw [assignFrom_append, hrest]
  unfold prefixOf
  cases hx : (assignFrom nm sfx (wins nm pri ms) own [] W).find? (·.1 == e.1) with
  | none =>
    have := List.find?_eq_none.mp hx e he
    simp at this
  | some x =>
    have hb : (x.1 == e.1) = true := List.find?_some (p := fun y : α × Str => y.1 == e.1) hx
    rw [List.find?_append, hx]
    simp only [Option.some_or, Option.map_some, Option.getD_some]
    rw [hP x (List.mem_of_find?_eq_some hx), beq_iff_eq.mp hb]

/-- A copy that stays present under an unchanged name keeps its label across another copy's
rename, leave or return. At `x`, copy `a` has been present under its name since `o`'s
generation. Every other copy present under the same name came to it, by a rename or a return,
after `o` (`e` has `o` in its history): one that left isn't named at all, and one that renamed
away no longer shares the name. Then `a` keeps its plain name. -/
theorem keeps_label (h : NHist) {gen : Nat → Nat} (hg : h.GenMono gen) {x a o : Nat}
    {ms : List Nat} {own : List Str} {nm sfx : Nat → Str} {s : Nat → Nat}
    (hnd : ms.Nodup) (ha : a ∈ ms) (hs : ∀ b ∈ ms, h.SinceIs gen x b (s b)) (hso : s a = gen o)
    (hlater : ∀ b ∈ ms, b ≠ a → nm b = nm a →
      ∃ e, Anc h.par e x ∧ h.Mark e b ∧ Anc h.par o e ∧ o ≠ e)
    (hown : ∀ b ∈ ms, wins nm (fun b => (s b, b)) ms b = true → Names.taken own (nm b) = false) :
    prefixOf (assign nm sfx (fun b => (s b, b)) ms own) a = nm a := by
  apply winner_label hnd ha _ hown
  apply List.all_eq_true.mpr
  intro b hb
  by_cases hba : b = a
  · simp [hba]
  by_cases hn : nm b = nm a
  · obtain ⟨e, hex, hm, hoe, hne⟩ := hlater b hb hba hn
    have := h.later_mark hg hex hm hoe hne (hs b hb)
    simp [lexLt, hso, this]
  · simp [hn]

/-! Examples. Copy 0 is this one; copies 1 and 2 are others, with suffixes as below. -/

def sfxOf : Nat → Str
  | 1 => "1a2b3c4d".toList
  | 2 => "5e6f7a8b".toList
  | _ => "00000000".toList

/-- The names here of the `default` workspaces of `ms`, named by `nm`, present under their names
since `since`. -/
def defaults (nm : Nat → String) (since : Nat → Nat) (ms : List Nat) : List String :=
  ms.map fun a => String.ofList (localName 0
    (assign (fun b => (nm b).toList) sfxOf (fun b => (since b, b)) ms []) a "default".toList)

-- At an old operation `y`, copy 1 is `longhost`.
#guard defaults (fun _ => "longhost") (fun _ => 1) [1] == ["longhost/default"]

-- Copy 1 renames itself `short`; copy 2, joining later as `longhost`, takes the name it freed.
-- So `longhost/default` in a view `jj undo` brings back from `y` is copy 1's by `y`'s naming,
-- and copy 2's by today's: it must be read by `y`'s (`resolve_at_origin`), as the commit rule
-- does, not by the naming now.
#guard defaults (fun | 1 => "short" | _ => "longhost") (fun _ => 1) [1, 2] ==
  ["short/default", "longhost/default"]

-- Copy 1, `laptop`, forgotten; copy 2, a new clone named `laptop` too, is the only one present.
#guard defaults (fun _ => "laptop") (fun _ => 1) [2] == ["laptop/default"]

-- Copy 2 has been `laptop` since generation 3; copy 1 returns at generation 9, or renames
-- itself `laptop` then: copy 2 keeps the plain name.
#guard defaults (fun _ => "laptop") (fun | 1 => 9 | _ => 3) [1, 2] ==
  ["laptop-1a2b/default", "laptop/default"]

-- Claims of the same generation fall back to key order.
#guard defaults (fun _ => "laptop") (fun _ => 5) [1, 2] ==
  ["laptop/default", "laptop-5e6f/default"]

-- Two copies whose keys share a suffix, renamed alike, are still told apart.
#guard (let ms := [1, 3]
  let sx : Nat → Str := fun _ => "1a2b3c4d".toList
  ms.map fun a => String.ofList (localName 0
    (assign (fun _ => "x".toList) sx (fun b => (5, b)) ms []) a "default".toList)) ==
  ["x/default", "x-1a2b/default"]

/-! Cases where candidate prefixes collide: every workspace still gets its own name. Copies
are numbered from 1 in the order given, as `names_conform` gives them in key order; copy 0 is
this one, not among them. -/

/-- The names here of this copy's own `own`, then of each copy's `default`, the copies given as
name, suffix and since. -/
def namesOf (cs : List (String × String × Nat)) (own : List String) : List String :=
  let ms := (List.range cs.length).map (· + 1)
  let cOf (b : Nat) := cs.getD (b - 1) ("", "", 0)
  let asg := assign (fun b => (cOf b).1.toList) (fun b => (cOf b).2.1.toList)
    (fun b => ((cOf b).2.2, b)) ms (own.map String.toList)
  (own.map fun w => String.ofList (localName 0 asg 0 w.toList)) ++
    ms.map fun b => String.ofList (localName 0 asg b "default".toList)

-- Two copies named alike whose suffixes start alike: the first in key order, of the same since,
-- keeps the name, and the other's shortest qualified name is free.
#guard namesOf [("mac", "aaaa1111", 0), ("mac", "aaaa2222", 0)] [] ==
  ["mac/default", "mac-aaaa/default"]

-- The copy present under the name longer keeps it, though its key is later.
#guard namesOf [("mac", "aaaa1111", 7), ("mac", "aaaa2222", 3)] [] ==
  ["mac-aaaa/default", "mac/default"]

-- A copy whose plain name is another's shorter qualified name: copies that keep their plain
-- names are named first, so the other takes a longer one.
#guard namesOf [("mac", "aaaa1111", 5), ("mac", "bbbb0000", 0), ("mac-aaaa", "12345678", 0)]
    [] == ["mac-aaaa1111/default", "mac/default", "mac-aaaa/default"]

-- A name of this copy's own that started with the longer prefix another forced.
#guard namesOf [("beta", "1a2b3c4d", 0)] ["beta/x", "beta-1a2b/default"] ==
  ["beta/x", "beta-1a2b/default", "beta-1a2b3c4d/default"]

end Naming

/-! ## 3. Leaving and joining again under one key -/

namespace Rejoin

variable (h : Hist)

/-- `Presence.leave_sticks`, for a key used again after leaving. `R` holds the operations the copy
pushes after joining again. The copy pushes none of its work between leaving and joining again
(the daemon syncs only a copy whose record says it joined: `Copies.right_hive`), and the
leave's forget follows all the work it pushed before (design.md, "Leaving"). Then the copy is
absent at every operation that has the forget, until one that has work it pushed after joining
again. -/
theorem leave_sticks_until_rejoin {f x k : Nat} {R : Nat → Prop} (hF : h.forget f k)
    (hbefore : ∀ w, h.work w k → ¬ R w → Anc h.par w f) (hfx : Anc h.par f x)
    (hnoR : ∀ w, Anc h.par w x → h.work w k → ¬ R w) : ¬ h.Present x k :=
  h.absence_persists (h.forget_absent hF) hfx (fun w hw hW => hbefore w hW (hnoR w hw hW))

/-- Joining again is work, which brings the copy back wherever no forget saw it: a forget the
leave wrote included, and a daemon's that hadn't seen it. -/
theorem rejoin_returns {j x k : Nat} (hJ : h.work j k) (hjx : Anc h.par j x)
    (hunseen : ∀ f, Anc h.par f x → h.forget f k → ¬ Anc h.par j f) : h.Present x k :=
  h.unseen_work_survives hJ hjx hunseen

/-- A `jj` command that loaded the repository before the leave and wrote its operation `l` after
it, which the copy pushes once it has joined again, is work by the same key: it keeps the copy
present, as the copy is anyway, and needs no forget. -/
theorem late_work_same_key {l x k : Nat} (hL : h.work l k) (hlx : Anc h.par l x)
    (hunseen : ∀ f, Anc h.par f x → h.forget f k → ¬ Anc h.par l f) : h.Present x k :=
  h.unseen_work_survives hL hlx hunseen

end Rejoin

end Musubi.Identity

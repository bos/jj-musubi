/-
Executable checks of structural node observations. A raw id names one canonical body, even
when another copy writes the same body again. These checks read labels, embeddings and parents;
they do not infer body, object or local availability from a ghost structural label.
-/
import Musubi.NodeSys

namespace Musubi.NodeSys.Exec

open Musubi.NodeSettle

structure GrowObs where
  rawNext : Nat
  labelNext : Nat
  rawPar : Nat → List Nat
  labelPar : Nat → List Nat
  emb : Nat → Nat

def observe (g : Sys) (s : NS) (emb : Nat → Nat) : GrowObs :=
  ⟨g.next, s.next, g.par, s.par, emb⟩

/-- The bounded obligations of the structural embedding, independently of availability. -/
def scopeB (a : GrowObs) : Bool :=
  (List.range a.labelNext).all (fun x => decide (a.emb x < a.rawNext) &&
    decide (a.rawPar (a.emb x) = (a.labelPar x).map a.emb)) &&
  (List.range a.labelNext).all (fun x => (List.range a.labelNext).all
    (fun y => decide (a.emb x = a.emb y → x = y)))

theorem scopeB_sound {g : Sys} {s : NS} {emb : Nat → Nat}
    (h : scopeB (observe g s emb) = true) : Scoped s emb g := by
  simp only [scopeB, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨fun x y hx hy he => h.2 x hx y hy he,
    fun x hx => (h.1 x hx).1, fun x hx => (h.1 x hx).2⟩

/-- Every bounded obligation of `GrowR`, including reuse and coverage of new raw ids. -/
def growB (a b : GrowObs) : Bool :=
  [decide (a.labelNext ≤ b.labelNext),
   decide (a.rawNext ≤ b.rawNext),
   (List.range a.labelNext).all (fun x => decide (b.emb x = a.emb x)),
   (List.range a.rawNext).all (fun y => decide (b.rawPar y = a.rawPar y)),
   (List.range a.labelNext).all (fun x => decide (b.labelPar x = a.labelPar x)),
   (List.range b.labelNext).all
     (fun x => decide (a.labelNext ≤ x → b.emb x < b.rawNext)),
   (List.range b.labelNext).all
     (fun x => decide (a.labelNext ≤ x → b.rawPar (b.emb x) = (b.labelPar x).map b.emb)),
   (List.range b.labelNext).all (fun x => (List.range a.labelNext).all
     (fun y => decide (a.labelNext ≤ x → b.emb x < a.rawNext → a.emb y ≠ b.emb x))),
   (List.range b.labelNext).all (fun x => (List.range b.labelNext).all
     (fun y => decide (a.labelNext ≤ x → a.labelNext ≤ y → b.emb x = b.emb y → x = y))),
   (List.range b.rawNext).all (fun y => decide (y < a.rawNext) ||
     (List.range b.labelNext).any (fun x => decide (a.labelNext ≤ x ∧ b.emb x = y)))].all id

theorem growB_sound {g g' : Sys} {s s' : NS} {emb emb' : Nat → Nat}
    (h : growB (observe g s emb) (observe g' s' emb') = true) :
    GrowR g g' s s' emb emb' := by
  simp only [growB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    id_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.any_eq_true] at h
  rcases h with ⟨hn, hr, he, hraw, hpar, hb, hpn, hre, hinj, hcover⟩
  refine ⟨hn, hr, he, hraw, hpar, ?_, ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    exact hb x h2 h1
  · intro x h1 h2
    exact hpn x h2 h1
  · intro x h1 h2 h3 y hy
    exact hre x h2 y hy h1 h3
  · intro x y hx1 hx2 hy1 hy2 heq
    exact hinj x hx2 y hy2 hx1 hy1 heq
  · intro y h1 h2
    rcases hcover y h2 with h | ⟨x, hx, hnew, heq⟩
    · exact False.elim (Nat.not_lt_of_ge h1 h)
    · exact ⟨x, hnew, hx, heq⟩

/-- A complete normal head cannot be a remembered dropped name or a cached renaming key
when the hub drops a subset of the node's originals. A raw remembered name only implies
its original is dropped; other versions of that original need not be remembered names.
The cache's cause is a dropped original in the key's immutable raw ancestry, rather than
an assumed equality between a cached lookup and full normalization. -/
theorem unsuperseded_of_normal {par : Nat → List Nat} {orig : Nat → Nat}
    {nodeD hubD named cached : Nat → Bool} {head : Nat}
    (hnormal : ∀ x, Anc par x head → nodeD (orig x) = false)
    (hsub : ∀ o, hubD o = true → nodeD o = true)
    (hnamed : named head = true → hubD (orig head) = true)
    (hcached : cached head = true → ∃ x, Anc par x head ∧ hubD (orig x) = true) :
    named head = false ∧ cached head = false := by
  have survives : ∀ x, Anc par x head → hubD (orig x) = false := by
    intro x hx
    cases h : hubD (orig x)
    · rfl
    · have hn := hnormal x hx
      rw [hsub _ h] at hn
      cases hn
  constructor
  · cases h : named head
    · rfl
    · have hs := survives head Anc.refl
      rw [hnamed h] at hs
      cases hs
  · cases h : cached head
    · rfl
    · obtain ⟨x, hx, hd⟩ := hcached h
      have hs := survives x hx
      rw [hd] at hs
      cases hs

end Musubi.NodeSys.Exec

/-
Presence through a contraction (docs/internals/design.md, "Presence through an abandon").

Which copies are present at an operation is worked out from the history below it
(`Presence.lean`), and the canonical view shows a copy's workspaces exactly where it is
present. A contraction (`Contract.lean`) keeps every surviving operation's view but changes the
history below it: dropping a copy's work, or a forget of it, would change presence there, and
the view would no longer agree with it. So a contraction stamps an operation it keeps with the
presence it had, wherever the presence worked out from its new parents would differ, and
presence at a stamped operation is its stamp.

Abstractly, `val x` is the presence at `x` before anything is dropped, and `step x ps seen` works
it out at `x` from its parents' presences `ps`, asking `seen c p` whether work `c`, which a
parent's presence names, is in the history below parent `p`. Presence names work by its
original identity, which a contraction keeps (`musubi.original-parents`; here operations are
their own identities), so no value changes. Work no operation stands for any more, as it was
dropped, counts as seen below every parent: a merge keeps it only where every parent does.

A history is the original parents `par` and the operations dropped from it so far, `gone`; its
parents are `cpar par gone`. The implementation works on the history as it now is, contracting
it again, so the theorems are about any history and what is dropped from it next.

- `pres_eq`: with the stamps, presence at every operation that survives is what it was.
- `stamp_union`, `sid_union`: dropping `D₁` and then `D₂` stamps every operation as dropping
  both at once does, and so gives it the same id; so the order of two drops doesn't matter
  (`sid_comm`). Whether an operation is stamped, and with what, depends only on the history
  that is left and on what is gone, never on the order in which it went.
- `stamp_none`: a history nothing was dropped from has no stamps.
- `sid_eq`, `sid_superseded_ne`: as for `cid` (`Contract.cid_eq`, `Contract.superseded_ne`),
  two ids are equal only for the same operation with the same proper ancestors gone, so no id an
  operation had before something below it was dropped is any id after.
-/
import Musubi.Contract

namespace Musubi.PresenceContract

open Musubi.Contract

variable {V : Type} (par : Nat → List Nat) (val : Nat → V)
  (step : Nat → List (Nat × V) → (Nat → Nat → Prop) → V)

/-- Whether work `c` counts as in the history below `p`, in a history with parents `P` from
which `gone` was dropped: it is, or no operation stands for it any more. -/
def seen (P : Nat → List Nat) (gone : Nat → Bool) (c p : Nat) : Prop :=
  gone c = true ∨ Anc P c p

/-- Presence at `x` worked out from its parents' in a history with parents `P` from which
`gone` was dropped, each parent's as it was. -/
def computed (P : Nat → List Nat) (gone : Nat → Bool) (x : Nat) : V :=
  step x ((P x).map fun p => (p, val p)) (seen P gone)

open Classical in
/-- What a contraction stamps `x` with: its presence, where working it out would give another. -/
noncomputable def stamp (P : Nat → List Nat) (gone : Nat → Bool) (x : Nat) : Option V :=
  if computed val step P gone x = val x then none else some (val x)

/-- Presence at `x` in a history with parents `P` from which `gone` was dropped: its stamp, or
worked out from its parents'. -/
noncomputable def pres (P : Nat → List Nat) (gone : Nat → Bool) (x : Nat) : V :=
  match stamp val step P gone x with
  | some v => v
  | none =>
    step x ((P x).map fun p => (p, if p < x then pres P gone p else val p)) (seen P gone)
termination_by x
decreasing_by omega

variable {par val step}

/-- With the stamps, presence at every operation that survives what was dropped is what it was
before anything was dropped. -/
theorem pres_eq (hlt : ParLt par) (gone : Nat → Bool) (x : Nat) :
    pres val step (cpar par gone) gone x = val x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [pres]
    have hmap : ((cpar par gone x).map fun p =>
        (p, if p < x then pres val step (cpar par gone) gone p else val p)) =
        (cpar par gone x).map fun p => (p, val p) := by
      apply List.map_congr_left
      intro q hq
      have hqx := (parLt_cpar hlt) x q hq
      simp [hqx, ih q hqx]
    unfold stamp
    by_cases hc : computed val step (cpar par gone) gone x = val x
    · simp only [hc, ↓reduceIte, hmap]
      exact hc
    · simp [hc]

/-- Dropping `D₁` and then `D₂` works presence out at every operation as dropping both at once
does: the parents agree (`cpar_union`), and so does what is gone. -/
theorem computed_union (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    computed val step (cpar (cpar par D₁) D₂) (union D₁ D₂) x =
      computed val step (cpar par (union D₁ D₂)) (union D₁ D₂) x := by
  have : cpar (cpar par D₁) D₂ = cpar par (union D₁ D₂) := funext (cpar_union hlt D₁ D₂)
  rw [this]

/-- Dropping `D₁` and then `D₂` stamps every operation as dropping both at once does. -/
theorem stamp_union (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    stamp val step (cpar (cpar par D₁) D₂) (union D₁ D₂) x =
      stamp val step (cpar par (union D₁ D₂)) (union D₁ D₂) x := by
  unfold stamp
  rw [computed_union hlt]

/-! ## Ids -/

/-- An operation id: a hash of the operation's content, which `α` stands for, and its parents'
ids, as `Contract.CId`, but with content of any type: here the immutable content and the
stamp. -/
inductive SId (α : Type)
  | mk (content : α) (parents : List (SId α))

/-- The content an id hashes. -/
def SId.content {α : Type} : SId α → α
  | .mk c _ => c

/-- Ids with fuel. -/
def sidF {α : Type} (content : Nat → α) (P : Nat → List Nat) : Nat → Nat → SId α
  | 0, x => .mk (content x) []
  | f + 1, x => .mk (content x) ((P x).map (sidF content P f))

/-- The id of `x` in a history with parents `P`, its content `content x`. -/
def sid {α : Type} (content : Nat → α) (P : Nat → List Nat) (x : Nat) : SId α :=
  sidF content P (x + 1) x

theorem sidF_fuel {α : Type} {content : Nat → α} {P : Nat → List Nat} (hlt : ParLt P)
    {f g x : Nat} (hf : x < f) (hg : x < g) : sidF content P f x = sidF content P g x := by
  induction f generalizing g x with
  | zero => omega
  | succ f ih =>
    cases g with
    | zero => omega
    | succ g =>
      simp only [sidF, SId.mk.injEq, true_and]
      apply List.map_congr_left
      intro q hq
      have := hlt x q hq
      exact ih (by omega) (by omega)

theorem sid_eq_mk {α : Type} {content : Nat → α} {P : Nat → List Nat} (hlt : ParLt P)
    (x : Nat) : sid content P x = .mk (content x) ((P x).map (sid content P)) := by
  simp only [sid, sidF, SId.mk.injEq, true_and]
  apply List.map_congr_left
  intro q hq
  have := hlt x q hq
  exact sidF_fuel hlt (by omega) (by omega)

variable (content : Nat → Nat)

/-- What an id hashes once `gone` is dropped from `par`: an operation's immutable content and
its stamp. -/
noncomputable def scontent (P : Nat → List Nat) (gone : Nat → Bool) (x : Nat) : Nat × Option V :=
  (content x, stamp val step P gone x)

/-- Dropping `D₁` and then `D₂` gives the ids, stamps and all, that dropping both at once
gives. -/
theorem sid_union (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    sid (scontent (val := val) (step := step) content (cpar (cpar par D₁) D₂) (union D₁ D₂))
        (cpar (cpar par D₁) D₂) x =
      sid (scontent (val := val) (step := step) content (cpar par (union D₁ D₂))
        (union D₁ D₂)) (cpar par (union D₁ D₂)) x := by
  have : cpar (cpar par D₁) D₂ = cpar par (union D₁ D₂) := funext (cpar_union hlt D₁ D₂)
  rw [this]

/-- Hence the order of two drops doesn't matter. -/
theorem sid_comm (hlt : ParLt par) (D₁ D₂ : Nat → Bool) (x : Nat) :
    sid (scontent (val := val) (step := step) content (cpar (cpar par D₁) D₂) (union D₁ D₂))
        (cpar (cpar par D₁) D₂) x =
      sid (scontent (val := val) (step := step) content (cpar (cpar par D₂) D₁) (union D₂ D₁))
        (cpar (cpar par D₂) D₁) x := by
  rw [sid_union content hlt, sid_union content hlt]
  have : union D₁ D₂ = union D₂ D₁ := by funext y; simp [union, Bool.or_comm]
  rw [this]

/-! ## Nothing dropped -/

/-- Nothing gone. -/
def none' : Nat → Bool := fun _ => false

theorem ddAux_nodup {s l : List Nat} (hl : l.Nodup) (hs : ∀ a ∈ l, a ∉ s) : ddAux s l = l := by
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

/-- With nothing dropped, the parents are as they were, where no operation lists a parent
twice. -/
theorem cpar_none (hlt : ParLt par) (hnd : ∀ x, (par x).Nodup) (x : Nat) :
    cpar par none' x = par x := by
  have hexp : exp par none' = fun p => [p] := funext fun p => by rw [exp_eq hlt]; simp [none']
  have hfm : (par x).flatMap (exp par none') = par x := by rw [hexp]; simp
  unfold cpar dd
  rw [hfm]
  exact ddAux_nodup (hnd x) (fun _ _ h => by simp at h)

/-- Where presence is what working it out on the history gives, a history nothing was dropped
from has no stamps. -/
theorem stamp_none (hlt : ParLt par) (hnd : ∀ x, (par x).Nodup)
    (hval : ∀ x, val x = computed val step par none' x) (x : Nat) :
    stamp val step (cpar par none') none' x = none := by
  have : cpar par none' = par := funext (cpar_none hlt hnd)
  unfold stamp
  rw [this, ← hval]
  simp

/-! ## When ids agree -/

/-- Lists whose images are equal are equal, where equal images have equal sources. -/
theorem map_eq_of_first {α β : Type} {f g : α → β} (hfg : ∀ a b, f a = g b → a = b) :
    ∀ {l l' : List α}, l.map f = l'.map g → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hfg a b h.1, map_eq_of_first hfg h.2]

/-- Requires injective immutable content. Two survivors' ids, each in a history `par` from
which some operations are gone, are equal only for the same operation, whose proper ancestors
the two dropped. -/
theorem sid_eq (hlt : ParLt par) (hinj : Function.Injective content) {D D' : Nat → Bool}
    {x y : Nat}
    (h : sid (scontent (val := val) (step := step) content (cpar par D) D) (cpar par D) x =
      sid (scontent (val := val) (step := step) content (cpar par D') D') (cpar par D') y) :
    x = y ∧ ∀ a, Anc par a x → a ≠ x → D a = D' a := by
  have hlt₁ := parLt_cpar (D := D) hlt
  have hlt₂ := parLt_cpar (D := D') hlt
  have hxy : x = y := by
    have := congrArg (fun i => (SId.content i).1) h
    rw [sid_eq_mk hlt₁, sid_eq_mk hlt₂] at this
    exact hinj this
  subst hxy
  refine ⟨rfl, ?_⟩
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [sid_eq_mk hlt₁, sid_eq_mk hlt₂] at h
    simp only [SId.mk.injEq] at h
    obtain ⟨-, h⟩ := h
    let s := sid (scontent (val := val) (step := step) content (cpar par D) D) (cpar par D)
    let s' := sid (scontent (val := val) (step := step) content (cpar par D') D') (cpar par D')
    have hfirst : ∀ q r, s q = s' r → q = r := by
      intro q r hqr
      have := congrArg (fun i => (SId.content i).1) hqr
      simp only [s, s'] at this
      rw [sid_eq_mk hlt₁, sid_eq_mk hlt₂] at this
      exact hinj this
    have hl : cpar par D x = cpar par D' x := map_eq_of_first hfirst h
    rw [← hl] at h
    have hq : ∀ q ∈ cpar par D x, s q = s' q := List.map_inj_left.1 h
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

/-- Once what is gone has grown from `D'` to include `x` or one of its proper ancestors, the id
`x` had is no id of any operation that survives. -/
theorem sid_superseded_ne (hlt : ParLt par) (hinj : Function.Injective content)
    {D D' : Nat → Bool} {x : Nat}
    (hsup : D x = true ∨ ∃ a, Anc par a x ∧ a ≠ x ∧ D a = true ∧ D' a = false)
    {y : Nat} (hy : D y = false) :
    sid (scontent (val := val) (step := step) content (cpar par D') D') (cpar par D') x ≠
      sid (scontent (val := val) (step := step) content (cpar par D) D) (cpar par D) y := by
  intro h
  obtain ⟨rfl, hagree⟩ := sid_eq content hlt hinj h
  rcases hsup with hx | ⟨a, hA, hne, hDa, hD'a⟩
  · rw [hx] at hy; exact Bool.noConfusion hy
  · have := hagree a hA hne
    rw [hDa, hD'a] at this
    exact Bool.noConfusion this

end Musubi.PresenceContract

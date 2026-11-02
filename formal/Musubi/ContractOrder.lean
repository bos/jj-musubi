/-
The ancestry check when a push contracts its expected head. A dropped head stands for all
of its surviving images, not for its original identity. This relation is weaker than
original ancestry while that head is dropped. Once the dropped set stops changing, heads
that survived it again form an ordinary ancestry chain.
-/
import Musubi.Contract
import Musubi.ExecSound

namespace Musubi.Contract

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

/-- The executable hub check also refuses an empty image. -/
def belowB (par : Nat → List Nat) (D : Nat → Bool) (a b : Nat) : Bool :=
  let images := exp par D a
  !images.isEmpty && images.all (fun p => Exec.ancB par p b)

theorem belowB_iff (hlt : ParLt par) :
    belowB par D a b = true ↔ exp par D a ≠ [] ∧ Below par D a b := by
  simp [belowB, Below, List.all_eq_true, Exec.ancB_iff hlt]

theorem belowB_survivor_iff (hlt : ParLt par) (ha : D a = false) :
    belowB par D a b = true ↔ Anc par a b := by
  rw [belowB_iff hlt, below_survivor_iff hlt ha]
  simp [exp_eq hlt, ha]

/-- A fixed-record suffix recovers original ancestry at each acceptance. Earlier history
may contain a comparison whose expected head was dropped; it need not be an original chain. -/
theorem stable_suffix_chain (hlt : ParLt par) (heads : Nat → Nat) (D : Nat → Bool)
    (hsurvives : ∀ i, D (heads i) = false)
    (hstep : ∀ i, Below par D (heads i) (heads (i + 1))) :
    ∀ i j, i ≤ j → Anc par (heads i) (heads j) := by
  intro i j hij
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact Anc.refl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i
      exact Anc.refl
    · exact (ih (by omega)).trans
        ((below_survivor_iff hlt (hsurvives j)).1 (hstep j))

end Musubi.Contract

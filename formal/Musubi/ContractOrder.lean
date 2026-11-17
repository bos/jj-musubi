/-
The hub's comparison and a node's frontier, computed. A dropped head stands for all of its
surviving images, not for its original identity: `belowB` checks `Contract.Below` and that the
images are nonempty, as the hub does, and `frontier` computes `Contract.frontierSet`. Once the
dropped set stops changing, heads that survived it again form an ordinary ancestry chain
(`stable_suffix_chain`).
-/
import Musubi.Contract
import Musubi.ExecSound

namespace Musubi.Contract

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


/-! ## The frontier, computed -/

/-- `frontierSet`, computed: the heads' surviving images, without duplicates, less those below
another. With the heads surviving, `frontier par D (heads ++ [known])` is the advance to what
survives of `known`; with records that drop a head, it is the frontier the node adopts them
with. -/
def frontier (par : Nat → List Nat) (D : Nat → Bool) (hs : List Nat) : List Nat :=
  Exec.maxL par (dd (hs.flatMap (exp par D)))

theorem setP_frontier (hlt : ParLt par) (D : Nat → Bool) (hs : List Nat) :
    Exec.setP (frontier par D hs) = frontierSet par D (Exec.setP hs) := by
  rw [frontier, Exec.setP_maxL hlt]
  congr 1
  funext x
  exact propext (mem_dd.trans (by simp [Exec.setP, List.mem_flatMap]))

theorem mem_frontier (hlt : ParLt par) {hs : List Nat} {x : Nat} :
    x ∈ frontier par D hs ↔ frontierSet par D (Exec.setP hs) x :=
  Iff.of_eq (congrFun (setP_frontier hlt D hs) x)

theorem ddAux_nodup (seen l : List Nat) : (ddAux seen l).Nodup := by
  induction l generalizing seen with
  | nil => simp [ddAux]
  | cons a l ih =>
    simp only [ddAux]
    split
    · exact ih _
    · apply List.nodup_cons.2
      refine ⟨?_, ih _⟩
      intro ha
      exact (mem_ddAux.1 ha).2 (by simp)

theorem frontier_nodup : (frontier par D hs).Nodup := by
  unfold frontier Exec.maxL
  exact (ddAux_nodup [] _).filter _

theorem frontier_survives (hlt : ParLt par) {hs : List Nat} {h : Nat}
    (hh : h ∈ frontier par D hs) : D h = false :=
  frontierSet_survives hlt ((mem_frontier hlt).1 hh)

theorem frontier_lt (hlt : ParLt par) {hs : List Nat} {B h : Nat} (hb : ∀ g ∈ hs, g < B)
    (hh : h ∈ frontier par D hs) : h < B := by
  obtain ⟨⟨g, hg, hm⟩, -⟩ := (mem_frontier hlt).1 hh
  exact Nat.lt_of_le_of_lt ((mem_exp hlt hm).2.le hlt) (hb g hg)

/-- Every surviving operation below one of `hs` is below the frontier. -/
theorem frontier_covers (hlt : ParLt par) {hs : List Nat} {B : Nat} (hb : ∀ g ∈ hs, g < B)
    {a g : Nat} (hg : g ∈ hs) (ha : Anc par a g) (hD : D a = false) :
    ∃ y ∈ frontier par D hs, Anc par a y := by
  obtain ⟨y, hy, hay⟩ := frontierSet_covers hlt (H := Exec.setP hs) hb hg ha hD
  exact ⟨y, (mem_frontier hlt).2 hy, hay⟩

/-- So every surviving image of one of `hs` is below the frontier. -/
theorem frontier_covers_image (hlt : ParLt par) {hs : List Nat} {B : Nat}
    (hb : ∀ g ∈ hs, g < B) {g p : Nat} (hg : g ∈ hs) (hp : p ∈ exp par D g) :
    ∃ y ∈ frontier par D hs, Anc par p y :=
  frontier_covers hlt hb hg (mem_exp hlt hp).2 (mem_exp hlt hp).1

/-- When the frontier is one head, every input passes the hub's comparison against it. -/
theorem frontier_singleton_below (hlt : ParLt par) {hs : List Nat} {B k h : Nat}
    (hb : ∀ g ∈ hs, g < B) (hk : k ∈ hs) (he : frontier par D hs = [h]) : Below par D k h := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := frontier_covers_image hlt hb hk hp
  rw [he] at hq
  exact (List.mem_singleton.1 hq) ▸ hpq

/-- A merge of the frontier is past every input, in the hub's comparison: its expected head may
be dropped, so this is `Below`, not original ancestry. -/
theorem frontier_merge_below (hlt : ParLt par) {hs : List Nat} {o k : Nat}
    (hb : ∀ g ∈ hs, g < o) (hk : k ∈ hs) : Below (upd par o (frontier par D hs)) D k o := by
  have hL := fun p hp => frontier_lt (D := D) hlt hb (h := p) hp
  intro p hp
  rw [exp_upd hlt hL (hb k hk)] at hp
  obtain ⟨h, hh, hph⟩ := frontier_covers_image hlt hb hk hp
  exact (anc_upd_new hlt hL).2 (Or.inr ⟨h, hh, hph⟩)

/-- The same merge keeps all surviving work below the inputs. -/
theorem frontier_merge_keeps (hlt : ParLt par) {hs : List Nat} {o x g : Nat}
    (hb : ∀ g ∈ hs, g < o) (hg : g ∈ hs) (hxg : Anc par x g) (hD : D x = false) :
    Anc (upd par o (frontier par D hs)) x o := by
  have hL := fun p hp => frontier_lt (D := D) hlt hb (h := p) hp
  obtain ⟨q, hq, hxq⟩ := frontier_covers hlt hb hg hxg hD
  exact (anc_upd_new hlt hL).2 (Or.inr ⟨q, hq, hxq⟩)

/-- With the heads surviving, the frontier of the heads and `known` is the heads followed by
`known`'s images, less those below another. -/
theorem frontier_advance (hlt : ParLt par) {heads : List Nat} {known : Nat}
    (hs : ∀ h ∈ heads, D h = false) :
    frontier par D (heads ++ [known]) = Exec.maxL par (dd (heads ++ exp par D known)) := by
  unfold frontier
  congr 2
  rw [List.flatMap_append, List.flatMap_singleton]
  congr 1
  have : ∀ l : List Nat, (∀ h ∈ l, D h = false) → l.flatMap (exp par D) = l := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      rw [List.flatMap_cons, exp_eq hlt, hl a (by simp), ih (fun h hh => hl h (by simp [hh]))]
      rfl
  exact this heads hs

end Musubi.Contract

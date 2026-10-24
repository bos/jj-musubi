/-
The presence rule (`Presence.lean`) on a finite history, executable, for the oracle
(docs/internals/conformance.md, "Presence"): operation `x` is the history's `x`th entry, and
`presentB` and `latestB` are proved to compute `Present` and `UMax` (`presentB_iff`,
`mem_latestB`). The search for an ancestor never goes below it, so the oracle answers quickly
for the small histories the conformance test makes.
-/
import Musubi.Presence

namespace Musubi.Presence

/-- An operation as the oracle receives it. -/
structure EOp where
  parents : List Nat := []
  work : Option Nat := none
  forgets : List Nat := []
deriving Inhabited

namespace EHist

variable (ops : List EOp)

def opAt (x : Nat) : EOp := ops.getD x {}
def par (x : Nat) : List Nat := (opAt ops x).parents
def workB (x k : Nat) : Bool := (opAt ops x).work == some k
def forgetB (x k : Nat) : Bool := (opAt ops x).forgets.contains k

/-- The history `ops` stands for. -/
def hist : Hist where
  par := par ops
  work x k := workB ops x k = true
  forget x k := forgetB ops x k = true

/-- Whether each operation's parents come before it. -/
def orderedB : Bool := (List.range ops.length).all fun x => (par ops x).all (· < x)

theorem parLt (ho : orderedB ops = true) : ParLt (par ops) := by
  intro y p hp
  by_cases hy : y < ops.length
  · simp only [orderedB, List.all_eq_true, List.mem_range, decide_eq_true_eq] at ho
    exact ho y hy p hp
  · have : opAt ops y = {} := by
      simp [opAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hy)]
    simp [par, this] at hp

/-- `a ∈ anc*(x)`, searching only operations above `a`. -/
def ancB (a x : Nat) : Bool :=
  a == x || (decide (a < x) && (par ops x).any fun p => if p < x then ancB a p else false)
termination_by x

theorem ancB_iff (ho : orderedB ops = true) (a x : Nat) :
    ancB ops a x = true ↔ Anc (par ops) a x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [ancB]
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
      List.any_eq_true]
    constructor
    · rintro (rfl | ⟨-, p, hp, hrec⟩)
      · exact Anc.refl
      · split at hrec
        · rename_i hpx
          exact Anc.step hp ((ih p hpx).1 hrec)
        · exact absurd hrec (by simp)
    · intro hA
      by_cases hx : a = x
      · exact Or.inl hx
      · rcases anc_cases hA with e | ⟨p, hp, hap⟩
        · exact absurd e hx
        · have hpx := parLt ops ho x p hp
          refine Or.inr ⟨Anc.lt_of_ne (parLt ops ho) hA hx, p, hp, ?_⟩
          simp only [hpx, ↓reduceIte]
          exact (ih p hpx).2 hap

def coveredB (x k w : Nat) : Bool :=
  (List.range (x + 1)).any fun f => forgetB ops f k && ancB ops f x && ancB ops w f

theorem coveredB_iff (ho : orderedB ops = true) (x k w : Nat) :
    coveredB ops x k w = true ↔ (hist ops).Covered ((hist ops).AncOf x) k w := by
  simp only [coveredB, List.any_eq_true, List.mem_range, Bool.and_eq_true, ancB_iff ops ho]
  constructor
  · rintro ⟨f, -, ⟨hF, hfx⟩, hwf⟩
    exact ⟨f, hfx, hF, hwf⟩
  · rintro ⟨f, hfx, hF, hwf⟩
    exact ⟨f, Nat.lt_succ_of_le (hfx.le (parLt ops ho)), ⟨hF, hfx⟩, hwf⟩

def uncovB (x k w : Nat) : Bool := ancB ops w x && workB ops w k && !coveredB ops x k w

theorem uncovB_iff (ho : orderedB ops = true) (x k w : Nat) :
    uncovB ops x k w = true ↔ (hist ops).Uncov x k w := by
  have hc := coveredB_iff ops ho x k w
  simp only [uncovB, Bool.and_eq_true, Bool.not_eq_true', ancB_iff ops ho]
  constructor
  · rintro ⟨⟨hwx, hW⟩, hn⟩
    exact ⟨hwx, hW, fun c => by rw [← hc] at c; simp [c] at hn⟩
  · rintro ⟨hwx, hW, hn⟩
    refine ⟨⟨hwx, hW⟩, ?_⟩
    cases e : coveredB ops x k w
    · rfl
    · exact absurd (hc.1 e) hn

def presentB (x k : Nat) : Bool := (List.range (x + 1)).any fun w => uncovB ops x k w

theorem presentB_iff (ho : orderedB ops = true) (x k : Nat) :
    presentB ops x k = true ↔ (hist ops).Present x k := by
  simp only [presentB, List.any_eq_true, List.mem_range, uncovB_iff ops ho]
  constructor
  · rintro ⟨w, -, hwx, hW, hn⟩
    exact ⟨w, hwx, hW, hn⟩
  · rintro ⟨w, hwx, hW, hn⟩
    exact ⟨w, Nat.lt_succ_of_le (hwx.le (parLt ops ho)), hwx, hW, hn⟩

/-- `k`'s latest work in `anc*(x)` that no forget saw. -/
def latestB (x k : Nat) : List Nat :=
  let u := (List.range (x + 1)).filter fun w => uncovB ops x k w
  u.filter fun c => u.all fun c' => !ancB ops c c' || c' == c

theorem mem_latestB (ho : orderedB ops = true) (x k c : Nat) :
    c ∈ latestB ops x k ↔ (hist ops).UMax x k c := by
  have bound : ∀ w, (hist ops).Uncov x k w → w < x + 1 :=
    fun w hu => Nat.lt_succ_of_le (hu.1.le (parLt ops ho))
  simp only [latestB, List.mem_filter, List.mem_range, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, uncovB_iff ops ho]
  constructor
  · rintro ⟨⟨-, hu⟩, hall⟩
    refine ⟨hu, fun c' hc' hcc' => ?_⟩
    rcases hall c' ⟨bound c' hc', hc'⟩ with h | h
    · rw [← Bool.not_eq_true, ancB_iff ops ho] at h
      exact absurd hcc' h
    · exact h
  · rintro ⟨hu, hmax⟩
    refine ⟨⟨bound c hu, hu⟩, fun c' ⟨_, hc'⟩ => ?_⟩
    by_cases hcc' : Anc (par ops) c c'
    · exact Or.inr (hmax c' hc' hcc')
    · left
      cases e : ancB ops c c'
      · rfl
      · exact absurd ((ancB_iff ops ho c c').1 e) hcc'

/-- The copies an operation of `ops` works for or forgets. -/
def copies : List Nat :=
  ops.flatMap fun o => o.work.toList ++ o.forgets

/-! ## Smoke tests, checked at build time

A copy works (0); a daemon forgets it (1) while it works again (2); the two merge (3); its
own daemon writes something after the forget (4); and everything merges (5). -/

private def scenario : List EOp :=
  [{ work := some 7 }, { parents := [0], forgets := [7] }, { parents := [0], work := some 7 },
    { parents := [1, 2] }, { parents := [1] }, { parents := [3, 4] }]

#guard orderedB scenario
#guard (List.range 6).map (presentB scenario · 7) = [true, false, true, true, false, true]
#guard latestB scenario 3 7 = [2]
#guard latestB scenario 5 7 = [2]

end EHist

end Musubi.Presence

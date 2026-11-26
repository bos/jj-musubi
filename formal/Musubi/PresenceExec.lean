/-
The presence rule (`Presence.lean`) on a finite history, executable, for the oracle
(docs/internals/conformance.md, "Presence"): operation `x` is the history's `x`th entry, and
`presentB` and `latestB` are proved to compute `Present` and `UMax` (`presentB_iff`,
`mem_latestB`). The search for an ancestor never goes below it, so the oracle answers quickly
for the small histories the conformance test makes.
-/
import Musubi.Presence
import Musubi.ParentsBefore
import Musubi.Identity

namespace Musubi.Presence

/-- An operation as the oracle receives it. -/
structure EOp where
  parents : List Nat := []
  work : Option Nat := none
  forgets : List Nat := []
  /-- A record of the name of the copy whose work this is (`musubi.name`), as a number. -/
  name : Option Nat := none
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
def orderedB : Bool := parentsBefore (ops.map (·.parents))

theorem parLt (ho : orderedB ops = true) : ParLt (par ops) := by
  intro y p hp
  by_cases hy : y < ops.length
  · exact parentsBefore_lt ho (i := y) (q := par ops y)
      (by simp [par, opAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hy]) hp
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

/-! ## Names (`Identity.lean`) -/

/-- The name operation `x` records for copy `k`: only its work's. -/
def namedB (x k : Nat) : Option Nat := if workB ops x k then (opAt ops x).name else none

/-- The history `ops` stands for, with its name records. -/
def nhist : Identity.NHist := { toHist := hist ops, named := namedB ops }

/-- The largest of a list. -/
def maxList : List Nat → Option Nat
  | [] => none
  | n :: ns => some ((maxList ns).elim n (max n))

theorem maxList_spec : ∀ {ns : List Nat} {m : Nat}, maxList ns = some m →
    m ∈ ns ∧ ∀ n ∈ ns, n ≤ m
  | [], _, h => by simp [maxList] at h
  | n :: ns, m, h => by
    simp only [maxList, Option.some.injEq] at h
    cases e : maxList ns with
    | none =>
      rw [e] at h
      simp only [Option.elim_none] at h
      subst h
      have : ns = [] := by
        cases ns with
        | nil => rfl
        | cons _ _ => simp [maxList] at e
      subst this
      simp
    | some m' =>
      rw [e] at h
      simp only [Option.elim_some] at h
      subst h
      obtain ⟨hm', hle⟩ := maxList_spec e
      refine ⟨?_, ?_⟩
      · rcases Nat.le_total n m' with hl | hl
        · rw [Nat.max_eq_right hl]; exact List.mem_cons_of_mem _ hm'
        · rw [Nat.max_eq_left hl]; exact List.mem_cons_self
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact Nat.le_max_left _ _
        · exact Nat.le_trans (hle a ha) (Nat.le_max_right _ _)

theorem maxList_none : ∀ {ns : List Nat}, maxList ns = none → ns = []
  | [], _ => rfl
  | _ :: _, h => by simp [maxList] at h

/-- `k`'s latest name records in `anc*(x)`. -/
def latestRecsB (x k : Nat) : List Nat :=
  let r := (List.range (x + 1)).filter fun m => ancB ops m x && (namedB ops m k).isSome
  r.filter fun m => r.all fun m' => !ancB ops m m' || m' == m

theorem mem_latestRecsB (ho : orderedB ops = true) (x k m : Nat) :
    m ∈ latestRecsB ops x k ↔ (nhist ops).LatestRec x k m := by
  have bound : ∀ m, Anc (par ops) m x → m < x + 1 :=
    fun m hm => Nat.lt_succ_of_le (hm.le (parLt ops ho))
  simp only [latestRecsB, List.mem_filter, List.mem_range, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq, Bool.and_eq_true, ancB_iff ops ho]
  show _ ↔ Anc (par ops) m x ∧ (namedB ops m k).isSome ∧ _
  constructor
  · rintro ⟨⟨-, hm, hr⟩, hall⟩
    refine ⟨hm, hr, fun m' hm' hr' hmm' => ?_⟩
    rcases hall m' ⟨bound m' hm', hm', hr'⟩ with h | h
    · rw [← Bool.not_eq_true, ancB_iff ops ho] at h
      exact absurd hmm' h
    · exact h
  · rintro ⟨hm, hr, hmax⟩
    refine ⟨⟨bound m hm, hm, hr⟩, fun m' ⟨_, hm', hr'⟩ => ?_⟩
    by_cases hmm' : Anc (par ops) m m'
    · exact Or.inr (hmax m' hm' hr' hmm')
    · left
      cases e : ancB ops m m'
      · rfl
      · exact absurd ((ancB_iff ops ho m m').1 e) hmm'

/-- `k`'s name at `x`: the greatest its latest records there give; none where it has recorded
none, and its name is the one its key embeds. -/
def nameB (x k : Nat) : Option Nat :=
  maxList ((latestRecsB ops x k).filterMap (namedB ops · k))

theorem nameB_some (ho : orderedB ops = true) {init : Nat → Nat} {x k n : Nat}
    (h : nameB ops x k = some n) : (nhist ops).NameIs init x k n := by
  obtain ⟨hn, hle⟩ := maxList_spec h
  obtain ⟨m, hm, hmn⟩ := List.mem_filterMap.mp hn
  refine Or.inl ⟨m, (mem_latestRecsB ops ho x k m).1 hm, hmn, fun m' n' hm' hn' => ?_⟩
  exact hle n' (List.mem_filterMap.mpr ⟨m', (mem_latestRecsB ops ho x k m').2 hm', hn'⟩)

theorem nameB_none (ho : orderedB ops = true) {init : Nat → Nat} {x k : Nat}
    (h : nameB ops x k = none) : (nhist ops).NameIs init x k (init k) := by
  refine Or.inr ⟨fun m hm => ?_, rfl⟩
  cases e : namedB ops m k with
  | none => exact e
  | some n₀ =>
    exfalso
    have hlt := parLt ops ho
    obtain ⟨m₀, ⟨hm₀x, hm₀r⟩, hmax⟩ := Musubi.exists_max_le
      (Q := fun m => Anc (par ops) m x ∧ (namedB ops m k).isSome)
      ⟨hm, by rw [e]; rfl⟩ (fun m hm => hm.1.le hlt)
    have hl := (nhist ops).latest_of_max hlt hm₀x hm₀r (fun m' h₁ h₂ => hmax m' ⟨h₁, h₂⟩)
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hm₀r
    have hmem : n ∈ (latestRecsB ops x k).filterMap (namedB ops · k) :=
      List.mem_filterMap.mpr ⟨m₀, (mem_latestRecsB ops ho x k m₀).2 hl, hn⟩
    rw [maxList_none h] at hmem
    simp at hmem

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

/-! Copy 7 works (0), records the name 3 (1), is forgotten (2) and returns (3); copy 8, on
another line, records the name 3 too (4); the two merge (5). -/

private def renames : List EOp :=
  [{ work := some 7 }, { parents := [0], work := some 7, name := some 3 },
    { parents := [1], forgets := [7] }, { parents := [2], work := some 7 },
    { parents := [0], work := some 8, name := some 3 }, { parents := [3, 4] }]

#guard orderedB renames
#guard (List.range 6).map (nameB renames · 7) = [none, some 3, some 3, some 3, none, some 3]
#guard nameB renames 5 8 = some 3

end EHist

end Musubi.Presence

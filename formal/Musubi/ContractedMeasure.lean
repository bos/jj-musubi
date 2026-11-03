/-
The record-aware executable progress check uses surviving images. The original mAdv can
increase when an advance replaces a dropped expected head by several surviving heads. These
definitions extend that check; they do not prove termination of the full union relation.
-/
import Musubi.ContractedExec

namespace Musubi.Exec

open Musubi Contract

def uncoveredImages (par : Nat → List Nat) (D : Nat → Bool)
    (heads : List Nat) (known : Nat) : Nat :=
  ((exp par D known).filter (fun p => !heads.any (ancB par p))).length

theorem uncoveredImages_after_advance (hlt : ParLt par)
    (hb : ∀ h ∈ heads, h < B) (hk : known < B) :
    uncoveredImages par D (advanceImages par D heads known) known = 0 := by
  unfold uncoveredImages
  have hnil : (exp par D known).filter
      (fun p => !(advanceImages par D heads known).any (ancB par p)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro p hp
    obtain ⟨h, hh, ha⟩ := advanceImages_covers hlt hb hk (Or.inr hp)
    have he : (advanceImages par D heads known).any (ancB par p) = true :=
      List.any_eq_true.2 ⟨h, hh, (ancB_iff hlt).2 ha⟩
    simp [he]
  rw [hnil]
  rfl

theorem uncoveredImages_singleton_zero (hlt : ParLt par) :
    uncoveredImages par D [h] known = 0 ↔ Below par D known h := by
  simp [uncoveredImages, List.filter_eq_nil_iff, Below, ancB_iff hlt]

def SEState.advCE (ses : SEState) (n : Nat) : Nat :=
  uncoveredImages ses.es.parF (ses.nodeDF n).contains
    (ses.es.nodeOf n).heads (ses.es.nodeOf n).known.2

def SEState.settledCE (ses : SEState) (n : Nat) : Bool :=
  match (ses.es.nodeOf n).heads with
  | [] => false
  | x :: _ =>
    (ses.es.nodeOf n).heads.all (· == x) && ancB ses.es.parF x ses.es.hub.head &&
      (!(ses.nodeDF n).contains (ses.es.nodeOf n).known.2 ||
        belowB ses.es.parF (ses.nodeDF n).contains (ses.es.nodeOf n).known.2 x) &&
      (List.range (ses.es.hub.seq + 1)).all fun i =>
        (exp ses.es.parF (ses.nodeDF n).contains (ses.es.hub.histF i)).all fun p =>
          ancB ses.es.parF x p || ancB ses.es.parF p x

def SEState.rmeasureCE (N : Nat) (ses : SEState) :
    Nat × Nat × Nat × Nat × Nat × Nat :=
  (cntE N (fun n => !(ses.es.consistentE n && ses.settledCE n)),
    cntE N (fun n => !ses.es.consistentE n), sumN N ses.es.staleRE,
    sumN N ses.es.missE, sumN N ses.advCE, sumN N ses.es.multiE)

def SEState.recordMeasureCE (N : Nat) (ses : SEState) :=
  ((ses.pendE N, ses.lagE N, ses.rmeasureCE N), ses.recordLagE N)

def SEState.recordRankCE (N : Nat) (ses : SEState) : List Nat :=
  let ((p, l, a, b, c, d, e, f), records) := ses.recordMeasureCE N
  [p, l, a, b, c, d, e, f, records]

/-- The lexicographic order used by the Rust harness's vector comparison. -/
def rankLess : List Nat → List Nat → Bool
  | [], ys => !ys.isEmpty
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x == y then rankLess xs ys else decide (x < y)

/-- Without dropped operations the extended check is exactly the old one. -/
theorem rmeasureCE_without_drops {ses : SEState} {N : Nat} (hlt : ParLt ses.es.parF)
    (hD : ∀ n x, (ses.nodeDF n).contains x = false) :
    ses.rmeasureCE N = ses.es.rmeasureE N := by
  have ha : ∀ n, ses.advCE n = ses.es.advE n := by
    intro n
    unfold SEState.advCE uncoveredImages
    rw [exp_eq hlt, hD]
    unfold EState.advE
    cases he : (ses.es.nodeOf n).heads.any (ancB ses.es.parF (ses.es.nodeOf n).known.2)
      <;> simp [he]
  have he : ∀ n x, exp ses.es.parF (ses.nodeDF n).contains x = [x] := by
    intro n x
    rw [exp_eq hlt, hD]
    rfl
  have hs : ∀ n, ses.settledCE n = ses.es.settledE n := by
    intro n
    unfold SEState.settledCE EState.settledE
    cases (ses.es.nodeOf n).heads <;>
      simp only [hD, he, Bool.not_false, Bool.true_or, Bool.and_true,
        List.all_cons, List.all_nil]
  have hadv : ses.advCE = ses.es.advE := funext ha
  simp only [SEState.rmeasureCE, EState.rmeasureE, hadv, hs]

end Musubi.Exec

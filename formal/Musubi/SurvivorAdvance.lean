/-
The local frontier step needed when the known hub head was dropped here. Waiting for its
originator is not progress after that copy left: add the head's surviving images instead.
This model checks the frontier effect and its optional merge, not the full retry refinement.
-/
import Musubi.ContractOrder
import Musubi.Supersede

namespace Musubi.Contract

/-- Add all surviving images, retaining every old head not covered by another head. -/
def advanceImages (par : Nat → List Nat) (D : Nat → Bool)
    (heads : List Nat) (known : Nat) : List Nat :=
  Exec.maxL par (dd (heads ++ exp par D known))

theorem advanceImages_set (hlt : ParLt par) :
    Exec.setP (advanceImages par D heads known) =
      maxSet par (fun x => x ∈ heads ∨ x ∈ exp par D known) := by
  rw [advanceImages, Exec.setP_maxL hlt]
  congr 1
  funext x
  exact propext (mem_dd.trans List.mem_append)

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

theorem advanceImages_nodup : (advanceImages par D heads known).Nodup := by
  unfold advanceImages Exec.maxL
  exact (ddAux_nodup [] _).filter _

theorem advanceImages_survives (hlt : ParLt par)
    (hs : ∀ h ∈ heads, D h = false) {h : Nat}
    (hh : h ∈ advanceImages par D heads known) : D h = false := by
  have hm : maxSet par (fun x => x ∈ heads ∨ x ∈ exp par D known) h := by
    rw [← advanceImages_set hlt]
    exact hh
  exact hm.1.elim (hs h) (fun hx => (mem_exp hlt hx).1)

theorem advanceImages_lt (hlt : ParLt par)
    (hb : ∀ h ∈ heads, h < B) (hk : known < B) {h : Nat}
    (hh : h ∈ advanceImages par D heads known) : h < B := by
  have hm : maxSet par (fun x => x ∈ heads ∨ x ∈ exp par D known) h := by
    rw [← advanceImages_set hlt]
    exact hh
  exact hm.1.elim (hb h) (fun hh => Nat.lt_of_le_of_lt ((mem_exp hlt hh).2.le hlt) hk)

/-- Adding the images loses neither local work nor any image needed for the hub check. -/
theorem advanceImages_covers (hlt : ParLt par)
    (hb : ∀ h ∈ heads, h < B) (hk : known < B) {x : Nat}
    (hx : x ∈ heads ∨ x ∈ exp par D known) :
    ∃ h ∈ advanceImages par D heads known, Anc par x h := by
  have hbound : ∀ y, y ∈ heads ∨ y ∈ exp par D known → y < B := by
    intro y hy
    exact hy.elim (hb y) (fun hy => Nat.lt_of_le_of_lt ((mem_exp hlt hy).2.le hlt) hk)
  obtain ⟨h, hh, hxh⟩ := below_max hlt hbound hx
  refine ⟨h, ?_, hxh⟩
  change Exec.setP (advanceImages par D heads known) h
  rwa [advanceImages_set hlt]

/-- When no merge is needed, the sole surviving head already passes the comparison. -/
theorem advanceImages_singleton_ready (hlt : ParLt par)
    (hb : ∀ h ∈ heads, h < B) (hk : known < B)
    (he : advanceImages par D heads known = [h]) : Below par D known h := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := advanceImages_covers hlt hb hk (Or.inr hp)
  rw [he] at hq
  have hqh : q = h := by simpa using hq
  exact hqh ▸ hpq

/-- Fresh operations do not change the images of an older head. -/
theorem exp_upd (hlt : ParLt par) (hL : ∀ p ∈ L, p < o) (hx : x < o) :
    exp (upd par o L) D x = exp par D x := by
  have hlt' := parLt_upd hlt hL
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rw [exp_eq hlt', exp_eq hlt, upd_ne _ _ (Nat.ne_of_lt hx)]
    split
    · apply flatMap_congr_mem
      intro p hp
      exact ih p (hlt x p hp) (by have := hlt x p hp; omega)
    · rfl

/-- Merging the resulting frontier gives one head past every surviving image. Its
expected head may be dropped; the conclusion is the contracted comparison, not original
ancestry of that expected head. -/
theorem advanceImages_merge_ready (hlt : ParLt par)
    (hb : ∀ h ∈ heads, h < o) (hk : known < o) :
    Below (upd par o (advanceImages par D heads known)) D known o := by
  have hL := fun p hp => advanceImages_lt (D := D) hlt hb hk (h := p) hp
  intro p hp
  rw [exp_upd hlt hL hk] at hp
  obtain ⟨h, hh, hph⟩ := advanceImages_covers hlt hb hk (Or.inr hp)
  exact (anc_upd_new hlt hL).2 (Or.inr ⟨h, hh, hph⟩)

/-- The same merge retains all work below the old heads. -/
theorem advanceImages_merge_keeps (hlt : ParLt par)
    (hb : ∀ h ∈ heads, h < o) (hk : known < o) {x h : Nat}
    (hh : h ∈ heads) (hxh : Anc par x h) :
    Anc (upd par o (advanceImages par D heads known)) x o := by
  have hL := fun p hp => advanceImages_lt (D := D) hlt hb hk (h := p) hp
  obtain ⟨q, hq, hhq⟩ := advanceImages_covers hlt hb hk (Or.inl hh)
  exact (anc_upd_new hlt hL).2 (Or.inr ⟨q, hq, hxh.trans hhq⟩)

end Musubi.Contract

/-
The accepted base's images (#138). `NodeAdapter::read_heads` refuses a history that has lost
the base the hub accepted, testing each image of the base that `to_node` gives against the op
heads. Once the node drops the base, the base has several images, one for each of the
operations below it that survive. `Covered` says that every image is below a head. It holds
when the core sets the base, and it survives each way the base, the drops or the op heads change
after that, so one image below a head means all are.

The executable models leave the accepted base out, so nothing here is checked against the code
or the oracle: each lemma covers one Rust step, under what it assumes of that step. Operations
are raw, original identities, as in `Supersede.lean`: renaming one, as taking records or
undoing a `jj op abandon` does, leaves it the same operation.

- `NodeCore::step` sets the base to `known` when `is_ancestor(known, head)` holds, which tests
  every image of `known` against that head (`covered_of_below`). After `advance(known)`
  succeeds it sets the base to `known` anyway: the op heads then cover every surviving image
  (`covered_advance`), and a merge of them keeps that (`covered_upd`, `covered_heads`).
- A node's dropped originals only grow (**DroppedGrows**): pending drops it notices in
  `settle`, and drops it takes with the hub's records, keep or rename what they don't drop,
  and a record the hub loses leaves its drops pending again (`covered_drops`).
- Taking a record that drops the base renames it to the first of its images, contracting by
  the drops so far and the record's (`exp_union`): `covered_drops`, then `covered_image`.
  Where the hub lost records this node took, the base becomes the root, below every head.
- jj's op heads only move up: a new operation descends from heads, jj removes a head only when
  a new head descends from it, and `jj op abandon` refuses the current operation, so the drops
  it makes are never op heads, whose rewrites are the same operations (`covered_upd`,
  `covered_heads`). This is `Supersede.lean`'s `abandon` step, which drops no head.
- The node's store holds the history contracted by its drops, where ancestry between
  survivors is raw ancestry (`anc_cpar_iff`): every image is below a head there too
  (`covered_contracted`).

So `read_heads` can require every image to be below a head: no state these steps reach fails
that, and a history that kept only some of the images, which only lost history could be, does.
-/
import Musubi.ContractOrder
import Musubi.SurvivorAdvance

namespace Musubi.Contract

/-- Every surviving image of `base` is below one of `heads`. -/
def Covered (par : Nat → List Nat) (D : Nat → Bool) (heads : List Nat) (base : Nat) : Prop :=
  ∀ p ∈ exp par D base, ∃ h ∈ heads, Anc par p h

variable {par : Nat → List Nat} {D E : Nat → Bool} {heads heads' L : List Nat}
  {base o p B known h : Nat}

/-- The core sets the base below a head: `is_ancestor` passed for that head. -/
theorem covered_of_below (hh : h ∈ heads) (hb : Below par D base h) :
    Covered par D heads base :=
  fun p hp => ⟨h, hh, hb p hp⟩

/-- Or it sets the base after advancing the op heads to its surviving images. -/
theorem covered_advance (hlt : ParLt par) (hb : ∀ h ∈ heads, h < B) (hk : known < B) :
    Covered par D (advanceImages par D heads known) known :=
  fun _ hp => advanceImages_covers hlt hb hk (Or.inr hp)

/-- More drops, noticed or taken, keep every image below a head: each new image is below an
old one. -/
theorem covered_drops (hlt : ParLt par) (hDE : ∀ x, D x = true → E x = true)
    (hc : Covered par D heads base) : Covered par E heads base := by
  intro p hp
  obtain ⟨hpE, hpb⟩ := mem_exp hlt hp
  have hpD : D p = false := by
    cases hd : D p
    · rfl
    · rw [hDE p hd] at hpE
      contradiction
  obtain ⟨q, hq, hpq⟩ := exp_covers hlt hpb hpD
  obtain ⟨g, hg, hqg⟩ := hc q hq
  exact ⟨g, hg, hpq.trans hqg⟩

/-- Records that drop the base rename it to one of its images. Under any drops, that image's
own images are then below a head. -/
theorem covered_image (hlt : ParLt par) (hc : Covered par D heads base)
    (hp : p ∈ exp par D base) : Covered par E heads p := by
  intro q hq
  obtain ⟨g, hg, hpg⟩ := hc p hp
  exact ⟨g, hg, (mem_exp hlt hq).2.trans hpg⟩

/-- The op heads move up: each old head is below a new one. -/
theorem covered_heads (hc : Covered par D heads base)
    (hup : ∀ g ∈ heads, ∃ g' ∈ heads', Anc par g g') : Covered par D heads' base := by
  intro p hp
  obtain ⟨g, hg, hpg⟩ := hc p hp
  obtain ⟨g', hg', hgg'⟩ := hup g hg
  exact ⟨g', hg', hpg.trans hgg'⟩

/-- A new operation `o` changes neither the images of an older base nor any ancestry below the
old heads. -/
theorem covered_upd (hlt : ParLt par) (hL : ∀ p ∈ L, p < o) (hbase : base < o)
    (hheads : ∀ g ∈ heads, g < o) (hc : Covered par D heads base) :
    Covered (upd par o L) D heads base := by
  intro p hp
  rw [exp_upd hlt hL hbase] at hp
  obtain ⟨g, hg, hpg⟩ := hc p hp
  exact ⟨g, hg, (anc_upd_iff hlt hL (hheads g hg)).2 hpg⟩

/-- `read_heads` tests the images in the node's store, which is the history contracted by its
drops. There, too, every image is below a head. -/
theorem covered_contracted (hlt : ParLt par) (hc : Covered par D heads base) :
    ∀ p ∈ exp par D base, ∃ g ∈ heads, Anc (cpar par D) p g := by
  intro p hp
  obtain ⟨g, hg, hpg⟩ := hc p hp
  exact ⟨g, hg, (anc_cpar_iff hlt (mem_exp hlt hp).1).2 hpg⟩

end Musubi.Contract

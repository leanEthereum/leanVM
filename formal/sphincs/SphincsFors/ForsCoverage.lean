import SphincsFors.Uniform
import Mathlib.Data.BitVec

/-!
The full view of a 266-bit message digest (its index and one leaf per FORS tree) is a bijection,
so a uniform digest gives a uniform view; and FORS coverage of a view by a fixed disclosure table.
The bit-decomposition argument is adapted from leanVM b7a107256 for 24 unpinned trees.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000
set_option exponentiation.threshold 512

namespace SphincsFors.Concrete

abbrev FullDigestView := Index × (IndexGroup → FtsLeaf)

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, digestLeaves digest)

theorem fullDigestView_injective : Function.Injective fullDigestView := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position < totalHeight
  · have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin view.1) heq
    have hbit := congrArg (fun bits : BitVec totalHeight => bits.getLsbD position) hcomponent
    simpa [fullDigestView, digestIndex, BitVec.getLsbD_extractLsb', hindex] using hbit
  · let treeIndex := (position - totalHeight) / ftsTreeHeight
    have htreeIndex : treeIndex < ftsTrees := by
      have hposition' : position < 266 := by
        simpa [messageDigestBits, totalHeight, ftsTrees, ftsTreeHeight] using hposition
      have hindex' : 26 ≤ position := by
        simpa [totalHeight] using Nat.le_of_not_gt hindex
      simp only [treeIndex, ftsTrees, ftsTreeHeight, totalHeight]
      omega
    let tree : IndexGroup := ⟨treeIndex, htreeIndex⟩
    let within := (position - totalHeight) % ftsTreeHeight
    have hwithin : within < ftsTreeHeight := by
      simp only [within, ftsTreeHeight]
      omega
    have hoffset : totalHeight + ftsTreeHeight * tree.val + within = position := by
      have hindex' : totalHeight ≤ position := Nat.le_of_not_gt hindex
      simp only [tree, treeIndex, within]
      calc
        totalHeight + ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight) +
            (position - totalHeight) % ftsTreeHeight =
            totalHeight + ((position - totalHeight) % ftsTreeHeight +
              ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight)) := by omega
        _ = totalHeight + (position - totalHeight) := by rw [Nat.mod_add_div]
        _ = position := Nat.add_sub_of_le hindex'
    have hcomponent := congrArg (fun view : FullDigestView => BitVec.ofFin (view.2 tree)) heq
    change left.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight =
      right.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight at hcomponent
    have hbit := congrArg (fun bits : BitVec ftsTreeHeight => bits.getLsbD within) hcomponent
    simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
    rwa [hoffset] at hbit

theorem fullDigestView_bijective : Function.Bijective fullDigestView := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fullDigestView_injective, ?_⟩
  rw [card_bitVec, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← pow_add]
  rfl

theorem evalDist_fullDigestView_uniform :
    𝒟[fullDigestView <$> ($ᵗ MessageDigest : ProbComp MessageDigest)] =
    𝒟[($ᵗ FullDigestView : ProbComp FullDigestView)] :=
  evalDist_map_bijective_uniform_cross (α := MessageDigest) (β := FullDigestView)
    fullDigestView fullDigestView_bijective

/-- The leaves disclosed by signatures at each FORS instance. Sets count distinct openings. -/
abbrev Disclosures := Index → FtsTree → Finset FtsLeaf

def Covered (revealed : Disclosures) (view : FullDigestView) : Prop :=
  ∀ tree : FtsTree, view.2 tree ∈ revealed view.1 tree

instance (revealed : Disclosures) : DecidablePred (Covered revealed) :=
  fun view => inferInstanceAs (Decidable (∀ tree : FtsTree, view.2 tree ∈ revealed view.1 tree))

end SphincsFors.Concrete

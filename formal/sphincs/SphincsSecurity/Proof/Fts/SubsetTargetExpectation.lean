import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.SubsetTargetAssignment
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sum_leaf_partial_product (required : Finset FtsTree) (weight : FtsTree → FtsLeaf → Nat) :
    (∑ leaves : FtsTree → FtsLeaf, ∏ tree ∈ required, weight tree (leaves tree)) =
      Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) * ∏ tree ∈ required, ∑ leaf : FtsLeaf, weight tree leaf := by
  have hprod (leaves : FtsTree → FtsLeaf) := Fintype.prod_ite_mem required (fun tree => weight tree (leaves tree))
  simp only [← hprod]
  rw [← Fintype.prod_sum (fun tree leaf => if tree ∈ required then weight tree leaf else 1)]
  have hsum (tree : FtsTree) : (∑ leaf : FtsLeaf, if tree ∈ required then weight tree leaf else 1) =
      if tree ∈ required then ∑ leaf : FtsLeaf, weight tree leaf else Fintype.card FtsLeaf := by
    split_ifs <;> simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  simp only [hsum]
  rw [← Finset.prod_sdiff (Finset.subset_univ required)]
  rw [Finset.prod_ite_of_true (fun tree ht => ht), Finset.prod_ite_of_false (fun tree ht => (Finset.mem_sdiff.mp ht).2)]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ required), Finset.card_univ]

theorem sourceSubsetMatch_index (target : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty)
    (index : Index) (leaves : FtsTree → FtsLeaf) :
    sourceSubsetMatch target (index, leaves) required =
      if index = target.1 then ∏ tree ∈ required, (if leaves tree = target.2 tree then 1 else 0) else 0 := by
  by_cases hi : index = target.1
  · simp only [sourceSubsetMatch, sourceTreeMatch, hi, true_and, if_true]
  · obtain ⟨tree, htree⟩ := hne
    simp only [sourceSubsetMatch, sourceTreeMatch, hi, false_and, if_false]
    exact Finset.prod_eq_zero htree rfl

theorem sum_sourceSubsetMatch (target : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty) :
    (∑ source : FewTimeView, sourceSubsetMatch target source required) =
      Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) := by
  rw [Fintype.sum_prod_type]
  simp only [sourceSubsetMatch_index target required hne, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [sum_leaf_partial_product required (fun tree leaf => if leaf = target.2 tree then 1 else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.prod_const_one, mul_one]

theorem expected_sourceSubsetMatch (target : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * (sourceSubsetMatch target source required : ENNReal)) =
      (Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) : Nat) / (Fintype.card FewTimeView : ENNReal) := by
  simp only [probOutput_uniformSample, tsum_fintype]
  rw [← Finset.mul_sum, ← Nat.cast_sum, sum_sourceSubsetMatch target required hne]
  exact mul_comm _ _

theorem normalized_expected_sourceSubsetMatch (target : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty) :
    (Fintype.card FtsLeaf ^ required.card : Nat) *
      (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * (sourceSubsetMatch target source required : ENNReal)) =
      (Fintype.card Index : ENNReal)⁻¹ := by
  have hcard : Fintype.card FewTimeView = Fintype.card FtsLeaf ^ Fintype.card FtsTree * Fintype.card Index := by
    simp only [FewTimeView, Fintype.card_prod, Fintype.card_fun]
    exact mul_comm _ _
  have hle : required.card ≤ Fintype.card FtsTree := Finset.card_le_univ required
  have hexp : required.card + (Fintype.card FtsTree - required.card) = Fintype.card FtsTree := by omega
  have hzero : ((Fintype.card FtsLeaf ^ Fintype.card FtsTree : Nat) : ENNReal) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (ne_of_gt (Fintype.card_pos)))
  have hfinite : ((Fintype.card FtsLeaf ^ Fintype.card FtsTree : Nat) : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [expected_sourceSubsetMatch target required hne, div_eq_mul_inv, ← mul_assoc, ← Nat.cast_mul, ← pow_add, hexp, hcard,
    Nat.cast_mul, ENNReal.mul_inv (Or.inl hzero) (Or.inl hfinite),
    ← mul_assoc, ENNReal.mul_inv_cancel hzero hfinite, one_mul]

end SphincsSecurity.Concrete

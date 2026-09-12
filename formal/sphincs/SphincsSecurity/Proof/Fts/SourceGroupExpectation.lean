import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.NormalizedTargetMatches

/-! ## TargetBlockExpectation -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_symm (target source : FewTimeView) (required : Finset FtsTree) :
    sourceSubsetMatch target source required = sourceSubsetMatch source target required := by
  unfold sourceSubsetMatch
  apply Finset.prod_congr rfl
  intro tree _
  simp only [sourceTreeMatch, eq_comm]

theorem sourceSubsetMatch_index_leaf (source : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty)
    (index : Index) (leaves : FtsTree → FtsLeaf) :
    sourceSubsetMatch (index, leaves) source required =
      (if source.1 = index then 1 else 0) * ∏ tree ∈ required, (if leaves tree = source.2 tree then 1 else 0) := by
  rw [sourceSubsetMatch_symm, sourceSubsetMatch_index source required hne]
  by_cases hi : index = source.1 <;> simp only [hi, eq_comm, if_true, if_false, one_mul, zero_mul]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def sourceGroupLeaves {α : Type} (groups : α → Finset FtsTree) (sources : α → FewTimeView) (tree : FtsTree) : FtsLeaf :=
  if h : ∃ slot, tree ∈ groups slot then (sources h.choose).2 tree else default

theorem sourceGroupLeaves_of_mem {α : Type} (groups : α → Finset FtsTree) (sources : α → FewTimeView)
    (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j))) (slot : α) (tree : FtsTree) (htree : tree ∈ groups slot) :
    sourceGroupLeaves groups sources tree = (sources slot).2 tree := by
  have hex : ∃ slot, tree ∈ groups slot := ⟨slot, htree⟩
  have heq : hex.choose = slot := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisjoint hne) hex.choose_spec htree
  simp only [sourceGroupLeaves, dif_pos hex, heq]

theorem sum_leaf_sourceGroupMatches {α : Type} [Fintype α] (groups : α → Finset FtsTree)
    (hne : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (sources : α → FewTimeView) (index : Index) :
    (∑ leaves : FtsTree → FtsLeaf, ∏ slot : α, sourceSubsetMatch (index, leaves) (sources slot) (groups slot)) =
      Fintype.card FtsLeaf ^ (Fintype.card FtsTree - (Finset.univ.biUnion groups).card) *
        ∏ slot : α, if (sources slot).1 = index then 1 else 0 := by
  classical
  have hprod (leaves : FtsTree → FtsLeaf) :
      (∏ slot : α, ∏ tree ∈ groups slot, if leaves tree = (sources slot).2 tree then 1 else 0) =
        ∏ tree ∈ Finset.univ.biUnion groups, if leaves tree = sourceGroupLeaves groups sources tree then 1 else 0 := by
    rw [Finset.prod_biUnion (fun i _ j _ hij => hdisjoint hij)]
    apply Finset.prod_congr rfl
    intro slot _
    apply Finset.prod_congr rfl
    intro tree htree
    rw [sourceGroupLeaves_of_mem groups sources hdisjoint slot tree htree]
  simp only [sourceSubsetMatch_index_leaf _ _ (hne _), Finset.prod_mul_distrib, hprod, ← Finset.mul_sum]
  rw [sum_leaf_partial_product (Finset.univ.biUnion groups)
    (fun tree leaf => if leaf = sourceGroupLeaves groups sources tree then 1 else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.prod_const_one, mul_one]
  exact mul_comm _ _

theorem sum_sourceGroupMatches {α : Type} [Fintype α] (groups : α → Finset FtsTree)
    (hne : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (sources : α → FewTimeView) :
    (∑ target : FewTimeView, ∏ slot : α, sourceSubsetMatch target (sources slot) (groups slot)) =
      Fintype.card FtsLeaf ^ (Fintype.card FtsTree - (Finset.univ.biUnion groups).card) *
        ∑ index : Index, ∏ slot : α, if (sources slot).1 = index then 1 else 0 := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun index _ => sum_leaf_sourceGroupMatches groups hne hdisjoint sources index)

theorem normalized_target_leaf_rate (required : Finset FtsTree) :
    (Fintype.card FtsLeaf ^ required.card : Nat) *
      ((Fintype.card FtsLeaf ^ (Fintype.card FtsTree - required.card) : Nat) / (Fintype.card FewTimeView : ENNReal)) =
        (Fintype.card Index : ENNReal)⁻¹ := by
  have hcard : Fintype.card FewTimeView = Fintype.card FtsLeaf ^ Fintype.card FtsTree * Fintype.card Index := by
    simp only [FewTimeView, Fintype.card_prod, Fintype.card_fun]
    exact mul_comm _ _
  have hle : required.card ≤ Fintype.card FtsTree := Finset.card_le_univ required
  have hexp : required.card + (Fintype.card FtsTree - required.card) = Fintype.card FtsTree := by omega
  have hzero : ((Fintype.card FtsLeaf ^ Fintype.card FtsTree : Nat) : ENNReal) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero _ (ne_of_gt Fintype.card_pos))
  have hfinite : ((Fintype.card FtsLeaf ^ Fintype.card FtsTree : Nat) : ENNReal) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [div_eq_mul_inv, ← mul_assoc, ← Nat.cast_mul, ← pow_add, hexp, hcard,
    Nat.cast_mul, ENNReal.mul_inv (Or.inl hzero) (Or.inl hfinite),
    ← mul_assoc, ENNReal.mul_inv_cancel hzero hfinite, one_mul]

theorem expected_normalized_sourceGroupMatches {α : Type} [Fintype α] (groups : α → Finset FtsTree)
    (hne : ∀ slot, (groups slot).Nonempty) (hdisjoint : Pairwise (fun i j => Disjoint (groups i) (groups j)))
    (sources : α → FewTimeView) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      ∏ slot : α, normalizedSourceSubsetMatch target (sources slot) (groups slot)) =
        (Fintype.card Index : ENNReal)⁻¹ *
          ∑ index : Index, ∏ slot : α, if (sources slot).1 = index then (1 : ENNReal) else 0 := by
  classical
  have hcard : (Finset.univ.biUnion groups).card = ∑ slot : α, (groups slot).card :=
    Finset.card_biUnion (fun i _ j _ hij => hdisjoint hij)
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, ← hcard, probOutput_uniformSample, tsum_fintype]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Nat.cast_sum, sum_sourceGroupMatches groups hne hdisjoint sources, Nat.cast_mul]
  calc
    _ = ((Fintype.card FtsLeaf ^ (Finset.univ.biUnion groups).card : Nat) *
        ((Fintype.card FtsLeaf ^ (Fintype.card FtsTree - (Finset.univ.biUnion groups).card) : Nat) /
          (Fintype.card FewTimeView : ENNReal))) *
        (∑ index : Index, ∏ slot : α, if (sources slot).1 = index then 1 else 0 : Nat) := by
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [normalized_target_leaf_rate]
      simp only [Nat.cast_sum, Nat.cast_prod, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

end SphincsSecurity.Concrete

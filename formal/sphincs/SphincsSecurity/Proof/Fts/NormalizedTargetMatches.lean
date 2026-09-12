import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FutureCoverageBound
import SphincsSecurity.Proof.Fts.SubsetTargetExpectation

/-! ## TargetCacheProductQuery -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset FtsTree) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedSourceSubsetMatch (target source : FewTimeView) (required : Finset FtsTree) : ENNReal :=
  (Fintype.card FtsLeaf ^ required.card : Nat) * (sourceSubsetMatch target source required : ENNReal)

theorem normalizedSourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset FtsTree)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_prod, Finset.card_biUnion hdisjoint]

theorem expected_normalizedSourceSubsetMatch (target : FewTimeView) (required : Finset FtsTree) (hne : required.Nonempty) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] * normalizedSourceSubsetMatch target source required) =
      (Fintype.card Index : ENNReal)⁻¹ := by
  simp only [normalizedSourceSubsetMatch, mul_left_comm (Pr[= _ | ($ᵗ FewTimeView : ProbComp FewTimeView)]), ENNReal.tsum_mul_left]
  exact normalized_expected_sourceSubsetMatch target required hne

theorem expected_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (selected : Finset (Fin m)) (hselected : selected.Nonempty) (hgroups : ∀ slot ∈ selected, (groups slot).Nonempty)
    (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' source, Pr[= source | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) = (Fintype.card Index : ENNReal)⁻¹ := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint]
  obtain ⟨slot, hslot⟩ := hselected
  obtain ⟨tree, htree⟩ := hgroups slot hslot
  exact expected_normalizedSourceSubsetMatch target _ ⟨tree, Finset.mem_biUnion.mpr ⟨slot, hslot, htree⟩⟩

theorem expected_hash_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset FtsTree)
    (selected : Finset (Fin m)) (hselected : selected.Nonempty) (hgroups : ∀ slot ∈ selected, (groups slot).Nonempty)
    (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹ := by
  rw [expected_uniformHashOutput_admissible_weight
    (fun source => ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)),
    expected_normalizedSourceSubsetMatch_prod target groups selected hselected hgroups hdisjoint]

end SphincsSecurity.Concrete

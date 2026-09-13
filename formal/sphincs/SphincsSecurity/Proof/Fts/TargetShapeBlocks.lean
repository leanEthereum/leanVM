import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
import SphincsSecurity.Proof.Fts.TargetSourceMultiplicity
import SphincsSecurity.Proof.Fts.WeightedTargetGroups
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

abbrev TargetShapeSlot (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) := groups ⊕ remaining

def targetShapeSlotGroup (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : TargetShapeSlot groups remaining → Finset FtsTree
  | .inl group => group.val
  | .inr tree => {tree.val}

theorem targetShapeSlotGroup_nonempty (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) (slot : TargetShapeSlot groups remaining) : (targetShapeSlotGroup groups remaining slot).Nonempty := by
  cases slot with
  | inl group => exact hvalid.nonempty group.val group.property
  | inr tree => exact Finset.singleton_nonempty tree.val

theorem targetShapeSlotGroup_disjoint (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree)
    (hvalid : TargetShapeValid groups remaining) : Pairwise (fun i j => Disjoint (targetShapeSlotGroup groups remaining i) (targetShapeSlotGroup groups remaining j)) := by
  intro first second hne
  cases first with
  | inl first =>
      cases second with
      | inl second =>
          exact hvalid.disjoint first.val first.property second.val second.property
            (fun heq => hne (congrArg Sum.inl (Subtype.ext heq)))
      | inr second => exact (hvalid.remaining first.val first.property).mono_right (Finset.singleton_subset_iff.mpr second.property)
  | inr first =>
      cases second with
      | inl second => exact ((hvalid.remaining second.val second.property).mono_right (Finset.singleton_subset_iff.mpr first.property)).symm
      | inr second =>
          apply Finset.disjoint_left.mpr
          intro tree hfirst hsecond
          have heq : first.val = second.val := (Finset.mem_singleton.mp hfirst).symm.trans (Finset.mem_singleton.mp hsecond)
          exact hne (congrArg Sum.inr (Subtype.ext heq))

noncomputable def targetShapeSlotWeight (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (payload : HashInput)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : TargetShapeSlot groups remaining → FewTimeView → ENNReal
  | .inl _ => excludedCacheSourceCount key.parameter cache (tweakableHashInput key.parameter .message payload)
  | .inr _ => optionalSourceCount (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root payload log)

theorem targetShapeMoments_eq_weightedGroups (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeMoments key cache log payload target groups remaining =
      ∏ slot : TargetShapeSlot groups remaining, ∑ source : FewTimeView,
        targetShapeSlotWeight key cache log payload groups remaining slot source *
          normalizedSourceSubsetMatch target source (targetShapeSlotGroup groups remaining slot) := by
  simp only [Fintype.prod_sum_type, targetShapeSlotWeight, targetShapeSlotGroup,
    ← normalizedCachedTargetSubsetMatch_eq_sourceCount, ← normalizedTargetTreeMatchCount_eq_sourceCount,
    Finset.prod_coe_sort, targetShapeMoments, normalizedTargetLogProduct, normalizedTargetLogMatch]
  rw [Finset.prod_coe_sort remaining (fun tree => (Fintype.card FtsLeaf : ENNReal) *
    (targetTreeMatchCount (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root payload log) target tree : ENNReal))]

noncomputable def excludedCacheIndexCount (parameter : PublicParameter) (cache : QueryCache HashSpec) (targetInput : HashInput) (index : Index) : ENNReal :=
  cacheMessageWeight parameter (fun input source => if input = targetInput then 0 else if source.1 = index then 1 else 0) cache

theorem excludedCacheSourceCount_index (parameter : PublicParameter) (cache : QueryCache HashSpec) (targetInput : HashInput) (index : Index) :
    (∑ source : FewTimeView, if source.1 = index then excludedCacheSourceCount parameter cache targetInput source else 0) =
      excludedCacheIndexCount parameter cache targetInput index := by
  have heq (source : FewTimeView) : (if source.1 = index then excludedCacheSourceCount parameter cache targetInput source else 0) =
      excludedCacheSourceCount parameter cache targetInput source * (if source.1 = index then 1 else 0) := by
    split_ifs <;> simp only [mul_one, mul_zero]
  simp only [heq, excludedCacheSourceCount_weight, excludedCacheIndexCount]

theorem expected_targetShapeMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * targetShapeMoments key cache log payload target groups remaining) =
      (Fintype.card Index : ENNReal)⁻¹ * ∑ index : Index,
        excludedCacheIndexCount key.parameter cache (tweakableHashInput key.parameter .message payload) index ^ groups.card *
          ((signingSlotsAtIndex (eligibleSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root payload log) index).card : ENNReal) ^ remaining.card := by
  classical
  simp only [targetShapeMoments_eq_weightedGroups]
  rw [expected_weighted_targetGroups _ (targetShapeSlotGroup_nonempty groups remaining hvalid)
    (targetShapeSlotGroup_disjoint groups remaining hvalid)]
  simp only [Fintype.prod_sum_type, targetShapeSlotWeight, excludedCacheSourceCount_index, optionalSourceCount_index,
    Finset.prod_const, Finset.card_univ, Fintype.card_coe]

end SphincsSecurity.Concrete

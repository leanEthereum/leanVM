import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.TargetShapeOperators
import SphincsSecurity.Proof.Fts.TargetShapeReindex
import SphincsSecurity.Proof.Fts.NormalizedTargetCacheQuery
import SphincsSecurity.Proof.Fts.TargetSigningMatchFactors

/-! ## ClosedTargetMixedSigning -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetMixedMoment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Fin m → Finset FtsTree) (required : Finset FtsTree) : ENNReal :=
  normalizedTargetCacheProduct key.parameter cache (tweakableHashInput key.parameter .message payload) target groups *
    normalizedTargetLogProduct key cache log payload target required

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetShapeMoments (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) : TargetShapeVector :=
  fun groups remaining =>
    (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
      (tweakableHashInput key.parameter .message payload) target group) *
        normalizedTargetLogProduct key cache log payload target remaining

theorem targetShapeMoments_eq_indexed (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetShapeMoments key cache log payload target groups remaining =
      normalizedTargetMixedMoment key cache log payload target (targetGroupAt groups) remaining := by
  simp only [targetShapeMoments, normalizedTargetMixedMoment, normalizedTargetCacheProduct, prod_targetGroupAt]

theorem targetShapeMoments_cacheLower_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    targetCacheLower (targetShapeMoments key cache log payload target) groups remaining =
      (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
        ∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed,
          normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload)
            target (targetGroupAt groups slot)) * normalizedTargetLogProduct key cache log payload target remaining := by
  rw [sum_targetGroupAt_removed_products, Finset.sum_mul]
  rfl

theorem targetShapeMoments_reuse_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    targetReuseStep (targetShapeMoments key cache log payload target) groups remaining =
      (∏ group ∈ groups, normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) target group) *
          ∑ selected ∈ remaining.powerset.erase ∅,
            normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
              normalizedTargetLogProduct key cache log payload target (remaining \ selected) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro selected hselected
  have hnot := hvalid.new_group (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2)
  simp only [targetShapeMoments, Finset.prod_insert hnot]
  ring

theorem targetShapeMoments_cross_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) :
    (∑ removed ∈ (Finset.univ : Finset (Fin groups.card)).powerset.erase ∅,
      ∑ trees ∈ remaining.powerset,
        (∏ slot ∈ (Finset.univ : Finset (Fin groups.card)) \ removed,
          normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload)
            target (targetGroupAt groups slot)) * normalizedTargetLogProduct key cache log payload target (remaining \ trees)) =
      targetCacheLower (targetShapeMoments key cache log payload target) groups remaining +
        targetCacheLower (targetTreeLower (targetShapeMoments key cache log payload target)) groups remaining := by
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_targetGroupAt_removed_products, Finset.sum_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset remaining)]
  simp only [Finset.sdiff_empty, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rfl

end SphincsSecurity.Concrete

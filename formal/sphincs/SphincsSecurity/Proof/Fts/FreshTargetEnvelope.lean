import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeQuery
import SphincsSecurity.Proof.Fts.FreshTargetShapeAverage
import SphincsSecurity.Proof.Fts.TargetIndexEnvelope
import SphincsSecurity.Proof.Fts.TargetShapeExpectation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_fresh_targetShapeEnvelope (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key cache log payload target) groups remaining) =
        (Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key cache log) groups.card remaining.card := by
  rw [targetShapeEnvelope_expected]
  have heq : ∀ G R, TargetShapeValid G R →
      (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * targetShapeMoments key cache log payload target G R) =
        (Fintype.card Index : ENNReal)⁻¹ * liftTargetIndexVector (targetIndexMoments key cache log) G R :=
    fun G R hv => expected_fresh_targetShapeMoments key cache log payload hfresh hsigned G R hv
  rw [targetShapeEnvelope_congr uniform reuse arrival queries signings heq groups remaining hvalid,
    targetShapeEnvelope_mul, targetShapeEnvelope_lift uniform reuse arrival queries signings _ groups remaining hvalid]

theorem targetShapeMoments_cacheQuery_self_vector (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload target =
      targetShapeMoments key before log payload target := by
  funext groups remaining
  exact targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining _ output hfresh hsigned (Or.inr rfl)

theorem expected_cacheQuery_freshTargetEnvelope (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload (hashOutputFewTimeView output))
          groups remaining else 0)) =
      (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
        targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card := by
  simp only [targetShapeMoments_cacheQuery_self_vector key before log payload _ _ hfresh hsigned]
  rw [expected_uniformHashOutput_admissible_weight
    (fun target => targetShapeEnvelope uniform reuse arrival queries signings (targetShapeMoments key before log payload target) groups remaining),
    expected_fresh_targetShapeEnvelope key before log payload hfresh hsigned uniform reuse arrival queries signings groups remaining hvalid]
  exact (mul_assoc _ _ _).symm

end SphincsSecurity.Concrete

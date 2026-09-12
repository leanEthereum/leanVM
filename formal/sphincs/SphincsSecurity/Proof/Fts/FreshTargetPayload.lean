import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CachedTargetIncrement
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem cacheMessageWeight_exclude_fresh (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (hfresh : cache targetInput = none) (weight : FewTimeView → ENNReal) :
    cacheMessageWeight parameter (fun input source => if input = targetInput then 0 else weight source) cache =
      cacheMessageWeight parameter (fun _ source => weight source) cache := by
  unfold cacheMessageWeight
  apply tsum_congr
  intro input
  by_cases heq : input = targetInput
  · subst input
    simp only [cacheMessageEntryWeight, hfresh]
  · unfold cacheMessageEntryWeight
    cases cache input <;> simp only [heq, if_false]

theorem targetShapeMoments_fresh_payload_eq (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (first second : HashInput)
    (hfirst : cache (tweakableHashInput key.parameter .message first) = none)
    (hsecond : cache (tweakableHashInput key.parameter .message second) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (target : FewTimeView) :
    targetShapeMoments key cache log first target = targetShapeMoments key cache log second target := by
  funext groups remaining
  unfold targetShapeMoments normalizedTargetLogProduct normalizedTargetLogMatch
  simp only [normalizedCachedTargetSubsetMatch_eq_weight,
    cacheMessageWeight_exclude_fresh key.parameter cache _ hfirst,
    cacheMessageWeight_exclude_fresh key.parameter cache _ hsecond,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log first hfirst hsigned,
    eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log second hsecond hsigned]

end SphincsSecurity.Concrete

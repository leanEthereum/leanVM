import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
import SphincsSecurity.Proof.Fts.TargetShapeEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem normalizedTargetLogProduct_cache_stable (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (remaining : Finset FtsTree)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    normalizedTargetLogProduct key after log payload target remaining = normalizedTargetLogProduct key before log payload target remaining := by
  simp only [normalizedTargetLogProduct, normalizedTargetLogMatch, eligibleSigningViews_cache_stable key before after log payload hcache hsigned]

theorem expected_cacheQuery_targetShapeMoments (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (input : HashInput) (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : FtsProbeSimulation.MessageHashInput key.parameter input) (hne : input ≠ tweakableHashInput key.parameter .message payload) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining) =
        targetShapeQuery (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          (targetShapeMoments key before log payload target) groups remaining := by
  simp only [targetShapeMoments_eq_indexed, normalizedTargetMixedMoment,
    normalizedTargetLogProduct_cache_stable key before _ log payload target remaining (QueryCache.le_cacheQuery before hfresh) hsigned,
    ← mul_assoc, ENNReal.tsum_mul_right]
  rw [expected_normalizedTargetCacheProduct_cacheQuery key.parameter before _ target (targetGroupAt groups)
    (fun slot => hvalid.nonempty _ (targetGroupAt_mem groups slot))
    (fun i j hij => hvalid.disjoint _ (targetGroupAt_mem groups i) _ (targetGroupAt_mem groups j)
      (fun heq => hij (targetGroupAt_injective groups heq))) input hfresh hmessage hne]
  unfold targetShapeQuery
  rw [targetShapeMoments_cacheLower_eq]
  simp only [targetShapeMoments_eq_indexed, normalizedTargetMixedMoment]
  ring

theorem targetShapeMoments_cacheQuery_unchanged (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hskip : ¬ FtsProbeSimulation.MessageHashInput key.parameter input ∨ input = tweakableHashInput key.parameter .message payload) :
    targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining =
      targetShapeMoments key before log payload target groups remaining := by
  simp only [targetShapeMoments,
    normalizedTargetLogProduct_cache_stable key before _ log payload target remaining (QueryCache.le_cacheQuery before hfresh) hsigned]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  rcases hskip with hmessage | rfl
  · simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery key.parameter before _ target group input output hfresh,
      hmessage, false_and, if_false, add_zero]
  · simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery_self key.parameter before _ target group output hfresh]

theorem expected_randomOracle_targetShapeMoments_le (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining)
    (input : HashInput) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      targetShapeMoments key result.2 log payload target groups remaining) ≤
        targetShapeQuery (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
          (targetShapeMoments key before log payload target) groups remaining := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  by_cases hfresh : before input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining) ≤ _
    by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input
    · by_cases heq : input = tweakableHashInput key.parameter .message payload
      · simp only [targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining input _ hfresh hsigned (Or.inr heq),
          ENNReal.tsum_mul_right, hmass, one_mul]
        exact le_self_add
      · exact (expected_cacheQuery_targetShapeMoments key before log payload target groups remaining hvalid input hfresh hsigned hmessage heq).le
    · simp only [targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining input _ hfresh hsigned (Or.inl hmessage),
        ENNReal.tsum_mul_right, hmass, one_mul]
      exact le_self_add
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    exact le_self_add

end SphincsSecurity.Concrete

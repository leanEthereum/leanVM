import SphincsSecurity.Proof.Fts.CertificateCacheExceptionGrowth
import SphincsSecurity.Proof.Fts.MessageCacheProjection
import SphincsSecurity.Proof.Reference.BoundaryMessageCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers MessageHashInput messageHashCharge)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] messageDeficitMoment cachedIndexExcessMoment positiveScoreMoment
set_option backward.isDefEq.respectTransparency false

theorem messageDeficitMoment_messageAnswers (parameter : PublicParameter) (root : Digest) (before after : QueryCache HashSpec)
    (hanswers : messageAnswers parameter before = messageAnswers parameter after) (power : Nat) :
    messageDeficitMoment parameter root before power = messageDeficitMoment parameter root after power := by
  have heq := messageOnlyCache_eq_of_messageAnswers_eq parameter before after hanswers
  have hscore (cache : QueryCache HashSpec) (message : Message) :
      messageDeficitScore parameter root message (messageOnlyCache parameter cache) = messageDeficitScore parameter root message cache := by
    simp only [messageDeficitScore, cachedMessageEntryCount_messageOnlyCache, cachedMessageEntryCountWhere_messageOnlyCache]
  unfold messageDeficitMoment
  apply Finset.sum_congr rfl
  intro message _
  rw [← hscore before message, ← hscore after message, heq]

theorem certificateCacheExceptionWeight_messageAnswers_le (key : SecretKey) (before after : QueryCache HashSpec)
    (hafter : Finite after) (hanswers : messageAnswers key.parameter before = messageAnswers key.parameter after)
    (hcard : QueryCache.enncard before ≤ QueryCache.enncard after) :
    certificateCacheExceptionWeight key after ≤ certificateCacheExceptionWeight key before := by
  have hcardReal : (QueryCache.enncard before).toReal ≤ (QueryCache.enncard after).toReal := by
    apply ENNReal.toReal_mono _ hcard
    rw [← hafter.cachedInputs_ncard_toENNReal_eq_enncard]
    finiteness
  have hindex : cachedIndexExcessMoment key.parameter after ≤ cachedIndexExcessMoment key.parameter before := by
    unfold cachedIndexExcessMoment
    apply Finset.sum_le_sum
    intro index _
    apply positiveScoreMoment_mono
    have hm : cachedIndexMultiplicity key.parameter before index = cachedIndexMultiplicity key.parameter after index :=
      cacheMessageWeight_messageAnswers_congr key.parameter before after hanswers _
    simp only [cachedIndexExcessScore, ← hm]
    exact sub_le_sub_left (div_le_div_of_nonneg_right hcardReal (by positivity)) _
  unfold certificateCacheExceptionWeight
  rw [← messageDeficitMoment_messageAnswers key.parameter key.root before after hanswers]
  exact add_le_add le_rfl (ENNReal.div_le_div_right hindex _)

theorem certificateCacheExceptionWeight_nonmessage (key : SecretKey) (cache : QueryCache HashSpec) (hfinite : Finite cache)
    (input : HashInput) (hfresh : cache input = none) (hmessage : ¬MessageHashInput key.parameter input) (output : HashOutput) :
    certificateCacheExceptionWeight key (cache.cacheQuery input output) ≤ certificateCacheExceptionWeight key cache := by
  apply certificateCacheExceptionWeight_messageAnswers_le key cache (cache.cacheQuery input output)
    (finite_cacheQuery hfinite input output)
  · funext payload
    exact (QueryCache.cacheQuery_of_ne cache output (fun heq => hmessage ⟨payload, heq⟩)).symm
  · rw [enncard_cacheQuery_of_fresh cache input output hfresh]
    exact le_self_add

theorem expected_certificateCacheExceptionWeight_rom (key : SecretKey) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (romImpl input).run cache] * certificateCacheExceptionWeight key result.2) ≤
      certificateCacheExceptionWeight key cache + hashQueryCharge (fun cache hash => messageHashCharge key.parameter cache hash * certificateCacheExceptionRate) cache input := by
  apply expected_potential_romImpl_le_charge (certificateCacheExceptionWeight key) _ ?_ input cache hfinite
  intro current hcurrent hash hnew
  by_cases hm : MessageHashInput key.parameter hash
  · simpa only [messageHashCharge, if_pos hm, one_mul] using expected_certificateCacheExceptionWeight_le key current hcurrent hash hnew
  · simp only [messageHashCharge, if_neg hm, zero_mul, add_zero]
    calc
      _ ≤ ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * certificateCacheExceptionWeight key current :=
        ENNReal.tsum_le_tsum fun output => mul_le_mul' le_rfl (certificateCacheExceptionWeight_nonmessage key current hcurrent hash hnew hm output)
      _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_certificateCacheExceptionWeight_boundary (key : SecretKey) (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | boundaryRun key.parameter computation cache] * certificateCacheExceptionWeight key result.2) ≤
      certificateCacheExceptionWeight key cache +
        (∑' result, Pr[= result | boundaryRun key.parameter computation cache] * result.1.2.messageCalls.length) * certificateCacheExceptionRate := by
  have h := expected_potential_simulateQ_le_queryCharge (certificateCacheExceptionWeight key)
    (fun cache hash => messageHashCharge key.parameter cache hash * certificateCacheExceptionRate)
    (expected_certificateCacheExceptionWeight_rom key) computation cache hfinite
  rw [expectedQueryCharge_mul, ← expectedBoundaryMessageCalls_eq_queryCharge key.parameter computation cache,
    ← boundaryRun_forget key.parameter computation cache, tsum_probOutput_map_mul] at h
  exact h

end SphincsSecurity.Concrete

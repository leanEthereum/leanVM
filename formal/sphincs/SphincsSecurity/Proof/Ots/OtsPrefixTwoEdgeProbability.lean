import SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge
import SphincsSecurity.Proof.Reference.ReferenceQueryAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
attribute [local instance] Classical.propDecidable

noncomputable def prefixTwoEdgeRate (q : Nat) : ENNReal :=
  ((3 / 2 : ENNReal) + 4 * ((q : ENNReal) / Fintype.card Digest) +
    2 * ((q : ENNReal) / Fintype.card Digest)^2) / Fintype.card Digest

noncomputable def prefixTwoEdgeGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF Bool := do
  let parameter ← 𝒟[sampleParameter]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let other ← 𝒟[PMF.uniformOfFintype segment.ErasedSecrets]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]
  let result ← 𝒟[PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => segment.seedGame inputs (hencoding parameter) (hgraph parameter) auxiliary other.val ftsSecret words endpoint adversary)
    (fun _ _ => none)]
  pure (decide (PartialChainEndpoint.TwoEdgeEvent result.2.2 result.1))

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hresult
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hresult

theorem prefixTwoEdgeGame_le (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[= true | prefixTwoEdgeGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] ≤
      (prefixTwoEdgeRate q) * ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary q] * (count : ENNReal) := by
  have h : 1 * (∑' result, Pr[= result | prefixTwoEdgeGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (if result = true then 1 else 0)) ≤
      ∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary q] * ((prefixTwoEdgeRate q) * (count : ENNReal)) := by
    unfold prefixTwoEdgeGame prefixIdealCostGame
    apply QueryCap.scaled_expectation_bind_le
    intro parameter hparameter
    apply QueryCap.scaled_expectation_bind_le
    intro ftsSecret _
    apply QueryCap.scaled_expectation_bind_le
    intro selections hselections
    apply QueryCap.scaled_expectation_bind_le
    intro other _
    apply QueryCap.scaled_expectation_bind_le
    intro auxiliary hauxiliary
    let words := referenceFamilyWords selections dummy
    let segment := OtsPrefix.atAddress parameter words address
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
    let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
    let cost := fun result : Bool × SigningBoundaryTrace => result.2.hashCalls
    have hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery (computation endpoint)) →
        result.2 ≤ cost result.1 :=
      fun endpoint result hresult => segment.seedGame_counted_le inputs hencoding hgraph auxiliary other.val
        ftsSecret words endpoint adversary result hresult
    have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl) computation (fun _ _ => none)).support,
        cost result.2.1 ≤ q :=
      prefixObservedRun_hashCalls_le parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
        address.1 address.2.1 address.2.2.1 address.2.2.2 dummy adversary selections (pmf_mem_of_evalDist _ selections hselections)
        q hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
    have htwoEdge := PartialChainEndpoint.realRun_twoEdgeEvent_le_cap_cost (fun _ => OtsPrefix.uniformImpl) computation cost q hcharge hreal hsmall
    simp only [one_mul, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
    simpa only [prefixTwoEdgeRate, PMF.evalDist_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply, decide_eq_true_eq,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero,
      PartialChainEndpoint.expectation_scale] using htwoEdge
  simpa only [one_mul, mul_ite, mul_one, mul_zero, tsum_ite_eq,
    mul_left_comm _ (prefixTwoEdgeRate q), ENNReal.tsum_mul_left] using h

end SphincsSecurity.Concrete

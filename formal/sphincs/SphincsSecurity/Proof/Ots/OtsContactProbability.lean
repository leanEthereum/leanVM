import SphincsSecurity.Proof.Ots.OtsContactEvents
import SphincsSecurity.Proof.Ots.OtsPrefixObservedBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒟[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalDist_eq (mx := computation) (mx' := 𝒟[computation]) rfl result).mpr hresult

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒟[law]) : result ∈ law.support := by
  change result ∈ (𝒟[law]).support at hresult
  simpa only [PMF.evalDist_eq, SPMF.support_liftM] using hresult

theorem referenceContactGame_newContact_le (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) (budget : Nat) (hbound : HasHashQueryBound scheme adversary budget) (hsmall : budget < Fintype.card Digest) :
    let law := referenceContactGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
    ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      Pr[fun result => result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address | law] ≤
      ∑' result, Pr[= result | law] * (result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : ENNReal) := by
  dsimp only
  have h : ((1 - (budget : ENNReal) / Fintype.card Digest) * (Fintype.card Digest : ENNReal)) *
      (∑' result : InstrumentedResult ContactResult, Pr[= result | prefixContactObservedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (if result.2.2.NewContact result.1 (referenceFamilyWords result.2.1 dummy) address then 1 else 0)) ≤
      ∑' result : InstrumentedResult ContactResult, Pr[= result | prefixContactObservedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) address dummy adversary] *
        (result.2.2.restartCharge result.1 (referenceFamilyWords result.2.1 dummy) address : ENNReal) := by
    unfold prefixContactObservedGame prefixInstrumentedObservedGame
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
    have hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
        (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary) (fun _ _ => none)).support,
        result.2.1.2.hashCalls ≤ budget :=
      prefixObservedRun_hashCalls_le parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret
        address.1 address.2.1 address.2.2.1 address.2.2.2 dummy adversary selections (pmf_mem_of_evalDist _ selections hselections)
        budget hbound other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
    have hseed := contactSeed_newContact_le parameter words address inputs hencoding hgraph auxiliary other.val ftsSecret adversary budget hreal hsmall
    simp only [← PMF.monad_map_eq_map, evalDist_map, tsum_probOutput_bind_mul, tsum_probOutput_map_mul, tsum_probOutput_pure_mul]
    simpa only [PMF.evalDist_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero, mul_assoc] using hseed
  simpa only [prefixContactObservedGame_original, probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero] using h

end SphincsSecurity.Concrete

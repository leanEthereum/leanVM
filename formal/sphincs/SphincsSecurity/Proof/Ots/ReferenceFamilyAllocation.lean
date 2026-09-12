import SphincsSecurity.Proof.Ots.OtsPrefixAllocation
import SphincsSecurity.Proof.Ots.ReferenceFamilyGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

noncomputable def referenceRecordedRest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ProbComp ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain) :=
  let words := referenceFamilyWords selections dummy
  simulateQ (fixedHashWorld f) (QueryCap.recorded (CausalFrontierProgram.game key.parameter f key.ftsSecret words
    (canonicalGraphFrontier key.otsSecret labels words) adversary))

theorem referenceRecordedRest_erased (key : SecretKey) (f : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.fst <$> referenceRecordedRest key f labels selections dummy adversary =
      referenceFamilyFrontierRest key f labels selections dummy adversary := by
  rw [referenceRecordedRest, ← simulateQ_map, QueryCap.recorded_forget, CausalFrontierProgram.fixed_game,
    referenceFamilyFrontierRest, causalFrontierGame_eq]

abbrev ReferenceRecordedResult := PublicParameter × ReferenceFamily × ((Bool × SigningBoundaryTrace) × List OracleWorld.Domain)

def ReferenceRecordedResult.erase (result : ReferenceRecordedResult) : ReferenceFamily × (Bool × SigningBoundaryTrace) :=
  (result.2.1, result.2.2.1)

noncomputable def referenceRecordedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF ReferenceRecordedResult := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let reference ← 𝒟[referenceFamilyOracleSample key inputs (hencoding parameter)]
  let f := finiteHashAnswer ∅ inputs reference.2
  let result ← 𝒟[referenceRecordedRest key f
    (canonicalGraphLabels parameter otsSecret ftsSecret f) reference.1 dummy adversary]
  pure (parameter, reference.1, result)

theorem referenceRecordedGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    ReferenceRecordedResult.erase <$> referenceRecordedGame inputs hencoding dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  unfold referenceRecordedGame referenceFamilyGame
  simp only [map_bind, map_pure, ReferenceRecordedResult.erase]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  rw [← referenceRecordedRest_erased, evalDist_map, bind_map_left]

theorem referenceRecordedGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) : result.2.2.1.2.hashCalls ≤ q := by
  apply referenceFamilyGame_hashCalls_le dummy adversary q hbound result.erase
  rw [← referenceRecordedGame_erased, support_map]
  exact ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete

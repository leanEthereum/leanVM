import SphincsSecurity.Proof.Ots.OtsPrefixSeedAllocation
import SphincsSecurity.Proof.Ots.OtsPrefixObservedSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

noncomputable def prefixCountedObservedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF PrefixCountedResult := do
  let parameter ← 𝒟[sampleParameter]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let other ← 𝒟[PMF.uniformOfFintype segment.ErasedSecrets]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]
  let result ← 𝒟[(PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.seedGame inputs (hencoding parameter) (hgraph parameter) auxiliary other.val ftsSecret words endpoint adversary))
    (fun _ _ => none)).map (fun result => result.2.1)]
  pure (parameter, selections, result)

theorem prefixCountedObservedGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixCountedObservedGame inputs hencoding hgraph address dummy adversary =
      prefixCountedSourceGame inputs hencoding hgraph address dummy adversary := by
  symm
  unfold prefixCountedSourceGame prefixCountedSeedRest prefixCountedObservedGame
  dsimp only
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  rw [swap_samples 𝒟[sampleOtsSecrets] 𝒟[sampleFtsSecrets]]
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  rw [swap_samples 𝒟[sampleOtsSecrets] 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]]
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  rw [segment.sampleOtsSecrets_eq_split]
  simp only [bind_assoc, pure_bind, OtsPrefix.seedGame_replaceSecret]
  apply congrArg (𝒟[PMF.uniformOfFintype segment.ErasedSecrets] >>= ·)
  funext other
  rw [reverse_three_samples 𝒟[PMF.uniformOfFintype Digest]
    𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
    𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]]
  apply congrArg (𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections] >>= ·)
  funext auxiliary
  rw [segment.realRun_empty_forget]
  have hselected (secret : Digest) :
      segment.replaceChain other.val secret address.1 address.2.1 address.2.2.1 address.2.2.2 = secret :=
    segment.replaceChain_self other.val secret
  simp only [bind_assoc, hselected]
  dsimp only [segment, words]
  simp only [OtsPrefix.seedGame_replaceSecret]

theorem prefixCountedObservedGame_original (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixCountedObservedGame inputs hencoding hgraph address dummy adversary =
      ReferenceRecordedResult.prefixCounted address dummy <$> referenceRecordedGame inputs hencoding dummy adversary := by
  rw [prefixCountedObservedGame_eq, prefixCountedSourceGame_eq]

end SphincsSecurity.Concrete

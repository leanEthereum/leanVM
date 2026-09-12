import SphincsSecurity.Proof.Ots.OtsPrefixInstrumentedSeed
import SphincsSecurity.Proof.Ots.OtsPrefixObservedSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable {Result : Type} (observer : FrontierObserver Result)

noncomputable def prefixInstrumentedSeedRest (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress key.parameter words address
  let tables ← 𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs hencoding hgraph selections]
  let result ← 𝒟[simulateQ (segment.fixedImpl tables)
    (segment.instrumentedSeedGame observer inputs hencoding hgraph auxiliary (segment.replaceChain key.otsSecret 0) key.ftsSecret words
      (PartialChainEndpoint.evaluate tables (key.otsSecret address.1 address.2.1 address.2.2.1 address.2.2.2)) adversary)]
  pure (key.parameter, selections, result)

theorem prefixInstrumentedSeedRest_eq (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixInstrumentedSeedRest observer key inputs hencoding hgraph address dummy adversary = (do
      let reference ← 𝒟[referenceFamilyOracleSample key inputs hencoding]
      let oracle := finiteHashAnswer ∅ inputs reference.2
      let result ← 𝒟[referenceInstrumentedRest observer key oracle
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle) reference.1 dummy adversary]
      pure (key.parameter, reference.1, result)) := by
  rw [referenceFamilyOracleSample_eq_prefixSeed key inputs hencoding hgraph address.1 address.2.1 address.2.2.1 address.2.2.2
    (fun selections => referenceFamilyWords selections dummy address.1 address.2.1 address.2.2.1 address.2.2.2)]
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind, evalDist_map, bind_assoc, bind_map_left]
  unfold prefixInstrumentedSeedRest
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress key.parameter words address
  apply congrArg (𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)] >>= ·)
  funext tables
  apply congrArg (𝒟[segment.referenceAuxSeedLaw inputs hencoding hgraph selections] >>= ·)
  funext auxiliary
  rw [segment.referenceSeedGame_instrumented observer inputs hencoding hgraph auxiliary key.root key.otsSecret key.ftsSecret
    selections dummy rfl tables adversary]

noncomputable def prefixInstrumentedSourceGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  prefixInstrumentedSeedRest observer ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter) address dummy adversary

theorem prefixInstrumentedSourceGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixInstrumentedSourceGame observer inputs hencoding hgraph address dummy adversary =
      referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  simp only [prefixInstrumentedSourceGame, referenceInstrumentedGame, prefixInstrumentedSeedRest_eq]

noncomputable def prefixInstrumentedObservedGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let other ← 𝒟[PMF.uniformOfFintype segment.ErasedSecrets]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]
  let result ← 𝒟[(PartialChainEndpoint.realRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => segment.instrumentedSeedGame observer inputs (hencoding parameter) (hgraph parameter)
      auxiliary other.val ftsSecret words endpoint adversary) (fun _ _ => none)).map (fun result => result.2.1)]
  pure (parameter, selections, result)

theorem prefixInstrumentedObservedGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixInstrumentedObservedGame observer inputs hencoding hgraph address dummy adversary =
      prefixInstrumentedSourceGame observer inputs hencoding hgraph address dummy adversary := by
  symm
  unfold prefixInstrumentedSourceGame prefixInstrumentedSeedRest prefixInstrumentedObservedGame
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
  simp only [bind_assoc, pure_bind, OtsPrefix.instrumentedSeedGame_replaceSecret]
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
  simp only [OtsPrefix.instrumentedSeedGame_replaceSecret]

theorem prefixInstrumentedObservedGame_original (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixInstrumentedObservedGame observer inputs hencoding hgraph address dummy adversary =
      referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  rw [prefixInstrumentedObservedGame_eq, prefixInstrumentedSourceGame_eq]

end SphincsSecurity.Concrete

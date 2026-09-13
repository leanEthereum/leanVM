import SphincsSecurity.Proof.Ots.OtsPrefixSeedGame
import SphincsSecurity.Proof.Ots.ReferenceFamilyAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem OtsPrefix.referenceSeedGame_counted (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph)
    (root : Digest) (secrets : OtsFrontierValues) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (hword : referenceFamilyWords selections dummy segment.lay segment.tree segment.leaf segment.chainIdx = segment.digit)
    (tables : Fin segment.digit.val → Digest → Digest) (adversary : Adversary) :
    let key : SecretKey := ⟨segment.parameter, root, secrets, ftsSecret⟩
    let oracle := finiteHashAnswer ∅ inputs (referenceFamilySeedTable key inputs hencoding
      (segment.referenceSeed inputs hencoding hgraph selections tables auxiliary))
    (fun result => (result.1, QueryCap.calls segment.Selects result.2)) <$>
      referenceRecordedRest key oracle (canonicalGraphLabels segment.parameter secrets ftsSecret oracle) selections dummy adversary =
      simulateQ (segment.fixedImpl tables) (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
        (segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain secrets 0) ftsSecret
          (referenceFamilyWords selections dummy)
          (PartialChainEndpoint.evaluate tables (secrets segment.lay segment.tree segment.leaf segment.chainIdx)) adversary)) := by
  dsimp only
  rw [referenceRecordedRest, ← simulateQ_map, QueryCap.recorded_counted, segment.seedGame_replaceSecret, OtsPrefix.seedGame,
    segment.game_counted_source tables auxiliary.high _ ftsSecret (referenceFamilyWords selections dummy) (by rw [hword])]
  rw [segment.referenceSeedFrontier_eq inputs hencoding hgraph auxiliary root secrets ftsSecret selections _ hword tables,
    segment.referenceSeedOracle_eq inputs hencoding hgraph auxiliary root secrets ftsSecret selections _ hword tables]

abbrev PrefixCountedResult := PublicParameter × ReferenceFamily × ((Bool × SigningBoundaryTrace) × Nat)

noncomputable def ReferenceRecordedResult.prefixCounted (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (result : ReferenceRecordedResult) : PrefixCountedResult :=
  (result.1, result.2.1, result.2.2.1,
    QueryCap.calls (OtsPrefix.atAddress result.1 (referenceFamilyWords result.2.1 dummy) address).Selects result.2.2.2)

noncomputable def prefixCountedSeedRest (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF PrefixCountedResult := do
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress key.parameter words address
  let tables ← 𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs hencoding hgraph selections]
  let result ← 𝒟[simulateQ (segment.fixedImpl tables) (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
    (segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain key.otsSecret 0) key.ftsSecret words
      (PartialChainEndpoint.evaluate tables (key.otsSecret address.1 address.2.1 address.2.2.1 address.2.2.2)) adversary))]
  pure (key.parameter, selections, result)

theorem prefixCountedSeedRest_eq (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixCountedSeedRest key inputs hencoding hgraph address dummy adversary = (do
      let reference ← 𝒟[referenceFamilyOracleSample key inputs hencoding]
      let oracle := finiteHashAnswer ∅ inputs reference.2
      let result ← 𝒟[referenceRecordedRest key oracle
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle) reference.1 dummy adversary]
      pure (ReferenceRecordedResult.prefixCounted address dummy (key.parameter, reference.1, result))) := by
  rw [referenceFamilyOracleSample_eq_prefixSeed key inputs hencoding hgraph address.1 address.2.1 address.2.2.1 address.2.2.2
    (fun selections => referenceFamilyWords selections dummy address.1 address.2.1 address.2.2.1 address.2.2.2)]
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind, evalDist_map, bind_assoc, bind_map_left]
  unfold prefixCountedSeedRest
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress key.parameter words address
  apply congrArg (𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)] >>= ·)
  funext tables
  apply congrArg (𝒟[segment.referenceAuxSeedLaw inputs hencoding hgraph selections] >>= ·)
  funext auxiliary
  rw [← segment.referenceSeedGame_counted inputs hencoding hgraph auxiliary key.root key.otsSecret key.ftsSecret
    selections dummy rfl tables adversary, evalDist_map, bind_map_left]
  rfl

noncomputable def prefixCountedSourceGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF PrefixCountedResult := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  prefixCountedSeedRest ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter) address dummy adversary

theorem prefixCountedSourceGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixCountedSourceGame inputs hencoding hgraph address dummy adversary =
      ReferenceRecordedResult.prefixCounted address dummy <$> referenceRecordedGame inputs hencoding dummy adversary := by
  simp only [prefixCountedSourceGame, referenceRecordedGame, prefixCountedSeedRest_eq, map_bind, map_pure]

end SphincsSecurity.Concrete

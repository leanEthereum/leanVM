import SphincsSecurity.Proof.Ots.OtsPrefixSeedGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

noncomputable def prefixSeedRest (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
  let tables ← 𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)]
  let auxiliary ← 𝒟[segment.referenceAuxSeedLaw inputs hencoding hgraph selections]
  let result ← 𝒟[simulateQ (segment.fixedImpl tables)
    (segment.seedGame inputs hencoding hgraph auxiliary (segment.replaceChain key.otsSecret 0) key.ftsSecret words
      (PartialChainEndpoint.evaluate tables (key.otsSecret lay tree leaf chainIdx)) adversary)]
  pure (selections, result)

theorem prefixSeedRest_eq (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixSeedRest key inputs hencoding hgraph lay tree leaf chainIdx dummy adversary = (do
      let reference ← 𝒟[referenceFamilyOracleSample key inputs hencoding]
      let oracle := finiteHashAnswer ∅ inputs reference.2
      let result ← 𝒟[referenceFamilyFrontierRest key oracle
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle) reference.1 dummy adversary]
      pure (reference.1, result)) := by
  rw [referenceFamilyOracleSample_eq_prefixSeed key inputs hencoding hgraph lay tree leaf chainIdx
    (fun selections => referenceFamilyWords selections dummy lay tree leaf chainIdx)]
  simp only [← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind, evalDist_map,
    bind_assoc, bind_map_left]
  unfold prefixSeedRest
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  let words := referenceFamilyWords selections dummy
  let segment : OtsPrefix := ⟨key.parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
  apply congrArg (𝒟[PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)] >>= ·)
  funext tables
  apply congrArg (𝒟[segment.referenceAuxSeedLaw inputs hencoding hgraph selections] >>= ·)
  funext auxiliary
  rw [segment.referenceSeedGame_eq inputs hencoding hgraph auxiliary key.root key.otsSecret key.ftsSecret selections dummy rfl tables]

noncomputable def prefixSourceGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  prefixSeedRest ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter)
    lay tree leaf chainIdx dummy adversary

theorem prefixSourceGame_eq (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    prefixSourceGame inputs hencoding hgraph lay tree leaf chainIdx dummy adversary =
      referenceFamilyGame inputs hencoding dummy adversary := by
  simp only [prefixSourceGame, referenceFamilyGame, prefixSeedRest_eq]

theorem prefixSourceGame_hashCalls_le (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support
      (prefixSourceGame (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary)
        (canonicalGraphInputs_subset_gameInputs adversary) lay tree leaf chainIdx dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  rw [prefixSourceGame_eq] at hresult
  exact referenceFamilyGame_hashCalls_le dummy adversary q hbound result hresult

end SphincsSecurity.Concrete

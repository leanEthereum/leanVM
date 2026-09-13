import SphincsSecurity.Proof.Ots.ReferenceEncodingLazySource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs Finset.univ referenceEncodingRest

abbrev EncodingContextResult (Result : Type) := PublicParameter × ReferenceFamily × (EncodingPosition → Digest) × Result

noncomputable def referenceEncodingContextRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (EncodingPosition → Digest) × Result) := do
  let reference ← 𝒟[referenceFamilyOracleSample key inputs hencoding]
  let oracle := finiteHashAnswer ∅ inputs reference.2
  let labels := canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret oracle
  let result ← 𝒟[referenceInstrumentedRest observer key oracle labels reference.1 dummy adversary]
  pure (reference.1, canonicalGraphMessage labels, result)

theorem referenceEncodingContextRest_lazy {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingContextRest observer key inputs hencoding dummy adversary = (do
      let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
      let outside ← 𝒟[PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)]
      let result ← Prod.fst <$> referenceEncodingLazyRest observer key inputs hencoding outside selections dummy adversary
      pure (selections, outsideGraphMessage key inputs hencoding outside, result)) := by
  have hrest : referenceEncodingContextRest observer key inputs hencoding dummy adversary = (do
      let reference ← 𝒟[referenceFamilyOracleSample key inputs hencoding]
      let result ← 𝒟[referenceEncodingRest observer key inputs hencoding (fun cell => reference.2 cell.val)
        reference.1 (reference.2 ∘ encodingInputCell key.parameter inputs hencoding) dummy adversary]
      pure (reference.1, canonicalGraphMessage
        (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (finiteHashAnswer ∅ inputs reference.2)), result)) := by
    unfold referenceEncodingContextRest
    apply evalDist_bind_congr (m := SPMF)
    intro reference hreference
    have hselected := referenceFamilyOracleSample_selections key inputs hencoding hgraph reference
      (by simpa only [PMF.evalDist_eq, SPMF.support_eq_support, SPMF.support_liftM] using hreference)
    dsimp only
    rw [referenceEncodingRest_table observer key inputs hencoding hgraph reference.1 reference.2 hselected.symm dummy adversary]
  rw [hrest]
  simp only [referenceFamilyOracleSample, ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalDist_bind, evalDist_map, bind_assoc, bind_map_left, referenceFamilyOracleTable,
    referenceEncodingRest_join, canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph]
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  apply congrArg (𝒟[PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)] >>= ·)
  funext outside
  have hmessages : canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) = outsideGraphMessage key inputs hencoding outside := rfl
  rw [hmessages]
  have h := congrArg (fun law : SPMF Result => law >>= fun result =>
    pure (selections, outsideGraphMessage key inputs hencoding outside, result))
      (referenceEncodingLazyRest_original observer key inputs hencoding outside selections dummy adversary)
  rw [← referenceEncodingPrior_complete] at h
  simpa only [referenceEncodingPrior, ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalDist_bind, evalDist_map, bind_assoc, bind_map_left] using h

noncomputable def referenceEncodingContextGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (EncodingContextResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let result ← referenceEncodingContextRest observer ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) dummy adversary
  pure (parameter, result)

theorem referenceEncodingContextGame_erased {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : EncodingContextResult Result => (result.1, result.2.1, result.2.2.2)) <$>
      referenceEncodingContextGame observer inputs hencoding dummy adversary =
        referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  simp only [referenceEncodingContextGame, referenceEncodingContextRest, referenceInstrumentedGame,
    map_bind, map_pure, bind_assoc, pure_bind]

theorem referenceEncodingContextGame_lazy {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingContextGame observer inputs hencoding dummy adversary = (do
      let parameter ← 𝒟[sampleParameter]
      let otsSecret ← 𝒟[sampleOtsSecrets]
      let ftsSecret ← 𝒟[sampleFtsSecrets]
      let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
      let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
      let outside ← 𝒟[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))]
      let result ← Prod.fst <$> referenceEncodingLazyRest observer key inputs (hencoding parameter) outside selections dummy adversary
      pure (parameter, selections, outsideGraphMessage key inputs (hencoding parameter) outside, result)) := by
  simp only [referenceEncodingContextGame, referenceEncodingContextRest_lazy observer _ inputs _ (hgraph _) dummy adversary,
    bind_assoc, pure_bind]

end SphincsSecurity.Concrete

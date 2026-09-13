import SphincsSecurity.Proof.Ots.EncodingOracleObservation
import SphincsSecurity.Proof.Ots.ReferenceEncodingPriorSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs Finset.univ

noncomputable def referenceEncodingLazyRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    SPMF (Result × (canonicalEncodingInputs key.parameter → Finset HashOutput)) :=
  let words := referenceFamilyWords selections dummy
  let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) words
  EncodingObservation.lazyRun key.parameter inputs hencoding outside
    (observer key.parameter words frontier (referenceEncodingProgram key inputs hencoding outside selections dummy adversary))
    (referenceEncodingAllowed key.parameter (outsideGraphMessage key inputs hencoding outside) selections)

theorem referenceEncodingLazyRest_original {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (complete (referenceEncodingAllowed key.parameter (outsideGraphMessage key inputs hencoding outside) selections) >>= fun encoding =>
      𝒟[referenceEncodingRest observer key inputs hencoding outside selections encoding dummy adversary]) =
        Prod.fst <$> referenceEncodingLazyRest observer key inputs hencoding outside selections dummy adversary := by
  unfold referenceEncodingRest referenceEncodingLazyRest
  exact EncodingObservation.lazyRun_original key.parameter inputs hencoding outside _ _
    (referenceEncodingAllowed_nonempty key.parameter (outsideGraphMessage key inputs hencoding outside) selections)

noncomputable def referenceEncodingLazyGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let outside ← 𝒟[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))]
  let result ← Prod.fst <$> referenceEncodingLazyRest observer key inputs (hencoding parameter) outside selections dummy adversary
  pure (parameter, selections, result)

theorem referenceEncodingLazyGame_original {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingLazyGame observer inputs hencoding dummy adversary =
      referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  rw [← referenceEncodingTableGame_original observer inputs hencoding hgraph dummy adversary]
  unfold referenceEncodingLazyGame referenceEncodingTableGame
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  apply congrArg (𝒟[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))] >>= ·)
  funext outside
  rw [← bind_assoc, referenceEncodingLazyRest_original observer ⟨parameter, 0, otsSecret, ftsSecret⟩
    inputs (hencoding parameter) outside selections dummy adversary]

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.Ots.EncodingTablePrior
import SphincsSecurity.Proof.Ots.ReferenceEncodingSource
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs Finset.univ

noncomputable def referenceEncodingTableGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (InstrumentedResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let outside ← 𝒟[PMF.uniformOfFintype (NonencodingRows parameter inputs (hencoding parameter))]
  let encoding ← complete (referenceEncodingAllowed parameter (outsideGraphMessage key inputs (hencoding parameter) outside) selections)
  let result ← 𝒟[referenceEncodingRest observer key inputs (hencoding parameter) outside selections encoding dummy adversary]
  pure (parameter, selections, result)

theorem referenceEncodingTableGame_original {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceEncodingTableGame observer inputs hencoding dummy adversary =
      referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  rw [← referenceEncodingGame_original observer inputs hencoding hgraph dummy adversary,
    referenceEncodingGame_conditioned]
  unfold referenceEncodingTableGame
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
  rw [← referenceEncodingPrior_complete]
  simp only [referenceEncodingPrior, ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalDist_bind, evalDist_map, bind_assoc, bind_map_left]

end SphincsSecurity.Concrete

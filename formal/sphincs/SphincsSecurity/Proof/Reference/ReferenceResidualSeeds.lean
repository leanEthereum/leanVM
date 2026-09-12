import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.PublicReferenceResidual
import SphincsSecurity.Proof.Reference.ReferenceResidualGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

structure ReferenceAuxiliary (inputs : Finset HashInput) where
  selections : ReferenceFamily
  rows : CanonicalEncodingRows
  seed : inputs → HashOutput

noncomputable def referenceAuxiliarySample (inputs : Finset HashInput) : PMF (ReferenceAuxiliary inputs) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
      (fun rows => (PMF.uniformOfFintype (inputs → HashOutput)).map
        (fun seed => ⟨selections, Function.uncurry rows, seed⟩)))

theorem graphReferenceSample_eq_auxiliary (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :
    graphReferenceSample parameter inputs hencoding =
      (referenceAuxiliarySample inputs).bind (fun auxiliary =>
        (PMF.uniformOfFintype CanonicalGraphLabels).map (fun labels =>
          (auxiliary.selections, (labels, canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))) := by
  have hseed (selections : ReferenceFamily) (labels : CanonicalGraphLabels)
      (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput) :
      (PMF.uniformOfFintype (UniformTableSplit.Outside (canonicalEncodingCell parameter inputs hencoding labels) → HashOutput)).map
          (fun remaining => (selections, (labels, UniformTableSplit.join (canonicalEncodingCell parameter inputs hencoding labels)
            (canonicalEncodingCell_injective parameter inputs hencoding labels) (Function.uncurry rows) remaining))) =
        (PMF.uniformOfFintype (inputs → HashOutput)).map (fun seed =>
          (selections, (labels, canonicalReferenceResidual parameter inputs hencoding labels (Function.uncurry rows) seed))) := by
    have h := congrArg (fun law : PMF (inputs → HashOutput) => law.map (fun table => (selections, (labels, table))))
      (UniformTableSplit.uniform_overwrite (canonicalEncodingCell parameter inputs hencoding labels)
        (canonicalEncodingCell_injective parameter inputs hencoding labels) (Function.uncurry rows))
    simpa only [PMF.map_comp, Function.comp_def, canonicalReferenceResidual] using h.symm
  unfold graphReferenceSample referenceAuxiliarySample
  simp only [hseed, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [PMF.bind_comm]
  apply congrArg (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit
    decodeEncodingOutput_invalid_nonempty selections).bind
  funext rows
  simp only [PMF.map, Function.comp_def]
  rw [PMF.bind_comm]

theorem referenceResidualGame_eq_auxiliary (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceResidualGame inputs hencoding dummy adversary = (do
      let parameter ← 𝒟[sampleParameter]
      let otsSecret ← 𝒟[sampleOtsSecrets]
      let ftsSecret ← 𝒟[sampleFtsSecrets]
      let auxiliary ← 𝒟[referenceAuxiliarySample inputs]
      let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
      let f := programmedHash parameter otsSecret ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs (hencoding parameter) labels auxiliary.rows auxiliary.seed))
      let result ← 𝒟[referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret⟩ f labels auxiliary.selections dummy adversary]
      pure (auxiliary.selections, result)) := by
  simp only [referenceResidualGame, graphReferenceSample_eq_auxiliary,
    ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map, evalDist_bind, evalDist_map, bind_assoc, bind_map_left]

end SphincsSecurity.Concrete

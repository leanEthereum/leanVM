import SphincsSecurity.Proof.Ots.ReferenceFamilyConditioning
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

namespace UniformTableSplit

theorem uniform_outside {Index Cell Answer : Type} [Fintype Index] [Fintype Cell] [Fintype Answer]
    [Nonempty Answer] [DecidableEq Index] [DecidableEq Cell]
    (embed : Index → Cell) (hinj : Function.Injective embed) :
    (PMF.uniformOfFintype (Cell → Answer)).map (fun table => fun cell : Outside embed => table cell.val) =
      PMF.uniformOfFintype (Outside embed → Answer) := by
  rw [uniform_join embed hinj, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def, join_outside, PMF.bind_const]
  exact PMF.map_id _

end UniformTableSplit

structure ReferenceFamilySeed (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) where
  selections : ReferenceFamily
  nonencoding : NonencodingRows parameter inputs hencoding
  selectedRows : EncodingPosition → Fin encodingAttemptLimit → HashOutput
  encoding : canonicalEncodingInputs parameter → HashOutput

noncomputable def referenceFamilySeedLawAt (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (selections : ReferenceFamily) :
    PMF (ReferenceFamilySeed parameter inputs hencoding) :=
  (PMF.uniformOfFintype (NonencodingRows parameter inputs hencoding)).bind (fun nonencoding =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
      (fun selectedRows => (PMF.uniformOfFintype (canonicalEncodingInputs parameter → HashOutput)).map
        (fun encoding => ⟨selections, nonencoding, selectedRows, encoding⟩)))

noncomputable def referenceFamilySeedLaw (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) : PMF (ReferenceFamilySeed parameter inputs hencoding) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
    (referenceFamilySeedLawAt parameter inputs hencoding)

noncomputable def referenceFamilySeedTable (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (seed : ReferenceFamilySeed key.parameter inputs hencoding) : inputs → HashOutput :=
  referenceFamilyOracleTable key inputs hencoding seed.nonencoding seed.selectedRows
    (fun cell => seed.encoding cell.val)

theorem referenceFamilyOracleSample_eq_seed (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) :
    referenceFamilyOracleSample key inputs hencoding =
      (referenceFamilySeedLaw key.parameter inputs hencoding).map
        (fun seed => (seed.selections, referenceFamilySeedTable key inputs hencoding seed)) := by
  rw [referenceFamilyOracleSample, referenceFamilySeedLaw, PMF.map_bind]
  apply congrArg (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind
  funext selections
  rw [referenceFamilySeedLawAt, PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext nonencoding
  rw [PMF.map_bind]
  apply congrArg (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit
    decodeEncodingOutput_invalid_nonempty selections).bind
  funext selectedRows
  rw [← UniformTableSplit.uniform_outside
    (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding nonencoding))
    (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding nonencoding))]
  simp only [PMF.map_comp, Function.comp_def, referenceFamilySeedTable]

end SphincsSecurity.Concrete

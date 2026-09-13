import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.FirstSuccessPrefix
import SphincsSecurity.Proof.Residual.PublicResidualLookup
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def canonicalPrefixResidual (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) : inputs → HashOutput :=
  UnrestrictedRowSwap.prefixOverwrite (canonicalEncodingCell parameter inputs hencoding labels)
    (canonicalEncodingCell_injective parameter inputs hencoding labels) (FirstSuccessPrefix.familyKept selections) rows seed

noncomputable def knownPrefixResidual (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) : inputs → HashOutput :=
  UnrestrictedRowSwap.prefixOverwrite (knownEncodingCell parameter inputs hencoding known)
    (knownEncodingCell_injective parameter inputs hencoding known) (FirstSuccessPrefix.familyKept selections) rows seed

theorem canonicalPrefixResidual_eq_known (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels))
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) :
    canonicalPrefixResidual parameter inputs hencoding labels selections rows seed =
      knownPrefixResidual parameter inputs hencoding known selections rows seed := by
  unfold canonicalPrefixResidual knownPrefixResidual
  congr 1
  exact canonicalEncodingCell_eq_known parameter inputs hencoding words disclosed known otsSecret ftsSecret labels hagrees

theorem knownPrefixResidual_lookup (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : inputs) :
    knownPrefixResidual parameter inputs hencoding known selections rows seed input =
      (knownEncodingRowAt parameter inputs hencoding known input).elim (seed input)
        (fun row => if FirstSuccessPrefix.familyKept selections row then rows row else seed input) := by
  cases hrow : knownEncodingRowAt parameter inputs hencoding known input with
  | none =>
      exact UnrestrictedRowSwap.prefixOverwrite_outside _ _ _ _ _ input
        ((knownEncodingRowAt_none parameter inputs hencoding known input).mp hrow)
  | some row =>
      have heq := (knownEncodingRowAt_some parameter inputs hencoding known input row).mp hrow
      rw [← heq]
      exact UnrestrictedRowSwap.prefixOverwrite_embed _ _ _ _ _ row

theorem knownPrefixResidual_structural (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput)
    (input : inputs) (position : Position) (hat : AtPosition parameter input.val position) :
    knownPrefixResidual parameter inputs hencoding known selections rows seed input = seed input := by
  rw [knownPrefixResidual_lookup,
    knownEncodingRowAt_structural parameter inputs hencoding known input position hat]
  rfl

theorem canonicalReferenceResidual_prefix_law (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) (selections : ReferenceFamily) :
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
      (fun rows => (PMF.uniformOfFintype (inputs → HashOutput)).map
        (fun seed => canonicalReferenceResidual parameter inputs hencoding labels (Function.uncurry rows) seed)) =
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
      (fun rows => (PMF.uniformOfFintype (inputs → HashOutput)).map
        (fun seed => canonicalPrefixResidual parameter inputs hencoding labels selections (Function.uncurry rows) seed)) :=
  FirstSuccessPrefix.overwrite_table_eq_prefix decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty
    selections (canonicalEncodingCell parameter inputs hencoding labels) (canonicalEncodingCell_injective parameter inputs hencoding labels)

end SphincsSecurity.Concrete

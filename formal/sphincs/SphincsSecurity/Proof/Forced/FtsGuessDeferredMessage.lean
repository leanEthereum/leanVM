import SphincsSecurity.Proof.Forced.FtsGuessNearDeferred
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput

theorem message_not_probe (parameter : PublicParameter) (input : HashInput)
    (hmessage : MessageHashInput parameter input) : FtsProbeSimulation.decodeProbe? parameter input = none := by
  rw [FtsProbeSimulation.decodeProbe?_eq_none_iff]
  obtain ⟨payload, rfl⟩ := hmessage
  intro probe heq
  have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) heq).1
  exact HashDomain.noConfusion hdomain

theorem knownEncodingCell_not_message (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (input : inputs)
    (hmessage : MessageHashInput parameter input.val) :
    input ∉ Set.range (knownEncodingCell parameter inputs hencoding known) := by
  rintro ⟨row, heq⟩
  have hat : AtEncodingPosition parameter (knownEncodingCell parameter inputs hencoding known row).val row.1 := ⟨_, rfl⟩
  rw [heq] at hat
  exact ResidualByteFrontend.message_not_encoding parameter input.val hmessage row.1 hat

theorem canonicalEncodingCell_not_message (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) (input : inputs)
    (hmessage : MessageHashInput parameter input.val) :
    input ∉ Set.range (canonicalEncodingCell parameter inputs hencoding labels) := by
  rintro ⟨row, heq⟩
  have hat : AtEncodingPosition parameter (canonicalEncodingCell parameter inputs hencoding labels row).val row.1 := ⟨_, rfl⟩
  rw [heq] at hat
  exact ResidualByteFrontend.message_not_encoding parameter input.val hmessage row.1 hat

theorem residualWorld_message (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (rows : CanonicalEncodingRows)
    (input : inputs) (hmessage : MessageHashInput parameter input.val) :
    residualWorld parameter inputs hencoding known rows (.inr input.val) =
      liftM ((SeedSpec inputs).query (.inr input)) := by
  rw [residualWorld, residualProgram, dif_pos input.property,
    dif_neg (knownEncodingCell_not_message parameter inputs hencoding known input hmessage)]

theorem auxiliaryHashProgram_message (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (rows : CanonicalEncodingRows) (input : inputs) (hmessage : MessageHashInput parameter input.val) :
    auxiliaryHashProgram parameter otsSecret labels inputs hencoding rows input.val =
      liftM ((SeedSpec inputs).query (.inr input)) := by
  have hd : decodePosition parameter input.val = none := by
    obtain ⟨payload, heq⟩ := hmessage
    rw [← heq]
    exact decodePosition_message parameter payload
  rw [auxiliaryHashProgram, message_not_probe parameter input.val hmessage, hd, residualProgram,
    dif_pos input.property, dif_neg (canonicalEncodingCell_not_message parameter inputs hencoding labels input hmessage)]

theorem referenceProgram_message (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords)
    (input : inputs) (hmessage : MessageHashInput parameter input.val) :
    referenceProgram parameter root otsSecret labels inputs hencoding selections rows dummy (.inl (.inr input.val)) =
      liftM ((SeedSpec inputs).query (.inr input)) :=
  auxiliaryHashProgram_message parameter otsSecret labels inputs hencoding rows input hmessage

end SphincsSecurity.Concrete.FtsGuessHash

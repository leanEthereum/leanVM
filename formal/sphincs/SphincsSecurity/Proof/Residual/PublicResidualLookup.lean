import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.PublicReferenceResidual
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def knownEncodingRowAt (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (input : inputs) : Option EncodingRow :=
  letI : Decidable (∃ row, knownEncodingCell parameter inputs hencoding known row = input) := Classical.propDecidable _
  if h : ∃ row, knownEncodingCell parameter inputs hencoding known row = input then some h.choose else none

theorem knownEncodingRowAt_some (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (input : inputs) (row : EncodingRow) :
    knownEncodingRowAt parameter inputs hencoding known input = some row ↔
      knownEncodingCell parameter inputs hencoding known row = input := by
  unfold knownEncodingRowAt
  split
  · rename_i h
    constructor
    · intro heq
      exact Option.some.inj heq ▸ h.choose_spec
    · intro heq
      exact congrArg some (knownEncodingCell_injective parameter inputs hencoding known (h.choose_spec.trans heq.symm))
  · rename_i h
    constructor
    · simp
    · intro heq
      exact (h ⟨row, heq⟩).elim

theorem knownEncodingRowAt_none (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels) (input : inputs) :
    knownEncodingRowAt parameter inputs hencoding known input = none ↔
      input ∉ Set.range (knownEncodingCell parameter inputs hencoding known) := by
  constructor
  · intro hnone
    rintro ⟨row, hrow⟩
    have hsome := (knownEncodingRowAt_some parameter inputs hencoding known input row).mpr hrow
    rw [hnone] at hsome
    cases hsome
  · intro hout
    cases h : knownEncodingRowAt parameter inputs hencoding known input with
    | none => rfl
    | some row => exact (hout ⟨row, (knownEncodingRowAt_some parameter inputs hencoding known input row).mp h⟩).elim

theorem knownEncodingRowAt_structural (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (input : inputs) (position : Position) (hat : AtPosition parameter input.val position) :
    knownEncodingRowAt parameter inputs hencoding known input = none :=
  (knownEncodingRowAt_none parameter inputs hencoding known input).mpr
    (knownEncodingCell_not_structural parameter inputs hencoding known input position hat)

end SphincsSecurity.Concrete

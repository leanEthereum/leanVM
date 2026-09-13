import SphincsSecurity.Proof.Ots.EncodingFreshRow
import SphincsSecurity.Proof.Ots.ReferenceFamilyGame
import SphincsSecurity.Proof.Base.UniformTableObservation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def encodingSelectionAllowed (selection : ReferenceSelection) : Fin encodingAttemptLimit → Finset HashOutput :=
  match selection with
  | none => fun _ => FirstSuccessTable.invalid decodeEncodingOutput
  | some (index, word) =>
      if (FirstSuccessTable.fiber decodeEncodingOutput word).Nonempty then
        FirstSuccessTable.allowed decodeEncodingOutput index word else fun _ => Finset.univ

theorem encodingSelectionAllowed_nonempty (selection : ReferenceSelection) :
    ∀ coordinate, (encodingSelectionAllowed selection coordinate).Nonempty := by
  cases selection with
  | none => exact fun _ => decodeEncodingOutput_invalid_nonempty
  | some selected =>
      obtain ⟨index, word⟩ := selected
      simp only [encodingSelectionAllowed]
      split_ifs with hfiber
      · exact FirstSuccessTable.allowed_nonempty decodeEncodingOutput index word decodeEncodingOutput_invalid_nonempty hfiber
      · exact fun _ => Finset.univ_nonempty

theorem encodingSelectionAllowed_fresh (selection : ReferenceSelection) (dummy : Encoding) (coordinate : Fin encodingAttemptLimit) :
    FreshEncodingSupport ((selection.map Prod.snd).getD dummy) (encodingSelectionAllowed selection coordinate) := by
  cases selection with
  | none =>
      exact Or.inr fun output ho => Or.inl ((FirstSuccessTable.mem_invalid _ _).mp ho)
  | some selected =>
      obtain ⟨index, word⟩ := selected
      simp only [Option.map_some, Option.getD_some, encodingSelectionAllowed]
      split_ifs
      · exact firstSuccess_allowed_fresh index word coordinate
      · exact Or.inl rfl

theorem encoding_afterSelect_complete (selection : ReferenceSelection) :
    𝒟[FirstSuccessTable.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selection] =
      complete (encodingSelectionAllowed selection) := by
  rw [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection)]
  cases selection with
  | none => rfl
  | some selected =>
      obtain ⟨index, word⟩ := selected
      by_cases hfiber : (FirstSuccessTable.fiber decodeEncodingOutput word).Nonempty
      · simp only [FirstSuccessTable.afterSelect, dif_pos hfiber, encodingSelectionAllowed, if_pos hfiber]
        rfl
      · simp only [FirstSuccessTable.afterSelect, dif_neg hfiber, encodingSelectionAllowed, if_neg hfiber]
        rfl

end SphincsSecurity.Concrete

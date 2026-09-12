import SphincsSecurity.Proof.Ots.EncodingFamilyObservation
import SphincsSecurity.Proof.Base.UniformTableJoin
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs UniformTableSplit.join

noncomputable def referenceEncodingAllowed (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : canonicalEncodingInputs parameter → Finset HashOutput :=
  UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
    (encodingFamilyAllowed selections) (fun _ => Finset.univ)

theorem referenceEncodingAllowed_nonempty (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : ∀ cell, (referenceEncodingAllowed parameter messages selections cell).Nonempty :=
  UniformTableSplit.join_nonempty _ _ _ _ (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)

noncomputable def referenceEncodingPrior (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) : PMF (canonicalEncodingInputs parameter → HashOutput) :=
  (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
    (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside (referenceFamilyCell parameter messages) → HashOutput)).map
      (UniformTableSplit.join (referenceFamilyCell parameter messages) (referenceFamilyCell_injective parameter messages)
        (Function.uncurry rows)))

theorem referenceEncodingPrior_uniform (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    referenceEncodingPrior parameter messages selections =
      uniformTable (referenceEncodingAllowed parameter messages selections)
        (referenceEncodingAllowed_nonempty parameter messages selections) := by
  have h := UniformTableSplit.uniformTable_join (referenceFamilyCell parameter messages)
    (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => Finset.univ)
    (encodingFamilyAllowed_nonempty selections) (fun _ => Finset.univ_nonempty)
  rw [uniformTable_univ, ← encoding_family_uniform selections, PMF.bind_map] at h
  exact h

theorem referenceEncodingPrior_complete (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) :
    𝒟[referenceEncodingPrior parameter messages selections] = complete (referenceEncodingAllowed parameter messages selections) := by
  rw [referenceEncodingPrior_uniform, complete_of_nonempty _ (referenceEncodingAllowed_nonempty parameter messages selections)]

theorem referenceEncodingAllowed_fresh (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter)
    (position : EncodingPosition) (hposition : AtEncodingPosition parameter cell.val position) :
    FreshEncodingSupport (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx)
      (referenceEncodingAllowed parameter messages selections cell) := by
  by_cases hc : cell ∈ Set.range (referenceFamilyCell parameter messages)
  · obtain ⟨row, rfl⟩ := hc
    have hp := atEncodingPosition_unique hposition
      (show AtEncodingPosition parameter (referenceFamilyCell parameter messages row).val row.1 from ⟨_, rfl⟩)
    subst position
    rw [referenceEncodingAllowed, UniformTableSplit.join_embed]
    exact encodingSelectionAllowed_fresh (selections row.1) (dummy row.1.lay row.1.tree row.1.leafIdx) row.2
  · have hrow := UniformTableSplit.join_outside (referenceFamilyCell parameter messages)
      (referenceFamilyCell_injective parameter messages) (encodingFamilyAllowed selections) (fun _ => (Finset.univ : Finset HashOutput))
      (⟨cell, hc⟩ : UniformTableSplit.Outside (referenceFamilyCell parameter messages))
    exact Or.inl hrow

end SphincsSecurity.Concrete

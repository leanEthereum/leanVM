module

public import XmssSecurity.Proof.WinningEventReduction
public import XmssSecurity.Proof.HashInputLemmas

@[expose] public section

open OracleSpec

namespace XmssSecurity

/-- Recover the leaf index tag from a well-formed serialized encoding input. Inputs outside the encoding domain return `none`. -/
noncomputable def encodingInputLeafIndex? (parameter : PublicParameter)
    (candidate : HashInput) : Option LeafIndex :=
  if h : ∃ leafIndex input,
      Concrete.CacheView.encodingInput parameter leafIndex input = candidate then
    some (Classical.choose h)
  else
    none

@[simp]
theorem encodingInputLeafIndex?_encodingInput (parameter : PublicParameter)
    (leafIndex : LeafIndex) (input : Message × Randomness) :
    encodingInputLeafIndex? parameter
      (Concrete.CacheView.encodingInput parameter leafIndex input) = some leafIndex := by
  unfold encodingInputLeafIndex?
  split <;> rename_i h
  · obtain ⟨chosenInput, hchosen⟩ := Classical.choose_spec h
    have hleafIndex : Classical.choose h = leafIndex :=
      Concrete.CacheView.leafIndex_eq_of_encodingInput_eq parameter hchosen
    rw [hleafIndex]
  · exfalso
    exact h ⟨leafIndex, input, rfl⟩

theorem exists_encodingInput_of_encodingInputLeafIndex?_eq_some
    (parameter : PublicParameter) (candidate : HashInput) (leafIndex : LeafIndex)
    (hleafIndex : encodingInputLeafIndex? parameter candidate = some leafIndex) :
    ∃ input : Message × Randomness,
      Concrete.CacheView.encodingInput parameter leafIndex input = candidate := by
  unfold encodingInputLeafIndex? at hleafIndex
  split at hleafIndex <;> rename_i h
  · obtain ⟨input, hinput⟩ := Classical.choose_spec h
    have heq : Classical.choose h = leafIndex := Option.some.inj hleafIndex
    rw [heq] at hinput
    exact ⟨input, hinput⟩
  · contradiction

end XmssSecurity

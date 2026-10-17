import XmssSecurity.Proof.WinningEventReduction
import XmssSecurity.Proof.HashInputLemmas

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

/-- `target` is the serialized input of the unique returned signature at the leaf index encoded by `candidate`. -/
def IsSignedEncodingTarget (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (candidate target : HashInput) : Prop :=
  ∃ request signature,
    SigningTranscript.Returned log request signature ∧
    encodingInputLeafIndex? parameter candidate = some request.leafIndex ∧
    target = Concrete.CacheView.encodingInput parameter request.leafIndex
      (request.message, signature.randomness)

theorem IsSignedEncodingTarget.unique
    {parameter : PublicParameter} {log : QueryLog SigningSpec}
    (hvalid : SigningTranscript.Valid log) {candidate left right : HashInput}
    (hleft : IsSignedEncodingTarget parameter log candidate left)
    (hright : IsSignedEncodingTarget parameter log candidate right) :
    left = right := by
  obtain ⟨leftRequest, leftSignature, hleftReturned, hleftLeafIndex, rfl⟩ := hleft
  obtain ⟨rightRequest, rightSignature, hrightReturned, hrightLeafIndex, rfl⟩ := hright
  have hleafIndex : leftRequest.leafIndex = rightRequest.leafIndex :=
    Option.some.inj (hleftLeafIndex.symm.trans hrightLeafIndex)
  obtain ⟨hrequest, hsignature⟩ :=
    SigningTranscript.returned_eq_of_same_leafIndex hvalid hleftReturned hrightReturned hleafIndex
  subst rightRequest
  subst rightSignature
  rfl

/-- Select the returned signature input at the candidate input's leaf index. If no signature was returned at that leaf index, leave the candidate unchanged. -/
noncomputable def signedEncodingTargetInput (parameter : PublicParameter)
    (log : QueryLog SigningSpec) (candidate : HashInput) : HashInput := by
  classical
  exact if h : ∃ target, IsSignedEncodingTarget parameter log candidate target then
      Classical.choose h
    else
      candidate

theorem signedEncodingTargetInput_eq_of_target
    {parameter : PublicParameter} {log : QueryLog SigningSpec}
    (hvalid : SigningTranscript.Valid log) {candidate target : HashInput}
    (htarget : IsSignedEncodingTarget parameter log candidate target) :
    signedEncodingTargetInput parameter log candidate = target := by
  classical
  unfold signedEncodingTargetInput
  split <;> rename_i h
  · exact IsSignedEncodingTarget.unique hvalid (Classical.choose_spec h) htarget
  · exact (h ⟨target, htarget⟩).elim

end XmssSecurity

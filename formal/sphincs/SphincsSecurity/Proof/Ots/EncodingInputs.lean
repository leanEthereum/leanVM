import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingSelectionCache
namespace SphincsSecurity.Concrete

noncomputable def canonicalEncodingInputs (parameter : PublicParameter) : Finset HashInput :=
  Finset.univ.biUnion fun position : EncodingPosition =>
    (Finset.univ : Finset (Digest × Fin encodingAttemptLimit)).image fun pair =>
      encodingRetryInput parameter position pair.1 pair.2.val

attribute [local irreducible] canonicalEncodingInputs

theorem encodingRetryInput_mem_canonicalEncodingInputs (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Fin encodingAttemptLimit) :
    encodingRetryInput parameter position message counter.val ∈ canonicalEncodingInputs parameter := by
  classical
  rw [canonicalEncodingInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨position, ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(message, counter), rfl⟩

end SphincsSecurity.Concrete

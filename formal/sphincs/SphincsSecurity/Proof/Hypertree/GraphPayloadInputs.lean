import SphincsSecurity.Proof.Hypertree.CanonicalGraphSampling
namespace SphincsSecurity.Concrete

attribute [local irreducible] canonicalPayloadInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem digestBytes_mem_canonicalPayloadInputs (value : Digest) : digestBytes value ∈ canonicalPayloadInputs := by
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    flatMap_mem_canonicalPayloadInputs [value] (by change 1 ≤ numChains; decide)

theorem nodePayload_mem_canonicalPayloadInputs (left right : Digest) : nodePayload left right ∈ canonicalPayloadInputs := by
  simpa only [nodePayload, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    flatMap_mem_canonicalPayloadInputs [left, right] (by change 2 ≤ numChains; decide)

theorem orderedPayload_mem_canonicalPayloadInputs (order : Bool) (left right : Digest) :
    orderedPayload order left right ∈ canonicalPayloadInputs := by
  cases order <;> exact nodePayload_mem_canonicalPayloadInputs _ _

theorem leafPayload_mem_canonicalPayloadInputs (values : ChainIndex → Digest) : leafPayload values ∈ canonicalPayloadInputs :=
  flatMap_mem_canonicalPayloadInputs (List.ofFn values) (by simp only [List.length_ofFn, le_refl])

theorem ftsRootsPayload_mem_canonicalPayloadInputs (values : FtsTree → Digest) : ftsRootsPayload values ∈ canonicalPayloadInputs :=
  flatMap_mem_canonicalPayloadInputs (List.ofFn values) (by simp only [List.length_ofFn]; decide)

theorem graphInput_mem_of_payload (parameter : PublicParameter) (position : Position) (payload : HashInput)
    (hp : payload ∈ canonicalPayloadInputs) : tweakableHashInput parameter position.domain payload ∈ canonicalGraphInputs parameter := by
  classical
  rw [canonicalGraphInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  exact ⟨position, Finset.mem_image.mpr ⟨payload, hp, rfl⟩⟩

end SphincsSecurity.Concrete

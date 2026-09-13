import SphincsSecurity.Statement

namespace SphincsSecurity

theorem layerHeight_le (lay : Layer) : layerHeight lay ≤ maxLayerHeight := by
  unfold layerHeight maxLayerHeight
  split <;> omega

abbrev Signature.counter (signature : Signature) (lay : Layer) : Counter :=
  (signature.layers lay).counter

abbrev Signature.chainValue (signature : Signature) (lay : Layer) : ChainIndex → Digest :=
  (signature.layers lay).chainValues

abbrev PaddedLayer := Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)

/-- Restrict an intermediate proof's padded path to the layer's actual height. -/
abbrev LayerSignature.ofPadded (lay : Layer) (part : PaddedLayer) : LayerSignature lay :=
  ⟨part.1, part.2.1, fun level => part.2.2 (level.castLE (layerHeight_le lay))⟩

@[ext]
theorem LayerSignature.ext {lay : Layer} {left right : LayerSignature lay}
    (hcounter : left.counter = right.counter) (hvalues : left.chainValues = right.chainValues)
    (hpath : left.path = right.path) : left = right := by
  cases left
  cases right
  simp_all

end SphincsSecurity

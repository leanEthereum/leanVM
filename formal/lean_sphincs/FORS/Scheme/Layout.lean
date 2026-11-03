import FORS.Scheme.Bytes

/-! The signature's byte layout: the randomizer, then per FORS tree the secret and the `a` auth
nodes, then per layer from the bottom up the WOTS+C counter, chain values and authentication path,
as the forest's layout (`crates/sphincs/src/scheme.rs::Signature::to_bytes`) with FORS in place of
the forest. -/

namespace FORS

variable [Params]

/-- One tree's opening: the secret, then the path. -/
def serializeTree (opening : TreeOpening) : List UInt8 :=
  bytesLE 16 opening.secret ++ (List.ofFn opening.path).flatMap (bytesLE 16)

/-- One layer: the counter, the 64 chain values, the path. -/
def serializeLayer {lay : Layer} (part : LayerSignature lay) : List UInt8 :=
  bytesLE 4 part.counter ++ (List.ofFn part.chainValues).flatMap (bytesLE 16) ++
    (List.ofFn part.path).flatMap (bytesLE 16)

def serializeSignature (signature : Signature) : List UInt8 :=
  bytesLE 16 signature.randomness ++
  (List.ofFn fun κ : FTree => serializeTree (signature.fors κ)).flatten ++
  (List.ofFn fun k : Fin numLayers => serializeLayer (signature.layers (layerUp k.val))).flatten

theorem digest_vector_length {n : Nat} (values : Fin n → Digest) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = n * 16 := by
  simp [List.length_flatMap, bytesLE_length]
  exact List.length_ofFn

theorem serializeTree_length (opening : TreeOpening) :
    (serializeTree opening).length = 16 * (forsHeight + 1) := by
  simp only [serializeTree, List.length_append, bytesLE_length, digest_vector_length]
  ring

theorem serializeLayer_length {lay : Layer} (part : LayerSignature lay) :
    (serializeLayer part).length = 1028 + 16 * layerHeight lay := by
  simp only [serializeLayer, List.length_append, bytesLE_length, digest_vector_length]
  change 4 + 64 * 16 + layerHeight lay * 16 = _
  omega

/-- The layer heights add up to the height. -/
theorem sum_layerHeight : ∑ lay : Layer, layerHeight lay = totalHeight := by
  have h1 := Params.lower_le
  have h2 := Params.numLayers_pos
  have hmax : lowerHeight ≤ maxLayerHeight := by
    unfold maxLayerHeight
    have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
      rw [← Nat.mul_succ]; congr 1; omega
    omega
  have hsplit : ∀ lay : Layer, layerHeight lay =
      lowerHeight + (if lay = topLayer then maxLayerHeight - lowerHeight else 0) := by
    intro lay
    unfold layerHeight
    by_cases h : lay.val = 0
    · have hl : lay = topLayer := Fin.ext h
      rw [if_pos h, if_pos hl]
      omega
    · have hl : lay ≠ topLayer := fun e => h (congrArg Fin.val e)
      rw [if_neg h, if_neg hl, Nat.add_zero]
  rw [Finset.sum_congr rfl fun lay _ => hsplit lay, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  unfold maxLayerHeight at hmax ⊢
  have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
    rw [← Nat.mul_succ]; congr 1; omega
  rw [Nat.mul_comm numLayers lowerHeight]
  omega

/-- The layers listed from the bottom up are every layer once. -/
theorem layerUp_bijective : Function.Bijective fun k : Fin numLayers => layerUp k.val := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => ?_, rfl⟩
  have h := congrArg Fin.val h
  simp only [layerUp] at h
  have := a.isLt; have := b.isLt
  exact Fin.ext (by omega)

/-- **Serialized size.** Every signature, malformed or not, serializes to
`16 + 16 k (a + 1) + 1028 d + 16 h` bytes. -/
theorem signature_size (signature : Signature) :
    (serializeSignature signature).length =
      16 + 16 * forsTrees * (forsHeight + 1) + 1028 * numLayers + 16 * totalHeight := by
  simp only [serializeSignature, List.length_append, bytesLE_length, List.length_flatten,
    List.map_ofFn, Function.comp_def, serializeTree_length, serializeLayer_length, List.sum_ofFn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum,
    Function.Bijective.sum_comp layerUp_bijective (fun lay => layerHeight lay), sum_layerHeight]
  ring

end FORS

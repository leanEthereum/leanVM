import Sphincs.Bytes

/-! The forest signature's byte layout: the randomizer, then per coordinate and per sub-tree the 6
chain values and the 3 auth nodes, then the 4 top-tree auth nodes, then the WOTS+C counter, chain
values and authentication path, as `crates/sphincs/src/scheme.rs::Signature::to_bytes` lays out the
FORS signature. -/

namespace Sphincs

/-- One coordinate's opening: sub-tree 0 (values, path), sub-tree 1 (values, path), top path. -/
def serializeCoord (opening : CoordOpening) : List UInt8 :=
  (List.ofFn fun j : SubIdx => (List.ofFn (opening.sub j).values).flatMap (bytesLE 16) ++
    (List.ofFn (opening.sub j).path).flatMap (bytesLE 16)).flatten ++
  (List.ofFn opening.top).flatMap (bytesLE 16)

def serializeSignature (signature : Signature) : List UInt8 :=
  bytesLE 16 signature.randomness ++
  (List.ofFn fun c : Coord => serializeCoord (signature.forest c)).flatten ++
  bytesLE 4 (signature.layers topLayer).counter ++
  (List.ofFn (signature.layers topLayer).chainValues).flatMap (bytesLE 16) ++
  (List.ofFn (signature.layers topLayer).path).flatMap (bytesLE 16)

theorem digest_vector_length {n : Nat} (values : Fin n → Digest) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = n * 16 := by
  simp [List.length_flatMap, bytesLE_length]
  exact List.length_ofFn

theorem serializeCoord_length (opening : CoordOpening) : (serializeCoord opening).length = 352 := by
  simp only [serializeCoord, List.length_append, digest_vector_length, List.length_flatten,
    List.map_ofFn, Function.comp_def, List.sum_ofFn, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  decide

/-- **Serialized size.** Every forest signature, malformed or not, serializes to 4276 bytes. -/
theorem signature_size (signature : Signature) : (serializeSignature signature).length = 4276 := by
  simp only [serializeSignature, List.length_append, bytesLE_length, digest_vector_length,
    List.length_flatten, List.map_ofFn, Function.comp_def, serializeCoord_length, List.sum_ofFn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  decide

end Sphincs

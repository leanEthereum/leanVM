import WhirAeneas.Hash.BatchInterface

namespace WhirAeneas.Hash

/-- The four bytes of a 32-bit word, least significant byte first. -/
def encodeWord (word : Word) : List (BitVec 8) :=
  List.ofFn fun i : Fin 4 => (word >>> (8 * i.val)).setWidth 8

/-- The 64-byte, little-endian serialization of a Merkle-pair block. -/
def encodeBlock (block : Vector Word 16) : List (BitVec 8) :=
  List.ofFn fun i : Fin 64 =>
    (block[i.val / 4]'(by omega) >>> (8 * (i.val % 4))).setWidth 8

@[simp] theorem encodeWord_length (word : Word) : (encodeWord word).length = 4 := by
  simp [encodeWord]

@[simp] theorem encodeBlock_length (block : Vector Word 16) : (encodeBlock block).length = 64 := by
  simp [encodeBlock]

theorem getD_encodeWord (word : Word) (i : Nat) (hi : i < 4) :
    (encodeWord word).getD i 0 = (word >>> (8 * i)).setWidth 8 := by
  simp only [encodeWord, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left hi, Option.getD_some]

theorem getD_encodeBlock (block : Vector Word 16) (i j : Nat)
    (hi : i < 16) (hj : j < 4) :
    (encodeBlock block).getD (4 * i + j) 0 =
      (block[i] >>> (8 * j)).setWidth 8 := by
  have hindex : 4 * i + j < 64 := by omega
  have hdiv : (4 * i + j) / 4 = i := by omega
  have hmod : (4 * i + j) % 4 = j := by omega
  simp only [encodeBlock, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left hindex, Option.getD_some, hdiv, hmod]

/-- Little-endian decoding recovers every 32-bit word, not only concrete test words. -/
theorem decode_encodeWord (word : Word) :
    BitVec.ofNat 32 (((encodeWord word).getD 0 0).toNat +
      256 * ((encodeWord word).getD 1 0).toNat +
      65536 * ((encodeWord word).getD 2 0).toNat +
      16777216 * ((encodeWord word).getD 3 0).toNat) = word := by
  simp only [getD_encodeWord word 0 (by omega), getD_encodeWord word 1 (by omega),
    getD_encodeWord word 2 (by omega), getD_encodeWord word 3 (by omega)]
  apply BitVec.eq_of_toNat_eq
  have hbound := word.isLt
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow] at *
  norm_num at *
  omega

@[simp] theorem blockWords_encodeBlock (block : Vector Word 16) :
    blockWords (encodeBlock block) 0 = block := by
  apply Vector.ext
  intro i hi
  simp only [blockWords, Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add]
  have hzero := getD_encodeBlock block i 0 hi (by omega)
  simp only [Nat.add_zero] at hzero
  rw [hzero,
    getD_encodeBlock block i 1 hi (by omega),
    getD_encodeBlock block i 2 hi (by omega),
    getD_encodeBlock block i 3 hi (by omega)]
  simpa only [getD_encodeWord _ 0 (by omega), getD_encodeWord _ 1 (by omega),
    getD_encodeWord _ 2 (by omega), getD_encodeWord _ 3 (by omega)]
    using decode_encodeWord block[i]

/-- The byte interface hashes a serialized 64-byte block with the actual shared RFC hash. -/
@[simp] theorem hashBytes_encodeBlock (block : Vector Word 16) :
    hashBytes (encodeBlock block) = LeanVMCircuits.Rec.hash64 block := by
  simp only [hashBytes, encodeBlock_length, blockWords_encodeBlock]
  change LeanVMCircuits.Rec.blake2s256 64 block [] = LeanVMCircuits.Rec.hash64 block
  rfl

/-- The 32-byte digest serialization at the Rust `U8` boundary. -/
def encodeDigest (words : Vector Word 8) : Digest :=
  .from (List.ofFn fun i : Fin 32 =>
    (⟨(words[i.val / 4]'(by omega) >>> (8 * (i.val % 4))).setWidth 8⟩ : Aeneas.Std.U8))
    (by simp)

@[simp] theorem encodeDigest_length (words : Vector Word 8) :
    (encodeDigest words).val.length = 32 := by
  simp [encodeDigest]

theorem getD_encodeDigest (words : Vector Word 8) (i j : Nat)
    (hi : i < 8) (hj : j < 4) :
    (encodeDigest words).val.getD (4 * i + j) 0#u8 =
      (⟨(words[i] >>> (8 * j)).setWidth 8⟩ : Aeneas.Std.U8) := by
  have hindex : 4 * i + j < 32 := by omega
  have hdiv : (4 * i + j) / 4 = i := by omega
  have hmod : (4 * i + j) % 4 = j := by omega
  simp only [encodeDigest, Aeneas.Std.Array.from_val,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left hindex, Option.getD_some, hdiv, hmod]

/-- The digest-word interface decodes every serialized RFC digest exactly. -/
@[simp] theorem digestWords_encodeDigest (words : Vector Word 8) :
    digestWords (encodeDigest words) = words := by
  apply Vector.ext
  intro i hi
  simp only [digestWords, Vector.getElem_ofFn]
  have hzero := getD_encodeDigest words i 0 hi (by omega)
  simp only [Nat.add_zero] at hzero
  rw [hzero,
    getD_encodeDigest words i 1 hi (by omega),
    getD_encodeDigest words i 2 hi (by omega),
    getD_encodeDigest words i 3 hi (by omega)]
  simpa only [Aeneas.Std.UScalar.val,
    getD_encodeWord _ 0 (by omega), getD_encodeWord _ 1 (by omega),
    getD_encodeWord _ 2 (by omega), getD_encodeWord _ 3 (by omega)]
    using decode_encodeWord words[i]

#print axioms decode_encodeWord
#print axioms blockWords_encodeBlock
#print axioms digestWords_encodeDigest
#print axioms hashBytes_encodeBlock

end WhirAeneas.Hash
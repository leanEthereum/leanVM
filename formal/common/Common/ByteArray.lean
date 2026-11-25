/-
  Common.ByteArray

  The length of a byte array's list, and of a string's UTF-8 bytes; little-endian bytes of a bit
  vector determine it.
-/

module

public import Init

@[expose] public section

/-!
# Byte arrays as lists

`ByteArray.toList` is a well-founded loop, which a `module` cannot evaluate (the proof of its
termination is not exported), so its length is a lemma: `ByteArray.length_toList`, and for a
string's UTF-8 bytes `String.length_toList_toUTF8`. `Common.ofFn_extractLsb'_bytes_injective`: a bit
vector's bytes, least significant first (the body of `HashSig.littleEndianBytes` and the schemes'
`bytesLE`), determine it.
-/

namespace ByteArray

theorem length_toList_loop (b : ByteArray) :
    ∀ (n i : Nat) (r : List UInt8), b.size - i = n →
      (toList.loop b i r).length = r.length + (b.size - i)
  | 0, i, r, h => by
    rw [toList.loop]
    split
    · omega
    · rw [List.length_reverse, h, Nat.add_zero]
  | n + 1, i, r, h => by
    rw [toList.loop]
    split
    · rw [length_toList_loop b n (i + 1) _ (by omega), List.length_cons]
      omega
    · omega

theorem length_toList (b : ByteArray) : b.toList.length = b.size := by
  rw [toList, length_toList_loop b _ 0 [] rfl, List.length_nil, Nat.zero_add, Nat.sub_zero]

end ByteArray

theorem String.length_toList_toUTF8 (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
  rw [ByteArray.length_toList]
  simp

/-- A bit vector of `8 * n` bits is determined by its `n` bytes, least significant first. -/
theorem Common.ofFn_extractLsb'_bytes_injective (n : Nat) :
    Function.Injective fun value : BitVec (8 * n) =>
      List.ofFn fun index : Fin n => UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8) := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrArg (fun bytes : List UInt8 => bytes[i / 8]?) h
  simp only [List.getElem?_ofFn, dite_eq_left hj, Option.some.injEq] at hbyte
  have hbits := congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

end

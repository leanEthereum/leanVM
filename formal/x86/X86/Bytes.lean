module

public import X86.Keccak.Spec
public import X86.Keccak.LittleEndian

/-!
# Bytes, words and the schemes' hash

The schemes' byte strings as words: a digest is two words, low first (`digestLo`, `digestHi`), a
message four (`word256`), and `H` over Keccak-f[1600] is `keccak256`'s four lanes
(`keccakHash_keccakF`, `truncate_keccakHash`).
-/

@[expose] public section

namespace X86

open LeanVM.Protocol.KeccakHash HashSig HashSig.OverPermutation Keccak

/-- A 128-bit value's low word. -/
def digestLo (d : BitVec 128) : UInt64 := UInt64.ofNat d.toNat

/-- A 128-bit value's high word. -/
def digestHi (d : BitVec 128) : UInt64 := UInt64.ofNat (d.toNat / 2 ^ 64)

/-- Word `i` of a 256-bit value, low first. -/
def word256 (v : BitVec 256) (i : Nat) : UInt64 := UInt64.ofNat (v.toNat / 2 ^ (64 * i))

/-- The 128-bit value of two words, low first. -/
def ofWords (lo hi : UInt64) : BitVec 128 := BitVec.ofNat 128 (lo.toNat + 2 ^ 64 * hi.toNat)

theorem littleEndianBytes_16 (d : BitVec 128) :
    littleEndianBytes 16 d = wordsBytes [digestLo d, digestHi d] := by
  refine Proof.littleEndianBytes_eq_wordsBytes 16 d _ rfl fun q hq ↦ ?_
  simp only [List.length_cons, List.length_nil] at hq
  interval_cases q <;> simp [digestLo, digestHi, UInt64.toNat_ofNat']

theorem littleEndianBytes_32 (v : BitVec 256) :
    littleEndianBytes 32 v = wordsBytes ((List.range 4).map (word256 v)) := by
  refine Proof.littleEndianBytes_eq_wordsBytes 32 v _ (by simp) fun q hq ↦ ?_
  simp only [List.length_map, List.length_range] at hq
  simp [List.getD_eq_getElem?_getD, hq, word256, UInt64.toNat_ofNat']

theorem digestLo_ofWords (lo hi : UInt64) : digestLo (ofWords lo hi) = lo := by
  apply UInt64.toNat_inj.mp
  have := lo.toNat_lt
  have := hi.toNat_lt
  simp only [digestLo, ofWords, BitVec.toNat_ofNat, UInt64.toNat_ofNat'] at *
  omega

theorem digestHi_ofWords (lo hi : UInt64) : digestHi (ofWords lo hi) = hi := by
  apply UInt64.toNat_inj.mp
  have := lo.toNat_lt
  have := hi.toNat_lt
  simp only [digestHi, ofWords, BitVec.toNat_ofNat, UInt64.toNat_ofNat'] at *
  omega

theorem ofWords_digest (d : BitVec 128) : ofWords (digestLo d) (digestHi d) = d := by
  apply BitVec.eq_of_toNat_eq
  have := d.isLt
  simp only [digestLo, digestHi, ofWords, BitVec.toNat_ofNat, UInt64.toNat_ofNat'] at *
  omega

/-- `H` over Keccak-f[1600] is the little-endian number of `keccak256`'s four lanes. -/
theorem keccakHash_keccakF (input : HashInput) :
    Id.run (keccakHash (m := Id) LeanVM.Semantics.keccakF1600 input) =
      BitVec.ofNat 256 (∑ i : Fin 4, (keccak256 input)[i].toNat * 2 ^ (64 * i.val)) := by
  rw [← Proof.foldr_digestBytes, keccakHash, Id.run_map]
  rfl

/-- `Truncate_16(H(input))` is `keccak256`'s first two lanes. -/
theorem truncate_keccakHash (input : HashInput) :
    truncateHash (Id.run (keccakHash (m := Id) LeanVM.Semantics.keccakF1600 input)) =
      ofWords (keccak256 input)[0] (keccak256 input)[1] := by
  rw [keccakHash_keccakF]
  exact Proof.truncateHash_sum _

end X86

module

public import NativeRustcArm.SphincsVerify.Rev
public import NativeRustc.Sphincs.EncodeFacts
public import NativeRustcArm.Sym.Run

/-!
# The digest as the 128-bit number `b109` loads

`b109` loads the digest's first 16 bytes as two words and reverses each (`rev`): the high word
`x9` and the low word `x10` of `u128::from_be_bytes` (`beNat_split`). A word's value is the
little-endian number of its bytes (`toNat_eq_leNat`), a reversed word's the big-endian
(`rev64_toNat`), and the bytes of a loaded word are the bytes (`bytes_ofBytes`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Sphincs NativeRustcArm.Sym

@[expose] public section

theorem natOfBytes_eq_leNat : ∀ bs : List UInt8, Nat.ofBytes bs = leNat bs
  | [] => rfl
  | b :: bs => by
    show Nat.ofBytes bs * 256 + b.toNat = b.toNat + 256 * leNat bs
    rw [natOfBytes_eq_leNat bs]
    omega

/-- A word's value: the little-endian number of its bytes. -/
theorem toNat_eq_leNat (y : BitVec 64) : y.toNat = leNat ((List.range 8).map (byteOf y)) := by
  have hb := Sym.ofBytes_byteOf y 0 8
  simp only [Nat.zero_add] at hb
  rw [Sym.ofBytes_natCast] at hb
  have h := Int.ofNat.inj hb
  rw [← natOfBytes_eq_leNat, h]
  have := y.isLt
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

/-- The bytes of a loaded word. -/
theorem bytes_ofBytes (bs : List UInt8) (h : bs.length = 8) :
    (List.range 8).map (byteOf (BitVec.ofInt 64 (Int.ofBytes bs))) = bs := by
  have hlt := Sym.natOfBytes_lt bs
  rw [h] at hlt
  have hx : (BitVec.ofInt 64 (Int.ofBytes bs)).toNat = Nat.ofBytes bs := by
    rw [Sym.ofBytes_natCast, BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  apply List.ext_getElem (by simp [h])
  intro t h1 h2
  rw [List.getElem_map, List.getElem_range, byteOf_mod, hx, Sym.natOfBytes_div bs t h2]
  simp

/-- A reversed word's value: the big-endian number of the word's bytes. -/
theorem rev64_toNat (x : BitVec 64) :
    (UnOp.apply .rev .W64 x).toNat = beNat ((List.range 8).map (byteOf x)) := by
  rw [toNat_eq_leNat (UnOp.apply .rev .W64 x), beNat]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range, List.getElem_reverse, List.getElem_map,
    List.getElem_range, byteOf_rev64 x h1]
  simp only [List.length_map, List.length_range]

/-- **The digest's number**: `x9 · 2⁶⁴ + x10`, the reversed words of its two halves. -/
theorem beNat_split (A B : List UInt8) (hA : A.length = 8) (hB : B.length = 8) :
    (UnOp.apply .rev .W64 (BitVec.ofInt 64 (Int.ofBytes A))).toNat * 2 ^ 64 +
      (UnOp.apply .rev .W64 (BitVec.ofInt 64 (Int.ofBytes B))).toNat = beNat (A ++ B) := by
  rw [rev64_toNat, rev64_toNat, bytes_ofBytes A hA, bytes_ofBytes B hB, beNat_append8 A B hB]

end

end NativeRustcArm.SphincsVerifyProof

module

public import NativeRustcArm.Sym

/-!
# The padding's arithmetic

`keccak256_words`'s padding computes, from the bytes past the whole blocks `r = len - 136 N`
(`r < 136`), the offset of the padded lane `r & !7` (`padIdx_val`: `8 (r / 8)`) and the padding
word `1 << ((r & 7) << 3)` (`padLow_val`: `1 <<< 8 (r % 8)`), both checked for each `r` by the
kernel. The whole blocks' count `len / 136` as rustc computes it, by the high word of a product
(`nb_val`), and the words' count `17 nb` (`nb17_val`).
-/

namespace NativeRustcVmArm.WordsHash

open NativeRustcArm NativeRustcArm.Sym

public section

theorem sub_mul_val {len nb : Nat} (h : 136 * nb ≤ len) :
    BinOp.apply .sub .W64 (BitVec.ofNat 64 len)
      (BinOp.apply .mul .W64 (BitVec.ofNat 64 nb) (BitVec.ofNat 64 136)) =
      BitVec.ofNat 64 (len - 136 * nb) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.toNat_sub, BitVec.toNat_mul,
    BitVec.toNat_ofNat]
  omega

theorem and_val_aux : ∀ r < 136,
    BinOp.apply .and .W64 (BitVec.ofNat 64 r) (BitVec.ofNat 64 18446744073709551608) =
      BitVec.ofNat 64 (8 * (r / 8)) := by
  decide +kernel

theorem low_val_aux : ∀ r < 136,
    BinOp.apply .lslv .W64 (BitVec.ofNat 64 1) (UnOp.apply (.ubfm 61 2) .W64 (BitVec.ofNat 64 r)) =
      ((1 : UInt64) <<< (8 * (r % 8)).toUInt64).toBitVec := by
  decide +kernel

theorem memExtE0 (i : Nat) :
    UnOp.apply (.memExtend ⟨.UXTX, .E0⟩) .W64 (BitVec.ofNat 64 i) = BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp [UnOp.apply, BitVec.apply_mem_extend, BitVec.unsigned]
  omega

theorem umulh_toNat (a b : BitVec 64) :
    (BinOp.apply .umulh .W64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    BitVec.unsigned]
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb
    simpa using this
  rw [show ((a.toNat : Int) * (b.toNat : Int)) = ((a.toNat * b.toNat : Nat) : Int) by push_cast; rfl]
  have hw : RegWidth.W64.bits = 64 := rfl
  rw [hw, Nat.shiftRight_eq_div_pow]
  omega

theorem lsr7 (v : BitVec 64) : (UnOp.apply (.ubfm 7 63) .W64 v).toNat = v.toNat / 128 := by
  simp only [UnOp.apply, Sym.low_W64, Sym.ext_W64, evalUBFM, BitVec.take]
  have hw : RegWidth.W64.bits = 64 := rfl
  simp only [hw]
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- **The whole blocks' count**, by the high word of `len` times `⌈2 ^ 71 / 136⌉`. -/
theorem nb_val (x : Nat) (hx : x < 2 ^ 64) :
    UnOp.apply (.ubfm 7 63) .W64 (BinOp.apply .umulh .W64 (BitVec.ofNat 64 x)
      (BitVec.ofNat 64 17361641481138401521)) = BitVec.ofNat 64 (x / 136) := by
  apply BitVec.eq_of_toNat_eq
  rw [lsr7, umulh_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show 17361641481138401521 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show x / 136 < 2 ^ 64 by omega)]
  omega

/-- The words of the whole blocks, `nb + (nb << 4)`. -/
theorem nb17_val (n : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 n) (UnOp.apply (.shift .LSL 4) .W64 (BitVec.ofNat 64 n)) =
      BitVec.ofNat 64 (17 * n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BinOp.apply, UnOp.apply, shiftW, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

end

end NativeRustcVmArm.WordsHash

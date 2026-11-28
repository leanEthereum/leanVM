module

public import NativeRustcX64.Sym

/-!
# `keccak256_words` (x86-64): the arithmetic of its counts and padding

The whole blocks' count `len / 136` as rustc computes it, the high word of `len` times
`⌈2 ^ 71 / 136⌉` shifted right by 7 (`nb_val`); `17 nb` as `nb + (nb << 4)` (`nb17_val`); the high
word with its low 7 bits cleared, `128 nb` (`and128_val`). The padding, from the bytes past the
whole blocks `r = len - 136 nb < 136`: the padded lane's offset `r & !7` (`and8_val`) and the
padding word `1 << 8 r` (`padWord_val`, `8 r` by a scaled LEA truncated to 32 bits), both checked for
each `r` by the kernel.
-/

namespace NativeRustcVmX64.WordsHash

open NativeRustcX64 NativeRustcX64.Sym

public section

theorem mulhi_toNat (a b : BitVec 64) :
    (BinOp.apply .mulhi .W64 a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have ha := a.isLt
  have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    have := Nat.mul_lt_mul'' ha hb
    simpa using this
  generalize hP : a.toNat * b.toNat = P at hab
  have hP' : ((a.toNat : Int) * (b.toNat : Int)) = (P : Int) := by rw [← hP]; push_cast; rfl
  show (ext .W64 (BitVec.ofInt 64 (((low .W64 a).unsigned * (low .W64 b).unsigned) >>> 64))).toNat = _
  rw [ext_W64, low_W64, low_W64]
  show (BitVec.ofInt 64 (((a.toNat : Int) * (b.toNat : Int)) >>> 64)).toNat = _
  rw [hP', Int.shiftRight_eq_div_pow,
    show (P : Int) / ((2 ^ 64 : Nat) : Int) = ((P / 2 ^ 64 : Nat) : Int) by omega,
    BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  omega

theorem shr7_toNat (v : BitVec 64) :
    (BinOp.apply .shr .W64 v (BitVec.ofNat 64 7)).toNat = v.toNat / 128 := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 7) = 7 := by decide
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

/-- **The whole blocks' count.** -/
theorem nb_val (x : BitVec 64) :
    BinOp.apply .shr .W64 (BinOp.apply .mulhi .W64 x (BitVec.ofNat 64 17361641481138401521))
      (BitVec.ofNat 64 7) = BitVec.ofNat 64 (x.toNat / 136) := by
  have hx := x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [shr7_toNat, mulhi_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 17361641481138401521 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show x.toNat / 136 < 2 ^ 64 by omega)]
  omega

/-- The high word's `toNat`, by `len / 136`. -/
theorem mhi_div (x : BitVec 64) :
    (BinOp.apply .mulhi .W64 x (BitVec.ofNat 64 17361641481138401521)).toNat / 128 =
      x.toNat / 136 := by
  have hx := x.isLt
  rw [mulhi_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 17361641481138401521 < 2 ^ 64 by decide)]
  omega

/-- **`17 nb`** as `nb + (nb << 4)`. -/
theorem nb17_val (n : Nat) :
    BinOp.apply .add .W64 (BitVec.ofNat 64 n) (BinOp.apply .shl .W64 (BitVec.ofNat 64 n)
      (BitVec.ofNat 64 4)) = BitVec.ofNat 64 (17 * n) := by
  have hs : shiftCount .W64 (BitVec.ofNat 64 4) = 4 := by decide
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, hs, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem testBit_mask128 (i : Nat) :
    (18446744073709551488 : Nat).testBit i = (decide (7 ≤ i) && decide (i < 64)) := by
  rw [show (18446744073709551488 : Nat) = (2 ^ 57 - 1) * 2 ^ 7 by decide, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one]
  by_cases h : 7 ≤ i <;> simp [h] <;> omega

/-- **The high word with its low 7 bits cleared.** -/
theorem and128_val (v : BitVec 64) :
    BinOp.apply .and .W64 v (BitVec.ofNat 64 18446744073709551488) =
      BitVec.ofNat 64 (128 * (v.toNat / 128)) := by
  have hv := v.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 18446744073709551488 < 2 ^ 64 by decide),
    Nat.mod_eq_of_lt (show 128 * (v.toNat / 128) < 2 ^ 64 by omega)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_mask128, show 128 * (v.toNat / 128) = v.toNat / 2 ^ 7 * 2 ^ 7 by
    omega, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h7 : 7 ≤ i
  · by_cases h64 : i < 64
    · simp [h7, h64, show i - 7 + 7 = i by omega]
    · have : v.toNat.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv
        (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h7, h64, show i - 7 + 7 = i by omega, this]
  · simp [h7]

/-- The padded lane's offset, `r & !7`. -/
theorem and8_val : ∀ r < 136,
    BinOp.apply .and .W64 (BitVec.ofNat 64 r) (BitVec.ofNat 64 18446744073709551608) =
      BitVec.ofNat 64 (8 * (r / 8)) := by
  decide +kernel

/-- `8 r` from the raw scaled LEA, truncated to 32 bits. -/
@[expose] def oct32 (x : BitVec 64) : BitVec 64 :=
  UnOp.apply .trunc .W32 (BinOp.apply .mul .W64 x (BitVec.ofNat 64 8))

/-- The padding word, `1 << 8 r`. -/
theorem padWord_val : ∀ r < 136,
    BinOp.apply .shl .W64 (BitVec.ofNat 64 1) (oct32 (BitVec.ofNat 64 r)) =
      ((1 : UInt64) <<< (8 * (r % 8)).toUInt64).toBitVec := by
  decide +kernel

end

end NativeRustcVmX64.WordsHash

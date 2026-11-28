module

public import NativeRustcArm.WotsLeaf.Codeword.Exec
public import NativeRustcArm.Sym

/-!
# The digits as the loop computes them

Bits `s, s + 1` of the 128-bit digest `2 ^ 64 hi + lo`: from `lo >>> s` and `hi << (64 - s)` below
64 (`digit_lo`), from `hi >>> (s - 64)` above (`digit_hi`); the executor's `digitSym d` is digit
`d` (`byteOf_digitSym`).
-/

namespace NativeRustcArm.WotsLeafProof.Codeword

open NativeRustcArm.Sym

public section

theorem digit_lo (lo hi : BitVec 64) {s : Nat} (hs : s + 1 < 64) :
    (((hi <<< 1) <<< (63 - s)) ||| (lo >>> s)).toNat % 4 =
      (2 ^ 64 * hi.toNat + lo.toNat) >>> s % 4 := by
  show _ % 2 ^ 2 = _ % 2 ^ 2
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi2 : i < 2
  · simp only [hi2, decide_true, Bool.true_and]
    rw [Nat.testBit_shiftRight, Nat.testBit_two_pow_mul_add _ lo.isLt,
      Sym.ite_pos (show s + i < 64 by omega)]
    rw [← BitVec.getLsbD, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ushiftRight]
    simp only [BitVec.getLsbD]
    by_cases h : i < 63 - s
    · simp [h]
    · simp [h]; omega
  · simp [hi2]

theorem digit_hi (lo hi : BitVec 64) {s : Nat} (h64 : 64 ≤ s) :
    (hi >>> (s - 64)).toNat % 4 = (2 ^ 64 * hi.toNat + lo.toNat) >>> s % 4 := by
  show _ % 2 ^ 2 = _ % 2 ^ 2
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi2 : i < 2
  · simp only [hi2, decide_true, Bool.true_and]
    rw [Nat.testBit_shiftRight, Nat.testBit_two_pow_mul_add _ lo.isLt,
      Sym.ite_neg (show ¬ s + i < 64 by omega), BitVec.toNat_ushiftRight, Nat.testBit_shiftRight]
    congr 1
    omega
  · simp [hi2]

theorem and3 (a : Nat) : (a % 4294967296 &&& 3) % 18446744073709551616 = a % 4 := by
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega


/-- **Digit `d`** of the digest, as the executor's value of `digitSym d`. -/
theorem toNat_digitSym [Labels] (env : Env) {lo hi : BitVec 64} (h8 : env.regs .X8 = hi)
    (h9 : env.regs .X9 = lo) (h10 : env.regs .X10 = hi <<< 1) {d : Nat} (hd : 2 * d < 128) :
    ((digitSym d).eval env).toNat = (2 ^ 64 * hi.toNat + lo.toNat) >>> (2 * d) % 4 := by
  unfold digitSym
  split
  · rename_i hs
    rw [← digit_lo lo hi (s := 2 * d) (by omega)]
    sym_simp
    rw [h9, h10]
    have e1 : (BitVec.ofNat 64 (4294967295 - 2 * d)).toNat % RegWidth.W64.bits = 63 - 2 * d := by
      show (4294967295 - 2 * d) % 2 ^ 64 % 64 = _
      omega
    have e2 : (BitVec.ofNat 64 (2 * d)).toNat % RegWidth.W64.bits = 2 * d := by
      show (2 * d) % 2 ^ 64 % 64 = _
      omega
    rw [e1, e2, BitVec.ushiftRight_eq]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    exact and3 _
  · rename_i hs
    rw [← digit_hi lo hi (s := 2 * d) (by omega)]
    sym_simp
    rw [h8]
    have e2 : (BitVec.ofNat 64 (2 * d)).toNat % RegWidth.W64.bits = 2 * d - 64 := by
      show (2 * d) % 2 ^ 64 % 64 = _
      omega
    rw [e2, BitVec.ushiftRight_eq]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    exact and3 _

/-- **Digit `d`** of the digest, the byte the loop stores. -/
theorem byteOf_digitSym [Labels] (env : Env) {lo hi : BitVec 64} (h8 : env.regs .X8 = hi)
    (h9 : env.regs .X9 = lo) (h10 : env.regs .X10 = hi <<< 1) {d : Nat} (hd : 2 * d < 128) :
    byteOf ((digitSym d).eval env) 0 =
      UInt8.ofNat ((2 ^ 64 * hi.toNat + lo.toNat) >>> (2 * d) &&& 3) := by
  rw [show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, ← toNat_digitSym env h8 h9 h10 hd]
  simp [byteOf]

end

end NativeRustcArm.WotsLeafProof.Codeword

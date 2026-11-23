module

public import NativeRustcVmArm.Field.Norm

/-!
# 32-bit counters and tests

The values of the executor's 32-bit operations and comparisons on counters below `2^32`, and its
64-bit comparisons with literals, as `Nat` facts.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm NativeRustcArm.Sym

public section

theorem low32_toNat (x : BitVec 64) : (low .W32 x).toNat = x.toNat % 2 ^ 32 := by
  rw [low_W32, BitVec.toNat_setWidth]

theorem trunc32_toNat (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [UnOp.apply, ext_W32, BitVec.toNat_setWidth, low32_toNat]
  omega

theorem sub32_toNat {x : BitVec 64} (h1 : 1 ≤ x.toNat) (h2 : x.toNat < 2 ^ 32) :
    (BinOp.apply .sub .W32 x (BitVec.ofNat 64 1)).toNat = x.toNat - 1 := by
  simp only [BinOp.apply, ext_W32, BitVec.toNat_setWidth, BitVec.toNat_sub, low32_toNat,
    BitVec.toNat_ofNat]
  omega

theorem sub64_toNat {x : BitVec 64} (h1 : 1 ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 1)).toNat = x.toNat - 1 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem eq32_one (x : BitVec 64) :
    CmpOp.apply .eq .W32 x (BitVec.ofNat 64 1) = decide (x.toNat % 2 ^ 32 = 1) := by
  simp only [CmpOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, low32_toNat,
    low32_toNat, BitVec.toNat_ofNat]

theorem eq64_lit (x : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 n) = decide (x.toNat = n) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn]

theorem bit32_zero (x : BitVec 64) : (low .W32 x).getLsbD 0 = decide (x.toNat % 2 = 1) := by
  simp [low_W32, BitVec.getLsbD, Nat.testBit_zero]

end

end NativeRustcVmArm.Field

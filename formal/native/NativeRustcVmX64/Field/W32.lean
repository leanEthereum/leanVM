module

public import NativeRustcX64.Sym

/-!
# Counters and tests (x86-64)

The values of the executor's 32-bit operations and comparisons on counters below `2^32`, and its
64-bit ones, as `Nat` facts.
-/

namespace NativeRustcVmX64.Field

open NativeRustcX64 NativeRustcX64.Sym

public section

theorem low32_toNat (x : BitVec 64) : (low .W32 x).toNat = x.toNat % 2 ^ 32 := toNat_low .W32 x

theorem trunc32_toNat (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat = x.toNat % 2 ^ 32 := by
  simp only [UnOp.apply, toNat_ext, low32_toNat]

theorem sub32_toNat {x : BitVec 64} (h1 : 1 ≤ x.toNat) (h2 : x.toNat < 2 ^ 32) :
    (BinOp.apply .sub .W32 x (BitVec.ofNat 64 1)).toNat = x.toNat - 1 := by
  simp only [BinOp.apply, toNat_ext, BitVec.toNat_sub, low32_toNat, BitVec.toNat_ofNat]
  show (2 ^ 32 - 1 % 2 ^ 64 % 2 ^ 32 + x.toNat % 2 ^ 32) % 2 ^ 32 = _
  omega

theorem sub64_toNat {x : BitVec 64} (h1 : 1 ≤ x.toNat) :
    (BinOp.apply .sub .W64 x (BitVec.ofNat 64 1)).toNat = x.toNat - 1 := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

theorem eq32_zero (x : BitVec 64) :
    CmpOp.apply .eq .W32 x (BitVec.ofNat 64 0) = decide (x.toNat % 2 ^ 32 = 0) := by
  simp only [CmpOp.apply]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, low32_toNat,
    low32_toNat, BitVec.toNat_ofNat]

theorem eq64_zero (x : BitVec 64) :
    CmpOp.apply .eq .W64 x (BitVec.ofNat 64 0) = decide (x.toNat = 0) := by
  simp only [CmpOp.apply, low_W64]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat]

theorem and_self_apply (x : BitVec 64) : BinOp.apply .and .W64 x x = x := by
  simp only [BinOp.apply, low_W64, ext_W64, BitVec.and_self]

end

end NativeRustcVmX64.Field

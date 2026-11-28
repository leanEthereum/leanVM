module

public import NativeRustcArm.Sym
public import NativeRustcVm.Field.Rust

/-!
# Normalising the field functions' symbolic values

The executor's operations at width 64 as plain `BitVec 64` operations (`and_apply`, `mul_apply`,
`rbit_apply`, `lsr_apply`, `ubfm_lsr`, …; `sym_simp` would leave them at the width's type, which
`ac_rfl` does not identify with `BitVec 64`), rewritten by `field_ops at h`. Then rustc's order of
the reduction (`v = hi >> 62 ^ hi >> 61 ^ hi >> 1` for `hi` before its shift,
`lo ^ v << 1 ^ v << 3 ^ v << 4 ^ v`) as `Field.reduce` (`reduce_of`), and `kmul` from its two carry-less halves
(`kmul_of`): `ac_rfl` does not normalise below a shift or `reverse`, so each half is matched
separately.
-/

namespace NativeRustcVmArm.Field

open NativeRustcArm NativeRustcArm.Sym

public section

theorem ubfm_lsr (x : BitVec 64) (s : Nat) (hs : s < 64) :
    UnOp.apply (.ubfm s 63) .W64 x = x >>> s := by
  simp only [UnOp.apply, low_W64, ext_W64, evalUBFM]
  rw [ite_eq_left (by show 63 % 64 ≥ s % 64; omega)]
  ext i hi
  simp only [BitVec.take, BitVec.getElem_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ushiftRight, Nat.mod_eq_of_lt hs, BitVec.getElem_ushiftRight]
  show (decide (i < 63 % 64 - s + 1) && x.getLsbD (s + (0 + i))) = x.getLsbD (s + i)
  rw [Nat.zero_add]
  by_cases h : i < 63 % 64 - s + 1
  · rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_false h, Bool.false_and]
    exact (BitVec.getLsbD_of_ge x _ (by omega)).symm

theorem rbit_apply (x : BitVec 64) : UnOp.apply .rbit .W64 x = x.reverse := by
  simp only [UnOp.apply, low_W64, ext_W64]

theorem lsl_apply (x : BitVec 64) (n : Nat) : UnOp.apply (.shift .LSL n) .W64 x = x <<< n := by
  simp only [UnOp.apply, low_W64, ext_W64, shiftW]

theorem lsr_apply (x : BitVec 64) (n : Nat) : UnOp.apply (.shift .LSR n) .W64 x = x >>> n := by
  simp only [UnOp.apply, low_W64, ext_W64, shiftW, BitVec.ushiftRight_eq]

theorem and_apply (x y : BitVec 64) : BinOp.apply .and .W64 x y = x &&& y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem orr_apply (x y : BitVec 64) : BinOp.apply .orr .W64 x y = x ||| y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem eor_apply (x y : BitVec 64) : BinOp.apply .eor .W64 x y = x ^^^ y := by
  simp only [BinOp.apply, low_W64, ext_W64]

theorem mul_apply (x y : BitVec 64) : BinOp.apply .mul .W64 x y = x * y := by
  simp only [BinOp.apply, low_W64, ext_W64]

/-- rustc's reduction of `hi · x^64 + lo`, `R` the high word before its shift by one. -/
theorem reduce_of (L R : BitVec 64) :
    L ^^^ ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) <<< 1 ^^^
        ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) <<< 3 ^^^
        ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) <<< 4 ^^^ ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) =
      NativeRustcVm.Field.reduce L (R >>> 1) := by
  have hv : R >>> 1 ^^^ (R >>> 1 >>> 63 ^^^ R >>> 1 >>> 61 ^^^ R >>> 1 >>> 60) =
      (R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1 := by
    simp only [← BitVec.shiftRight_add, Nat.reduceAdd,
      BitVec.ushiftRight_eq_zero (show 64 ≤ 64 by decide), BitVec.zero_xor]
    ac_rfl
  simp only [NativeRustcVm.Field.reduce, hv]
  ac_rfl

/-- `kmul` from its halves: `L` the low word of the carry-less product, `R` the high word before
its shift. -/
theorem kmul_of {a b L R : BitVec 64} (hL : L = NativeRustcVm.Field.clmulLow a b)
    (hR : R = (NativeRustcVm.Field.clmulLow a.reverse b.reverse).reverse) :
    L ^^^ ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) <<< 1 ^^^
        ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) <<< 3 ^^^
        ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) <<< 4 ^^^ ((R >>> 62 ^^^ R >>> 61) ^^^ R >>> 1) =
      NativeRustcVm.Field.kmul a b := by
  rw [reduce_of, hL, hR]
  rfl

end

/-- Rewrites the executor's width-64 operations in a summary's values to `BitVec 64` ones. -/
syntax "field_ops" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| field_ops $[$loc]?) =>
    `(tactic| simp only [NativeRustcArm.Sym.eval, NativeRustcVmArm.Field.rbit_apply,
      NativeRustcVmArm.Field.lsl_apply, NativeRustcVmArm.Field.lsr_apply,
      NativeRustcVmArm.Field.and_apply, NativeRustcVmArm.Field.orr_apply,
      NativeRustcVmArm.Field.eor_apply, NativeRustcVmArm.Field.mul_apply,
      NativeRustcVmArm.Field.ubfm_lsr _ _ (show 62 < 64 by decide)] $[$loc]?)

end NativeRustcVmArm.Field

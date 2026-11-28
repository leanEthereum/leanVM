module

public import NativeRustcVmArm.Transcript.Glue
public import NativeVm.Input

/-!
# The arithmetic of the transcript's blocks

What the executor's operations compute on the values the transcript's functions handle:
`ubfm x, k, 63` is `x >>> k` (`evalUBFM_lsr`), `ubfm x, 63, 62` is `x <<< 1` (`evalUBFM_lsl1`); an
index register scaled by `8` in an address (`memExtend3_toNat`); `(l >>> 3) | 1` is `streamEnd l`
(`streamEnd_eval`).
-/

namespace NativeRustcVmArm.Transcript

open NativeRustcArm NativeRustcArm.Sym

public section

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

/-- `ubfm x, k, 63` (`lsr x, #k`). -/
theorem evalUBFM_lsr (x : BitVec 64) {k : Nat} (hk : k < 64) :
    (evalUBFM (w := .W64) x k 63 : BitVec 64) = x >>> k := by
  have hb : RegWidth.W64.bits = 64 := rfl
  apply BitVec.eq_of_toNat_eq
  simp only [evalUBFM, hb, Nat.mod_eq_of_lt hk, show 63 % 64 = 63 from rfl,
    show 63 ≥ k from by omega, ↓reduceIte, BitVec.toNat_setWidth, toNat_take',
    BitVec.toNat_ushiftRight]
  have h1 : x.toNat >>> k < 2 ^ (63 - k + 1) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add,
      show 63 - k + 1 + k = 64 by omega]
    exact x.isLt
  have h2 : 2 ^ (63 - k + 1) ≤ 2 ^ 64 := Nat.pow_le_pow_right (by omega) (by omega)
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]

/-- `ubfm x, 63, 62` (`lsl x, #1`): twice `x`, modulo `2 ^ 64`. -/
theorem evalUBFM_lsl1_toNat (x : BitVec 64) :
    (evalUBFM (w := .W64) x 63 62 : BitVec 64).toNat = 2 * x.toNat % 2 ^ 64 := by
  have hb : RegWidth.W64.bits = 64 := rfl
  simp only [evalUBFM, hb, show 63 % 64 = 63 from rfl, show 62 % 64 = 62 from rfl,
    show ¬ (62 ≥ 63) from by omega, ↓reduceIte, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    toNat_take']
  rw [show 64 - 63 = 1 from rfl, Nat.shiftLeft_eq]
  have := x.isLt
  simp only [Nat.reducePow, Nat.reduceAdd] at this ⊢
  omega

/-- An index scaled by `8` (`[xn, xm, lsl #3]`). -/
theorem memExtend3_toNat (x : BitVec 64) :
    (BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩)).toNat = x.toNat * 8 % 2 ^ 64 := by
  simp only [BitVec.apply_mem_extend, BitVec.unsigned]
  rw [Int.shiftLeft_eq, BitVec.toNat_ofInt]
  push_cast
  omega

theorem or_one_eq (n : Nat) : n ||| 1 = 2 * (n / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero =>
    rw [Nat.testBit_or, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    simp only [show (1 : Nat) % 2 = 1 from rfl, show (2 * (n / 2) + 1) % 2 = 1 by omega,
      decide_true, Bool.or_true]
  | succ j =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * (n / 2) + 1) / 2 = n / 2 by omega, show (1 : Nat) / 2 = 0 from rfl,
      Nat.zero_testBit, Bool.or_false]

/-- `(l >>> 3) | 1`, the stream's end. -/
theorem streamEnd_eval (x : BitVec 64) :
    (evalUBFM (w := .W64) x 3 63 ||| BitVec.ofNat 64 1 : BitVec 64).toNat =
      NativeVm.streamEnd x.toNat := by
  rw [evalUBFM_lsr x (by decide), BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, show 1 % 2 ^ 64 = 1 from rfl, or_one_eq]
  simp only [NativeVm.streamEnd, NativeVm.maxStream]
  omega

end

end NativeRustcVmArm.Transcript

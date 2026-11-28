module

public import NativeRustcX64.Sym
public import NativeVm.Input

/-!
# Arithmetic of the decoded area's offsets, as the x86-64 blocks compute them

`(l >> 3) | 1` is the stream's end `streamEnd l` (`streamEnd_eval`).
-/

namespace NativeRustcVmX64.Transcript

open NativeRustcX64 NativeRustcX64.Sym

public section

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
    (x.ushiftRight (shiftCount .W64 (BitVec.ofNat 64 3)) ||| BitVec.ofNat 64 1).toNat =
      NativeVm.streamEnd x.toNat := by
  rw [show shiftCount .W64 (BitVec.ofNat 64 3) = 3 from rfl, BitVec.toNat_or]
  change (x >>> 3).toNat ||| (BitVec.ofNat 64 1).toNat = _
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show 1 % 2 ^ 64 = 1 from rfl, or_one_eq]
  simp only [NativeVm.streamEnd, NativeVm.maxStream]
  omega

theorem low8_replaceLow (x : BitVec 64) (y : BitVec 8) : low .W8 (x.replaceLow y) = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi8 : i < 8 := hi
  simp only [low, BitVec.replaceLow, BitVec.getLsbD_setWidth]
  change (decide (i < 8) && (decide (i < 64) && ((x.drop 8) ++ y).getLsbD i)) = _
  rw [BitVec.getLsbD_append]
  simp [hi8, show i < 64 by omega]

/-- `mov $1, %bl`: the low byte `1`. -/
theorem merge_one_mod (x : BitVec 64) :
    (BinOp.apply .merge .W8 x (BitVec.ofNat 64 1)).toNat % 256 = 1 := by
  have h := congrArg BitVec.toNat (low8_replaceLow x (low .W8 (BitVec.ofNat 64 1)))
  rw [toNat_low, toNat_low] at h
  exact h

/-- `mov %ebx, %eax`: the low byte kept. -/
theorem trunc32_mod (x : BitVec 64) :
    (UnOp.apply .trunc .W32 x).toNat % 256 = x.toNat % 256 := by
  rw [UnOp.apply, toNat_ext, toNat_low]
  exact Nat.mod_mod_of_dvd _ (by decide)

end

end NativeRustcVmX64.Transcript

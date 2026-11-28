module

public import NativeRustcVmX64.KeccakGkr.SlotWeights.Exec

/-!
# `slot_weights`: the blocks' arithmetic (x86-64)

The values of the symbolic expressions `SlotWeights.Exec` names (`packS`, `ptrS`, `lenS`: the
segment coordinates `eq_kernel` takes; `r14S`, `rowS`, `colS`: a product's row and column), the
loops' tests as comparisons of numbers, and AL at the return.
-/

namespace NativeRustcVmX64.KeccakGkr.SlotWeights

open NativeRustcX64 NativeRustcX64.Sym

public section

variable [Labels] (env : Env)

omit [Labels] in
theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

omit [Labels] in
/-- Two small numbers as words are equal when they are. -/
theorem beq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, BitVec.toNat_eq, toNat_ofNat_lt ha,
    toNat_ofNat_lt hb]

omit [Labels] in
/-- Small numbers added as words. -/
theorem add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add]

theorem packS_eval :
    packS.eval env = BitVec.ofNat 64 ((env.regs .rdi).toNat - 4) := by
  have := (env.regs .rdi).isLt
  unfold packS
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64]
  apply BitVec.eq_of_toNat_eq
  split <;> rename_i h <;> simp_all [BitVec.ult] <;> omega

theorem ptrS_eval (h : (env.regs .rdi).toNat - 4 ≤ (env.regs .rdx).toNat) :
    ptrS.eval env = env.regs .rsi + BitVec.ofNat 64 (16 * ((env.regs .rdi).toNat - 4)) := by
  have := (env.regs .rdi).isLt
  have := (env.regs .rdx).isLt
  unfold ptrS
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, packS_eval]
  split
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [show shiftCount .W64 (BitVec.ofNat 64 4) = 4 by decide, BitVec.toNat_shiftLeft,
      toNat_ofNat_lt (by omega), Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    simp only [Width.bits]
    omega
  · rename_i hc
    simp [BitVec.ult] at hc
    omega

theorem lenS_eval (h : (env.regs .rdi).toNat - 4 ≤ (env.regs .rdx).toNat) :
    (lenS.eval env).toNat = (env.regs .rdx).toNat - ((env.regs .rdi).toNat - 4) := by
  have := (env.regs .rdi).isLt
  have := (env.regs .rdx).isLt
  unfold lenS
  simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, packS_eval]
  split
  · rw [BitVec.toNat_sub, toNat_ofNat_lt (by omega)]
    omega
  · rename_i hc
    simp [BitVec.ult] at hc
    omega

/-- `25 (segment + first)`. -/
theorem r14S_eval {s f : Nat} (hs : (env.regs .rcx).toNat = s) (hf : (env.load 0 16 8).toNat = f)
    (h : s + f < 4) : (r14S.eval env).toNat = 25 * (s + f) := by
  unfold r14S
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, BitVec.toNat_mul, hs, hf,
    BitVec.toNat_ofNat]
  omega

/-- A product's row: `25 (first + segment) + j / 64`. -/
theorem rowS_eval {a j : Nat} (h14 : (env.regs .r14).toNat = a) (h15 : (env.regs .r15).toNat = j)
    (ha : a < 2 ^ 32) (hj : j < 2 ^ 32) : (rowS.eval env).toNat = a + j / 64 := by
  unfold rowS
  simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, BitVec.toNat_add, h14,
    show shiftCount .W64 (BitVec.ofNat 64 6) = 6 by decide]
  rw [show ((env.regs .r15).ushiftRight 6).toNat = j / 64 by
    rw [BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, h15, Nat.shiftRight_eq_div_pow]]
  omega

omit [Labels] in
theorem and63 (y : Nat) : (y &&& 63) = y % 64 := by
  rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- A product's offset in its row: `16 (j % 64)`. -/
theorem colS_eval {j : Nat} (h15 : (env.regs .r15).toNat = j) :
    (colS.eval env).toNat = 16 * (j % 64) := by
  unfold colS
  simp only [Sym.eval, BinOp.apply, UnOp.apply, toNat_ext, show shiftCount .W32 (BitVec.ofNat 64 4) = 4
    by decide]
  rw [BitVec.toNat_shiftLeft, low, BitVec.toNat_setWidth, toNat_ext, BitVec.toNat_and, low,
    BitVec.toNat_setWidth, toNat_ext, low, BitVec.toNat_setWidth, h15, low, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat]
  simp only [Width.bits]
  rw [show 63 % 2 ^ 64 % 2 ^ 32 = 63 from rfl, and63, Nat.shiftLeft_eq]
  omega

end

end NativeRustcVmX64.KeccakGkr.SlotWeights

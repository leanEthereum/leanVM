module

public import NativeRustcVmX64.Top.Leanvm.Basic

/-!
# `leanvm_verify`: its checks' conditions (x86-64)

Each exit condition of the checks' blocks on the values `CheckedEntryPre` and `Aligned` give: `b0` (`L`
below `2 ^ 32`), `b1` (`n ≤ 536870910`), `b2` (the decoded area's count at least
`decodedWords L`), `b3` (the working area's at least `WORK_WORDS`), `b4`, `b5` (the decoded and the
working areas nonzero and 8-aligned), `b7` (the bytecode nonzero and 8-aligned when nonempty), and
the zero tests of `b6`, `b8`, `b9`, `b11`, `b15`.
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeVm

public section

theorem low8_toNat (x : BitVec 64) : (low .W8 x).toNat = x.toNat % 256 := by
  simp [low, BitVec.toNat_setWidth]

/-- The low three bits zero. -/
theorem and7_eq {x : BitVec 64} (h : x.toNat % 8 = 0) :
    CmpOp.apply .eq .W8 (BinOp.apply .and .W8 x (BitVec.ofNat 64 7)) (BitVec.ofNat 64 0) = true := by
  simp only [CmpOp.apply, BinOp.apply, low_ext, beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, low8_toNat, low8_toNat]
  have e : (BitVec.ofNat 64 7).toNat % 256 = 2 ^ 3 - 1 := by decide
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  simp only [low8_toNat, BitVec.toNat_ofNat]
  omega

/-- A nonzero word. -/
theorem nz_eq {x : BitVec 64} (h : x ≠ 0) :
    CmpOp.apply .eq .W64 (BinOp.apply .and .W64 x x) (BitVec.ofNat 64 0) = false := by
  simp only [CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self]
  simpa using h

theorem merge_low (x y : BitVec 64) : low .W8 (BinOp.apply .merge .W8 x y) = low .W8 y := by
  rw [BinOp.apply, low8_replaceLow]

variable [Labels] (env : Env)

theorem cond_b0 {L : Nat} (h : env.load 1 8 8 = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) :
    (SBool.cmp .eq .W64 (.bin .shr .W64 (.load 1 8 8) (.lit 32)) (.lit 0)).not.eval env = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, h, shiftCount,
    shiftMask, Bool.not_eq_false', beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have e : (low .W8 (BitVec.ofNat 64 32)).toNat &&& 63 = 32 := by decide
  rw [e, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega : L < 2 ^ 64)]
  simp only [Nat.zero_mod]
  exact Nat.div_eq_of_lt hL

theorem cond_b1 {n : Nat} (h : env.load 1 24 8 = BitVec.ofNat 64 n) (hn : n ≤ 536870910) :
    ((SBool.cmp .ult .W64 (.load 1 24 8) (.lit 536870910)).not.and
      (SBool.cmp .eq .W64 (.load 1 24 8) (.lit 536870910)).not).eval env = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h]
  have hlt : n < 2 ^ 64 := by omega
  rcases Nat.lt_or_ge n 536870910 with h1 | h1
  · have : (BitVec.ofNat 64 n).ult (BitVec.ofNat 64 536870910) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]; simp; omega
    simp [this]
  · have : n = 536870910 := by omega
    subst this
    decide

theorem cond_b2 {L : Nat} {db : BitVec 64} (h72 : env.load 1 72 8 = db)
    (hrbx : env.regs .rbx = BitVec.ofNat 64 L) (hL : L < 2 ^ 32) (hd : decodedWords L ≤ db.toNat) :
    (SBool.cmp .ult .W64 (.load 1 72 8) (.bin .add .W64 (.lit 395289)
      (.bin .or .W64 (.bin .shr .W64 (.reg .rbx) (.lit 3)) (.lit 1)))).eval env = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h72, hrbx]
  have := dw_toNat (x := BitVec.ofNat 64 L) (by rw [BitVec.toNat_ofNat]; omega) hL
  simp only [BitVec.ult, this]
  simp
  omega

theorem cond_b3 {wb : BitVec 64} (h88 : env.load 1 88 8 = wb) (hw : 61944 ≤ wb.toNat) :
    (SBool.cmp .ult .W64 (.load 1 88 8) (.lit 61944)).eval env = false := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h88, BitVec.ult]
  simp
  omega

/-- `b4`, `b5`: an area nonzero and 8-aligned. -/
theorem cond_area {o : Nat} {x : BitVec 64} (h : env.load 1 o 8 = x) (h0 : x ≠ 0)
    (h8 : x.toNat % 8 = 0) :
    (SBool.cmp .eq .W8 (.bin .or .W8 (.bin .merge .W8 (.reg .rcx)
      (.ite (SBool.cmp .eq .W8 (.bin .and .W8 (.load 1 o 8) (.lit 7)) (.lit 0)).not (.lit 1) (.lit 0)))
      (.bin .merge .W8 (.reg .rax) (.ite (SBool.cmp .eq .W64 (.bin .and .W64 (.load 1 o 8)
        (.load 1 o 8)) (.lit 0)) (.lit 1) (.lit 0)))) (.lit 0)).not.eval env = false := by
  simp only [SBool.eval, Sym.eval, h, and7_eq h8, nz_eq h0, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte]
  simp only [CmpOp.apply, BinOp.apply, low_ext, low8_replaceLow]
  decide

/-- `b7`: the bytecode nonzero and 8-aligned. -/
theorem cond_b7 {x : BitVec 64} (h : env.regs .rbp = x) (h0 : x ≠ 0) (h8 : x.toNat % 8 = 0) :
    (SBool.cmp .eq .W8 (.bin .and .W8 (.bin .merge .W8 (.reg .rdi)
      (.ite (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rbp) (.reg .rbp)) (.lit 0)).not (.lit 1)
        (.lit 0)))
      (.bin .merge .W8 (.reg .r9) (.ite (SBool.cmp .eq .W8 (.bin .and .W8 (.reg .rbp) (.lit 7))
        (.lit 0)) (.lit 1) (.lit 0)))) (.lit 0)).eval env = false := by
  simp only [SBool.eval, Sym.eval, h, and7_eq h8, nz_eq h0, Bool.not_false, ↓reduceIte]
  simp only [CmpOp.apply, BinOp.apply, low_ext, low8_replaceLow]
  decide

/-- A zero test of a word. -/
theorem cond_zero {r : Reg64} {x : BitVec 64} (h : env.regs r = x) :
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg r) (.reg r)) (.lit 0)).eval env = (x == 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, BinOp.apply, low_W64, ext_W64, BitVec.and_self, h]
  rfl

end

end NativeRustcVmX64.Top.Leanvm

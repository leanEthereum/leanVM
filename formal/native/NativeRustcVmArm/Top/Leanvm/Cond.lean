module

public import NativeRustcVmArm.Top.Leanvm.Basic
public import NativeRustcVmArm.Field.Norm

/-!
# `leanvm_verify`: its checks' conditions

`b0`'s checks pass on what `EntryPre` gives (`cond0`): the working area's count at least
`WORK_WORDS`, the decoded area's at least `decodedWords L` (rustc computes it as
`((L >> 3) | 1) + 395289`, `dw_toNat`), `n ≤ 536870910`, `L < 2^32`. The tests of the other
blocks: a word zero (`beq0`), its low three bits zero (`band7`).
-/

namespace NativeRustcVmArm.Top.Leanvm

open NativeRustcArm NativeRustcArm.Sym NativeVm

public section

theorem orOne (n : Nat) : n ||| 1 = 2 * (n / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ i =>
    rw [Nat.testBit_succ, Nat.testBit_succ (2 * (n / 2) + 1),
      show (2 * (n / 2) + 1) / 2 = n / 2 by omega, Nat.testBit_succ 1]
    simp

/-- rustc's `decoded_words(L)`. -/
theorem dw_toNat {L : Nat} (hL : L < 2 ^ 32) :
    (((BitVec.ofNat 64 L) >>> 3 ||| BitVec.ofNat 64 1) + BitVec.ofNat 64 395289).toNat =
      decodedWords L := by
  rw [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega), show 1 % 2 ^ 64 = 1 from rfl, orOne]
  unfold decodedWords phaseBase streamEnd maxStream
  simp only [LeanVM.Protocol.Compile.wireMaxPhases]
  rw [show phaseWords = 49411 from rfl]
  omega

theorem beq0 (x : UInt64) : (x.toBitVec == BitVec.ofNat 64 0) = decide (x = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  exact ⟨fun h ↦ UInt64.toBitVec_inj.mp h, fun h ↦ by rw [h]; rfl⟩

theorem band7 (x : UInt64) :
    (x.toBitVec &&& BitVec.ofNat 64 7 == BitVec.ofNat 64 0) = decide (x.toNat % 8 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_and,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, show 7 % 2 ^ 64 = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

variable [Labels]

theorem evalReg0 (env : Env) {r : XReg} {x : UInt64} (h : env.regs r = x.toBitVec) :
    (SBool.cmp .eq .W64 (.reg r) (.lit 0)).eval env = decide (x = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h]
  exact beq0 x

theorem evalLoad0 (env : Env) {o : Nat} {x : UInt64} (h : env.load 1 o 8 = x.toBitVec) :
    (SBool.cmp .eq .W64 (.load 1 o 8) (.lit 0)).eval env = decide (x = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, h]
  exact beq0 x

theorem evalAnd7 (env : Env) {r : XReg} {x : UInt64} (h : env.regs r = x.toBitVec) :
    (SBool.not (SBool.cmp .eq .W64 (.bin .and .W64 (.reg r) (.lit 7)) (.lit 0))).eval env =
      !decide (x.toNat % 8 = 0) := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, BinOp.apply, ext_W64, h]
  rw [band7]

/-- **`b0`'s checks pass.** -/
theorem cond0 (env : Env) {L n : Nat} {db wb : BitVec 64}
    (h8 : env.load 1 8 8 = BitVec.ofNat 64 L) (h24 : env.load 1 24 8 = BitVec.ofNat 64 n)
    (h72 : env.load 1 72 8 = db) (h88 : env.load 1 88 8 = wb) (hL : L < 2 ^ 32)
    (hn : n ≤ 536870910) (hd : decodedWords L ≤ db.toNat) (hw : 61944 ≤ wb.toNat) :
    (SBool.ite (SBool.or (SBool.not (SBool.ite (SBool.ite
        (SBool.not (SBool.cmp CmpOp.ult RegWidth.W64 (.load 1 88 8) (.lit 61944)))
        (SBool.not (SBool.cmp CmpOp.ult RegWidth.W64 (.load 1 72 8)
          (.bin BinOp.add RegWidth.W64 (.bin BinOp.orr RegWidth.W64
            (.un (UnOp.ubfm 3 63) RegWidth.W64 (.load 1 8 8)) (.lit 1)) (.lit 395289))))
        (SBool.lit false))
      (SBool.not (SBool.cmp CmpOp.ult RegWidth.W64 (.load 1 24 8) (.lit 536870910)))
      (SBool.lit true)))
      (SBool.ite (SBool.ite
        (SBool.not (SBool.cmp CmpOp.ult RegWidth.W64 (.load 1 88 8) (.lit 61944)))
        (SBool.not (SBool.cmp CmpOp.ult RegWidth.W64 (.load 1 72 8)
          (.bin BinOp.add RegWidth.W64 (.bin BinOp.orr RegWidth.W64
            (.un (UnOp.ubfm 3 63) RegWidth.W64 (.load 1 8 8)) (.lit 1)) (.lit 395289))))
        (SBool.lit false))
        (SBool.cmp CmpOp.eq RegWidth.W64 (.load 1 24 8) (.lit 536870910))
        (SBool.lit false)))
      (SBool.cmp CmpOp.eq RegWidth.W64
        (.bin BinOp.and RegWidth.W64 (.load 1 8 8) (.lit 18446744069414584320)) (.lit 0))
      (SBool.lit false)).eval env = true := by
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, BinOp.apply, ext_W64, h8, h24, h72, h88,
    NativeRustcVmArm.Field.ubfm_lsr _ _ (show 3 < 64 by decide)]
  have e1 : wb.ult (BitVec.ofNat 64 61944) = false := by
    simp [BitVec.ult]; omega
  have e2 : db.ult (((BitVec.ofNat 64 L) >>> 3 ||| BitVec.ofNat 64 1) +
      BitVec.ofNat 64 395289) = false := by
    simp only [BitVec.ult, dw_toNat hL]; simp; omega
  have e3 : ((BitVec.ofNat 64 n).ult (BitVec.ofNat 64 536870910) ||
      (BitVec.ofNat 64 n == BitVec.ofNat 64 536870910)) = true := by
    have : n < 2 ^ 64 := by omega
    rw [ofNat_beq this (by decide)]
    simp [BitVec.ult]; omega
  have e4 : (BitVec.ofNat 64 L &&& BitVec.ofNat 64 18446744069414584320 ==
      BitVec.ofNat 64 0) = true := by
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show L < 2 ^ 64 by omega)]
    have h1 : L &&& 18446744069414584320 % 2 ^ 64 ≤ L := Nat.and_le_left
    have h2 : (L &&& 18446744069414584320 % 2 ^ 64) % 2 ^ 32 =
        (L % 2 ^ 32) &&& (18446744069414584320 % 2 ^ 64 % 2 ^ 32) := Nat.and_mod_two_pow
    rw [Nat.mod_eq_of_lt (show L &&& 18446744069414584320 % 2 ^ 64 < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt hL, show 18446744069414584320 % 2 ^ 64 % 2 ^ 32 = 0 from rfl,
      Nat.and_zero] at h2
    rw [h2]; rfl
  simp [e1, e2, e4]
  simpa using e3

end

end NativeRustcVmArm.Top.Leanvm

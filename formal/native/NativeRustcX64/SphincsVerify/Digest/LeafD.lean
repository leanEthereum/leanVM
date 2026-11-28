module

public import NativeRustcX64.SphincsVerify.Digest.LoopExec
public import NativeRustcX64.SphincsVerify.Digest.LeafLemmas
import Mathlib.Tactic.IntervalCases

/-!
# The bit loop's leaf, turns `18 .. 23` (x86-64)

Turn `c` of `b55` stores leaf `c`: the ten bits `10 c .. 10 c + 9` of `h_msg` (the bytes `z k`),
most significant first (`leaf_<c>`, `leaf_D`). Each turn by itself: the executor's value
in bit-level normal form, the loads resolved, the `add`s of disjoint bits as `or`s, the bit
`i` of both sides as a boolean formula in `i`, then each `i < 64`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym

public section

set_option linter.unusedSimpArgs false

/-- Turn `18`'s leaf. -/
theorem leaf_18 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 18))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 18 + j) / 8)) >>> (7 - (10 * 18 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b46, List.headD_cons]
  sym_simp
  rw [hx]
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [shiftCount, shiftMask, low, ext, Width.bits, BitVec.replaceLow, BitVec.setWidth_eq,
    add_self', BitVec.drop, Nat.zero_add, BitVec.zeroExtend_eq_setWidth]
  simp (disch := decide) only [hb, BitVec.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft,
    Nat.reduceAnd, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, extract_setWidth8, extract_app, setWidth8_app,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  simp only [mul2, mul4, add_bit_shl1, add_lea4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ite_one_zero, zero_app]
  simp [BitVec.getElem_append, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp

/-- Turn `19`'s leaf. -/
theorem leaf_19 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 19))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 19 + j) / 8)) >>> (7 - (10 * 19 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b46, List.headD_cons]
  sym_simp
  rw [hx]
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [shiftCount, shiftMask, low, ext, Width.bits, BitVec.replaceLow, BitVec.setWidth_eq,
    add_self', BitVec.drop, Nat.zero_add, BitVec.zeroExtend_eq_setWidth]
  simp (disch := decide) only [hb, BitVec.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft,
    Nat.reduceAnd, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, extract_setWidth8, extract_app, setWidth8_app,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  simp only [mul2, mul4, add_bit_shl1, add_lea4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ite_one_zero, zero_app]
  simp [BitVec.getElem_append, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp

/-- Turn `20`'s leaf. -/
theorem leaf_20 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 20))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 20 + j) / 8)) >>> (7 - (10 * 20 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b46, List.headD_cons]
  sym_simp
  rw [hx]
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [shiftCount, shiftMask, low, ext, Width.bits, BitVec.replaceLow, BitVec.setWidth_eq,
    add_self', BitVec.drop, Nat.zero_add, BitVec.zeroExtend_eq_setWidth]
  simp (disch := decide) only [hb, BitVec.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft,
    Nat.reduceAnd, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, extract_setWidth8, extract_app, setWidth8_app,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  simp only [mul2, mul4, add_bit_shl1, add_lea4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ite_one_zero, zero_app]
  simp [BitVec.getElem_append, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp

/-- Turn `21`'s leaf. -/
theorem leaf_21 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 21))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 21 + j) / 8)) >>> (7 - (10 * 21 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b46, List.headD_cons]
  sym_simp
  rw [hx]
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [shiftCount, shiftMask, low, ext, Width.bits, BitVec.replaceLow, BitVec.setWidth_eq,
    add_self', BitVec.drop, Nat.zero_add, BitVec.zeroExtend_eq_setWidth]
  simp (disch := decide) only [hb, BitVec.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft,
    Nat.reduceAnd, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, extract_setWidth8, extract_app, setWidth8_app,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  simp only [mul2, mul4, add_bit_shl1, add_lea4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ite_one_zero, zero_app]
  simp [BitVec.getElem_append, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp

/-- Turn `22`'s leaf. -/
theorem leaf_22 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 22))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 22 + j) / 8)) >>> (7 - (10 * 22 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b46, List.headD_cons]
  sym_simp
  rw [hx]
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [shiftCount, shiftMask, low, ext, Width.bits, BitVec.replaceLow, BitVec.setWidth_eq,
    add_self', BitVec.drop, Nat.zero_add, BitVec.zeroExtend_eq_setWidth]
  simp (disch := decide) only [hb, BitVec.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft,
    Nat.reduceAnd, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, extract_setWidth8, extract_app, setWidth8_app,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  simp only [mul2, mul4, add_bit_shl1, add_lea4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ite_one_zero, zero_app]
  simp [BitVec.getElem_append, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp

/-- Turn `23`'s leaf. -/
theorem leaf_23 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 23))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 23 + j) / 8)) >>> (7 - (10 * 23 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b46, List.headD_cons]
  sym_simp
  rw [hx]
  simp only [bitsVal, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp only [shiftCount, shiftMask, low, ext, Width.bits, BitVec.replaceLow, BitVec.setWidth_eq,
    add_self', BitVec.drop, Nat.zero_add, BitVec.zeroExtend_eq_setWidth]
  simp (disch := decide) only [hb, BitVec.reduceAdd, BitVec.reduceSetWidth, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceAnd, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.reduceExtractLsb', BitVec.reduceHShiftLeft,
    Nat.reduceAnd, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMod, extract_setWidth8, extract_app, setWidth8_app,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_setWidth, BitVec.setWidth_eq]
  simp only [mul2, mul4, add_bit_shl1, add_lea4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ite_one_zero, zero_app]
  simp [BitVec.getElem_append, BitVec.getMsbD_eq_getLsbD]
  interval_cases i <;> simp

/-- **Turns `18 .. 23`'s leaf.** -/
theorem leaf_D [Labels] (env : Env) (z : Nat → BitVec 8) {c : Nat} (hc1 : 18 ≤ c)
    (hc2 : c < 24) (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * c + j) / 8)) >>> (7 - (10 * c + j) % 8)) &&& 1 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 18 ∨ c = 19 ∨ c = 20 ∨ c = 21 ∨ c = 22 ∨ c = 23 := by
    omega
  · exact leaf_18 env z hx hb
  · exact leaf_19 env z hx hb
  · exact leaf_20 env z hx hb
  · exact leaf_21 env z hx hb
  · exact leaf_22 env z hx hb
  · exact leaf_23 env z hx hb

end

end NativeRustcX64.SphincsVerifyProof.Digest

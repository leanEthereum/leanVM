module

public import NativeRustcX64.SphincsVerify.Digest.LoopExec
public import NativeRustcX64.SphincsVerify.Digest.LeafLemmas
import Mathlib.Tactic.IntervalCases

/-!
# The bit loop's leaf, turns `6 .. 11` (x86-64)

Turn `c` of `b55` stores leaf `c`: the ten bits `10 c .. 10 c + 9` of `h_msg` (the bytes `z k`),
most significant first (`leaf_<c>`, `leaf_B`). Each turn by itself: the executor's value
in bit-level normal form, the loads resolved, the `add`s of disjoint bits as `or`s, the bit
`i` of both sides as a boolean formula in `i`, then each `i < 64`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym

public section

set_option linter.unusedSimpArgs false

/-- Turn `6`'s leaf. -/
theorem leaf_6 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 6))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 6 + j) / 8)) >>> (7 - (10 * 6 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b55, List.headD_cons]
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

/-- Turn `7`'s leaf. -/
theorem leaf_7 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 7))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 7 + j) / 8)) >>> (7 - (10 * 7 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b55, List.headD_cons]
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

/-- Turn `8`'s leaf. -/
theorem leaf_8 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 8))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 8 + j) / 8)) >>> (7 - (10 * 8 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b55, List.headD_cons]
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

/-- Turn `9`'s leaf. -/
theorem leaf_9 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 9))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 9 + j) / 8)) >>> (7 - (10 * 9 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b55, List.headD_cons]
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

/-- Turn `10`'s leaf. -/
theorem leaf_10 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 10))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 10 + j) / 8)) >>> (7 - (10 * 10 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b55, List.headD_cons]
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

/-- Turn `11`'s leaf. -/
theorem leaf_11 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 11))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 11 + j) / 8)) >>> (7 - (10 * 11 + j) % 8)) &&& 1 := by
  simp only [leafSym, run_b55, List.headD_cons]
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

/-- **Turns `6 .. 11`'s leaf.** -/
theorem leaf_B [Labels] (env : Env) (z : Nat → BitVec 8) {c : Nat} (hc1 : 6 ≤ c)
    (hc2 : c < 12) (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * c + j) / 8)) >>> (7 - (10 * c + j) % 8)) &&& 1 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 6 ∨ c = 7 ∨ c = 8 ∨ c = 9 ∨ c = 10 ∨ c = 11 := by
    omega
  · exact leaf_6 env z hx hb
  · exact leaf_7 env z hx hb
  · exact leaf_8 env z hx hb
  · exact leaf_9 env z hx hb
  · exact leaf_10 env z hx hb
  · exact leaf_11 env z hx hb

end

end NativeRustcX64.SphincsVerifyProof.Digest

module

public import NativeRustcX64.SphincsVerify.Digest.LoopExec
public import NativeRustcX64.SphincsVerify.Digest.LeafLemmas
import Mathlib.Tactic.IntervalCases

/-!
# The bit loop's leaf, turns `12 .. 17` (x86-64)

Turn `c` of `b55` stores leaf `c`: the ten bits `10 c .. 10 c + 9` of `h_msg` (the bytes `z k`),
most significant first (`leaf_<c>`, `leaf_C`). Each turn by itself: the executor's value
in bit-level normal form, the loads resolved, the `add`s of disjoint bits as `or`s, the bit
`i` of both sides as a boolean formula in `i`, then each `i < 64`.
-/

namespace NativeRustcX64.SphincsVerifyProof.Digest

open NativeRustcX64.Sym

public section

set_option linter.unusedSimpArgs false

/-- Turn `12`'s leaf. -/
theorem leaf_12 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 12))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 12 + j) / 8)) >>> (7 - (10 * 12 + j) % 8)) &&& 1 := by
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

/-- Turn `13`'s leaf. -/
theorem leaf_13 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 13))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 13 + j) / 8)) >>> (7 - (10 * 13 + j) % 8)) &&& 1 := by
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

/-- Turn `14`'s leaf. -/
theorem leaf_14 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 14))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 14 + j) / 8)) >>> (7 - (10 * 14 + j) % 8)) &&& 1 := by
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

/-- Turn `15`'s leaf. -/
theorem leaf_15 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 15))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 15 + j) / 8)) >>> (7 - (10 * 15 + j) % 8)) &&& 1 := by
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

/-- Turn `16`'s leaf. -/
theorem leaf_16 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 16))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 16 + j) / 8)) >>> (7 - (10 * 16 + j) % 8)) &&& 1 := by
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

/-- Turn `17`'s leaf. -/
theorem leaf_17 [Labels] (env : Env) (z : Nat → BitVec 8)
    (hx : env.regs .r12 = BitVec.ofNat 64 (10 * 17))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * 17 + j) / 8)) >>> (7 - (10 * 17 + j) % 8)) &&& 1 := by
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

/-- **Turns `12 .. 17`'s leaf.** -/
theorem leaf_C [Labels] (env : Env) (z : Nat → BitVec 8) {c : Nat} (hc1 : 12 ≤ c)
    (hc2 : c < 18) (hx : env.regs .r12 = BitVec.ofNat 64 (10 * c))
    (hb : ∀ k < 30, env.load 0 k 1 = BitVec.setWidth 64 (z k)) :
    leafSym.eval env =
      bitsVal fun j ↦ (BitVec.setWidth 64 (z ((10 * c + j) / 8)) >>> (7 - (10 * c + j) % 8)) &&& 1 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl : c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 ∨ c = 16 ∨ c = 17 := by
    omega
  · exact leaf_12 env z hx hb
  · exact leaf_13 env z hx hb
  · exact leaf_14 env z hx hb
  · exact leaf_15 env z hx hb
  · exact leaf_16 env z hx hb
  · exact leaf_17 env z hx hb

end

end NativeRustcX64.SphincsVerifyProof.Digest

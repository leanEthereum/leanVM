module

public import NativeRustcVm.Field.ClmulLow
public import NativeVm.Model.Field

/-!
# The product in `K`

`clmul a b` is the carry-less product in two words: the low word by `coeff_clmulLow`, the high
word the low word of the bit-reversed operands' product reversed back, the reversal being
`Polynomial.reflect 63` (`toPoly_reverse`, `coeff_clmul_snd`), so that the pair is CompPoly's
`carryLessMul` (`wordsToBitVec_clmul`). `reduce` is `BF64.reduceWords` (`reduce_eq`), so `kmul` is
`BF64.mul`, the model's `kmul` (`kmul_eq`).
-/

namespace NativeRustcVm.Field

open Polynomial BinaryField

public section

theorem natDegree_toPoly_le (v : BitVec 64) : (toPoly v).natDegree ≤ 63 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_toPoly, BitVec.getLsbD_of_ge v n (by omega)]
  rfl

/-- Bit reversal is reflection. -/
theorem toPoly_reverse (v : BitVec 64) : toPoly v.reverse = reflect 63 (toPoly v) := by
  ext n
  rw [coeff_reflect, coeff_toPoly, coeff_toPoly, BitVec.getLsbD_reverse, BitVec.getMsbD]
  by_cases h : n ≤ 63
  · rw [revAt_le h, show 64 - 1 - n = 63 - n by omega]
    simp [show n < 64 by omega]
  · have hr : revAt 63 n = n := revAt_eq_self_of_lt (by omega)
    rw [hr, BitVec.getLsbD_of_ge v n (by omega)]
    simp [show ¬ n < 64 by omega]

/-- **The high word** of `clmul` is the high half of the carry-less product. -/
theorem coeff_clmul_snd (a b : BitVec 64) (j : ℕ) :
    (toPoly (clmul a b).2).coeff j = (toPoly a * toPoly b).coeff (64 + j) := by
  have ha := natDegree_toPoly_le a
  have hb := natDegree_toPoly_le b
  rw [coeff_toPoly]
  simp only [clmul]
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse, BitVec.getMsbD]
  by_cases hj : j ≤ 62
  · simp only [show 1 + j < 64 by omega, decide_true, Bool.true_and,
      show 64 - 1 - (1 + j) = 62 - j by omega]
    rw [coeff_clmulLow _ _ (by omega), toPoly_reverse, toPoly_reverse, ← reflect_mul _ _ ha hb,
      coeff_reflect, revAt_le (by omega)]
    congr 1
    omega
  · have : ¬ 1 + j < 64 := by omega
    simp only [this, decide_false, Bool.false_and]
    rw [coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt (by omega))]
    rfl

/-- **`clmul` is the carry-less product**, `hi·x^64 + lo`. -/
theorem toPoly_clmul (a b : BitVec 64) :
    toPoly (clmul a b).2 * X ^ 64 + toPoly (clmul a b).1 = toPoly a * toPoly b := by
  ext k
  rw [coeff_add, coeff_mul_X_pow', coeff_toPoly (clmul a b).1]
  by_cases hk : k < 64
  · rw [ite_eq_right (by omega), zero_add]
    exact coeff_clmulLow a b hk
  · rw [ite_eq_left (by omega), coeff_clmul_snd, BitVec.getLsbD_of_ge _ k (by omega), zb_false,
      add_zero, show 64 + (k - 64) = k by omega]

/-- The polynomial of a pair of words, `hi·x^64 + lo`. -/
theorem toPoly_wordsToBitVec (hi lo : UInt64) :
    toPoly (BF64.wordsToBitVec (hi, lo)) = toPoly hi.toBitVec * X ^ 64 + toPoly lo.toBitVec := by
  have hh : BF64.highHalf (BF64.wordsToBitVec (hi, lo)) = hi.toBitVec := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BF64.highHalf, BF64.wordsToBitVec, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, hk, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hl : BF64.lowHalf (BF64.wordsToBitVec (hi, lo)) = lo.toBitVec := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BF64.lowHalf, BF64.wordsToBitVec, BitVec.getLsbD_setWidth, hk, decide_true,
      Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_left hk]
  rw [BF64.toPoly_halves, hh, hl]

theorem wordsToBitVec_clmul (a b : BitVec 64) :
    BF64.wordsToBitVec (UInt64.ofBitVec (clmul a b).2, UInt64.ofBitVec (clmul a b).1) =
      carryLessMul (w := 128) a b := by
  apply BF64.bitVec_toPoly_injective
  rw [toPoly_carryLessMul _ _ (by norm_num), ← toPoly_clmul, toPoly_wordsToBitVec]

/-- **`reduce` is `BF64.reduceWords`.** -/
theorem reduce_eq (lo hi : BitVec 64) :
    reduce lo hi = (BF64.reduceWords (UInt64.ofBitVec hi) (UInt64.ofBitVec lo)).toBitVec := by
  simp only [reduce, BF64.reduceWords, BF64.tailLow, BF64.tailHigh, UInt64.toBitVec_xor,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  simp [BitVec.shiftLeft_xor_distrib]
  ac_rfl

/-- **`reduce` gives the element the pair stands for** in `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`. -/
theorem toQuot_reduce (lo hi : BitVec 64) :
    BF64.toQuot (BF64.ofBitVec (reduce lo hi)) =
      AdjoinRoot.mk BF64.basePoly (toPoly hi * X ^ 64 + toPoly lo) := by
  rw [reduce_eq, BF64.toQuot, BF64.toPolyBF64, BF64.toBitVec_ofBitVec, BF64.reduceWords_eq,
    BF64.toPoly_reduce, toPoly_wordsToBitVec, UInt64.toBitVec_ofBitVec, UInt64.toBitVec_ofBitVec,
    AdjoinRoot.mk_eq_mk]
  refine ⟨-((toPoly hi * X ^ 64 + toPoly lo) / BF64.basePoly), ?_⟩
  rw [EuclideanDomain.mod_eq_sub_mul_div]
  ring

/-- The product in the quotient. -/
theorem toQuot_kmul (a b : BitVec 64) :
    BF64.toQuot (BF64.ofBitVec (kmul a b)) =
      AdjoinRoot.mk BF64.basePoly (toPoly a) * AdjoinRoot.mk BF64.basePoly (toPoly b) := by
  rw [kmul, toQuot_reduce, toPoly_clmul, map_mul]

/-- `kmul` is `BF64.mul`. -/
theorem kmul_eq_mul (a b : BitVec 64) :
    kmul a b = (BF64.mul (BF64.ofBitVec a) (BF64.ofBitVec b)).toBitVec := by
  rw [kmul, reduce_eq, BF64.reduceWords_eq, wordsToBitVec_clmul]
  rfl

/-- **`kmul` is the model's.** -/
theorem kmul_eq (a b : BitVec 64) :
    kmul a b = (NativeVm.Model.kmul (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec := by
  rw [kmul_eq_mul, BF64.mul_eq_mulShift]
  rfl

/-- `kmul` on the model's lanes. -/
theorem kmul_toBitVec (a b : UInt64) :
    kmul a.toBitVec b.toBitVec = (NativeVm.Model.kmul a b).toBitVec :=
  kmul_eq a.toBitVec b.toBitVec

end

end NativeRustcVm.Field

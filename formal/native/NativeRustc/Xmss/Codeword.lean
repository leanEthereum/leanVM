module

public import NativeRustc.Xmss.Model
public import NativeRustc.Digest

/-!
# `codeword` is the statement's codeword test

`is_codeword`'s count of the low bits plus twice the high bits of the digits is their sum
(`countOnes_digitSum`), so on the bytes of a digest `codeword` is `LeanXmss.Codeword.decode`'s test
(`isCodeword_iff`, `codeword_eq`), and its digits are `digestDigits` (`getD_digits`).
-/

@[expose] public section

namespace NativeRustc.Xmss

open HashSig LeanXmss

/-- `LOW`'s bits: the even ones. -/
theorem testBit_low : ∀ j < 128, low.testBit j = decide (j % 2 = 0) := by decide +kernel

/-- `!LOW`'s bits: the odd ones. -/
theorem testBit_notLow : ∀ j < 128, notLow.testBit j = decide (j % 2 = 1) := by decide +kernel

/-- A sum over `2 n` terms in pairs. -/
theorem sum_range_pairs (f : Nat → Nat) : ∀ n,
    ∑ j ∈ Finset.range (2 * n), f j = ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1))
  | 0 => rfl
  | n + 1 => by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      sum_range_pairs f n, Finset.sum_range_succ, Nat.add_assoc]

/-- A digit is its low bit plus twice its high bit. -/
theorem digit_bits (d i : Nat) :
    (d.testBit (2 * i)).toNat + 2 * (d.testBit (2 * i + 1)).toNat = d / 4 ^ i % 4 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, pow_succ,
    ← Nat.div_div_eq_div_mul, pow_mul]
  norm_num
  generalize d / 4 ^ i = y
  by_cases h1 : y % 2 = 1 <;> by_cases h2 : y / 2 % 2 = 1 <;> simp [h1, h2] <;> omega

/-- **`is_codeword`'s count is the sum of the 64 digits.** -/
theorem countOnes_digitSum (d : Nat) :
    countOnes (d &&& low) + 2 * countOnes (d &&& notLow) =
      ∑ i ∈ Finset.range 64, d / 4 ^ i % 4 := by
  have h : ∀ j ∈ Finset.range 128, ((d &&& low).testBit j).toNat +
      2 * ((d &&& notLow).testBit j).toNat =
      (d.testBit j && decide (j % 2 = 0)).toNat + 2 * (d.testBit j && decide (j % 2 = 1)).toNat :=
    fun j hj ↦ by
      rw [Finset.mem_range] at hj
      rw [Nat.testBit_and, Nat.testBit_and, testBit_low j hj, testBit_notLow j hj]
  rw [countOnes, countOnes, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl h,
    show 128 = 2 * 64 from rfl, sum_range_pairs]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← digit_bits]
  have h0 : 2 * i % 2 = 0 := by omega
  have h1 : (2 * i + 1) % 2 = 1 := by omega
  simp [h0, h1]

/-- Past `2^116`, the digits from the 59th are zero. -/
theorem digitSum_64 {d : Nat} (hd : d < 2 ^ 116) :
    ∑ i ∈ Finset.range 64, d / 4 ^ i % 4 = ∑ i ∈ Finset.range 58, d / 4 ^ i % 4 := by
  have hz : ∀ k, 58 ≤ k → d / 4 ^ k % 4 = 0 := fun k hk ↦ by
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hd (by
      rw [show (4 : Nat) ^ k = 2 ^ (2 * k) by rw [pow_mul]; rfl]
      exact Nat.pow_le_pow_right (by omega) (by omega)))]
  simp only [show 64 = 58 + 1 + 1 + 1 + 1 + 1 + 1 from rfl, Finset.sum_range_succ,
    hz 58 (by omega), hz 59 (by omega), hz 60 (by omega), hz 61 (by omega), hz 62 (by omega),
    hz 63 (by omega), Nat.add_zero]

/-- A digit of `digestDigits` as a number. -/
theorem digestDigits_val {n : Nat} (D : Digest) (i : Fin n) :
    (digestDigits D i).val = D.toNat / 4 ^ i.val % 4 := by
  rw [digestDigits, BitVec.val_toFin, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow,
    winternitzBits, pow_mul]
  rfl

/-- **`is_codeword` is `Codeword.Valid`.** -/
theorem isCodeword_iff (D : Digest) : isCodeword D.toNat = true ↔ Codeword.Valid D := by
  have hsum : Codeword.sum (digestDigits D) = ∑ i ∈ Finset.range 58, D.toNat / 4 ^ i % 4 := by
    rw [Codeword.sum]
    simp only [digestDigits_val]
    exact Fin.sum_univ_eq_sum_range (fun i ↦ D.toNat / 4 ^ i % 4) 58
  unfold Codeword.Valid
  rw [hsum, isCodeword, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, Nat.shiftRight_eq_div_pow,
    show winternitzBits * chainCount = 116 from rfl, targetSum]
  constructor
  · rintro ⟨h1, h2⟩
    have hd : D.toNat < 2 ^ 116 := by
      rw [Nat.div_eq_zero_iff] at h1; omega
    rw [countOnes_digitSum, digitSum_64 hd] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hd : D.toNat < 2 ^ 116 := by
      rw [Nat.div_eq_zero_iff] at h1; omega
    rw [countOnes_digitSum, digitSum_64 hd]
    exact ⟨h1, h2⟩

/-- **`codeword` of a digest's bytes is `Codeword.decode`'s test**, with the digits of
`digits`. -/
theorem codeword_eq (D : Digest) :
    codeword (le16 D) = if Codeword.Valid D then some (digits D.toNat) else none := by
  rw [codeword, leNat_le16]
  by_cases h : Codeword.Valid D
  · rw [ite_eq_left ((isCodeword_iff D).mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt (isCodeword_iff D).mp h), ite_eq_right h]

/-- **Digit `i` of `digits`** is the statement's. -/
theorem getD_digits (D : Digest) {i : Nat} (hi : i < 58) :
    ((digits D.toNat).getD i 0).toNat = (digestDigits (n := chainCount) D ⟨i, hi⟩).val := by
  rw [digestDigits_val, digits, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    show (3 : Nat) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, pow_mul]
  norm_num
  omega

end NativeRustc.Xmss

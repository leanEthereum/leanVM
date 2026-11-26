/-
  Rv64mc.Model.Extra.GrindingBits

  The compiled `grinding_bits` computes `u128::leading_zeros` in software: it smears a word's highest set bit
  right (`smear`: `y | y >> 1`, then shifts by 2, 4, 8, 16, 32), complements it, and counts the ones left with a
  SWAR popcount (`popc`). `smear y` is `2^L - 1` for `L` the word's bit length (`smear_eq`), and the popcount of its
  complement is `64 - L` (`popc_eq`, by the kernel over the 65 lengths). `fin` is the saturating `125 - c` the
  code ends with.
-/

import Rv64mc.Model.Transcript

namespace Rv64mc.Model

open LeanVM.Protocol.Verifier

/-- The smear of `y`'s highest set bit to every lower bit, as the code computes it. -/
def smear (y : BitVec 64) : BitVec 64 :=
  let s1 := y ||| y >>> 1
  let s2 := s1 ||| s1 >>> 2
  let s4 := s2 ||| s2 >>> 4
  let s8 := s4 ||| s4 >>> 8
  let s16 := s8 ||| s8 >>> 16
  s16 ||| s16 >>> 32

/-- The SWAR popcount, as the code computes it. -/
def popc (z : BitVec 64) : BitVec 64 :=
  let a := z - (z >>> 1 &&& 0x5555555555555555#64)
  let b := (a &&& 0x3333333333333333#64) + (a >>> 2 &&& 0x3333333333333333#64)
  (((b + b >>> 4) &&& 0x0F0F0F0F0F0F0F0F#64) * 0x0101010101010101#64) >>> 56

/-- The bits of a smear step: bit `i` of the result is set where some bit of `y` in `[i, i + 2k)` is. -/
private theorem smear_step {y z : BitVec 64} {k : Nat}
    (h : ∀ i, z.getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + k ∧ y.getLsbD j = true) :
    ∀ i, (z ||| z >>> k).getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + 2 * k ∧ y.getLsbD j = true := by
  intro i
  rw [BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, Bool.or_eq_true, h i, h (k + i)]
  constructor
  · rintro (⟨j, h1, h2, h3⟩ | ⟨j, h1, h2, h3⟩)
    · exact ⟨j, h1, by omega, h3⟩
    · exact ⟨j, by omega, by omega, h3⟩
  · rintro ⟨j, h1, h2, h3⟩
    by_cases hj : j < i + k
    · exact Or.inl ⟨j, h1, hj, h3⟩
    · exact Or.inr ⟨j, by omega, by omega, h3⟩

/-- Some bit of `n` at or above `i` is set exactly where `2^i ≤ n`. -/
private theorem exists_bit_iff {n i : Nat} : (∃ j, i ≤ j ∧ n.testBit j) ↔ 2 ^ i ≤ n := by
  constructor
  · rintro ⟨j, hij, hj⟩
    exact Nat.le_trans (Nat.pow_le_pow_right (by norm_num) hij) (Nat.ge_two_pow_of_testBit hj)
  · intro h
    have hne : n >>> i ≠ 0 := by
      rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_pos h (Nat.two_pow_pos i)).ne'
    obtain ⟨k, hk⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_shiftRight] at hk
    exact ⟨i + k, by omega, hk⟩

theorem bitLength_le_iff {n L : Nat} : bitLength n ≤ L ↔ n < 2 ^ L := by
  unfold bitLength
  split
  · subst_vars; simp
  · rename_i hn
    rw [← Nat.log2_lt hn]; omega

theorem lt_bitLength_iff {n i : Nat} : i < bitLength n ↔ 2 ^ i ≤ n := by
  rw [← Nat.not_le, bitLength_le_iff, Nat.not_lt]

theorem bitLength_le_64 (y : BitVec 64) : bitLength y.toNat ≤ 64 := bitLength_le_iff.2 y.isLt

/-- **The smear is `2^L - 1`**, `L` the word's bit length. -/
theorem smear_eq (y : BitVec 64) : smear y = BitVec.ofNat 64 (2 ^ bitLength y.toNat - 1) := by
  have h1 : ∀ i, y.getLsbD i = true ↔ ∃ j, i ≤ j ∧ j < i + 1 ∧ y.getLsbD j = true := fun i =>
    ⟨fun h => ⟨i, by omega, by omega, h⟩, fun ⟨j, h1, h2, h3⟩ => by rw [show i = j by omega]; exact h3⟩
  have h64 := smear_step (smear_step (smear_step (smear_step (smear_step (smear_step h1)))))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := h64 i
  simp only [smear] at e ⊢
  apply Bool.eq_iff_iff.2
  rw [e, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  simp only [hi, decide_true, Bool.true_and, decide_eq_true_eq, lt_bitLength_iff, ← exists_bit_iff,
    BitVec.getLsbD]
  constructor
  · rintro ⟨j, h1, -, h3⟩; exact ⟨j, h1, h3⟩
  · rintro ⟨j, h1, h3⟩
    have : j < 64 := by
      by_contra hc
      rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num)
        (by omega)))] at h3
      exact absurd h3 (by simp)
    exact ⟨j, h1, by omega, h3⟩

/-- The popcount of the complement of `2^L - 1`, for each of the 65 lengths. -/
theorem popc_eq {L : Nat} (hL : L ≤ 64) :
    popc (BitVec.ofNat 64 (2 ^ L - 1) ^^^ 18446744073709551615#64) = BitVec.ofNat 64 (64 - L) := by
  interval_cases L <;> decide +kernel

end Rv64mc.Model

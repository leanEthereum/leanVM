import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity

theorem positivePart_shift_even_le (score shift : ℝ) (power : Nat) (heven : Even power) :
    max (score + shift) 0 ^ power ≤ (max score 0 + shift) ^ power := by
  by_cases hnonneg : 0 ≤ score + shift
  · rw [max_eq_left hnonneg]
    exact pow_le_pow_left₀ hnonneg (add_le_add (le_max_left score 0) le_rfl) power
  · rw [max_eq_right (le_of_not_ge hnonneg)]
    by_cases hpower : power = 0
    · simp [hpower]
    · rw [zero_pow hpower]
      exact heven.pow_nonneg _

theorem bernoulliExcess_secondMoment_le (score probability : ℝ)
    (hprob : 0 ≤ probability) (hprob_one : probability ≤ 1) :
    probability * max (score + (1 - probability)) 0 ^ 2 +
        (1 - probability) * max (score + (-probability)) 0 ^ 2 ≤
      max score 0 ^ 2 + probability := by
  let d := max score 0
  have hmiss : 0 ≤ 1 - probability := sub_nonneg.mpr hprob_one
  calc
    _ ≤ probability * (d + (1 - probability)) ^ 2 +
        (1 - probability) * (d + (-probability)) ^ 2 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (1 - probability) 2 (by decide)) hprob)
        (mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (-probability) 2 (by decide)) hmiss)
    _ = d ^ 2 + probability * (1 - probability) := by ring
    _ ≤ _ := by dsimp only [d]; nlinarith [sq_nonneg probability]

end SphincsSecurity

import SphincsSecurity.Proof.Base.Prelude
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def fourthMomentBudget (q : Nat) (second fourth : ENNReal) : ENNReal :=
  fourth + 6138 * q * second + 6279174 * q.choose 2 + (2 : ENNReal) ^ 30 * q

theorem fourth_le_fourthMomentBudget (q : Nat) (second fourth : ENNReal) :
    fourth ≤ fourthMomentBudget q second fourth := by
  exact ((le_self_add.trans le_self_add).trans le_self_add)

theorem fourthMomentBudget_zero_le (q : Nat) (hq : q ≤ 2 ^ 127) :
    fourthMomentBudget q 0 0 / (2 : ENNReal) ^ 372 ≤ (q : ENNReal) / 2 ^ 223 := by
  have hchoose : 2 * q.choose 2 + q = q * q := by
    clear hq
    induction q with
    | zero => simp
    | succ q ih =>
        have hstep : (q + 1).choose 2 = q + q.choose 2 := by
          simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' q 1
        rw [hstep]
        nlinarith
  have hchooseReal : 2 * (q.choose 2 : ℝ) + q = (q : ℝ) * q := by exact_mod_cast hchoose
  have hqReal : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have hqNonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hproduct : (q : ℝ) * q ≤ q * 2 ^ 127 := mul_le_mul_of_nonneg_left hqReal hqNonneg
  apply (ENNReal.toReal_le_toReal (by simp [fourthMomentBudget]; finiteness) (by finiteness)).mp
  simp only [fourthMomentBudget, mul_zero, add_zero, zero_add]
  rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_div]
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, pow_succ] at hproduct ⊢
  nlinarith

end SphincsSecurity

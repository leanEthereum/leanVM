import SphincsSecurity.Proof.Deterministic.ReferenceDistribution
import SphincsSecurity.Proof.Seeded.Security

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem scheme_has_127_bits_of_classical_security :
    HasClassicalSecurityBits scheme 127 := by
  intro q hq adversary hbound
  by_cases hsmall : q < 2 ^ 127
  · have htable := tableBudget_from_deterministic adversary q (hsmall.trans (by norm_num)) hbound
    have hindependent := referenceBudget_from_table adversary (q - 1) (tableBudget_memo adversary (q - 1) htable)
    have hcomparison := forgeAdvantage_deterministic_le_reference adversary (q - 1) htable
    by_cases hone : q = 1
    · subst q
      have hbudget : HasHashQueryBound Concrete.scheme (memoAdversary adversary) 1 := by
        rw [hasHashQueryBound_iff] at hindependent ⊢
        exact hindependent.mono (by decide)
      have hsecurity := Concrete.security127 1 (by decide) (memoAdversary adversary) hbudget
      simp only [Nat.sub_self, Nat.cast_zero, ENNReal.zero_div, add_zero] at hcomparison
      exact hcomparison.trans hsecurity
    · have hsecurity := Concrete.security127 (q - 1) (by omega) (memoAdversary adversary) hindependent
      exact hcomparison.trans ((add_le_add hsecurity le_rfl).trans (seed_loss_absorbed q hq hsmall))
  · have hlarge : 2 ^ 127 ≤ q := Nat.le_of_not_gt hsmall
    calc
      forgeAdvantage scheme adversary ≤ 1 := probOutput_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl

end SphincsSecurity.Seeded

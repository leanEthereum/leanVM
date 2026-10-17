import XmssSecurity.Proof.Bridge.Model
import XmssSecurity.Proof.Interface

/-!
# leanXMSS has 127 bits of security

The real experiment is at most the model's game against the translated, memoized adversary plus one
seed guess per hash call after key generation, and the model's after-key-generation budget is the real
budget less the `K` calls of real key generation. The model's bound, two units per call plus the
slack, then fits in `q / 2^127`.
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Bridge

set_option backward.isDefEq.respectTransparency false

theorem keygenQueries_le (adversary : LeanXmss.Security.Adversary) (q : Nat)
    (hbound : LeanXmss.Security.HasHashQueryBound adversary q) : keygenQueries ≤ q := by
  let d : Derivations := ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩
  obtain ⟨r, hr⟩ := probComp_support_nonempty
    ((simulateQ randomOracle (honestRun d).withQueryLog).run (progCache 0 d))
  exact (afterKeygen_budget adversary q hbound 0 d r.1 r.2 hr).1

theorem final_arithmetic (q : Nat) (hK : keygenQueries ≤ q) (hq : q < 2 ^ 127) :
    ((2 * (q - keygenQueries) + lowerOrderSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
      ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hguess : ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤
      1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
    calc
      _ ≤ ((2 ^ 128 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
        ENNReal.div_le_div (by exact_mod_cast (by omega : q - keygenQueries ≤ 2 ^ 128)) le_rfl
      _ = ((2 ^ 128 : Nat) : ℝ≥0∞) / (((2 ^ 128 : Nat) : ℝ≥0∞) * ((2 ^ 128 : Nat) : ℝ≥0∞)) := by
        norm_num
      _ = _ := by
        simpa only [mul_one] using ENNReal.mul_div_mul_left 1 ((2 ^ 128 : Nat) : ℝ≥0∞)
          (c := ((2 ^ 128 : Nat) : ℝ≥0∞)) (by norm_num) (ENNReal.natCast_ne_top _)
  have hhalf : ((2 * q : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) = q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
    rw [show (2 ^ 128 : Nat) = 2 * 2 ^ 127 by norm_num, Nat.cast_mul, Nat.cast_mul]
    exact ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)
  calc
    _ ≤ ((2 * (q - keygenQueries) + lowerOrderSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
        1 / ((2 ^ 128 : Nat) : ℝ≥0∞) := add_le_add le_rfl hguess
    _ = ((2 * (q - keygenQueries) + lowerOrderSlack + 1 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      rw [← ENNReal.add_div, Nat.cast_succ]
    _ ≤ ((2 * q : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) := by
      apply ENNReal.div_le_div _ le_rfl
      have hK' := keygenQueries_eq
      simp only [lowerOrderSlack] at *
      exact_mod_cast (by omega : 2 * (q - keygenQueries) + 2 ^ 20 + 1 ≤ 2 * q)
    _ = _ := hhalf

/-- leanXMSS has 127 bits of classical security. -/
theorem leanXmss_security : LeanXmss.LeanXmssSecurityStatement := by
  intro q _ adversary hbound
  by_cases hsmall : q < 2 ^ 127
  · have hK := keygenQueries_le adversary q hbound
    have hlanes := Proof.concreteScheme_afterKeygenSecurity (q - keygenQueries) (by omega)
      (modelAdversary adversary) (afterKeygenBudget adversary q (by omega) hbound)
    calc LeanXmss.Security.forgeAdvantage adversary
        = Pr[= true | sampleMasterSeed >>= tableGame adversary] := forgeAdvantage_eq_tableGame adversary
      _ ≤ Pr[= true | cleanGame adversary] +
          ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
        tableGame_le_clean adversary q (by omega) hbound
      _ ≤ Pr[= true | refGame adversary] +
          ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
        add_le_add (cleanGame_le_ref adversary) le_rfl
      _ = forgeAdvantage Concrete.scheme (modelAdversary adversary) +
          ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by rw [refGame_eq]
      _ ≤ ((2 * (q - keygenQueries) + lowerOrderSlack : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) +
          ((q - keygenQueries : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := add_le_add hlanes le_rfl
      _ ≤ _ := final_arithmetic q hK hsmall
  · have hlarge : 2 ^ 127 ≤ q := Nat.le_of_not_gt hsmall
    calc
      LeanXmss.Security.forgeAdvantage adversary ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl

end XmssSecurity.Bridge

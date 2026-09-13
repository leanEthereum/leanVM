import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.FewTimeFresh
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_uniformHashOutput_admissible_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) =
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ *
        ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0) =
        ∑' target, if Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target then weight target else 0 := by
    by_cases h : Admissible (truncateMessageDigest output) <;> simp only [h, true_and, false_and, if_true, if_false, tsum_zero]
    simp
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      simp only [← signAttemptResultOfOutput_ne_none_iff]
      rw [probEvent_uniformHashOutput_admissible_view (fun view => view = target),
        probEvent_eq_eq_probOutput, mul_assoc]

end SphincsSecurity.Concrete

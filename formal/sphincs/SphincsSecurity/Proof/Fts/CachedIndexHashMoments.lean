import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.BernoulliExcessMoments
import SphincsSecurity.Proof.Fts.CachedIndexExcessScore
import SphincsSecurity.Proof.Fts.DigestSelectionIndex
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

def AdmissibleIndexOutput (index : Index) (output : HashOutput) : Prop :=
  Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index

theorem probEvent_uniformHashOutput_admissible_index (index : Index) :
    Pr[AdmissibleIndexOutput index | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 ^ 36 : Nat) : ENNReal)⁻¹ := by
  change Pr[fun output : HashOutput =>
    Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index |
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  have h := probEvent_uniformHashOutput_admissible_view (fun view => view.1 = index)
  rw [probEvent_uniform_view_index] at h
  have hcard : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  calc
    _ = ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹ := by
      simpa only [signAttemptResultOfOutput_ne_none_iff] using h
    _ = _ := by
      rw [hcard]
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem expected_uniformHashOutput_index_choice (index : Index) (accepted rejected : ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if AdmissibleIndexOutput index output then accepted else rejected)) =
      ((2 ^ 36 : Nat) : ENNReal)⁻¹ * accepted +
        (1 - ((2 ^ 36 : Nat) : ENNReal)⁻¹) * rejected := by
  have hnot : Pr[fun output => ¬ AdmissibleIndexOutput index output |
      ($ᵗ HashOutput : ProbComp HashOutput)] = 1 - ((2 ^ 36 : Nat) : ENNReal)⁻¹ := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (AdmissibleIndexOutput index)
    rw [probFailure_of_liftM_PMF, tsub_zero, probEvent_uniformHashOutput_admissible_index, add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by finiteness) h
  have hsplit (output : HashOutput) :
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if AdmissibleIndexOutput index output then accepted else rejected) =
        (if AdmissibleIndexOutput index output then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * accepted +
        (if ¬ AdmissibleIndexOutput index output then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * rejected := by
    by_cases h : AdmissibleIndexOutput index output <;>
      simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false, zero_mul, zero_add, add_zero]
  simp_rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite,
    probEvent_uniformHashOutput_admissible_index, hnot]

private theorem bernoulliExcess_secondMoment_ennreal (score : ℝ) (probability : ENNReal)
    (hprob : probability ≤ 1) :
    probability * positiveScoreMoment (score + (1 - probability.toReal)) 2 +
        (1 - probability) * positiveScoreMoment (score + (-probability.toReal)) 2 ≤
      positiveScoreMoment score 2 + probability := by
  have hp : probability ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hprob
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness)
    (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) hp]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hprob (by finiteness), ENNReal.toReal_one,
    positiveScoreMoment, ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _)]
  exact bernoulliExcess_secondMoment_le score probability.toReal ENNReal.toReal_nonneg
    ((ENNReal.toReal_mono (by finiteness) hprob).trans_eq ENNReal.toReal_one)

theorem positiveScoreMoment_mono (power : Nat) {before after : ℝ} (hle : before ≤ after) :
    positiveScoreMoment before power ≤ positiveScoreMoment after power :=
  ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_max_right _ _) (max_le_max hle le_rfl) power)

private theorem expected_cachedIndexScore_nonmessage_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hmessage : ¬ FtsProbeSimulation.MessageHashInput parameter input) (index : Index) (power : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) power) ≤
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) power := by
  simp_rw [cachedIndexExcessScore_cacheQuery parameter cache hfinite input _ hfresh index,
    hmessage, false_and, if_false, add_zero]
  calc
    _ ≤ ∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) power := by
      apply ENNReal.tsum_le_tsum
      intro output
      exact mul_le_mul' le_rfl (positiveScoreMoment_mono power (sub_le_self _ (by positivity)))
    _ = _ := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_cachedIndexScore_second_le (parameter : PublicParameter)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (index : Index) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      positiveScoreMoment (cachedIndexExcessScore parameter (cache.cacheQuery input output) index) 2) ≤
        positiveScoreMoment (cachedIndexExcessScore parameter cache index) 2 + ((2 ^ 36 : Nat) : ENNReal)⁻¹ := by
  by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input
  · simp_rw [cachedIndexExcessScore_cacheQuery parameter cache hfinite input _ hfresh index,
      hmessage, true_and]
    have hchoice (output : HashOutput) :
        positiveScoreMoment (cachedIndexExcessScore parameter cache index +
          (if Admissible (truncateMessageDigest output) ∧ (hashOutputFewTimeView output).1 = index then 1 else 0) -
          (2 ^ 36 : ℝ)⁻¹) 2 =
        if AdmissibleIndexOutput index output then
          positiveScoreMoment (cachedIndexExcessScore parameter cache index + (1 - (2 ^ 36 : ℝ)⁻¹)) 2
        else positiveScoreMoment (cachedIndexExcessScore parameter cache index + (-(2 ^ 36 : ℝ)⁻¹)) 2 := by
      unfold AdmissibleIndexOutput
      split_ifs <;> congr 1 <;> ring
    simp_rw [hchoice]
    rw [expected_uniformHashOutput_index_choice]
    have h := bernoulliExcess_secondMoment_ennreal (cachedIndexExcessScore parameter cache index)
      ((2 ^ 36 : Nat) : ENNReal)⁻¹ (by norm_num)
    simpa only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      Nat.cast_pow, Nat.cast_ofNat] using h
  · exact (expected_cachedIndexScore_nonmessage_le parameter cache hfinite input hfresh hmessage index 2).trans le_self_add

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.Fts.MessageDeficitCacheGrowth
import SphincsSecurity.Proof.Fts.CachedIndexHashMoments

/-! ## MessageDeficitBernoulli -/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem messageDeficit_secondMoment_le (score : ℝ) :
    (1 / 1024 : ℝ) * max (score - 1023) 0 ^ 2 +
      (1023 / 1024 : ℝ) * max (score + 1) 0 ^ 2 ≤ max score 0 ^ 2 + 1023 := by
  calc
    _ ≤ (1 / 1024 : ℝ) * (max score 0 - 1023) ^ 2 + (1023 / 1024 : ℝ) * (max score 0 + 1) ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (positivePart_shift_even_le score (-1023) 2 (by decide)) (by norm_num)
      · exact mul_le_mul_of_nonneg_left (positivePart_shift_even_le score 1 2 (by decide)) (by norm_num)
    _ = _ := by ring

theorem messageDeficit_secondMoment_ennreal (score : ℝ) :
    (1024 : ENNReal)⁻¹ * positiveScoreMoment (score - 1023) 2 +
      (1 - (1024 : ENNReal)⁻¹) * positiveScoreMoment (score + 1) 2 ≤ positiveScoreMoment score 2 + 1023 := by
  have hsub : (1 - (1024 : ENNReal)⁻¹).toReal = (1023 / 1024 : ℝ) := by
    rw [ENNReal.toReal_sub_of_le (by norm_num) (by finiteness)]
    norm_num [ENNReal.toReal_inv]
  apply (ENNReal.toReal_le_toReal (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness)).mp
  rw [ENNReal.toReal_add (by unfold positiveScoreMoment; finiteness) (by unfold positiveScoreMoment; finiteness),
    ENNReal.toReal_add (positiveScoreMoment_ne_top _ _) (by finiteness)]
  simpa only [ENNReal.toReal_mul, hsub, ENNReal.toReal_inv, ENNReal.toReal_ofNat, positiveScoreMoment,
    ENNReal.toReal_ofReal (pow_nonneg (le_max_right _ _) _), one_div] using messageDeficit_secondMoment_le score

end SphincsSecurity

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
open Concrete (Admissible)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] messageDeficitScore positiveScoreMoment messageDeficitMoment
set_option backward.isDefEq.respectTransparency false

theorem probEvent_uniformHashOutput_admissible :
    Pr[fun output => Admissible (truncateMessageDigest output) | ($ᵗ HashOutput : ProbComp HashOutput)] = (1024 : ENNReal)⁻¹ := by
  simpa only [and_true, probEvent_True_eq_sub, probFailure_of_liftM_PMF, tsub_zero, mul_one,
    Concrete.signAttemptResultOfOutput_ne_none_iff, ftsTreeHeight, Nat.reducePow, Nat.cast_ofNat] using
    Concrete.probEvent_uniformHashOutput_admissible_view (fun _ => True)

private theorem expected_admissible_choice (accepted rejected : ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then accepted else rejected)) =
      (1024 : ENNReal)⁻¹ * accepted + (1 - (1024 : ENNReal)⁻¹) * rejected := by
  have hnot : Pr[fun output => ¬Admissible (truncateMessageDigest output) | ($ᵗ HashOutput : ProbComp HashOutput)] = 1 - (1024 : ENNReal)⁻¹ := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (fun output => Admissible (truncateMessageDigest output))
    rw [probFailure_of_liftM_PMF, tsub_zero, probEvent_uniformHashOutput_admissible, add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by finiteness) h
  have hsplit (output : HashOutput) :
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * (if Admissible (truncateMessageDigest output) then accepted else rejected) =
        (if Admissible (truncateMessageDigest output) then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * accepted +
        (if ¬Admissible (truncateMessageDigest output) then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * rejected := by
    split_ifs <;> simp_all only [zero_mul, zero_add, add_zero]
  simp_rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite, probEvent_uniformHashOutput_admissible, hnot]

private theorem expected_messageDeficitMoment_at (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hat : MessageInputAt parameter root message input) (power : Nat) (charge : ENNReal)
    (hshift : (1024 : ENNReal)⁻¹ * positiveScoreMoment (messageDeficitScore parameter root message cache - 1023) power +
      (1 - (1024 : ENNReal)⁻¹) * positiveScoreMoment (messageDeficitScore parameter root message cache + 1) power ≤
      positiveScoreMoment (messageDeficitScore parameter root message cache) power + charge) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input output) power) ≤ messageDeficitMoment parameter root cache power + charge := by
  let rest := ∑ other ∈ Finset.univ.erase message, positiveScoreMoment (messageDeficitScore parameter root other cache) power
  have hbefore : messageDeficitMoment parameter root cache power = positiveScoreMoment (messageDeficitScore parameter root message cache) power + rest := by
    unfold messageDeficitMoment
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ message)).symm
  have hafter (output : HashOutput) : messageDeficitMoment parameter root (cache.cacheQuery input output) power =
      (if Admissible (truncateMessageDigest output) then positiveScoreMoment (messageDeficitScore parameter root message cache - 1023) power
       else positiveScoreMoment (messageDeficitScore parameter root message cache + 1) power) + rest := by
    unfold messageDeficitMoment
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ message)]
    apply congrArg₂ (· + ·)
    · rw [messageDeficitScore_cacheQuery _ _ _ _ hfinite _ _ hfresh, if_pos hat]
      split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro other hother
      rw [messageDeficitScore_cacheQuery _ _ _ _ hfinite _ _ hfresh,
        if_neg (fun h => (Finset.mem_erase.mp hother).1 (h.unique hat))]
  simp_rw [hafter, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  rw [expected_admissible_choice, hbefore]
  exact (add_le_add hshift le_rfl).trans_eq (add_right_comm _ _ rest)

private theorem expected_messageDeficitMoment_other (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hother : ¬∃ message, MessageInputAt parameter root message input) (power : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input output) power) = messageDeficitMoment parameter root cache power := by
  have heq (output : HashOutput) : messageDeficitMoment parameter root (cache.cacheQuery input output) power = messageDeficitMoment parameter root cache power := by
    unfold messageDeficitMoment
    apply Finset.sum_congr rfl
    intro message _
    rw [messageDeficitScore_cacheQuery _ _ _ _ hfinite _ _ hfresh, if_neg (fun h => hother ⟨message, h⟩)]
  simp_rw [heq, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_messageDeficitMoment_second_le (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input output) 2) ≤ messageDeficitMoment parameter root cache 2 + 1023 := by
  by_cases hat : ∃ message, MessageInputAt parameter root message input
  · obtain ⟨message, hat⟩ := hat
    exact expected_messageDeficitMoment_at parameter root message cache hfinite input hfresh hat 2 1023
      (messageDeficit_secondMoment_ennreal _)
  · rw [expected_messageDeficitMoment_other parameter root cache hfinite input hfresh hat]
    exact le_self_add

end SphincsSecurity

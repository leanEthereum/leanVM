import SphincsSecurity.Completeness.Game
import SphincsSecurity.Completeness.Signing
import SphincsSecurity.Completeness.Keygen
import SphincsSecurity.Completeness.Decay

/-!
# Completeness

The proofs of the two claims of `Completeness.lean`. Correctness is `Game.correct`, which
reads `verify_of_sign` of `Recovery.lean` off key generation. For completeness:

`Game.lean` pulls the seed out of the experiment and, through recovery, charges failure to signing
returning `none`. `Keygen.lean` shows key generation leaves every input a later search hashes
uncached, and `Signing.lean` charges a signing failure to its six searches: the randomizer search
(`Digest.lean`) and five counter searches (`Counter.lean`, with the code's size from `Code.lean`
and `Encoding.lean`). Each search is long enough that its failure decays exponentially
(`Decay.lean`), which is what closes the bound below.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

theorem digestFactor_pow_le : digestFactor ^ digestAttemptLimit ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ 21) := by
  have hroom : digestFactor + ((2 ^ 11 : Nat) : ℝ≥0∞)⁻¹ ≤ 1 :=
    digest_room digestReject digestReject_add
  have hhalf := pow_le_half_ennreal (2 ^ 11) (by positivity) digestFactor hroom
  rw [show digestAttemptLimit = 2 ^ 11 * 2 ^ 21 by rw [digestAttemptLimit]; norm_num, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hhalf _

theorem encoding_pow_le :
    failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ 18) := by
  have hroom : failMass (fun out => TargetSum.decodeDigest (truncateHash out))
      + ((2 ^ 14 : Nat) : ℝ≥0∞)⁻¹ ≤ 1 := by
    have h := failMass_encoding_add_le
    rwa [← Nat.cast_ofNat, ← Nat.cast_pow] at h
  have hhalf := pow_le_half_ennreal (2 ^ 14) (by positivity) _ hroom
  rw [show encodingAttemptLimit = 2 ^ 14 * 2 ^ 18 by rw [encodingAttemptLimit]; norm_num, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hhalf _

/-- Key generation then signing fails only if one of signing's six searches does. -/
theorem probEvent_signedWithKeys_none (seed : MasterSeed) (message : Message) :
    Pr[fun r => r.1.2 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signedWithKeys seed message)).run ∅]
      ≤ digestFactor ^ digestAttemptLimit + 5 * encodingBound := by
  rw [signedWithKeys]
  refine probEvent_bind_le _ _ _ ∅ _ (fun r hr => ?_)
  obtain ⟨hrand, hmsg, henc⟩ := keygen_fresh seed r hr message
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ r.2 0 ?_) ?_
  · rintro ⟨result, c⟩ _ hsome
    obtain ⟨signature, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp
  · rw [add_zero]
    exact probEvent_sign_none r.1.2 message r.2 hrand hmsg henc

theorem failure_le (message : Message) :
    Pr[= false | experiment message] ≤ digestFactor ^ digestAttemptLimit + 5 * encodingBound := by
  rw [experiment_eq, ← probEvent_eq_eq_probOutput]
  refine probEvent_prob_bind_le _ _ _ _ (fun seed _ => ?_)
  rw [probEvent_map]
  exact (probEvent_honest_false_le seed message).trans (probEvent_signedWithKeys_none seed message)

/-- The scheme is `2⁻²⁵⁶`-complete. -/
theorem complete : SphincsCompletenessStatement := by
  calc
    ∑' message : Message, Pr[= false | experiment message]
        ≤ ∑' _message : Message,
            ((2⁻¹ : ℝ≥0∞) ^ (2 ^ 21) + 5 * (2⁻¹ : ℝ≥0∞) ^ (2 ^ 18)) := by
          refine ENNReal.tsum_le_tsum fun message => ?_
          exact (failure_le message).trans
            (add_le_add digestFactor_pow_le (mul_le_mul_right encoding_pow_le _))
    _ = (2 : ℝ≥0∞) ^ 256 *
          ((2⁻¹ : ℝ≥0∞) ^ (2 ^ 21) + 5 * (2⁻¹ : ℝ≥0∞) ^ (2 ^ 18)) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := closing_sum

end SphincsSecurity.Completeness

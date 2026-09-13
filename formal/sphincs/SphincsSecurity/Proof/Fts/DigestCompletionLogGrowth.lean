import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.DigestSigningCompletion
import SphincsSecurity.Proof.Fts.NormalizedTargetLogSigning
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

theorem digestCompletion_normalizedTargetLogProduct_le_input
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (loop : DigestLoopRecord)
    (hloop : loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before))
    (result : (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : DigestCompletionPreservesMessages key loop result) :
    normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required ≤
      normalizedTargetLogProduct key before log payload target required +
        successfulSignerInputWeight key message (fun input source =>
          if input = tweakableHashInput key.parameter .message payload then 0
          else normalizedTargetLogIncrement key before log payload target required source) result := by
  have hcache := simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) before loop hloop
  have hproject : normalizedTargetLogProduct key result.2 (log ++ [⟨message, result.1.1⟩]) payload target required =
      normalizedTargetLogProduct key loop.2 (log ++ [⟨message, result.1.1⟩]) payload target required := by
    unfold normalizedTargetLogProduct normalizedTargetLogMatch
    rw [hcompletion.2]
  rw [hproject]
  cases hs : result.1.1 with
  | none =>
      rw [normalizedTargetLogProduct_append_none key before loop.2 log _ payload target required hcache hsigned
        (by simp [eligibleSigningView?])]
      simp only [successfulSignerInputWeight, hs, add_zero, le_refl]
  | some signature =>
      obtain ⟨output, houtput, _, hview⟩ := digestCompletion_successful_cached_output key message before loop hloop result hcompletion signature hs
      have hcached : loop.2 (tweakableHashInput key.parameter .message
          (messageDigestPayload key.root message signature.randomness)) = some output :=
        (congrFun hcompletion.2 (messageDigestPayload key.root message signature.randomness)).symm.trans houtput
      by_cases hsame : messageDigestPayload key.root message signature.randomness = payload
      · rw [normalizedTargetLogProduct_append_none key before loop.2 log _ payload target required hcache hsigned
          (by simp [eligibleSigningView?, hsame])]
        exact le_self_add
      · have hinput : tweakableHashInput key.parameter .message (messageDigestPayload key.root message signature.randomness) ≠
            tweakableHashInput key.parameter .message payload := by
          intro heq
          exact hsame (tweakableHashInput_injective key.parameter (by trivial) (by trivial) heq).2
        simp only [successfulSignerInputWeight, hs, hview, if_neg hinput]
        rw [normalizedTargetLogProduct_add_increment]
        apply Finset.prod_le_prod'
        intro tree _
        exact normalizedTargetLogMatch_le_of_eligibleView key before loop.2 log ⟨message, some signature⟩ payload target
          (hashOutputFewTimeView output) tree hcache hsigned (Or.inr (by
            simp [eligibleSigningView?, observedSigningView?, messageAnswers, hsame, hcached]))

theorem expected_digestCompletion_normalizedTargetLogProduct_le_of_exactReuse {α : Type}
    (key : SecretKey) (message : Message) (before : QueryCache HashSpec)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset FtsTree)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (reuse : ENNReal) (hreuse : exactDigestReuseWeight key message before ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish] *
      normalizedTargetLogProduct key (record result).2 (log ++ [⟨message, (record result).1.1⟩]) payload target required) ≤
      normalizedTargetLogProduct key before log payload target required +
        (Fintype.card Index : ENNReal)⁻¹ *
          (∑ selected ∈ required.powerset.erase ∅, normalizedTargetLogProduct key before log payload target (required \ selected)) +
        (∑ selected ∈ required.powerset.erase ∅,
          normalizedCachedTargetSubsetMatch key.parameter before (tweakableHashInput key.parameter .message payload) target selected *
            normalizedTargetLogProduct key before log payload target (required \ selected)) * reuse := by
  let computation := (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish
  let weight := fun input source => if input = tweakableHashInput key.parameter .message payload then 0
    else normalizedTargetLogIncrement key before log payload target required source
  have hweight (input : HashInput) (source : FewTimeView) :
      weight input source ≤ normalizedTargetLogIncrement key before log payload target required source := by
    unfold weight
    split_ifs; exact bot_le; exact le_rfl
  calc
    _ ≤ ∑' result, Pr[= result | computation] *
        (normalizedTargetLogProduct key before log payload target required + successfulSignerInputWeight key message weight (record result)) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support computation
      · change result ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run before >>= finish) at hr
        rw [mem_support_bind_iff] at hr
        obtain ⟨loop, hl, hf⟩ := hr
        exact mul_le_mul' le_rfl (digestCompletion_normalizedTargetLogProduct_le_input key message before log payload target required
          hsigned loop hl (record result) (hcompletion loop hl result hf))
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ normalizedTargetLogProduct key before log payload target required +
        ∑' result, Pr[= result | computation] * successfulSignerInputWeight key message weight (record result) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
    _ ≤ _ := by
      have hbound := (expected_digestCompletion_successfulInputWeight_le_allMessage key message before finish record
        (fun loop hl result hr => (hcompletion loop hl result hr).1) weight _ hweight reuse hreuse).trans
          (add_le_add (mul_le_of_le_one_left' (freshDigestSelectionProbability_le_one key message before)) le_rfl)
      simp only [weight, expected_normalizedTargetLogIncrement, cached_normalizedTargetLogIncrement] at hbound
      simpa only [add_assoc, computation, weight] using add_le_add
        (le_refl (normalizedTargetLogProduct key before log payload target required)) hbound

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.BankedTargetEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
attribute [local irreducible] signDigestLoop

theorem expected_digestCompletion_reuseTarget_le {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (message : Message)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1 >>= finish] *
      reuseTargetEnvelope key reuse budget payload target signatures
        ((record result).2, state.2 ++ [⟨message, (record result).1.1⟩]) groups remaining) ≤
      reuseTargetEnvelope key reuse budget payload target (signatures + 1) state groups remaining := by
  unfold reuseTargetEnvelope
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ budget signatures
    (fun G R hv => expected_digestCompletion_targetShapeMoments_le_of_exactReuse key message state.1 finish record hcompletion
      state.2 payload target G R hv hsigned reuse hreuse) groups remaining hvalid).trans
        (targetShapeEnvelope_signing_le _ _ _ budget signatures _ groups remaining hvalid)

theorem expected_digestCompletion_reuseNewTarget_le_mass_mul {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (state : CoverLogState) (message : Message)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1 >>= finish] *
      reuseNewTargetEnvelope key reuse budget signatures state.1
        ((record result).2, state.2 ++ [⟨message, (record result).1.1⟩]) groups remaining) ≤
      freshDigestSelectionProbability key message state.1 *
        ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  have h := expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul key message state.1 finish record hcompletion
    state.2 hsigned (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures groups remaining hvalid
  refine h.trans_eq ?_
  unfold reuseRawEnvelope observedRawIndexShapeVector
  rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]

theorem expected_digestCompletion_bankedTarget_le {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (finish : DigestLoopRecord → ProbComp α)
    (record : α → (Option Signature × Option FewTimeView) × QueryCache HashSpec)
    (hcompletion : ∀ loop ∈ support ((simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1),
      ∀ result ∈ support (finish loop), DigestCompletionPreservesMessages key loop (record result))
    (stopped : α → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | (simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run state.1 >>= finish] *
      bankedTargetEnvelope key reuse budget signatures required
        ((record result).2, state.2 ++ [⟨message, (record result).1.1⟩])
        (completedTargetBank key required ((record result).2, state.2 ++ [⟨message, (record result).1.1⟩]) bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        freshDigestSelectionProbability key message state.1 *
          ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required) *
            targetCertificateScale required := by
  have hvalid : TargetShapeValid ∅ required := by constructor <;> simp
  apply expected_bankedCacheWeight_step_le_of_split
  · intro result hr value
    rw [mem_support_bind_iff] at hr
    obtain ⟨loop, hl, hf⟩ := hr
    have hmessages := (hcompletion loop hl result hf).2
    rw [cacheMessageWeight_messageAnswers_congr key.parameter (record result).2 loop.2 hmessages value,
      cacheMessageWeight_messageAnswers_congr key.parameter (record result).2 loop.2 hmessages
        (fun input target => if state.1 input = none then value input target else 0)]
    exact cacheMessageWeight_of_le key.parameter value state.1 loop.2
      (simulateQ_romImpl_cache_le (signDigestLoop digestAttemptLimit key message) state.1 loop hl)
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required _ query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_digestCompletion_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state message finish record hcompletion hsigned hreuse ∅ required hvalid) le_rfl
  · have h := expected_digestCompletion_reuseNewTarget_le_mass_mul key reuse budget signatures state message finish record hcompletion
      hsigned ∅ required hvalid
    have hforecast (result : α) := newTargetCertificateForecast_eq key reuse budget signatures required state.1
      ((record result).2, state.2 ++ [⟨message, (record result).1.1⟩])
    simpa only [hforecast, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))

end SphincsSecurity.Concrete

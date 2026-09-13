import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ReuseRawEnvelope
import SphincsSecurity.Proof.Fts.DigestCompletionNewTarget

/-! ## NewTargetWorld -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem newTargetEnvelopeCharge_cacheQuery (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) :
    newTargetEnvelopeCharge key before (before.cacheQuery input output) log uniform reuse arrival queries signings groups remaining =
      if MessageHashInput key.parameter input ∧ Admissible (truncateMessageDigest output) then
        targetShapeEnvelope uniform reuse arrival queries signings
          (targetShapeMoments key (before.cacheQuery input output) log (payloadOf input) (hashOutputFewTimeView output)) groups remaining else 0 := by
  unfold newTargetEnvelopeCharge
  rw [cacheMessageWeight_cacheQuery key.parameter _ before input output hfresh,
    cacheMessageWeight_fresh_restriction, zero_add]
  simp only [hfresh, if_true]

end SphincsSecurity.Concrete

/-! ## ExpectedNewTargetEnvelope -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_signWithView_newTargetEnvelopeCharge_le_mass_mul (key : SecretKey) (message : Message)
    (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (hsigned : SigningDigestsCached key.parameter before key.root log)
    (uniform reuse arrival : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (simulateQ romImpl (signWithView key message)).run before] *
      newTargetEnvelopeCharge key before result.2 (log ++ [⟨message, result.1.1⟩]) uniform reuse arrival queries signings groups remaining) ≤
        freshDigestSelectionProbability key message before *
          ((Fintype.card Index : ENNReal)⁻¹ *
            targetIndexEnvelope uniform reuse arrival queries signings (targetIndexMoments key before log) groups.card remaining.card) := by
  rw [signWithView_run_eq_digestCompletion]
  exact expected_digestCompletion_newTargetEnvelopeCharge_le_mass_mul key message before
    (originalDigestCompletion key) id (fun loop _ result hr => originalDigestCompletion_preservesMessages key loop result hr)
    log hsigned uniform reuse arrival queries signings groups remaining hvalid

end SphincsSecurity.Concrete

/-! ## FreshTargetWorld -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def freshWorldTargetHashCost (parameter : PublicParameter) (cache : QueryCache HashSpec) : OracleWorld.Domain → Nat
  | .inl _ => 0
  | .inr input => if MessageHashInput parameter input ∧ cache input = none then 1 else 0

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput)
attribute [local instance] Classical.propDecidable

noncomputable abbrev reuseNewTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (before : QueryCache HashSpec) (after : CoverLogState) (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) : ENNReal :=
  newTargetEnvelopeCharge key before after.1 after.2 (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures groups remaining

theorem expected_randomOracle_reuseNewTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2) groups remaining) ≤
      (freshWorldTargetHashCost key.parameter state.1 (.inr input) : ENNReal) *
        ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output : HashOutput, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (state.1.cacheQuery input output, state.2) groups remaining) ≤ _
    simp only [reuseNewTargetEnvelope, newTargetEnvelopeCharge_cacheQuery key state.1 state.2 _ _ _ _ _ groups remaining input _ hfresh]
    by_cases hmessage : MessageHashInput key.parameter input
    · obtain ⟨payload, rfl⟩ := hmessage
      simp only [show MessageHashInput key.parameter (tweakableHashInput key.parameter .message payload) from ⟨payload, rfl⟩,
        true_and, payloadOf_tweakableHashInput, freshWorldTargetHashCost, hfresh, and_self, if_true, Nat.cast_one, one_mul]
      rw [expected_cacheQuery_freshTargetEnvelope key state.1 state.2 payload hfresh hsigned _ _ _ _ _ groups remaining hvalid]
      unfold reuseRawEnvelope observedRawIndexShapeVector
      rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
    · simp only [hmessage, false_and, if_false, mul_zero, tsum_zero, zero_le]
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    rw [reuseNewTargetEnvelope, newTargetEnvelopeCharge, cacheMessageWeight_fresh_restriction]
    exact zero_le

theorem expected_logTraced_world_reuseNewTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 result.2 groups remaining) ≤
      (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
        ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
          reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_reuseNewTarget_le key reuse budget signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      simp only [reuseNewTargetEnvelope, newTargetEnvelopeCharge, cacheMessageWeight_fresh_restriction, mul_zero, tsum_zero, zero_le]

theorem expected_logTraced_sign_reuseNewTarget_le_mass_mul (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (state : CoverLogState) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 result.2 groups remaining) ≤
      freshDigestSelectionProbability key message state.1 *
        ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state groups remaining) := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have hrun : (unloggedMappedAdversaryImpl key (.inr message)).run state.1 =
      (fun result => (result.1.1, result.2)) <$> (simulateQ romImpl (signWithView key message)).run state.1 :=
    (simulateQ_signWithView_fst_run key message state.1).symm
  have heq := congrArg (fun computation : ProbComp (Option Signature × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] *
      reuseNewTargetEnvelope key reuse budget signatures state.1 (result.2, state.2 ++ [⟨message, result.1⟩]) groups remaining) hrun
  rw [tsum_probOutput_map_mul] at heq
  have h := expected_signWithView_newTargetEnvelopeCharge_le_mass_mul key message state.1 state.2 hsigned
    (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures groups remaining hvalid
  refine heq.le.trans (h.trans_eq ?_)
  unfold reuseRawEnvelope observedRawIndexShapeVector
  rw [targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]

end SphincsSecurity.Concrete

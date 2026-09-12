import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.BankedCacheWeight
import SphincsSecurity.Proof.Fts.ReuseCachedTargets
import SphincsSecurity.Proof.Fts.ReuseTargetEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (MessageHashInput messageAnswers)
attribute [local instance] Classical.propDecidable

def TargetCoveredOn (key : SecretKey) (required : Finset FtsTree) (state : CoverLogState)
    (payload : HashInput) (target : FewTimeView) : Prop :=
  ∀ tree ∈ required, 0 < targetTreeMatchCount
    (eligibleSigningViews (messageAnswers key.parameter state.1) key.root payload state.2) target tree

def TargetCertificateAt (key : SecretKey) (required : Finset FtsTree) (state : CoverLogState)
    (input : HashInput) : Prop :=
  ∃ output, state.1 input = some output ∧ MessageHashInput key.parameter input ∧
    Admissible (truncateMessageDigest output) ∧
      TargetCoveredOn key required state (payloadOf input) (hashOutputFewTimeView output)

noncomputable def completedTargetBank (key : SecretKey) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) : HashInput → Bool :=
  fun input => bank input || decide (TargetCertificateAt key required state input)

noncomputable def targetCertificateScale (required : Finset FtsTree) : ENNReal :=
  ((Fintype.card FtsLeaf : ENNReal) ^ required.card)⁻¹

noncomputable def targetCertificateForecast (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (input : HashInput) (target : FewTimeView) : ENNReal :=
  reuseTargetEnvelope key reuse budget (payloadOf input) target signatures state ∅ required *
    targetCertificateScale required

noncomputable def bankedTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool) : ENNReal :=
  bankedCacheWeight key.parameter (targetCertificateForecast key reuse budget signatures required state) bank stopped state.1

noncomputable def targetCreationMultiplier (key : SecretKey) (cache : QueryCache HashSpec) :
    (OracleWorld + SigningSpec).Domain → ENNReal
  | .inl input => freshWorldTargetHashCost key.parameter cache input
  | .inr message => ((2 ^ ftsTreeHeight : Nat) : ENNReal) * freshDigestSelectionProbability key message cache

noncomputable def targetCreationPrice (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) : ENNReal :=
  (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
    reuseRawEnvelope key reuse budget signatures state ∅ required * targetCertificateScale required

theorem bankedTargetEnvelope_initial (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState)
    (hnone : ∀ input, MessageHashInput key.parameter input → state.1 input = none) :
    bankedTargetEnvelope key reuse budget signatures required state (fun _ => false) false = 0 := by
  rw [bankedTargetEnvelope, bankedCacheWeight_live, certificateBankCount_empty, zero_add]
  exact cacheMessageWeight_of_no_message key.parameter _ state.1 hnone

theorem bankedTargetEnvelope_stopped (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) :
    bankedTargetEnvelope key reuse budget signatures required state bank true = certificateBankCount bank :=
  bankedCacheWeight_stopped _ _ _ _

theorem targetCreationMultiplier_sign_mul_price (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (message : Message) :
    targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state =
      freshDigestSelectionProbability key message state.1 *
        ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required) *
          targetCertificateScale required := by
  have hcancel : ((2 ^ ftsTreeHeight : Nat) : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by norm_num [ftsTreeHeight]) (by finiteness)
  unfold targetCreationMultiplier targetCreationPrice
  calc
    _ = (((2 ^ ftsTreeHeight : Nat) : ENNReal) * ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹) *
        (freshDigestSelectionProbability key message state.1 *
          ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required) *
            targetCertificateScale required) := by ring
    _ = _ := by rw [hcancel, one_mul]

theorem completedTargetBank_of_certificate (key : SecretKey) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (input : HashInput)
    (hcovered : TargetCertificateAt key required state input) :
    completedTargetBank key required state bank input = true := by
  simp only [completedTargetBank, hcovered, decide_true, Bool.or_true]

theorem normalizedTargetLogProduct_ge_of_coveredOn (key : SecretKey) (required : Finset FtsTree)
    (state : CoverLogState) (payload : HashInput) (target : FewTimeView)
    (hcovered : TargetCoveredOn key required state payload target) :
    (Fintype.card FtsLeaf : ENNReal) ^ required.card ≤
      normalizedTargetLogProduct key state.1 state.2 payload target required := by
  rw [← Finset.prod_const]
  apply Finset.prod_le_prod'
  intro tree htree
  apply le_mul_of_one_le_right'
  exact_mod_cast Nat.succ_le_iff.mpr (hcovered tree htree)

theorem one_le_targetCertificateForecast_of_covered (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (input : HashInput) (target : FewTimeView)
    (hcovered : TargetCoveredOn key required state (payloadOf input) target) :
    1 ≤ targetCertificateForecast key reuse budget signatures required state input target := by
  have hmoment := normalizedTargetLogProduct_ge_of_coveredOn key required state (payloadOf input) target hcovered
  have hforecast : (Fintype.card FtsLeaf : ENNReal) ^ required.card ≤
      reuseTargetEnvelope key reuse budget (payloadOf input) target signatures state ∅ required := by
    apply hmoment.trans
    simpa only [reuseTargetEnvelope, observedTargetShapeVector, targetShapeMoments, Finset.prod_empty, one_mul] using
      (le_targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse
        (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹)
        budget signatures (observedTargetShapeVector key (payloadOf input) target state) ∅ required)
  have hzero : (Fintype.card FtsLeaf : ENNReal) ^ required.card ≠ 0 :=
    pow_ne_zero _ (by norm_num [FtsLeaf, ftsTreeHeight])
  have hfinite : (Fintype.card FtsLeaf : ENNReal) ^ required.card ≠ ∞ := by finiteness
  unfold targetCertificateForecast targetCertificateScale
  rw [← ENNReal.mul_inv_cancel hzero hfinite]
  exact mul_le_mul' hforecast le_rfl

theorem one_le_targetCertificateEntry_of_certificate (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (input : HashInput)
    (hcertificate : TargetCertificateAt key required state input) :
    1 ≤ cacheMessageEntryWeight key.parameter
      (targetCertificateForecast key reuse budget signatures required state) state.1 input := by
  obtain ⟨output, houtput, hmessage, hadmissible, hcovered⟩ := hcertificate
  simp only [cacheMessageEntryWeight, houtput, hmessage, hadmissible, and_self, if_true]
  exact one_le_targetCertificateForecast_of_covered key reuse budget signatures required state input _ hcovered

private theorem empty_targetShapeValid (required : Finset FtsTree) : TargetShapeValid ∅ required := by
  constructor <;> simp

theorem targetCreationPrice_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    targetCreationPrice key reuse smaller signatures required state ≤
      targetCreationPrice key reuse larger signatures required state := by
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact targetShapeEnvelope_queries_mono _ _ _ _ _ hbudget ∅ required (empty_targetShapeValid required)

theorem targetCreationPrice_signatures_mono (key : SecretKey) (reuse : ENNReal) (budget : Nat)
    (required : Finset FtsTree) (state : CoverLogState) {smaller larger : Nat} (hsignatures : smaller ≤ larger) :
    targetCreationPrice key reuse budget smaller required state ≤
      targetCreationPrice key reuse budget larger required state := by
  apply mul_le_mul' ?_ le_rfl
  apply mul_le_mul' le_rfl
  exact Function.monotone_iterate_of_id_le
    (show ∀ f : TargetShapeVector, f ≤ targetShapeSigning (Fintype.card Index : ENNReal)⁻¹ reuse f from
      fun _ _ _ => (le_self_add).trans le_self_add)
    hsignatures _ ∅ required

theorem bankedTargetEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (stopped : Bool)
    {smaller larger : Nat} (hbudget : smaller ≤ larger) :
    bankedTargetEnvelope key reuse smaller signatures required state bank stopped ≤
      bankedTargetEnvelope key reuse larger signatures required state bank stopped := by
  apply bankedCacheWeight_mono
  intro input target
  exact mul_le_mul' (reuseTargetEnvelope_budget_mono key reuse (payloadOf input) target signatures state
    hbudget ∅ required (empty_targetShapeValid required)) le_rfl

theorem newTargetCertificateForecast_eq (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (before : QueryCache HashSpec) (after : CoverLogState) :
    cacheMessageWeight key.parameter (fun input target => if before input = none then
      targetCertificateForecast key reuse budget signatures required after input target else 0) after.1 =
      reuseNewTargetEnvelope key reuse budget signatures before after ∅ required * targetCertificateScale required := by
  unfold reuseNewTargetEnvelope newTargetEnvelopeCharge
  rw [← cacheMessageWeight_mul_right]
  apply congrArg (fun weight => cacheMessageWeight key.parameter weight after.1)
  funext input target
  by_cases hfresh : before input = none
  · simp only [hfresh, if_true, targetCertificateForecast]
    rfl
  · simp only [hfresh, if_false, zero_mul]

theorem expected_logTraced_world_bankedTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : (OracleWorld + SigningSpec).Range (.inl input) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      bankedTargetEnvelope key reuse budget signatures required result.2
        (completedTargetBank key required result.2 bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse (budget + signingExecutionHashCost (.inl input)) signatures required state bank false +
        (freshWorldTargetHashCost key.parameter state.1 input : ENNReal) *
          ((((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) *
            reuseRawEnvelope key reuse budget signatures state ∅ required) * targetCertificateScale required := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inl input) state result hr
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required result.2 query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_world_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state input hsigned ∅ required (empty_targetShapeValid required)) le_rfl
  · have h := expected_logTraced_world_reuseNewTarget_le key reuse budget signatures state input hsigned
      ∅ required (empty_targetShapeValid required)
    simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))

theorem expected_logTraced_sign_bankedTarget_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : (OracleWorld + SigningSpec).Range (.inr message) × CoverLogState → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      bankedTargetEnvelope key reuse budget signatures required result.2
        (completedTargetBank key required result.2 bank) (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        freshDigestSelectionProbability key message state.1 *
          ((Fintype.card Index : ENNReal)⁻¹ * reuseRawEnvelope key reuse budget signatures state ∅ required) *
            targetCertificateScale required := by
  apply expected_bankedCacheWeight_step_le
  · intro result hr
    exact logTracedMappedAdversaryImpl_cache_le key (.inr message) state result hr
  · intro result _ query hcertificate
    exact one_le_targetCertificateEntry_of_certificate key reuse budget signatures required result.2 query
      (of_decide_eq_true hcertificate)
  · intro query target
    simp only [targetCertificateForecast, ← mul_assoc, ENNReal.tsum_mul_right]
    exact mul_le_mul' (expected_logTraced_sign_reuseTarget_le key reuse budget (payloadOf query) target
      signatures state hsigned message hreuse ∅ required (empty_targetShapeValid required)) le_rfl
  · have h := expected_logTraced_sign_reuseNewTarget_le_mass_mul key reuse budget signatures state hsigned message
      ∅ required (empty_targetShapeValid required)
    simpa only [newTargetCertificateForecast_eq, ← mul_assoc, ENNReal.tsum_mul_right] using
      mul_le_mul' h (le_refl (targetCertificateScale required))

end SphincsSecurity.Concrete

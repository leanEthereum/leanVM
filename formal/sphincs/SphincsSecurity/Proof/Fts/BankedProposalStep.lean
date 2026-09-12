import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.BankedTargetEnvelope
import SphincsSecurity.Proof.Fts.OriginalProposalExecution
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

def proposalRecordLogState (input : (OracleWorld + SigningSpec).Domain) (log : QueryLog SigningSpec)
    (record : ProposalExecutionRecord input) : CoverLogState :=
  (record.cache, log ++ signingLogFragment input record.output)

private theorem expected_pmfLift {α : Type} (computation : ProbComp α) (weight : α → ENNReal) :
    (∑' result, Pr[= result | (liftM computation : PMF α)] * weight result) =
      ∑' result, Pr[= result | computation] * weight result := rfl

private theorem expected_pmf_mono_of_support {α : Type} (law : PMF α) (first second : α → ENNReal)
    (hle : ∀ result ∈ law.support, first result ≤ second result) :
    (∑' result, Pr[= result | law] * first result) ≤ ∑' result, Pr[= result | law] * second result := by
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (hle result hr)
  · have hp : Pr[= result | law] = 0 := by
      rw [PMF.probOutput_eq_apply, PMF.apply_eq_zero_iff]
      exact hr
    rw [hp, zero_mul, zero_mul]

theorem originalAdversaryPMFImpl_run (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) :
    (originalAdversaryPMFImpl key input).run cache =
      (liftM ((unloggedMappedAdversaryImpl key input).run cache) : PMF _) := by
  rw [originalAdversaryPMFImpl, pmfSumImpl_eq_lift_add, originalAdversaryImpl_split]
  rfl

theorem expected_originalProposalRecord_logged (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : CoverLogState) (weight : CoverLogState → ENNReal) :
    (∑' record, Pr[= record | originalProposalRecord key input state.1] *
      weight (proposalRecordLogState input state.2 record)) =
      ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key input).run state] * weight result.2 := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  have h := congrArg (fun computation : PMF ((OracleWorld + SigningSpec).Range input × QueryCache HashSpec) =>
    ∑' result, Pr[= result | computation] * weight (result.2, state.2 ++ signingLogFragment input result.1))
      (originalProposalRecord_project key input state.1)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul, originalAdversaryPMFImpl_run, expected_pmfLift] at h
  exact h

theorem originalProposalRecord_world_hashCalls (key : SecretKey) (input : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (record : ProposalExecutionRecord (.inl input))
    (hr : record ∈ (originalProposalRecord key (.inl input) cache).support) :
    record.trace.hashCalls = signingExecutionHashCost (.inl input) := by
  rw [originalProposalRecord, PMF.mem_support_map_iff] at hr
  obtain ⟨result, _, rfl⟩ := hr
  cases input with
  | inl sample => rfl
  | inr input => rfl

noncomputable def bankedProposalRecordValue (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool)
    (input : (OracleWorld + SigningSpec).Domain) (record : ProposalExecutionRecord input) (stopped : Bool) : ENNReal :=
  let after := proposalRecordLogState input state.2 record
  bankedTargetEnvelope key reuse (budget - record.trace.hashCalls) signatures required after
    (completedTargetBank key required after bank) stopped

theorem expected_originalProposalRecord_world_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (input : OracleWorld.Domain)
    (stopped : ProposalExecutionRecord (.inl input) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hcost : signingExecutionHashCost (.inl input) ≤ budget) :
    (∑' record, Pr[= record | originalProposalRecord key (.inl input) state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inl input) record (stopped record)) ≤
      bankedTargetEnvelope key reuse budget signatures required state bank false +
        targetCreationMultiplier key state.1 (.inl input) * targetCreationPrice key reuse budget signatures required state := by
  let afterBudget := budget - signingExecutionHashCost (.inl input)
  let weight := fun current => bankedTargetEnvelope key reuse afterBudget signatures required current
    (completedTargetBank key required current bank) false
  have hstep := expected_logTraced_world_bankedTarget_le key reuse afterBudget signatures required state bank input
    (fun _ => false) hsigned
  have hrestore : afterBudget + signingExecutionHashCost (.inl input) = budget := Nat.sub_add_cancel hcost
  rw [hrestore] at hstep
  calc
    _ ≤ ∑' record, Pr[= record | originalProposalRecord key (.inl input) state.1] *
        weight (proposalRecordLogState (.inl input) state.2 record) := by
      apply expected_pmf_mono_of_support
      intro record hr
      have hc := originalProposalRecord_world_hashCalls key input state.1 record hr
      dsimp only [bankedProposalRecordValue, weight, afterBudget]
      rw [hc]
      exact bankedCacheWeight_discard_le _ _ _ _ _
    _ = ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] * weight result.2 :=
      expected_originalProposalRecord_logged key (.inl input) state weight
    _ ≤ bankedTargetEnvelope key reuse budget signatures required state bank false +
        targetCreationMultiplier key state.1 (.inl input) * targetCreationPrice key reuse afterBudget signatures required state := by
      simpa only [targetCreationMultiplier, targetCreationPrice, mul_assoc] using hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_budget_mono key reuse signatures required state (Nat.sub_le _ _)))

theorem expected_originalProposalRecord_sign_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : ProposalExecutionRecord (.inr message) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' record, Pr[= record | originalProposalRecord key (.inr message) state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) record (stopped record)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state := by
  let weight := fun current => bankedTargetEnvelope key reuse budget signatures required current
    (completedTargetBank key required current bank) false
  have hstep := expected_logTraced_sign_bankedTarget_le key reuse budget signatures required state bank message
    (fun _ => false) hsigned hreuse
  rw [← targetCreationMultiplier_sign_mul_price] at hstep
  calc
    _ ≤ ∑' record, Pr[= record | originalProposalRecord key (.inr message) state.1] *
        weight (proposalRecordLogState (.inr message) state.2 record) := by
      apply ENNReal.tsum_le_tsum
      intro record
      apply mul_le_mul' le_rfl
      exact (bankedCacheWeight_discard_le _ _ _ _ _).trans
        (bankedTargetEnvelope_budget_mono key reuse signatures required _ _ false (Nat.sub_le _ _))
    _ = ∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] * weight result.2 :=
      expected_originalProposalRecord_logged key (.inr message) state weight
    _ ≤ bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget signatures required state := hstep
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (targetCreationPrice_signatures_mono key reuse budget required state (Nat.le_succ _)))

theorem expected_coupled_bankedProposalRecord_le {α : Type}
    (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat) (required : Finset FtsTree)
    (state : CoverLogState) (bank : HashInput → Bool) (input : (OracleWorld + SigningSpec).Domain)
    (law : PMF α) (record : α → ProposalExecutionRecord input) (stopped : α → Bool) (bound : ENNReal)
    (hrecord : law.map record = originalProposalRecord key input state.1)
    (hbound : (∑' result, Pr[= result | originalProposalRecord key input state.1] *
      bankedProposalRecordValue key reuse budget signatures required state bank input result false) ≤ bound) :
    (∑' result, Pr[= result | law] *
      bankedProposalRecordValue key reuse budget signatures required state bank input (record result) (stopped result)) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        bankedProposalRecordValue key reuse budget signatures required state bank input (record result) false := by
      apply ENNReal.tsum_le_tsum
      intro result
      exact mul_le_mul' le_rfl (bankedCacheWeight_discard_le _ _ _ _ _)
    _ = ∑' result, Pr[= result | originalProposalRecord key input state.1] *
        bankedProposalRecordValue key reuse budget signatures required state bank input result false := by
      rw [← hrecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    _ ≤ bound := hbound

theorem expected_lengthBridge_sign_banked_le (key : SecretKey) (reuse : ENNReal) (budget signatures : Nat)
    (required : Finset FtsTree) (state : CoverLogState) (bank : HashInput → Bool) (message : Message)
    (stopped : Nat × ProposalExecutionRecord (.inr message) → Bool)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse) :
    (∑' result, Pr[= result | recordLengthBridge (originalProposalRecord key (.inr message) state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le] *
      bankedProposalRecordValue key reuse budget signatures required state bank (.inr message) result.2 (stopped result)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required state bank false +
        targetCreationMultiplier key state.1 (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required state :=
  expected_coupled_bankedProposalRecord_le key reuse budget signatures required state bank (.inr message)
    _ Prod.snd stopped _ (recordLengthBridge_record _ _ _ _)
    (expected_originalProposalRecord_sign_banked_le key reuse budget signatures required state bank message
      (fun _ => false) hsigned hreuse)

end SphincsSecurity.Concrete

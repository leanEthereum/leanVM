import SphincsSecurity.Proof.Fts.OriginalCacheExceptionBound
import SphincsSecurity.Proof.Fts.ProposalPrefixExponential
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme certificateLengthImpl certificateProposalImpl certificateCacheProposalImpl proposalPrefixWeight

private theorem certificateMonitorUpdate_log_cap (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord input) (hcap : state.2.log.length ≤ signatureLimit) :
    (certificateMonitorUpdate key budget required stopAfter input state length record).log.length ≤ signatureLimit := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · rw [certificateMonitorUpdate, if_pos hactive]
    have hvalid := hactive.2.2.1
    cases input <;>
      simp only [proposalRecordLogState, signingLogFragment, List.append_nil, List.length_append, List.length_singleton,
        ValidSigningStep] at hvalid ⊢ <;> omega
  · simpa only [certificateMonitorUpdate, if_neg hactive] using hcap

private theorem certificateMonitorUpdate_world_prefixWeight (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : OracleWorld.Domain) (state : CertificateMonitorState)
    (record : ProposalExecutionRecord (.inl input)) :
    proposalPrefixWeight (certificateMonitorUpdate key budget required stopAfter (.inl input) state 0 record).proposals
      (certificateMonitorUpdate key budget required stopAfter (.inl input) state 0 record).log.length =
        proposalPrefixWeight state.2.proposals state.2.log.length := by
  rw [certificateMonitorUpdate]
  split <;> simp only [proposalRecordLogState, signingLogFragment, List.append_nil, Nat.add_zero]

private theorem certificateMonitorUpdate_sign_prefixWeight (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (message : Message) (state : CertificateMonitorState)
    (length : Nat) (record : ProposalExecutionRecord (.inr message))
    (hactive : CertificateMonitorActive key budget (.inr message) state) :
    proposalPrefixWeight (certificateMonitorUpdate key budget required stopAfter (.inr message) state length record).proposals
      (certificateMonitorUpdate key budget required stopAfter (.inr message) state length record).log.length =
        proposalPrefixWeight (state.2.proposals + length) (state.2.log.length + 1) := by
  simp only [certificateMonitorUpdate, if_pos hactive, proposalRecordLogState, signingLogFragment,
    List.length_append, List.length_singleton]

theorem expected_certificateLengthImpl_prefixWeight (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (certificateLengthImpl key budget required stopAfter input).run state] *
      proposalPrefixWeight result.2.2.proposals result.2.2.log.length) = proposalPrefixWeight state.2.proposals state.2.log.length := by
  cases input with
  | inl input =>
      rw [certificateLengthImpl_world_run, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
      simp only [originalProposalAdvance, certificateMonitorUpdate_world_prefixWeight, ENNReal.tsum_mul_right,
        tsum_probOutput_of_liftM_PMF, one_mul]
  | inr message =>
      by_cases hactive : CertificateMonitorActive key budget (.inr message) state
      · rw [certificateLengthImpl_sign_run, if_pos hactive, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [originalProposalAdvance, certificateMonitorUpdate_sign_prefixWeight key budget required stopAfter message state _ _ hactive]
        have h := congrArg (fun law : PMF Nat => ∑' length, Pr[= length | law] *
          proposalPrefixWeight (state.2.proposals + length) (state.2.log.length + 1))
          (recordLengthBridge_length (originalProposalRecord key (.inr message) state.1)
            targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
        rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
        simp only [PMF.probOutput_eq_apply] at h
        simpa only [PMF.probOutput_eq_apply] using h.trans
          (expected_proposalPrefixWeight state.2.proposals state.2.log.length hactive.2.2.1)
      · rw [certificateLengthImpl_inactive_run key budget required stopAfter (.inr message) state hactive,
          ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        simp only [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_certificateLength_prefixWeight {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateMonitorState) :
    (∑' result, Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] *
      proposalPrefixWeight result.2.2.proposals result.2.2.log.length) = proposalPrefixWeight state.2.proposals state.2.log.length := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      simp only [ih]
      exact expected_certificateLengthImpl_prefixWeight key budget required stopAfter input state

theorem certificateLength_log_cap {Result : Type} (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateMonitorState) (hcap : state.2.log.length ≤ signatureLimit) (result : Result × CertificateMonitorState)
    (hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support) :
    result.2.2.log.length ≤ signatureLimit := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
      subst result
      exact hcap
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      obtain ⟨length, record, _, rfl⟩ := certificateLengthImpl_support key budget required stopAfter input state middle hm
      exact ih record.output _ (certificateMonitorUpdate_log_cap key budget required stopAfter input state length record hcap) result hr

theorem certificateLength_prefix_le {Result : Type} (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : CertificateMonitorState) (hcap : state.2.log.length ≤ signatureLimit) :
    Pr[fun result => ProposalPrefixExceptional result.2.2.proposals result.2.2.log.length |
      (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state] ≤
      proposalPrefixWeight state.2.proposals state.2.log.length := by
  rw [← expected_certificateLength_prefixWeight key budget required stopAfter computation state, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ ((simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state).support
  · by_cases hb : ProposalPrefixExceptional result.2.2.proposals result.2.2.log.length
    · rw [if_pos hb]
      simpa only [mul_one] using mul_le_mul' (le_refl
        (Pr[= result | (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state]))
        (proposalPrefixWeight_bad _ _ (certificateLength_log_cap key budget required stopAfter computation state hcap result hr) hb)
    · rw [if_neg hb]
      exact bot_le
  · have hz : (simulateQ (certificateLengthImpl key budget required stopAfter) computation).run state result = 0 := by
      simpa only [PMF.mem_support_iff, not_not] using hr
    simp only [PMF.probOutput_eq_apply, hz, ite_self, zero_mul, le_refl]

theorem certificateCacheProposal_prefix_le {Result : Type} (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : List Index × CertificateCacheMonitorState) (hcap : state.2.2.1.log.length ≤ signatureLimit) :
    Pr[fun result => ProposalPrefixExceptional result.2.2.2.1.proposals result.2.2.2.1.log.length |
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state] ≤
      proposalPrefixWeight state.2.2.1.proposals state.2.2.1.log.length := by
  have h := certificateLength_prefix_le key budget required stopAfter computation (certificateCacheMonitorProject state.2) hcap
  rw [← simulateQ_certificateProposalImpl_length key budget required stopAfter computation
    (state.1, certificateCacheMonitorProject state.2), probEvent_map] at h
  rw [← simulateQ_certificateCacheProposalImpl_project key budget required stopAfter computation state, probEvent_map] at h
  exact h

theorem certificateContextGame_prefix_le (adversary : Adversary) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
      certificateContextGame adversary budget required stopAfter stopped] ≤ (2 ^ 700 : ENNReal)⁻¹ := by
  rw [certificateContextGame, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] * proposalPrefixWeight 0 0 := by
      apply ENNReal.tsum_le_tsum
      intro generated
      apply mul_le_mul' le_rfl
      have h := certificateCacheProposal_prefix_le generated.1.1.2 budget required (stopAfter generated.1.1.2)
        (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
        ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) (Nat.zero_le _)
      simpa only [bind_pure_comp, probEvent_map, initialCertificateMonitor, List.length_nil, Function.comp_def] using h
    _ = proposalPrefixWeight 0 0 := by rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
    _ ≤ _ := proposalPrefixWeight_initial_le

theorem original_primitive_add_full_certificate_small_budget (dummy : OtsReferenceWords)
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ 3 * 2 ^ 114) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      (2 ^ 700 : ENNReal)⁻¹ :=
  (original_primitive_add_full_certificate_le_small_budget_add_prefix dummy adversary q hbound hsmall).trans
    (add_le_add le_rfl (certificateContextGame_prefix_le adversary q Finset.univ (fun _ => proposalPrefixStop) false))

end SphincsSecurity.Concrete

import SphincsSecurity.Proof.Fts.OriginalMessageAllocation
import SphincsSecurity.Proof.Reference.ReferencePrimitiveBound
import SphincsSecurity.Proof.Fts.CertificateCacheExceptionKernels
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] scheme certificateCacheExceptionWeight expectedBoundaryMessageCalls
  certificateCacheLengthImpl certificateLengthImpl certificateCacheProposalImpl

noncomputable def originalCacheHistoryWeight (key : SecretKey) (state : CertificateCacheMonitorState) : ENNReal :=
  if state.2.2 then 1 else certificateCacheExceptionWeight key state.1

private theorem probOutput_probCompLift {Result : Type} (computation : ProbComp Result) (result : Result) :
    Pr[= result | (liftM computation : PMF Result)] = Pr[= result | computation] := rfl

theorem expected_certificateCacheLengthImpl_of_record_function (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (counter : CertificateCacheMonitorState → ENNReal) (weight : ProposalExecutionRecord input → ENNReal)
    (hadvance : ∀ length record, counter
      (originalProposalAdvance (certificateCacheMonitorUpdate key budget required stopAfter) input state length record) = weight record) :
    (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] * counter result.2) =
      ∑' record, Pr[= record | originalProposalRecord key input state.1] * weight record := by
  simp only [certificateCacheLengthImpl, originalLengthImpl, lengthRecordImpl, StateT.run_mk]
  split
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]
    have h := congrArg (fun law : PMF (ProposalExecutionRecord input) =>
      ∑' record, Pr[= record | law] * weight record)
      (recordLengthBridge_record (originalProposalRecord key input state.1)
        targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le)
    rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
    exact h
  · rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
    simp only [hadvance]

theorem certificateCacheLengthImpl_original_cache (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState) :
    (fun result => (result.1, result.2.1)) <$> (certificateCacheLengthImpl key budget required stopAfter input).run state =
      (liftM ((simulateQ romImpl (expandedAdversaryImpl key input)).run state.1) : PMF _) := by
  have h := congrArg (Functor.map (fun result => (result.1, result.2.1)))
    (certificateCacheLengthImpl_project key budget required stopAfter input state)
  simp only [Functor.map_map] at h
  exact h.trans (certificateLengthImpl_original_cache key budget required stopAfter input (certificateCacheMonitorProject state))

theorem certificateCacheLengthImpl_finite (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) (result : (OracleWorld + SigningSpec).Range input × CertificateCacheMonitorState)
    (hr : result ∈ ((certificateCacheLengthImpl key budget required stopAfter input).run state).support) :
    Finite result.2.1 := by
  have hm := (PMF.mem_support_map_iff (fun result => (result.1, result.2.1)) _ _).mpr ⟨result, hr, rfl⟩
  rw [← PMF.monad_map_eq_map, certificateCacheLengthImpl_original_cache, probCompLift_support] at hm
  exact finite_cache_of_mem_support (expandedAdversaryImpl key input) state.1 result.1 result.2.1 hm hfinite

theorem expected_originalProposalRecord_cacheWeight (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' record, Pr[= record | originalProposalRecord key input cache] * certificateCacheExceptionWeight key record.cache) ≤
      certificateCacheExceptionWeight key cache +
        expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) cache * certificateCacheExceptionRate := by
  have h := congrArg (fun law => ∑' result, Pr[= result | law] * certificateCacheExceptionWeight key result.2)
    (originalProposalRecord_boundary key input cache)
  rw [← PMF.monad_map_eq_map, tsum_probOutput_map_mul] at h
  simp only [probOutput_probCompLift] at h
  rw [expectedBoundaryMessageCalls]
  exact h.le.trans (expected_certificateCacheExceptionWeight_boundary key (expandedAdversaryImpl key input) cache hfinite)

theorem expected_originalCacheHistoryWeight_step (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : (OracleWorld + SigningSpec).Domain) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) :
    (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
      originalCacheHistoryWeight key result.2) ≤ originalCacheHistoryWeight key state +
        expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) state.1 * certificateCacheExceptionRate := by
  rw [expected_certificateCacheLengthImpl_of_record_function key budget required stopAfter input state
    (originalCacheHistoryWeight key)
    (fun record => if state.2.2 || decide (CertificateCacheExceptional key state.1) ||
      decide (CertificateCacheExceptional key record.cache) then 1 else certificateCacheExceptionWeight key record.cache)
    (fun _ _ => rfl)]
  by_cases hhit : state.2.2 = true
  · simp only [hhit, Bool.true_or, if_true, mul_one, tsum_probOutput_of_liftM_PMF, originalCacheHistoryWeight]
    exact le_self_add
  · by_cases hbad : CertificateCacheExceptional key state.1
    · simp only [hbad, decide_true, Bool.or_true, Bool.true_or, if_true, mul_one, tsum_probOutput_of_liftM_PMF,
        originalCacheHistoryWeight, hhit, Bool.false_eq_true, if_false]
      exact (certificateCacheExceptionWeight_bad key state.1 hfinite hbad).trans le_self_add
    · simp only [hhit, Bool.false_or, hbad, decide_false, originalCacheHistoryWeight]
      apply le_trans _ (expected_originalProposalRecord_cacheWeight key input state.1 hfinite)
      apply ENNReal.tsum_le_tsum
      intro record
      by_cases hr : record ∈ (originalProposalRecord key input state.1).support
      · apply mul_le_mul' le_rfl
        split_ifs with hbadRecord
        · have hb := originalProposalRecord_boundary_support key input state.1 record hr
          have hm : (record.output, record.cache) ∈ support ((simulateQ romImpl (expandedAdversaryImpl key input)).run state.1) := by
            rw [← boundaryRun_forget key.parameter (expandedAdversaryImpl key input) state.1, support_map]
            exact ⟨((record.output, record.trace), record.cache), hb, rfl⟩
          exact certificateCacheExceptionWeight_bad key record.cache
            (finite_cache_of_mem_support (expandedAdversaryImpl key input) state.1 record.output record.cache hm hfinite)
            (of_decide_eq_true hbadRecord)
        · exact le_rfl
      · have hz : originalProposalRecord key input state.1 record = 0 := by
          simpa only [PMF.mem_support_iff, not_not] using hr
        rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]

theorem expected_originalCacheHistoryWeight_run {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) :
    (∑' result, Pr[= result | (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state] *
      originalCacheHistoryWeight key result.2) ≤ originalCacheHistoryWeight key state +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.1 *
          certificateCacheExceptionRate := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, expectedBoundaryMessageCalls_pure,
        zero_mul, add_zero, le_refl]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul,
        simulateQ_bind, simulateQ_spec_query, expectedBoundaryMessageCalls_bind]
      have hproject := congrArg (fun law => ∑' result, Pr[= result | law] *
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2)
        (certificateCacheLengthImpl_original_cache key budget required stopAfter input state)
      rw [tsum_probOutput_map_mul] at hproject
      simp only [probOutput_probCompLift] at hproject
      calc
        _ ≤ ∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
            (originalCacheHistoryWeight key result.2 +
              expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1 *
                certificateCacheExceptionRate) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ ((certificateCacheLengthImpl key budget required stopAfter input).run state).support
          · exact mul_le_mul' le_rfl (ih result.1 result.2
              (certificateCacheLengthImpl_finite key budget required stopAfter input state hfinite result hr))
          · have hz : (certificateCacheLengthImpl key budget required stopAfter input).run state result = 0 := by
              simpa only [PMF.mem_support_iff, not_not] using hr
            rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
        _ = (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
              originalCacheHistoryWeight key result.2) +
            (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
              expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1) *
                certificateCacheExceptionRate := by
          simp only [mul_add, ENNReal.tsum_add, ← mul_assoc, ENNReal.tsum_mul_right]
        _ ≤ (originalCacheHistoryWeight key state +
              expectedBoundaryMessageCalls key.parameter (expandedAdversaryImpl key input) state.1 * certificateCacheExceptionRate) +
            (∑' result, Pr[= result | (certificateCacheLengthImpl key budget required stopAfter input).run state] *
              expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) (next result.1)) result.2.1) *
                certificateCacheExceptionRate :=
          add_le_add (expected_originalCacheHistoryWeight_step key budget required stopAfter input state hfinite) le_rfl
        _ = _ := by rw [hproject]; ring

theorem certificateCacheLength_hit_le_message_cost {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : CertificateCacheMonitorState)
    (hfinite : Finite state.1) :
    Pr[fun result => result.2.2.2 = true |
      (simulateQ (certificateCacheLengthImpl key budget required stopAfter) computation).run state] ≤
      originalCacheHistoryWeight key state +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.1 *
          certificateCacheExceptionRate := by
  apply le_trans _ (expected_originalCacheHistoryWeight_run key budget required stopAfter computation state hfinite)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hhit : result.2.2.2 = true
  · simp only [hhit, if_true, originalCacheHistoryWeight, mul_one, le_refl]
  · simp only [hhit]
    exact bot_le

theorem certificateCacheProposal_hit_le_message_cost {Result : Type} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : List Index × CertificateCacheMonitorState)
    (hfinite : Finite state.2.1) :
    Pr[fun result => result.2.2.2.2 = true |
      (simulateQ (certificateCacheProposalImpl key budget required stopAfter) computation).run state] ≤
      originalCacheHistoryWeight key state.2 +
        expectedBoundaryMessageCalls key.parameter (simulateQ (expandedAdversaryImpl key) computation) state.2.1 *
          certificateCacheExceptionRate := by
  have h := certificateCacheLength_hit_le_message_cost key budget required stopAfter computation state.2 hfinite
  rw [← simulateQ_certificateCacheProposalImpl_length key budget required stopAfter computation state, probEvent_map] at h
  exact h

private theorem expected_probCompLift_of_map_eq {Source Result : Type}
    (source : ProbComp Source) (result : ProbComp Result) (project : Source → Result)
    (hproject : project <$> source = result) (cost : Result → ENNReal) :
    (∑' value, Pr[= value | (liftM source : PMF Source)] * cost (project value)) =
      ∑' value, Pr[= value | result] * cost value := by
  rw [← hproject, tsum_probOutput_map_mul]
  simp only [probOutput_probCompLift]

theorem certificateContextGame_cache_hit_le_original_message (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => result.2.2.2.2.2 = true | certificateContextGame adversary budget required stopAfter stopped] ≤
      originalCertificateMessageCost adversary * certificateCacheExceptionRate := by
  rw [certificateContextGame, probEvent_bind_eq_tsum]
  calc
    _ ≤ ∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        (expectedBoundaryMessageCalls generated.1.1.2.parameter
          (simulateQ (expandedAdversaryImpl generated.1.1.2)
            (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)) generated.2 * certificateCacheExceptionRate) := by
      apply ENNReal.tsum_le_tsum
      intro generated
      by_cases hg : generated ∈ (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _).support
      · have hb : generated ∈ support (boundaryRun 0 scheme.keygen ∅) := (probCompLift_support _ ▸ hg)
        have hn : (generated.1.1, generated.2) ∈ support ((simulateQ romImpl scheme.keygen).run ∅) := by
          rw [← boundaryRun_forget 0 scheme.keygen ∅, support_map]
          exact ⟨generated, hb, rfl⟩
        have hf := finite_cache_of_mem_support scheme.keygen ∅ generated.1.1 generated.2 hn finite_empty
        have hzero : originalCacheHistoryWeight generated.1.1.2
            (generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) = 0 := by
          rw [originalCacheHistoryWeight, if_neg Bool.false_ne_true]
          exact certificateCacheExceptionWeight_initial generated.1.1.2 generated.2
            (keygen_cache_message_none (generated.1.1, generated.2) hn)
        have h := certificateCacheProposal_hit_le_message_cost generated.1.1.2 budget required
          (stopAfter generated.1.1.2) (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)
          ([], generated.2, initialCertificateMonitor generated.1.2.hashCalls stopped, false) hf
        rw [hzero, zero_add] at h
        apply mul_le_mul' le_rfl
        simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using h
      · have hz : (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _) generated = 0 := by
          simpa only [PMF.mem_support_iff, not_not] using hg
        rw [PMF.probOutput_eq_apply, hz, zero_mul, zero_mul]
    _ = (∑' generated, Pr[= generated | (liftM (boundaryRun 0 scheme.keygen ∅) : PMF _)] *
        expectedBoundaryMessageCalls generated.1.1.2.parameter
          (simulateQ (expandedAdversaryImpl generated.1.1.2)
            (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1.1)) generated.2) * certificateCacheExceptionRate := by
      simp only [← mul_assoc, ENNReal.tsum_mul_right]
    _ = _ := by
      apply congrArg (· * certificateCacheExceptionRate)
      exact expected_probCompLift_of_map_eq (boundaryRun 0 scheme.keygen ∅)
        ((simulateQ romImpl scheme.keygen).run ∅) (fun result => (result.1.1, result.2))
        (boundaryRun_forget 0 scheme.keygen ∅) (fun generated =>
          expectedBoundaryMessageCalls generated.1.2.parameter
            (simulateQ (expandedAdversaryImpl generated.1.2)
              (FtsProbeSimulation.retainedGameRestComputation adversary generated.1.1)) generated.2)

theorem certificateContextGame_exception_le_cache_add_prefix (adversary : Adversary) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : SecretKey → CertificateStopRule) (stopped : Bool) :
    Pr[fun result => CertificateGameExceptional result.2 | certificateContextGame adversary budget required stopAfter stopped] ≤
      Pr[fun result => result.2.2.2.2.2 = true | certificateContextGame adversary budget required stopAfter stopped] +
      Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
        certificateContextGame adversary budget required stopAfter stopped] :=
  probEvent_or_le (certificateContextGame adversary budget required stopAfter stopped) _ _

theorem originalCertificateSource_full_le_original_message_add_prefix (adversary : Adversary) (q : Nat)
    (hbudget : q ≤ 2 ^ 127) (hbound : HasHashQueryBound scheme adversary q) :
    Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      ((2 ^ 128 : ENNReal)⁻¹ + certificateCacheExceptionRate) * originalCertificateMessageCost adversary +
      (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  have he := (certificateContextGame_exception_le_cache_add_prefix adversary q Finset.univ (fun _ => proposalPrefixStop) false).trans
    (add_le_add (certificateContextGame_cache_hit_le_original_message adversary q Finset.univ (fun _ => proposalPrefixStop) false) le_rfl)
  apply (originalCertificateSource_full_le_original_message_add_exception adversary q hbudget hbound).trans
  calc
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * originalCertificateMessageCost adversary + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
        (originalCertificateMessageCost adversary * certificateCacheExceptionRate +
          Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
            certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false]) := add_le_add le_rfl he
    _ = _ := by ring

theorem original_primitive_add_full_certificate_le_small_budget_add_prefix (dummy : OtsReferenceWords)
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ 3 * 2 ^ 114) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      Pr[OriginalFullCertificate | originalCertificateSource adversary] ≤
      (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
        certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false] := by
  have hbudget : q ≤ 2 ^ 127 := hsmall.trans (by norm_num)
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hp := referenceGraphContextGame_primitive_small_budget dummy adversary q hbound hsmall
  rw [hcard] at hp
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hp
  have hrate : (2 ^ 128 : ENNReal)⁻¹ + certificateCacheExceptionRate ≤ (7 / 4 : ENNReal) / 2 ^ 128 := by
    apply (add_le_add le_rfl certificateCacheExceptionRate_le).trans
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]
  have hc := (originalCertificateSource_full_le_original_message_add_prefix adversary q hbudget hbound).trans
    (add_le_add (add_le_add (mul_le_mul' hrate (originalCertificateMessageCost_le_referenceRecorded dummy adversary)) le_rfl) le_rfl)
  calc
    _ ≤ Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
        (((7 / 4 : ENNReal) / 2 ^ 128) *
          (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
            (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal)) +
          (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
          Pr[fun result => ProposalPrefixExceptional result.2.2.2.2.1.proposals result.2.2.2.2.1.log.length |
            certificateContextGame adversary q Finset.univ (fun _ => proposalPrefixStop) false]) := add_le_add le_rfl hc
    _ ≤ _ := by
      rw [← add_assoc, ← add_assoc]
      exact add_le_add (add_le_add hp le_rfl) le_rfl

end SphincsSecurity.Concrete

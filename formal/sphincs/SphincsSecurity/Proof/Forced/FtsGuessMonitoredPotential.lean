import SphincsSecurity.Proof.Forced.FtsGuessMonitoredValid
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State environment)
open RetainedResidual (proposalOfSigningRecord proposalOfWorldResult signingAnnotation worldMonitorValue completedSigningBankValue)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitorView_fst (state : MonitoredState) : (monitorView state).1 = state.1.1 := rfl

/-! ### World steps -/

theorem monitorView_snd (state : MonitoredState) : (monitorView state).2 = state.2 := rfl

theorem expected_monitoredWorldStep_potential_le (input : OracleWorld.Domain) (state : MonitoredState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) :
    (∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] *
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        certificateMonitorCharge (monitorKey parameter root) budget required (.inl input) (monitorView state) := by
  have hweight : (∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot
      budget required stopAfter input state] * certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) =
      ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (worldProgram parameter labels input) state.1] *
        worldMonitorValue (monitorKey parameter root) budget required stopAfter input (monitorView state) 0 (some result.1, result.2.1) := by
    rw [monitoredWorldStep, tsum_probOutput_map_mul]
    rfl
  rw [hweight]
  have hpointwise (hcache : ∀ result, cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels input) state.1 result ≠ 0 → messageAnswers parameter result.2.1 = messageAnswers parameter state.1.1) :
      (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (worldProgram parameter labels input) state.1] *
        worldMonitorValue (monitorKey parameter root) budget required stopAfter input (monitorView state) 0 (some result.1, result.2.1)) ≤
        certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) := by
    calc
      _ ≤ ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
          (worldProgram parameter labels input) state.1] *
          certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) := by
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
            (worldProgram parameter labels input) state.1] = 0
        · simp only [hr, zero_mul, le_refl]
        · apply mul_le_mul' le_rfl
          rw [SPMF.probOutput_eq_apply] at hr
          exact RetainedResidual.worldMonitorValue_le_of_messageHistory (monitorKey parameter root) budget required stopAfter input
            (monitorView state) 0 (some result.1, result.2.1) (hcache result hr)
      _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one
  cases input with
  | inl sample =>
      refine (hpointwise fun result hr => ?_).trans le_self_add
      rw [cachedForcedRun_world_unif'] at hr
      obtain ⟨answer, _, heq⟩ := map_nonzero_source' _ _ _ hr
      rw [heq]
  | inr hash =>
      have hin : hash ∈ inputs := hinputs (by simpa only [bind_pure] using mem_hashInputs_hash_bind hash pure)
      by_cases hmessage : MessageHashInput parameter hash
      · rw [cachedForcedRun_world_message' parameter root otsSecret labels inputs hencoding selections rows dummy slot hash hin hmessage state.1,
          tsum_probOutput_map_mul]
        by_cases hactive : CertificateMonitorActive (monitorKey parameter root) budget (.inl (.inr hash)) (monitorView state)
        · have hbound := expected_originalProposalRecord_world_banked_le (monitorKey parameter root) nearUniformDigestReuseWeight
            (budget - state.2.spent) (signatureLimit - state.2.log.length) required (certificateMonitorCoverState (monitorView state))
            state.2.bank (.inr hash) (fun _ => false) hactive.2.1.1 hactive.2.2.2
          calc
            _ ≤ ∑' result, Pr[= result | 𝒟[(romImpl (.inr hash)).run state.1.1]] *
                bankedProposalRecordValue (monitorKey parameter root) nearUniformDigestReuseWeight (budget - state.2.spent)
                  (signatureLimit - state.2.log.length) required (certificateMonitorCoverState (monitorView state)) state.2.bank
                  (.inl (.inr hash)) (proposalOfWorldResult (monitorKey parameter root).parameter (.inr hash) (result.1, result.2)) false := by
              apply ENNReal.tsum_le_tsum
              intro result
              apply mul_le_mul' le_rfl
              simp only [worldMonitorValue, Option.elim_some,
                certificateMonitorPotential_advance_active (monitorKey parameter root) budget required stopAfter (.inl (.inr hash))
                  (monitorView state) _ _ hactive, signingLogFragment, List.append_nil]
              exact bankedCacheWeight_discard_le _ _ _ _ _
            _ = ∑' record, Pr[= record | originalProposalRecord (monitorKey parameter root) (.inl (.inr hash)) (monitorView state).1] *
                bankedProposalRecordValue (monitorKey parameter root) nearUniformDigestReuseWeight (budget - state.2.spent)
                  (signatureLimit - state.2.log.length) required (certificateMonitorCoverState (monitorView state)) state.2.bank
                  (.inl (.inr hash)) record false := by
              rw [originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
              rfl
            _ ≤ _ := by
              have hlive : state.2.stopped = false := hactive.1
              simpa only [certificateMonitorPotential, certificateMonitorCoverState, monitorView_fst, monitorView_snd, hlive,
                certificateMonitorCharge, if_pos hactive] using hbound
        · simp only [worldMonitorValue, Option.elim_some, certificateMonitorCharge, if_neg hactive, add_zero,
            certificateMonitorPotential_advance_inactive (monitorKey parameter root) budget required stopAfter (.inl (.inr hash))
              (monitorView state) _ _ hactive, ENNReal.tsum_mul_right]
          exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)
      · refine (hpointwise fun result hr => ?_).trans le_self_add
        have hsupport := cachedForcedRun_world_hash_support' parameter root otsSecret labels inputs hencoding selections rows dummy slot
          hash state.1 result hr
        exact messageAnswers_eq_of_cache_of_ne parameter state.1.1 result.2.1 hash hmessage hsupport.1

/-! ### Signing steps -/

def secretLabels (secrets : Coordinate → Digest) : CanonicalProbeRouting.Labels
  | .ftsStart index tree leaf => secrets (index, tree, leaf)
  | .otsStart _ _ _ _ => 0
  | .graph _ => 0

theorem publicSigningWork_bank_digest (key : SecretKey) (known : CanonicalProbeRouting.Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (actual : CanonicalProbeRouting.Labels) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1).1, result.2)) <$>
      𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache] =
        RetainedResidual.digestCompletionValue known words selections actual <$>
          𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] := by
  rw [simulateQ_map, StateT.run_map, evalDist_map, Functor.map_map]
  exact publicSigningWork_complete_digest key known words selections actual message cache

theorem expected_publicSigningWork_bank_le (key : SecretKey) (known : CanonicalProbeRouting.Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (actual : CanonicalProbeRouting.Labels) (message : Message) (reuse : ENNReal)
    (budget signatures : Nat) (required : Finset FtsTree) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (bank : HashInput → Bool) (hsigned : SigningDigestsCached key.parameter cache key.root log)
    (hreuse : exactDigestReuseWeight key message cache ≤ reuse) :
    (∑' result, Pr[= result | 𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork key.parameter key.root known words
        selections message)).run cache]] *
      completedSigningBankValue key reuse budget signatures required log bank message
        ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1).1, result.2)) ≤
      bankedTargetEnvelope key reuse budget (signatures + 1) required (cache, log) bank false +
        targetCreationMultiplier key cache (.inr message) * targetCreationPrice key reuse budget (signatures + 1) required (cache, log) := by
  have h := congrArg (fun law => ∑' result, Pr[= result | law] *
    completedSigningBankValue key reuse budget signatures required log bank message result)
    (publicSigningWork_bank_digest key known words selections actual message cache)
  rw [tsum_probOutput_map_mul] at h
  rw [h]
  have hb := RetainedResidual.expected_digestCompletionValue_bank_le key reuse budget signatures required (cache, log) bank message
    known words selections actual hsigned hreuse
  simpa only [evalDist_map, probOutput_def, SPMF.evalDist_def] using hb

theorem expected_forcedSigning_bank_le (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (reuse : ENNReal) (signatures : Nat) (bank : HashInput → Bool)
    (hsigned : SigningDigestsCached parameter state.1.1 root state.2.log)
    (hreuse : exactDigestReuseWeight (monitorKey parameter root) message state.1.1 ≤ reuse) :
    (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (signingProgram message) state.1] *
      completedSigningBankValue (monitorKey parameter root) reuse (budget - state.2.spent) signatures required state.2.log bank message
        (result.1.1, result.2.1)) ≤
      bankedTargetEnvelope (monitorKey parameter root) reuse (budget - state.2.spent) (signatures + 1) required (state.1.1, state.2.log) bank false +
        targetCreationMultiplier (monitorKey parameter root) state.1.1 (.inr message) *
          targetCreationPrice (monitorKey parameter root) reuse (budget - state.2.spent) (signatures + 1) required (state.1.1, state.2.log) := by
  rw [cachedForcedRun_signingProgram' parameter root otsSecret labels inputs hencoding selections rows dummy slot message state.1 hvalid hinputs
    (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, fun _ => 0⟩ dummy), tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  calc
    _ ≤ ∑' secrets, Pr[= secrets | complete state.1.2.allowed] *
        (bankedTargetEnvelope (monitorKey parameter root) reuse (budget - state.2.spent) (signatures + 1) required (state.1.1, state.2.log) bank false +
          targetCreationMultiplier (monitorKey parameter root) state.1.1 (.inr message) *
            targetCreationPrice (monitorKey parameter root) reuse (budget - state.2.spent) (signatures + 1) required (state.1.1, state.2.log)) := by
      apply ENNReal.tsum_le_tsum
      intro secrets
      apply mul_le_mul' le_rfl
      exact expected_publicSigningWork_bank_le (monitorKey parameter root) (known otsSecret labels) (referenceFamilyWords selections dummy)
        selections (secretLabels secrets) message reuse (budget - state.2.spent) signatures required state.1.1 state.2.log bank hsigned hreuse
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_forcedSigning_certificateMonitor_le (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) (annotation : Nat × Index) :
    (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (signingProgram message) state.1] *
      certificateMonitorPotential (monitorKey parameter root) budget required
        (originalProposalAdvance (certificateMonitorUpdate (monitorKey parameter root) budget required stopAfter) (.inr message)
          (monitorView state) annotation.1
          (proposalOfSigningRecord message result.1 result.2.1 (result.1.1.2.elim annotation.2 Prod.fst)))) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        certificateMonitorCharge (monitorKey parameter root) budget required (.inr message) (monitorView state) := by
  by_cases hactive : CertificateMonitorActive (monitorKey parameter root) budget (.inr message) (monitorView state)
  · have hdata := hactive
    obtain ⟨hlive, ⟨hsigned, hcapacity, _⟩, hvalidStep, _⟩ := hdata
    have hremaining : signatureLimit - (state.2.log.length + 1) + 1 = signatureLimit - state.2.log.length := by
      change state.2.log.length < signatureLimit at hvalidStep
      omega
    have hreuse := exactDigestReuseWeight_le_near_uniform_of_clean_cache (monitorKey parameter root) state.1.1 state.2.spent
      hcapacity.spent_le hcapacity.cache_le hcapacity.no_deficit message
    calc
      _ ≤ ∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
          (signingProgram message) state.1] *
          completedSigningBankValue (monitorKey parameter root) nearUniformDigestReuseWeight (budget - state.2.spent)
            (signatureLimit - (state.2.log.length + 1)) required state.2.log state.2.bank message (result.1.1, result.2.1) := by
        apply ENNReal.tsum_le_tsum
        intro result
        apply mul_le_mul' le_rfl
        simp only [certificateMonitorPotential_advance_active (monitorKey parameter root) budget required stopAfter (.inr message)
          (monitorView state) _ _ hactive, signingLogFragment, List.length_append, List.length_singleton]
        exact RetainedResidual.bankedProposalRecordValue_le_completedSigningBank (monitorKey parameter root) nearUniformDigestReuseWeight
          (budget - state.2.spent) (signatureLimit - (state.2.log.length + 1)) required (certificateMonitorCoverState (monitorView state))
          state.2.bank message (proposalOfSigningRecord message result.1 result.2.1 (result.1.1.2.elim annotation.2 Prod.fst)) _
      _ ≤ _ := by
        have h := expected_forcedSigning_bank_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          message state hvalid hinputs nearUniformDigestReuseWeight (signatureLimit - (state.2.log.length + 1)) state.2.bank hsigned hreuse
        rw [hremaining] at h
        have hlive' : state.2.stopped = false := hlive
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, monitorView_fst, monitorView_snd, hlive',
          certificateMonitorCharge, if_pos hactive] using h
  · rw [certificateMonitorCharge, if_neg hactive, add_zero]
    simp only [certificateMonitorPotential_advance_inactive (monitorKey parameter root) budget required stopAfter (.inr message)
      (monitorView state) _ _ hactive, ENNReal.tsum_mul_right]
    exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

theorem expected_monitoredSignStep_potential_le (message : Message) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    (∑' result, Pr[= result | monitoredSignStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter message state] *
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        certificateMonitorCharge (monitorKey parameter root) budget required (.inr message) (monitorView state) := by
  rw [monitoredSignStep, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  calc
    _ ≤ ∑' annotation, Pr[= annotation | (liftM (signingAnnotation (monitorKey parameter root) budget message (monitorView state)) : SPMF _)] *
        (certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
          certificateMonitorCharge (monitorKey parameter root) budget required (.inr message) (monitorView state)) := by
      apply ENNReal.tsum_le_tsum
      intro annotation
      apply mul_le_mul' le_rfl
      exact expected_forcedSigning_certificateMonitor_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter message state hvalid hinputs annotation
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-! ### One adversary step -/

theorem expected_monitoredStep_potential_le (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query input) >>= next) state) :
    (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] *
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state) := by
  cases input with
  | inl input =>
      exact expected_monitoredWorldStep_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter input state (covered_world_inputs parameter root otsSecret inputs input next state hvalid hcovered)
  | inr message =>
      exact expected_monitoredSignStep_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter message state hvalid (covered_sign_digest parameter root otsSecret inputs message next state hvalid hcovered)

/-! ### Telescoping over the adversary run -/

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

noncomputable def expectedMonitoredCharge (computation : OracleComp (OracleWorld + SigningSpec) Forgery) :
    MonitoredState → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state =>
    certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state) +
      ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * next result.1.1.1 result.2) computation

theorem expectedMonitoredCharge_pure (forgery : Forgery) (state : MonitoredState) :
    expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (pure forgery) state = 0 := rfl

theorem expectedMonitoredCharge_query_bind (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState) :
    expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state) +
        ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] *
          expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next result.1.1.1) result.2 := rfl

include hauxiliary in
theorem covered_step_next (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query input) >>= next) state)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    CoveredRun parameter root otsSecret inputs (next result.1.1.1) result.2 := by
  cases input with
  | inl input =>
      exact covered_world_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
        next state hcovered result hresult
  | inr message =>
      exact covered_sign_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter message
        next state hvalid hauxiliary hcovered result hresult

include hauxiliary in
theorem expected_monitoredRun_potential_le (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state) (hcovered : CoveredRun parameter root otsSecret inputs computation state) :
    (∑' result, Pr[= result | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] *
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [monitoredRun_pure, tsum_probOutput_pure_mul, expectedMonitoredCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, tsum_probOutput_bind_mul, expectedMonitoredCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] *
            (certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2) +
              expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (next result.1.1.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] = 0
          · simp only [hr, zero_mul, le_refl]
          · rw [SPMF.probOutput_eq_apply] at hr
            rw [tsum_probOutput_map_mul]
            apply mul_le_mul' le_rfl
            exact ih result.1.1.1 result.2
              (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                input state hvalid result hr)
              (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                hauxiliary input next state hvalid hcovered result hr)
        _ = (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] * certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) +
            ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] *
              expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (next result.1.1.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ _ := by
          rw [← add_assoc]
          exact add_le_add (expected_monitoredStep_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy slot
            budget required stopAfter input next state hvalid hcovered) le_rfl

/-! ### Telescoping over the verifier -/

noncomputable def expectedWorldCharge {Result : Type} (computation : OracleComp OracleWorld Result) : MonitoredState → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state =>
    certificateMonitorCharge (monitorKey parameter root) budget required (.inl input) (monitorView state) +
      ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * next result.1.1.1 result.2) computation

theorem expectedWorldCharge_pure {Result : Type} (value : Result) (state : MonitoredState) :
    expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (pure value) state = 0 := rfl

theorem expectedWorldCharge_query_bind {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (state : MonitoredState) :
    expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (liftM (OracleWorld.query input) >>= next) state =
      certificateMonitorCharge (monitorKey parameter root) budget required (.inl input) (monitorView state) +
        ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] *
          expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (next result.1.1.1) result.2 := rfl

theorem expected_monitoredWorldRun_potential_le {Result : Type} (computation : OracleComp OracleWorld Result)
    (state : MonitoredState) (hinputs : hashInputs computation ⊆ inputs) :
    (∑' result, Pr[= result | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] *
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [monitoredWorldRun_pure, tsum_probOutput_pure_mul, expectedWorldCharge_pure, add_zero, le_refl]
  | query_bind input next ih =>
      rw [monitoredWorldRun_query_bind, tsum_probOutput_bind_mul, expectedWorldCharge_query_bind]
      calc
        _ ≤ ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] *
            (certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2) +
              expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (next result.1.1.1) result.2) := by
          apply ENNReal.tsum_le_tsum
          intro result
          rw [tsum_probOutput_map_mul]
          exact mul_le_mul' le_rfl (ih result.1.1.1 result.2 ((hashInputs_world_next input next result.1.1.1).trans hinputs))
        _ = (∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] * certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) +
            ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] *
              expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (next result.1.1.1) result.2 := by
          simp only [mul_add, ENNReal.tsum_add]
        _ ≤ _ := by
          rw [← add_assoc]
          exact add_le_add (expected_monitoredWorldStep_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy
            slot budget required stopAfter input state ((hashInputs_world_query input next).trans hinputs)) le_rfl

end SphincsSecurity.Concrete.FtsGuessHash

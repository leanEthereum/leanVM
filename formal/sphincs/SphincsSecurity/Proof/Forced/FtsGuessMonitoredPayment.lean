import SphincsSecurity.Proof.Forced.FtsGuessMonitoredPotential
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput)
open SecretGuessObservation (State)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
  (hauxiliary : ∀ seed : inputs → HashOutput,
    (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

/-! ### Run-level validity and coverage -/

theorem monitoredRun_valid {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : MonitoredState)
    (hvalid : Valid state) (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × MonitoredState)
    (hresult : monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) : Valid result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hvalid
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ih step.1.1.1 step.2
        (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state hvalid step hstep) tail htail

include hauxiliary in
theorem monitoredRun_covered (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState)
    (hvalid : Valid state) (hcovered : CoveredRun parameter root otsSecret inputs computation state)
    (result : AdversaryTrace × MonitoredState)
    (hresult : monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) : CoveredRun parameter root otsSecret inputs (pure result.1.1.1.1) result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ih step.1.1.1 step.2
        (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state hvalid step hstep)
        (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
          input next state hvalid hcovered step hstep) tail htail

theorem monitoredStep_inl (input : OracleWorld.Domain) (state : MonitoredState) :
    monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter (.inl input) state =
      monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state := rfl

/-! ### Creation counters -/

theorem monitoredStep_creation_counters (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    result.2.2.creationCost = state.2.creationCost +
        certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state) ∧
      result.2.2.creationMass = state.2.creationMass + certificateMonitorMass (monitorKey parameter root) budget input (monitorView state) := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep] at hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ⟨certificateMonitorUpdate_creationCost _ _ _ _ _ _ _ _, certificateMonitorUpdate_creationMass _ _ _ _ _ _ _ _⟩
  | inr message =>
      rw [monitoredStep, monitoredSignStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      obtain ⟨raw, _, rfl⟩ := map_nonzero_source' _ _ _ hresult
      exact ⟨certificateMonitorUpdate_creationCost _ _ _ _ _ _ _ _, certificateMonitorUpdate_creationMass _ _ _ _ _ _ _ _⟩

theorem expected_monitoredStep_creationCost (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * result.2.2.creationCost) =
      state.2.creationCost + certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state) := by
  calc
    _ = ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] *
        (state.2.creationCost + certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state)) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(monitoredStep_creation_counters parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state result hr).1]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, tsum_monitoredStep_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter input state hvalid, one_mul]

/-! ### Payment accumulators over the adversary run -/

noncomputable def expectedMonitoredPayment (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) : MonitoredState → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state =>
    charge input (monitorView state) +
      ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * next result.1.1.1 result.2) computation

theorem expectedMonitoredPayment_query_bind (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState) :
    expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      charge input (monitorView state) +
        ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] *
          expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
            (next result.1.1.1) result.2 := rfl

theorem expected_monitoredRun_accumulator (counter : CertificateMonitor → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state, Valid state →
      (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * counter result.2.2) = counter state.2 + charge input (monitorView state))
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState) (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * counter result.2.2) =
      counter state.2 +
        expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
          computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [monitoredRun_pure, tsum_probOutput_pure_mul, expectedMonitoredPayment, construct_pure, add_zero]
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, tsum_probOutput_bind_mul, expectedMonitoredPayment_query_bind]
      calc
        _ = ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] *
            (counter result.2.2 +
              expectedMonitoredPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                charge (next result.1.1.1) result.2) := by
          apply tsum_congr
          intro result
          by_cases hr : Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] = 0
          · simp only [hr, zero_mul]
          · rw [SPMF.probOutput_eq_apply] at hr
            rw [tsum_probOutput_map_mul]
            apply congrArg (_ * ·)
            exact ih result.1.1.1 result.2
              (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                input state hvalid result hr)
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [hstep input state hvalid, add_assoc]

theorem expected_monitoredRun_creationCost (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState)
    (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * result.2.2.creationCost) =
      state.2.creationCost +
        expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          computation state :=
  expected_monitoredRun_accumulator parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    CertificateMonitor.creationCost (certificateMonitorCharge (monitorKey parameter root) budget required)
    (fun input state hvalid => expected_monitoredStep_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot
      budget required stopAfter input state hvalid) computation state hvalid

/-! ### Payment accumulators over the verifier -/

noncomputable def expectedWorldPayment (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    {Result : Type} (computation : OracleComp OracleWorld Result) : MonitoredState → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state =>
    charge (.inl input) (monitorView state) +
      ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * next result.1.1.1 result.2) computation

theorem expectedWorldPayment_query_bind (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    {Result : Type} (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp OracleWorld Result) (state : MonitoredState) :
    expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
      (liftM (OracleWorld.query input) >>= next) state =
      charge (.inl input) (monitorView state) +
        ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] *
          expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
            (next result.1.1.1) result.2 := rfl

theorem expected_monitoredWorldRun_accumulator (counter : CertificateMonitor → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal)
    (hstep : ∀ input state, Valid state →
      (∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * counter result.2.2) = counter state.2 + charge (.inl input) (monitorView state))
    {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState) (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * counter result.2.2) =
      counter state.2 +
        expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
          computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [monitoredWorldRun_pure, tsum_probOutput_pure_mul, expectedWorldPayment, construct_pure, add_zero]
  | query_bind input next ih =>
      rw [monitoredWorldRun_query_bind, tsum_probOutput_bind_mul, expectedWorldPayment_query_bind]
      calc
        _ = ∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] *
            (counter result.2.2 +
              expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                charge (next result.1.1.1) result.2) := by
          apply tsum_congr
          intro result
          by_cases hr : Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
              required stopAfter input state] = 0
          · simp only [hr, zero_mul]
          · rw [SPMF.probOutput_eq_apply] at hr
            rw [tsum_probOutput_map_mul]
            apply congrArg (_ * ·)
            exact ih result.1.1.1 result.2
              (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                (.inl input) state hvalid result hr)
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [hstep input state hvalid, add_assoc]

theorem expected_monitoredWorldRun_creationCost {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState)
    (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * result.2.2.creationCost) =
      state.2.creationCost +
        expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          computation state :=
  expected_monitoredWorldRun_accumulator parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    CertificateMonitor.creationCost (certificateMonitorCharge (monitorKey parameter root) budget required)
    (fun input state hvalid => by
      rw [← monitoredStep_inl]
      exact expected_monitoredStep_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter (.inl input) state hvalid) computation state hvalid

/-! ### The completed run -/

noncomputable def verifyComputation (forgery : Forgery) : OracleComp OracleWorld Bool :=
  liftM (verify ⟨root, parameter⟩ forgery.message forgery.signature : OracleComp HashSpec Bool)

noncomputable def expectedCompletedCharge (adversary : Adversary) (state : MonitoredState) : ENNReal :=
  expectedMonitoredCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (adversary.main ⟨root, parameter⟩) state +
    ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      stopAfter (adversary.main ⟨root, parameter⟩) state] *
      expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (verifyComputation parameter root before.1.1.1.1) before.2

theorem monitoredCompletedRun_eq (adversary : Adversary) (state : MonitoredState) :
    monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter adversary state =
      (monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state >>= fun before =>
        (fun checked => ((before.1, checked.1), checked.2)) <$>
          monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (verifyComputation parameter root before.1.1.1.1) before.2) := rfl

include hauxiliary in
theorem expected_monitoredCompletedRun_potential_le (adversary : Adversary) (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state) :
    (∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] *
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView result.2)) ≤
      certificateMonitorPotential (monitorKey parameter root) budget required (monitorView state) +
        expectedCompletedCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          adversary state := by
  rw [monitoredCompletedRun_eq, tsum_probOutput_bind_mul, expectedCompletedCharge, ← add_assoc]
  calc
    _ ≤ ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] *
        (certificateMonitorPotential (monitorKey parameter root) budget required (monitorView before.2) +
          expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (verifyComputation parameter root before.1.1.1.1) before.2) := by
      apply ENNReal.tsum_le_tsum
      intro before
      by_cases hb : Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] = 0
      · simp only [hb, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hb
        rw [tsum_probOutput_map_mul]
        apply mul_le_mul' le_rfl
        have hfinal := monitoredRun_covered parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered before hb
        have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state hvalid before hb
        exact expected_monitoredWorldRun_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter (verifyComputation parameter root before.1.1.1.1) before.2
          (covered_pure parameter root otsSecret inputs before.1.1.1.1 before.2 hvalid' hfinal)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
    _ ≤ _ :=
      add_le_add (expected_monitoredRun_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered) le_rfl

theorem expected_monitoredCompletedRun_creationCost (adversary : Adversary) (state : MonitoredState) (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] * result.2.2.creationCost) =
      state.2.creationCost +
        expectedCompletedCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          adversary state := by
  rw [monitoredCompletedRun_eq, tsum_probOutput_bind_mul, expectedCompletedCharge, ← add_assoc]
  calc
    _ = ∑' before, Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] *
        (before.2.2.creationCost +
          expectedWorldCharge parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (verifyComputation parameter root before.1.1.1.1) before.2) := by
      apply tsum_congr
      intro before
      by_cases hb : Pr[= before | monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (adversary.main ⟨root, parameter⟩) state] = 0
      · simp only [hb, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hb
        rw [tsum_probOutput_map_mul]
        apply congrArg (_ * ·)
        exact expected_monitoredWorldRun_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
          required stopAfter (verifyComputation parameter root before.1.1.1.1) before.2
          (monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (adversary.main ⟨root, parameter⟩) state hvalid before hb)
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      rw [expected_monitoredRun_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter (adversary.main ⟨root, parameter⟩) state hvalid]

include hauxiliary in
theorem expected_monitoredCompletedRun_count_le_creationCost (adversary : Adversary) (spent : Nat) (stopped : Bool)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩)
      ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped)) :
    (∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped)] *
      certificateBankCount result.2.2.bank) ≤
      ∑' result, Pr[= result | monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped)] *
        result.2.2.creationCost := by
  have hvalid : Valid ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped) :=
    fun _ => Finset.univ_nonempty
  have hpotential := expected_monitoredCompletedRun_potential_le parameter root otsSecret labels inputs hencoding selections rows dummy slot
    budget required stopAfter hauxiliary adversary _ hvalid hcovered
  rw [expected_monitoredCompletedRun_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
    stopAfter adversary _ hvalid]
  have hzero : certificateMonitorPotential (monitorKey parameter root) budget required
      (monitorView ((∅, SecretGuessObservation.initialState PUnit.unit), initialCertificateMonitor spent stopped)) = 0 :=
    certificateMonitorPotential_initial (monitorKey parameter root) budget spent required ∅ stopped (fun _ _ => rfl)
  rw [hzero, zero_add] at hpotential
  simp only [initialCertificateMonitor, zero_add]
  refine le_trans ?_ hpotential
  exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

end SphincsSecurity.Concrete.FtsGuessHash

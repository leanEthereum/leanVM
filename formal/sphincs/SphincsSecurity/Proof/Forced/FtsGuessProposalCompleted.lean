import SphincsSecurity.Proof.Forced.FtsGuessProposalPayment
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace ENNReal
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State)
open RetainedResidual (proposalStop)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete signDigestLoop

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

/-! ### Creation mass along the verifier -/

theorem expected_monitoredWorldStep_creationMass (input : OracleWorld.Domain) (state : MonitoredState) (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * result.2.2.creationMass) =
      state.2.creationMass + certificateMonitorMass (monitorKey parameter root) budget (.inl input) (monitorView state) := by
  rw [← monitoredStep_inl]
  calc
    _ = ∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (.inl input) state] *
        (state.2.creationMass + certificateMonitorMass (monitorKey parameter root) budget (.inl input) (monitorView state)) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (.inl input) state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(monitoredStep_creation_counters parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter (.inl input) state result hr).2]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, tsum_monitoredStep_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter (.inl input) state hvalid, one_mul]

theorem expected_monitoredWorldRun_creationMass {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState)
    (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter computation state] * result.2.2.creationMass) =
      state.2.creationMass +
        expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (certificateMonitorMass (monitorKey parameter root) budget) computation state :=
  expected_monitoredWorldRun_accumulator parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    CertificateMonitor.creationMass (certificateMonitorMass (monitorKey parameter root) budget)
    (fun input state hvalid => expected_monitoredWorldStep_creationMass parameter root otsSecret labels inputs hencoding selections rows dummy
      slot budget required stopAfter input state hvalid) computation state hvalid

theorem expectedWorldPayment_mul (charge : (OracleWorld + SigningSpec).Domain → CertificateMonitorState → ENNReal) (rate : ENNReal)
    {Result : Type} (computation : OracleComp OracleWorld Result) (state : MonitoredState) :
    expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (fun input current => charge input current * rate) computation state =
      expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
        computation state * rate := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact (zero_mul _).symm
  | query_bind input next ih =>
      rw [expectedWorldPayment_query_bind, expectedWorldPayment_query_bind, add_mul, ← ENNReal.tsum_mul_right]
      congr 1
      apply tsum_congr
      intro result
      rw [ih result.1.1.1 result.2, mul_assoc]

/-! ### The proposal invariant along the verifier -/

theorem monitoredWorldStep_invariant (total : Nat) (word : List Index) (input : OracleWorld.Domain) (state : MonitoredState)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (hinv : ProposalInvariant parameter root total (word, state))
    (result : AdversaryStep (.inl input) × MonitoredState)
    (hresult : monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop stopAfter) input state result ≠ 0) :
    ProposalInvariant parameter root total (word, result.2) := by
  rw [monitoredWorldStep] at hresult
  obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source' _ _ _ hresult
  exact worldStep_proposalInvariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter total
    input (word, state) hinputs hinv raw hraw

theorem expectedWorldPayment_charge_le_mass_terminalPotential (total : Nat) (word : List Index) {Result : Type}
    (computation : OracleComp OracleWorld Result) (state : MonitoredState) (hvalid : Valid state)
    (hinputs : hashInputs computation ⊆ inputs) (hbudget : budget ≤ 2 ^ 127)
    (hinv : ProposalInvariant parameter root total (word, state)) :
    expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
      (certificateMonitorCharge (monitorKey parameter root) budget required) computation state ≤
      expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
        (fun input current => certificateMonitorMass (monitorKey parameter root) budget input current *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) word) computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [expectedWorldPayment_query_bind, expectedWorldPayment_query_bind]
      apply add_le_add (certificateMonitorCharge_le_terminalPrice_of_invariant (monitorKey parameter root) budget total required (.inl input)
        (word, monitorView state) hbudget hinv)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter) input state] = 0
      · simp only [hr, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hr
        apply mul_le_mul' le_rfl
        exact ih result.1.1.1 result.2
          (monitoredStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
            (.inl input) state hvalid result hr)
          ((hashInputs_world_next input next result.1.1.1).trans hinputs)
          (monitoredWorldStep_invariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter total
            word input state ((hashInputs_world_query input next).trans hinputs) hinv result hr)

/-! ### The completed proposal run -/

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

theorem expected_proposalCompletedRun_mass_terminalPotential (total : Nat) (adversary : Adversary) (state : ProposalState)
    (hvalid : Valid state.2) :
    (∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] *
      (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) result.2.1)) =
      ∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state] *
        ((before.2.2.2.creationMass +
          expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (certificateMonitorMass (monitorKey parameter root) budget) (verifyComputation parameter root before.1.1.1.1) before.2.2) *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) before.2.1) := by
  rw [proposalCompletedRun, tsum_probOutput_bind_mul]
  apply tsum_congr
  intro before
  by_cases hb : Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (adversary.main ⟨root, parameter⟩) state] = 0
  · simp only [hb, zero_mul]
  · rw [SPMF.probOutput_eq_apply] at hb
    apply congrArg (_ * ·)
    rw [tsum_probOutput_map_mul]
    have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (adversary.main ⟨root, parameter⟩) state.2 hvalid _
      (proposalRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        (adversary.main ⟨root, parameter⟩) state before hb)
    calc
      _ = ∑' checked, Pr[= checked | monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            stopAfter (verifyComputation parameter root before.1.1.1.1) before.2.2] * checked.2.2.creationMass *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) before.2.1 := by
        apply tsum_congr
        intro checked
        rw [mul_assoc]
      _ = _ := by
        rw [ENNReal.tsum_mul_right, expected_monitoredWorldRun_creationMass parameter root otsSecret labels inputs hencoding selections rows dummy
          slot budget required stopAfter _ before.2.2 hvalid']

include hauxiliary in
theorem expected_proposalCompletedRun_creationCost (adversary : Adversary) (state : ProposalState) (hvalid : Valid state.2)
    (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.2) :
    (∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter adversary state] * result.2.2.2.creationCost) =
      state.2.2.creationCost +
        (expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView current.2))
          (adversary.main ⟨root, parameter⟩) state +
        ∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state] *
          expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (certificateMonitorCharge (monitorKey parameter root) budget required) (verifyComputation parameter root before.1.1.1.1) before.2.2) := by
  rw [proposalCompletedRun, tsum_probOutput_bind_mul]
  calc
    _ = ∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state] *
        (before.2.2.2.creationCost +
          expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (certificateMonitorCharge (monitorKey parameter root) budget required) (verifyComputation parameter root before.1.1.1.1) before.2.2) := by
      apply tsum_congr
      intro before
      by_cases hb : Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (adversary.main ⟨root, parameter⟩) state] = 0
      · simp only [hb, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hb
        apply congrArg (_ * ·)
        rw [tsum_probOutput_map_mul]
        exact expected_monitoredWorldRun_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter _ before.2.2
          (monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
            (adversary.main ⟨root, parameter⟩) state.2 hvalid _
            (proposalRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
              (adversary.main ⟨root, parameter⟩) state before hb))
    _ = _ := by
      simp only [mul_add, ENNReal.tsum_add]
      rw [expected_proposalRun_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        hauxiliary (adversary.main ⟨root, parameter⟩) state hvalid hcovered, add_assoc]

include hauxiliary in
theorem expected_proposalCompletedRun_creationCost_le_mass_terminalPotential (total : Nat) (adversary : Adversary) (state : ProposalState)
    (hvalid : Valid state.2) (hcovered : CoveredRun parameter root otsSecret inputs (adversary.main ⟨root, parameter⟩) state.2)
    (hbudget : budget ≤ 2 ^ 127) (hinv : ProposalInvariant parameter root total state) :
    (∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) adversary state] * result.2.2.2.creationCost) ≤
      state.2.2.creationCost +
        ∑' result, Pr[= result | proposalCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter) adversary state] *
          (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) result.2.1) := by
  rw [expected_proposalCompletedRun_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop stopAfter) hauxiliary adversary state hvalid hcovered,
    expected_proposalCompletedRun_mass_terminalPotential parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      (proposalStop stopAfter) total adversary state hvalid]
  apply add_le_add le_rfl
  have hmain := expectedProposalPayment_charge_le_mass_terminalPotential parameter root otsSecret labels inputs hencoding selections rows dummy slot
    budget required stopAfter hauxiliary total (adversary.main ⟨root, parameter⟩) state hvalid hcovered hbudget hinv
  have hmass := expected_proposalRun_mass_terminalPotential parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
    required (proposalStop stopAfter) hauxiliary total (adversary.main ⟨root, parameter⟩) state hvalid hcovered
  have hworld : (∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state] *
        expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
          (certificateMonitorCharge (monitorKey parameter root) budget required) (verifyComputation parameter root before.1.1.1.1) before.2.2) ≤
      ∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state] *
        (expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
          (certificateMonitorMass (monitorKey parameter root) budget) (verifyComputation parameter root before.1.1.1.1) before.2.2 *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) before.2.1) := by
    apply ENNReal.tsum_le_tsum
    intro before
    by_cases hb : Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state] = 0
    · simp only [hb, zero_mul, le_refl]
    · rw [SPMF.probOutput_eq_apply] at hb
      apply mul_le_mul' le_rfl
      have hforced := proposalRun_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state before hb
      have hvalid' := monitoredRun_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state.2 hvalid _ hforced
      have hfinal := monitoredRun_covered parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) hauxiliary (adversary.main ⟨root, parameter⟩) state.2 hvalid hcovered _ hforced
      have hinv' := proposalRun_invariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        hauxiliary total (adversary.main ⟨root, parameter⟩) state hvalid hcovered hinv before hb
      rw [← expectedWorldPayment_mul]
      exact expectedWorldPayment_charge_le_mass_terminalPotential parameter root otsSecret labels inputs hencoding selections rows dummy slot
        budget required stopAfter total before.2.1 (verifyComputation parameter root before.1.1.1.1) before.2.2 hvalid'
        (covered_pure parameter root otsSecret inputs before.1.1.1.1 before.2.2 hvalid' hfinal) hbudget hinv'
  calc
    _ ≤ expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter)
          (fun input current => certificateMonitorMass (monitorKey parameter root) budget input (monitorView current.2) *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) current.1)
          (adversary.main ⟨root, parameter⟩) state +
        ∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state] *
          (expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
            (certificateMonitorMass (monitorKey parameter root) budget) (verifyComputation parameter root before.1.1.1.1) before.2.2 *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) before.2.1) :=
      add_le_add hmain hworld
    _ ≤ (state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1 +
          expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
            (proposalStop stopAfter)
            (fun input current => certificateMonitorMass (monitorKey parameter root) budget input (monitorView current.2) *
              terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) current.1)
            (adversary.main ⟨root, parameter⟩) state) +
        ∑' before, Pr[= before | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter) (adversary.main ⟨root, parameter⟩) state] *
          (expectedWorldPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
            (certificateMonitorMass (monitorKey parameter root) budget) (verifyComputation parameter root before.1.1.1.1) before.2.2 *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) before.2.1) :=
      add_le_add le_add_self le_rfl
    _ = _ := by
      rw [← hmass]
      simp only [add_mul, mul_add, ENNReal.tsum_add]

end SphincsSecurity.Concrete.FtsGuessHash

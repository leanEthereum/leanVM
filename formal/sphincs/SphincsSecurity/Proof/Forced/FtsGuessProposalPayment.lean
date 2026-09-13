import SphincsSecurity.Proof.Forced.FtsGuessProposalInvariant
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

/-! ### Creation counters along proposal steps -/

theorem proposalStep_creation_counters (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState)
    (result : AdversaryStep input × ProposalState)
    (hresult : proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    result.2.2.2.creationCost = state.2.2.creationCost +
        certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state.2) ∧
      result.2.2.2.creationMass = state.2.2.creationMass +
        certificateMonitorMass (monitorKey parameter root) budget input (monitorView state.2) :=
  monitoredStep_creation_counters parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
    state.2 _ (proposalStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
      state result hresult)

theorem proposalStep_bind_const {Other : Type} (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2)
    (after : SPMF Other) :
    (proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>=
      fun _ => after) = after := by
  have h := monitoredStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
    state.2 hvalid after
  rw [← proposalStep_erasure parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state,
    bind_map_left] at h
  exact h

theorem tsum_proposalStep_eq_one (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2) :
    (∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (proposalStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state
      hvalid (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

theorem expected_proposalStep_creationCost (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2) :
    (∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state] * result.2.2.2.creationCost) =
      state.2.2.creationCost + certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state.2) := by
  calc
    _ = ∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state] *
        (state.2.2.creationCost + certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView state.2)) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(proposalStep_creation_counters parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state result hr).1]
    _ = _ := by
      rw [ENNReal.tsum_mul_right, tsum_proposalStep_eq_one parameter root otsSecret labels inputs hencoding selections rows dummy slot budget
        required stopAfter input state hvalid, one_mul]

theorem expected_proposalStep_mass_terminalPotential (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState) (hvalid : Valid state.2)
    (hinputs : ∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) :
    (∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        input state] * (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1)) =
      state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 +
        certificateMonitorMass (monitorKey parameter root) budget input (monitorView state.2) *
          terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  calc
    _ = ∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state] *
        ((state.2.2.creationMass + certificateMonitorMass (monitorKey parameter root) budget input (monitorView state.2)) *
          terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(proposalStep_creation_counters parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state result hr).2]
    _ = (state.2.2.creationMass + certificateMonitorMass (monitorKey parameter root) budget input (monitorView state.2)) *
        ∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          input state] * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1 := by
      simp_rw [mul_left_comm _ (state.2.2.creationMass + certificateMonitorMass (monitorKey parameter root) budget input (monitorView state.2))]
      exact ENNReal.tsum_mul_left
    _ = _ := by
      rw [expected_proposalStep_terminalPotential parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state hvalid hinputs total payoff]
      exact add_mul _ _ _

/-! ### Payment accumulators along proposal runs -/

variable (hauxiliary : ∀ seed : inputs → HashOutput,
  (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)

noncomputable def expectedProposalPayment (charge : (OracleWorld + SigningSpec).Domain → ProposalState → ENNReal)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) : ProposalState → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state => charge input state +
    ∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state] * next result.1.1.1 result.2) computation

theorem expectedProposalPayment_query_bind (charge : (OracleWorld + SigningSpec).Domain → ProposalState → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Forgery) (state : ProposalState) :
    expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state =
      charge input state +
        ∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          stopAfter input state] *
          expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
            (next result.1.1.1) result.2 := rfl

include hauxiliary in
theorem expected_proposalRun_accumulator (counter : ProposalState → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → ProposalState → ENNReal)
    (hstep : ∀ input state, Valid state.2 →
      (∀ message, input = .inr message → hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs) →
      (∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state] * counter result.2) = counter state + charge input state)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ProposalState) (hvalid : Valid state.2)
    (hcovered : CoveredRun parameter root otsSecret inputs computation state.2) :
    (∑' result, Pr[= result | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        computation state] * counter result.2) =
      counter state +
        expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter charge
          computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [proposalRun_pure, tsum_probOutput_pure_mul, expectedProposalPayment, construct_pure, add_zero]
  | query_bind input next ih =>
      rw [proposalRun_query_bind, tsum_probOutput_bind_mul, expectedProposalPayment_query_bind]
      calc
        _ = ∑' result, Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] *
            (counter result.2 +
              expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
                charge (next result.1.1.1) result.2) := by
          apply tsum_congr
          intro result
          by_cases hr : Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
              stopAfter input state] = 0
          · simp only [hr, zero_mul]
          · rw [SPMF.probOutput_eq_apply] at hr
            rw [tsum_probOutput_map_mul]
            apply congrArg (_ * ·)
            exact ih result.1.1.1 result.2
              (proposalStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
                state hvalid result hr)
              (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
                input next state.2 hvalid hcovered (result.1, result.2.2)
                (proposalStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input
                  state result hr))
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [hstep input state hvalid (covered_step_digest parameter root otsSecret inputs input next state.2 hvalid hcovered), add_assoc]

/-! ### Invariants along proposal runs -/

include hauxiliary in
theorem proposalRun_invariant (total : Nat) (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ProposalState)
    (hvalid : Valid state.2) (hcovered : CoveredRun parameter root otsSecret inputs computation state.2)
    (hinv : ProposalInvariant parameter root total state) (result : AdversaryTrace × ProposalState)
    (hresult : proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
      computation state result ≠ 0) :
    ProposalInvariant parameter root total result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [proposalRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hinv
  | query_bind input next ih =>
      rw [proposalRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source' _ _ _ hresult
      have hforced := proposalStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        (proposalStop stopAfter) input state step hstep
      exact ih step.1.1.1 step.2
        (proposalStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
          input state hvalid step hstep)
        (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
          hauxiliary input next state.2 hvalid hcovered (step.1, step.2.2) hforced)
        (proposalStep_invariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter total input
          state hvalid
          (fun world heq => by subst heq; exact covered_world_inputs parameter root otsSecret inputs world next state.2 hvalid hcovered)
          (covered_step_digest parameter root otsSecret inputs input next state.2 hvalid hcovered) hinv step hstep) tail htail

include hauxiliary in
theorem expectedProposalPayment_charge_le_mass_terminalPotential (total : Nat)
    (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ProposalState) (hvalid : Valid state.2)
    (hcovered : CoveredRun parameter root otsSecret inputs computation state.2) (hbudget : budget ≤ 2 ^ 127)
    (hinv : ProposalInvariant parameter root total state) :
    expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
      (fun input current => certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView current.2)) computation state ≤
      expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
        (fun input current => certificateMonitorMass (monitorKey parameter root) budget input (monitorView current.2) *
          terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) current.1) computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => exact le_rfl
  | query_bind input next ih =>
      rw [expectedProposalPayment_query_bind, expectedProposalPayment_query_bind]
      apply add_le_add (certificateMonitorCharge_le_terminalPrice_of_invariant (monitorKey parameter root) budget total required input
        (state.1, monitorView state.2) hbudget hinv)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | proposalStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter) input state] = 0
      · simp only [hr, zero_mul, le_refl]
      · rw [SPMF.probOutput_eq_apply] at hr
        have hforced := proposalStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
          (proposalStop stopAfter) input state result hr
        apply mul_le_mul' le_rfl
        exact ih result.1.1.1 result.2
          (proposalStep_valid parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
            input state hvalid result hr)
          (covered_step_next parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required (proposalStop stopAfter)
            hauxiliary input next state.2 hvalid hcovered (result.1, result.2.2) hforced)
          (proposalStep_invariant parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter total
            input state hvalid
            (fun world heq => by subst heq; exact covered_world_inputs parameter root otsSecret inputs world next state.2 hvalid hcovered)
            (covered_step_digest parameter root otsSecret inputs input next state.2 hvalid hcovered) hinv result hr)

include hauxiliary in
theorem expected_proposalRun_mass_terminalPotential (total : Nat) (computation : OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : ProposalState) (hvalid : Valid state.2) (hcovered : CoveredRun parameter root otsSecret inputs computation state.2) :
    (∑' result, Pr[= result | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        computation state] *
      (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) result.2.1)) =
      state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1 +
        expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => certificateMonitorMass (monitorKey parameter root) budget input (monitorView current.2) *
            terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) current.1) computation state :=
  expected_proposalRun_accumulator parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
    (fun state => state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1)
    _ (fun input state hvalid hinputs => expected_proposalStep_mass_terminalPotential parameter root otsSecret labels inputs hencoding selections
      rows dummy slot budget required stopAfter total (terminalCertificatePrice required) input state hvalid hinputs) computation state hvalid hcovered

include hauxiliary in
theorem expected_proposalRun_creationCost (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : ProposalState)
    (hvalid : Valid state.2) (hcovered : CoveredRun parameter root otsSecret inputs computation state.2) :
    (∑' result, Pr[= result | proposalRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
        computation state] * result.2.2.2.creationCost) =
      state.2.2.creationCost +
        expectedProposalPayment parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
          (fun input current => certificateMonitorCharge (monitorKey parameter root) budget required input (monitorView current.2))
          computation state :=
  expected_proposalRun_accumulator parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter hauxiliary
    (fun state => state.2.2.creationCost) _
    (fun input state hvalid _ => expected_proposalStep_creationCost parameter root otsSecret labels inputs hencoding selections rows dummy slot
      budget required stopAfter input state hvalid) computation state hvalid hcovered

end SphincsSecurity.Concrete.FtsGuessHash

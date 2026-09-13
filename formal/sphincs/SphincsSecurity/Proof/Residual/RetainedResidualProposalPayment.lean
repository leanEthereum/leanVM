import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualProposalInvariant
import SphincsSecurity.Proof.Residual.RetainedResidualProposalRun
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

noncomputable def expectedProposalPayment
    (charge : (OracleWorld + SigningSpec).Domain → ProposalState inputs → ENNReal)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) : ProposalState inputs → ENNReal :=
  OracleComp.construct (fun _ _ => 0) (fun input _ next state => charge input state +
    ∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      result.1.elim 0 (fun answer => next answer result.2)) computation

theorem expectedProposalPayment_query_bind
    (charge : (OracleWorld + SigningSpec).Domain → ProposalState inputs → ENNReal)
    {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) :
    expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) state = charge input state +
        ∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
          result.1.elim 0 (fun answer =>
            expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2) := rfl

theorem expected_proposalRun_accumulator (counter : ProposalState inputs → ENNReal)
    (charge : (OracleWorld + SigningSpec).Domain → ProposalState inputs → ENNReal)
    (hstep : ∀ input state, MonitoredValid inputs state.2 → requestInputs key input ⊆ inputs →
      (∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        counter result.2) = counter state + charge input state)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) (hvalid : MonitoredValid inputs state.2) (hinputs : sourceInputs key computation ⊆ inputs) :
    (∑' result, Pr[= result | proposalRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      counter result.2) = counter state +
        expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge computation state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [proposalRun_pure, tsum_probOutput_pure_mul, expectedProposalPayment, construct_pure, add_zero]
  | query_bind input next ih =>
      rw [proposalRun_query_bind, tsum_probOutput_bind_mul]
      change _ = counter state + (charge input state +
        ∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
          result.1.elim 0 (fun answer =>
            expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2))
      calc
        _ = ∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
            (counter result.2 + result.1.elim 0 (fun answer =>
              expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required stopAfter charge (next answer) result.2)) := by
          apply tsum_congr
          intro result
          by_cases hr : Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
          · simp only [hr, zero_mul]
          · rw [SPMF.probOutput_eq_apply] at hr
            have hafter := proposalStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid result hr
            apply congrArg (_ * ·)
            rcases result with ⟨answer, after⟩
            cases answer with
            | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, add_zero]
            | some answer => exact ih answer after hafter ((sourceInputs_next_subset key input next answer).trans hinputs)
        _ = _ := by
          simp only [mul_add, ENNReal.tsum_add]
          rw [hstep input state hvalid ((requestInputs_subset key input next).trans hinputs), add_assoc]

theorem proposalStep_creation_counters (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs)
    (hvalid : MonitoredValid inputs state.2) (hinputs : requestInputs key input ⊆ inputs)
    (result : Option ((OracleWorld + SigningSpec).Range input) × ProposalState inputs)
    (hresult : proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    result.2.2.2.creationCost = state.2.2.creationCost + certificateMonitorCharge key budget required input (monitorView state.2) ∧
      result.2.2.2.creationMass = state.2.2.creationMass + certificateMonitorMass key budget input (monitorView state.2) := by
  have h := map_nonzero _ (Prod.map id Prod.snd) result hresult
  rw [proposalStep_erasure] at h
  exact monitoredStep_creation_counters key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state.2 hvalid hinputs _ h

theorem expected_proposalStep_creationCost (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs)
    (hvalid : MonitoredValid inputs state.2) (hinputs : requestInputs key input ⊆ inputs) :
    (∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      result.2.2.2.creationCost) = state.2.2.creationCost + certificateMonitorCharge key budget required input (monitorView state.2) := by
  have h := congrArg (fun law : SPMF (Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs) =>
    ∑' result, Pr[= result | law] * result.2.2.creationCost)
    (proposalStep_erasure key inputs hencoding words publicReplies selections rows budget required stopAfter input state)
  rw [tsum_probOutput_map_mul] at h
  exact h.trans (expected_monitoredStep_creationCost key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state.2 hvalid hinputs)

theorem expected_proposalStep_mass_terminalPotential (total : Nat) (payoff : List Index → ENNReal)
    (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs)
    (hvalid : MonitoredValid inputs state.2) (hinputs : requestInputs key input ⊆ inputs) :
    (∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1)) =
        state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 +
          certificateMonitorMass key budget input (monitorView state.2) *
            terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  let mass := state.2.2.creationMass + certificateMonitorMass key budget input (monitorView state.2)
  calc
    _ = ∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        (mass * terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) := by
      apply tsum_congr
      intro result
      by_cases hr : Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] = 0
      · simp only [hr, zero_mul]
      · rw [SPMF.probOutput_eq_apply] at hr
        rw [(proposalStep_creation_counters key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state hvalid hinputs result hr).2]
    _ = mass * ∑' result, Pr[= result | proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1 := by
      simp_rw [mul_left_comm _ mass]
      exact ENNReal.tsum_mul_left
    _ = _ := by
      rw [expected_proposalStep_terminalPotential key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hinputs hvalid total payoff]
      exact add_mul _ _ _

theorem expected_proposalRun_creationCost_le_mass_terminalPotential (total : Nat)
    {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ProposalState inputs) (hvalid : MonitoredValid inputs state.2) (hinputs : sourceInputs key computation ⊆ inputs)
    (hbudget : budget ≤ 2 ^ 127) (hinv : ProposalInvariant key total state) :
    (∑' result, Pr[= result | proposalRun key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter) computation state] *
      result.2.2.2.creationCost) ≤ state.2.2.creationCost +
      ∑' result, Pr[= result | proposalRun key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter) computation state] *
        (result.2.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) result.2.1) := by
  let first := fun input (state : ProposalState inputs) => certificateMonitorCharge key budget required input (monitorView state.2)
  let second := fun input (state : ProposalState inputs) => certificateMonitorMass key budget input (monitorView state.2) *
    terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1
  have hcharge : expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter) first computation state ≤
      expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter) second computation state := by
    induction computation using OracleComp.inductionOn generalizing state with
    | pure value => exact le_rfl
    | query_bind input next ih =>
        rw [expectedProposalPayment_query_bind, expectedProposalPayment_query_bind]
        apply add_le_add (certificateMonitorCharge_le_terminalPrice_of_invariant key budget total required input
          (state.1, monitorView state.2) hbudget hinv)
        apply ENNReal.tsum_le_tsum
        intro result
        by_cases hr : Pr[= result |
            proposalStep key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter) input state] = 0
        · simp only [hr, zero_mul, le_refl]
        · rw [SPMF.probOutput_eq_apply] at hr
          have hafter := proposalStep_valid key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter)
            input state hvalid result hr
          have hinv' := proposalStep_invariant key inputs hencoding words publicReplies selections rows budget total required stopAfter
            input state ((requestInputs_subset key input next).trans hinputs) hvalid hinv result hr
          apply mul_le_mul' le_rfl
          rcases result with ⟨answer, after⟩
          cases answer with
          | none => exact le_rfl
          | some answer => exact ih answer after hafter ((sourceInputs_next_subset key input next answer).trans hinputs) hinv'
  have hcost := expected_proposalRun_accumulator key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter)
    (fun state => state.2.2.creationCost) first
    (expected_proposalStep_creationCost key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter))
    computation state hvalid hinputs
  have hmass := expected_proposalRun_accumulator key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter)
    (fun state => state.2.2.creationMass * terminalProposalPotential (PMF.uniformOfFintype Index) total (terminalCertificatePrice required) state.1) second
    (expected_proposalStep_mass_terminalPotential key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter)
      total (terminalCertificatePrice required)) computation state hvalid hinputs
  calc
    _ = state.2.2.creationCost + expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter)
        first computation state := hcost
    _ ≤ state.2.2.creationCost + expectedProposalPayment key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter)
        second computation state := add_le_add le_rfl hcharge
    _ ≤ _ := by rw [hmass]; exact add_le_add le_rfl le_add_self

end SphincsSecurity.Concrete.RetainedResidual

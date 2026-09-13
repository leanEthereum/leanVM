import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualCoverageStep
import SphincsSecurity.Proof.Residual.RetainedResidualSource
import SphincsSecurity.Proof.Residual.RetainedResidualWorldCoverage
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

abbrev MonitoredState (inputs : Finset HashInput) := State inputs × CertificateMonitor

def monitorView {inputs : Finset HashInput} (state : MonitoredState inputs) : CertificateMonitorState :=
  (state.1.memory.external.cache, state.2)

noncomputable def signingAnnotation (key : SecretKey) (budget : Nat) (message : Message)
    (monitor : CertificateMonitorState) : PMF (Nat × Index) :=
  let lengths := if CertificateMonitorActive key budget (.inr message) monitor then
    proposalBlockLength targetProposalAcceptance targetProposalAcceptance_ne_zero targetProposalAcceptance_lt_one.le
  else PMF.pure 0
  lengths.bind fun length => (PMF.uniformOfFintype Index).map (length, ·)

noncomputable def monitoredWorldResult {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (before : MonitoredState inputs) (result : Option (OracleWorld.Range input) × State inputs) :
    Option (OracleWorld.Range input) × MonitoredState inputs :=
  (result.1, result.2, result.1.elim { before.2 with stopped := true } fun answer =>
    certificateMonitorUpdate key budget required stopAfter (.inl input) (monitorView before) 0
      (proposalOfWorldResult key.parameter input (answer, result.2.memory.external.cache)))

noncomputable def monitoredSigningResult {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message)
    (annotation : Nat × Index) (before : MonitoredState inputs) (result : Option SigningRecord × State inputs) :
    Option (Option Signature) × MonitoredState inputs :=
  match result.1 with
  | none => (none, result.2, { before.2 with stopped := true })
  | some record =>
      (some record.1.1, { result.2 with memory := result.2.memory.recordSigning message record },
        certificateMonitorUpdate key budget required stopAfter (.inr message) (monitorView before) annotation.1
          (proposalOfSigningRecord message record result.2.memory.external.cache (record.1.2.elim annotation.2 Prod.fst)))

theorem monitoredWorldResult_potential {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (before : MonitoredState inputs) (result : Option (OracleWorld.Range input) × State inputs) :
    certificateMonitorPotential key budget required
      (monitorView (monitoredWorldResult key budget required stopAfter input before result).2) =
      worldMonitorValue key budget required stopAfter input (monitorView before) 0 (cacheResult result) := by
  rcases result with ⟨answer, after⟩
  cases answer with
  | none => simp only [monitoredWorldResult, monitorView, worldMonitorValue, cacheResult, Option.elim_none,
      certificateMonitorPotential, bankedTargetEnvelope_stopped]
  | some answer => rfl

theorem monitoredSigningResult_some_potential {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message) (annotation : Nat × Index)
    (before : MonitoredState inputs) (record : SigningRecord) (after : State inputs) :
    certificateMonitorPotential key budget required
      (monitorView (monitoredSigningResult key budget required stopAfter message annotation before (some record, after)).2) =
      certificateMonitorPotential key budget required
        (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) (.inr message) (monitorView before) annotation.1
          (proposalOfSigningRecord message record after.memory.external.cache (record.1.2.elim annotation.2 Prod.fst))) := rfl

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

noncomputable def monitoredStep :
    (input : (OracleWorld + SigningSpec).Domain) → MonitoredState inputs →
      SPMF (Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
  | .inl input, state =>
      monitoredWorldResult key budget required stopAfter input state <$>
        lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state.1
  | .inr message, state =>
      (liftM (signingAnnotation key budget message (monitorView state)) : SPMF _) >>= fun annotation =>
        monitoredSigningResult key budget required stopAfter message annotation state <$>
          lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (simulateQ (embed inputs state.1.memory.routing)
              (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1

noncomputable def monitoredImpl : QueryImpl (OracleWorld + SigningSpec) (OptionT (StateT (MonitoredState inputs) SPMF)) :=
  fun input => OptionT.mk (StateT.mk (monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input))

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram
  certificateMonitorPotential certificateMonitorCharge bankedTargetEnvelope signDigestLoop
  certificateMonitorUpdate originalProposalAdvance proposalOfSigningRecord monitorView monitoredSigningResult

include words selections in
theorem digestInputs_of_request (message : Message) (known : Labels)
    (hinputs : requestInputs key (.inr message) ⊆ inputs) :
    hashInputs (signDigestLoop digestAttemptLimit key message) ⊆ inputs := by
  have h := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key known words selections message).trans hinputs
  simpa only [ResidualByteFrontend.hashInputs_publicSigningWork, publicDigestLoop_eq] using h

theorem expected_monitoredSigningResult_potential_le (message : Message) (annotation : Nat × Index)
    (state : MonitoredState inputs) (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (ha : ∀ coordinate, (state.1.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state.1)) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.1.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1] *
      certificateMonitorPotential key budget required
        (monitorView (monitoredSigningResult key budget required stopAfter message annotation state result).2)) ≤
      certificateMonitorPotential key budget required (monitorView state) +
        certificateMonitorCharge key budget required (.inr message) (monitorView state) := by
  have hin := digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs
  apply le_trans ?_ (expected_lazySigning_certificateMonitor_le key.parameter inputs hencoding words publicReplies selections rows
    state.1.memory.routing key rfl budget required stopAfter message (monitorView state) (fun _ => annotation.1)
    (fun result => result.1.elim annotation.2 (fun record => record.1.2.elim annotation.2 Prod.fst)) hin state.1
    (by unfold monitorView; rfl) ha hcovered)
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs state.1.memory.routing)
        (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1] = 0
  · simp only [hr, zero_mul, le_refl]
  · rw [SPMF.probOutput_eq_apply] at hr
    obtain ⟨record, hrecord⟩ := lazyRun_jointSigningProgram_some key.parameter inputs hencoding words publicReplies selections rows
      state.1.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin) state.1 ha hcovered result hr
    apply mul_le_mul' le_rfl
    have heq : result = (some record, result.2) := Prod.ext hrecord rfl
    rw [heq, monitoredSigningResult_some_potential]
    conv_rhs => dsimp only [Option.elim]
    exact le_refl _

theorem expected_monitoredStep_potential_le (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hinputs : requestInputs key input ⊆ inputs)
    (ha : ∀ coordinate, (state.1.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state.1)) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      certificateMonitorPotential key budget required (monitorView result.2)) ≤
      certificateMonitorPotential key budget required (monitorView state) + certificateMonitorCharge key budget required input (monitorView state) := by
  cases input with
  | inl input =>
      rw [monitoredStep, tsum_probOutput_map_mul]
      simp only [monitoredWorldResult_potential]
      exact expected_externalProgram_certificateMonitor_le key.parameter inputs hencoding words publicReplies selections rows
        key rfl budget required stopAfter input hinputs (monitorView state) (fun _ => 0) state.1 (by unfold monitorView; rfl) ha hcovered
  | inr message =>
      rw [monitoredStep, tsum_probOutput_bind_mul]
      simp only [tsum_probOutput_map_mul]
      calc
        _ ≤ ∑' annotation, Pr[= annotation | (liftM (signingAnnotation key budget message (monitorView state)) : SPMF _)] *
            (certificateMonitorPotential key budget required (monitorView state) +
              certificateMonitorCharge key budget required (.inr message) (monitorView state)) := by
          apply ENNReal.tsum_le_tsum
          intro annotation
          exact mul_le_mul' le_rfl (expected_monitoredSigningResult_potential_le key inputs hencoding words publicReplies selections rows
            budget required stopAfter message annotation state hinputs ha hcovered)
        _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Concrete.RetainedResidual

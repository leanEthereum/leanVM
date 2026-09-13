import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.MessageCertificateProjection
import SphincsSecurity.Proof.Residual.RetainedResidualWorldKernel
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def proposalOfWorldResult (parameter : PublicParameter) (input : OracleWorld.Domain)
    (result : OracleWorld.Range input × QueryCache HashSpec) : ProposalExecutionRecord (.inl input) :=
  ⟨result.1, result.2, signingBoundaryTrace parameter input result.1, none, 0⟩

noncomputable def worldMonitorValue (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : OracleWorld.Domain) (monitor : CertificateMonitorState)
    (length : Nat) (result : Option (OracleWorld.Range input) × QueryCache HashSpec) : ENNReal :=
  result.1.elim (certificateBankCount monitor.2.bank) fun answer =>
    certificateMonitorPotential key budget required
      (originalProposalAdvance (certificateMonitorUpdate key budget required stopAfter) (.inl input) monitor length
        (proposalOfWorldResult key.parameter input (answer, result.2)))

theorem worldMonitorValue_le_of_messageHistory (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : OracleWorld.Domain) (monitor : CertificateMonitorState)
    (length : Nat) (result : Option (OracleWorld.Range input) × QueryCache HashSpec)
    (hcache : messageAnswers key.parameter result.2 = messageAnswers key.parameter monitor.1) :
    worldMonitorValue key budget required stopAfter input monitor length result ≤ certificateMonitorPotential key budget required monitor := by
  rcases result with ⟨answer, cache⟩
  cases answer with
  | none => exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _
  | some answer =>
      by_cases hactive : CertificateMonitorActive key budget (.inl input) monitor
      · simp only [worldMonitorValue, Option.elim_some,
          certificateMonitorPotential_advance_active key budget required stopAfter (.inl input) monitor _ _ hactive,
          signingLogFragment, List.append_nil]
        have h := bankedProposalRecordValue_world_le_of_messageHistory key nearUniformDigestReuseWeight
          (budget - monitor.2.spent) (signatureLimit - monitor.2.log.length) required (certificateMonitorCoverState monitor)
          monitor.2.bank input (proposalOfWorldResult key.parameter input (answer, cache))
          (certificateMonitorUpdate key budget required stopAfter (.inl input) monitor length
            (proposalOfWorldResult key.parameter input (answer, cache))).stopped hcache
        simpa only [certificateMonitorPotential, hactive.1] using h
      · simp only [worldMonitorValue, Option.elim_some,
          certificateMonitorPotential_advance_inactive key budget required stopAfter (.inl input) monitor _ _ hactive]
        exact certificateBankCount_le_bankedCacheWeight _ _ _ _ _

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem expected_lazyWorld_nonmessage_certificateMonitor_le (routing : Routing)
    (key : SecretKey) (hparameter : key.parameter = parameter) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : HashInput) (hin : input ∈ inputs)
    (hmessage : ¬MessageHashInput parameter input) (monitor : CertificateMonitorState)
    (length : Option HashOutput × State inputs → Nat) (state : State inputs)
    (hcache : state.memory.external.cache = monitor.1)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input))) state] *
      worldMonitorValue key budget required stopAfter (.inr input) monitor (length result) (cacheResult result)) ≤
      certificateMonitorPotential key budget required monitor := by
  calc
    _ ≤ ∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query (.inr input))) state] * certificateMonitorPotential key budget required monitor := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
          (liftM (OracleWorld.query (.inr input))) state] = 0
      · simp only [hr, zero_mul, le_refl]
      · apply mul_le_mul' le_rfl
        apply worldMonitorValue_le_of_messageHistory
        have h := lazyByteRun_hash_nonmessage parameter inputs hencoding words publicReplies selections rows routing
          input hin state ha hcovered hmessage result hr
        simpa only [cacheResult, hparameter, hcache] using h
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_lazyWorld_message_certificateMonitor_le (routing : Routing)
    (key : SecretKey) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (hmessage : ∀ hash, input = .inr hash → MessageHashInput parameter hash)
    (monitor : CertificateMonitorState) (length : Option (OracleWorld.Range input) × State inputs → Nat)
    (state : State inputs) (hcache : state.memory.external.cache = monitor.1)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query input)) state] *
      worldMonitorValue key budget required stopAfter input monitor (length result) (cacheResult result)) ≤
      certificateMonitorPotential key budget required monitor + certificateMonitorCharge key budget required (.inl input) monitor := by
  by_cases hactive : CertificateMonitorActive key budget (.inl input) monitor
  · let weight : Option (OracleWorld.Range input) × QueryCache HashSpec → ENNReal := fun result =>
      result.1.elim (certificateBankCount monitor.2.bank) fun answer =>
        bankedProposalRecordValue key nearUniformDigestReuseWeight (budget - monitor.2.spent)
          (signatureLimit - monitor.2.log.length) required (certificateMonitorCoverState monitor) monitor.2.bank (.inl input)
          (proposalOfWorldResult key.parameter input (answer, result.2)) false
    have hkernel := congrArg (fun law : SPMF (Option (OracleWorld.Range input) × QueryCache HashSpec) =>
      ∑' result, Pr[= result | law] * weight result)
      (lazyByteRun_world_message_rom parameter inputs hencoding words publicReplies selections rows routing input hinputs hmessage state hcovered)
    rw [tsum_probOutput_map_mul, tsum_probOutput_map_mul] at hkernel
    simp only [Prod.map_fst, Prod.map_snd, id_eq, weight, Option.elim_some, hcache] at hkernel
    have hbound := expected_originalProposalRecord_world_banked_le key nearUniformDigestReuseWeight
      (budget - monitor.2.spent) (signatureLimit - monitor.2.log.length) required (certificateMonitorCoverState monitor)
      monitor.2.bank input (fun _ => false) hactive.2.1.1
      (by cases input <;> exact hactive.2.2.2)
    calc
      _ ≤ ∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
          (liftM (OracleWorld.query input)) state] * weight (cacheResult result) := by
        apply ENNReal.tsum_le_tsum
        intro result
        apply mul_le_mul' le_rfl
        cases hanswer : result.1 with
        | none => simp only [worldMonitorValue, cacheResult, hanswer, Option.elim_none, weight, le_refl]
        | some answer =>
            simp only [worldMonitorValue, cacheResult, hanswer, Option.elim_some, weight,
              certificateMonitorPotential_advance_active key budget required stopAfter (.inl input) monitor _ _ hactive,
              signingLogFragment, List.append_nil]
            exact bankedCacheWeight_discard_le _ _ _ _ _
      _ = ∑' record, Pr[= record | originalProposalRecord key (.inl input) monitor.1] *
          bankedProposalRecordValue key nearUniformDigestReuseWeight (budget - monitor.2.spent)
            (signatureLimit - monitor.2.log.length) required (certificateMonitorCoverState monitor) monitor.2.bank
            (.inl input) record false := by
        rw [hkernel, originalProposalRecord, ← PMF.monad_map_eq_map, tsum_probOutput_map_mul]
        rfl
      _ ≤ _ := by
        simpa only [certificateMonitorPotential, certificateMonitorCoverState, hactive.1, certificateMonitorCharge, if_pos hactive] using hbound
  · simp only [worldMonitorValue, certificateMonitorCharge, if_neg hactive, add_zero,
      certificateMonitorPotential_advance_inactive key budget required stopAfter (.inl input) monitor _ _ hactive]
    have hconstant (result : Option (OracleWorld.Range input) × State inputs) :
        (cacheResult result).1.elim (certificateBankCount monitor.2.bank)
          (fun _ => certificateBankCount monitor.2.bank) = certificateBankCount monitor.2.bank := by
      unfold cacheResult
      cases result.1 <;> rfl
    simp only [hconstant, ENNReal.tsum_mul_right]
    exact (mul_le_of_le_one_left' tsum_probOutput_le_one).trans (certificateBankCount_le_bankedCacheWeight _ _ _ _ _)

theorem expected_lazyWorld_certificateMonitor_le (routing : Routing)
    (key : SecretKey) (hparameter : key.parameter = parameter) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (monitor : CertificateMonitorState) (length : Option (OracleWorld.Range input) × State inputs → Nat)
    (state : State inputs) (hcache : state.memory.external.cache = monitor.1)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
        (liftM (OracleWorld.query input)) state] *
      worldMonitorValue key budget required stopAfter input monitor (length result) (cacheResult result)) ≤
      certificateMonitorPotential key budget required monitor + certificateMonitorCharge key budget required (.inl input) monitor := by
  cases input with
  | inl sample =>
      exact expected_lazyWorld_message_certificateMonitor_le parameter inputs hencoding words publicReplies selections rows routing
        key budget required stopAfter (.inl sample) hinputs (by intro hash heq; cases heq) monitor length state hcache hcovered
  | inr hash =>
      by_cases hmessage : MessageHashInput parameter hash
      · exact expected_lazyWorld_message_certificateMonitor_le parameter inputs hencoding words publicReplies selections rows routing
          key budget required stopAfter (.inr hash) hinputs
          (by intro other heq; cases heq; exact hmessage) monitor length state hcache hcovered
      · have hin : hash ∈ inputs := hinputs (by
          simpa only [bind_pure] using mem_hashInputs_hash_bind hash pure)
        exact (expected_lazyWorld_nonmessage_certificateMonitor_le parameter inputs hencoding words publicReplies selections rows routing
          key hparameter budget required stopAfter hash hin hmessage monitor length state hcache ha hcovered).trans le_self_add

theorem expected_externalProgram_certificateMonitor_le
    (key : SecretKey) (hparameter : key.parameter = parameter) (budget : Nat) (required : Finset FtsTree)
    (stopAfter : CertificateStopRule) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (monitor : CertificateMonitorState) (length : Option (OracleWorld.Range input) × State inputs → Nat)
    (state : State inputs) (hcache : state.memory.external.cache = monitor.1)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    (∑' result, Pr[= result | lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs parameter words selections (liftM (OracleWorld.query input))) state] *
      worldMonitorValue key budget required stopAfter input monitor (length result) (cacheResult result)) ≤
      certificateMonitorPotential key budget required monitor + certificateMonitorCharge key budget required (.inl input) monitor := by
  rw [lazyRun_externalProgram]
  exact expected_lazyWorld_certificateMonitor_le parameter inputs hencoding words publicReplies selections rows state.memory.routing
    key hparameter budget required stopAfter input hinputs monitor length state hcache ha hcovered

end SphincsSecurity.Concrete.RetainedResidual

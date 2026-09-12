import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.OriginalTerminalProposal
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredPayment
import SphincsSecurity.Proof.Residual.RetainedResidualProposalIndex
import SphincsSecurity.Proof.Residual.RetainedResidualProposalWord
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  lazyRun environment signDigestLoop ResidualByteFrontend.jointSigningProgram
set_option backward.isDefEq.respectTransparency false

abbrev ProposalState (inputs : Finset HashInput) := List Index × MonitoredState inputs

theorem monitoredSigningResult_completed {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (required : Finset FtsTree) (stopAfter : CertificateStopRule) (message : Message) (length : Nat)
    (fallback : Index) (before : MonitoredState inputs) (result : Option SigningRecord × State inputs) :
    monitoredSigningResult key budget required stopAfter message
        (length, (nativeSigningView result).elim fallback Prod.fst) before result =
      monitoredSigningResult key budget required stopAfter message (length, fallback) before result := by
  rcases result with ⟨record, after⟩
  cases record with
  | none => rfl
  | some record =>
      rcases record with ⟨⟨signature, view⟩, trace⟩
      cases view <;> rfl

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem completedNativeSigning_monitored (message : Message) (length : Nat) (state : MonitoredState inputs) :
    (fun result => monitoredSigningResult key budget required stopAfter message (length, result.2) state result.1) <$>
        completedNativeSigning key inputs hencoding words publicReplies selections rows message state.1 =
      ((liftM (PMF.uniformOfFintype Index) : SPMF Index) >>= fun fallback =>
        monitoredSigningResult key budget required stopAfter message (length, fallback) state <$>
          lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
            (simulateQ (embed inputs state.1.memory.routing)
              (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.1.memory.routing.known words selections message)) state.1) := by
  rw [completedNativeSigning, completeRecordIndex_fallback, map_bind]
  simp only [Functor.map_map, monitoredSigningResult_completed]

noncomputable def proposalStep :
    (input : (OracleWorld + SigningSpec).Domain) → ProposalState inputs →
      SPMF (Option ((OracleWorld + SigningSpec).Range input) × ProposalState inputs)
  | .inl input, state =>
      (fun result => (result.1, state.1, result.2)) <$>
        monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter (.inl input) state.2
  | .inr message, state =>
      if CertificateMonitorActive key budget (.inr message) (monitorView state.2) then
        (fun result =>
          let after := monitoredSigningResult key budget required stopAfter message
            (result.1.length + 1, result.2.2) state.2 result.2.1
          (after.1, state.1 ++ (result.1 ++ [result.2.2]), after.2)) <$>
          attachRejectedWord
            (completedNativeSigning key inputs hencoding words publicReplies selections rows message state.2.1)
            (originalRejectedProposal key (fun current => current.2.spent) (.inr message) (monitorView state.2))
      else
        (fun result => (result.1, state.1, result.2)) <$>
          monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter (.inr message) state.2

theorem proposalStep_erasure (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs) :
    Prod.map id Prod.snd <$>
        proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state =
      monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state.2 := by
  cases input with
  | inl input =>
      rw [proposalStep, Functor.map_map]
      exact id_map' _
  | inr message =>
      rw [proposalStep]
      split_ifs with hactive
      · rw [Functor.map_map]
        calc
          _ = (fun result => monitoredSigningResult key budget required stopAfter message
                (result.1, result.2.2) state.2 result.2.1) <$>
              ((fun result => (result.1.length + 1, result.2)) <$>
                attachRejectedWord
                  (completedNativeSigning key inputs hencoding words publicReplies selections rows message state.2.1)
                  (originalRejectedProposal key (fun current => current.2.spent) (.inr message) (monitorView state.2))) := by
            rw [Functor.map_map]
            rfl
          _ = _ := by
            rw [attachRejectedWord_length, map_bind, monitoredStep, signingAnnotation, if_pos hactive, pmfLift_bind]
            simp only [Functor.map_map, pmfLift_map, bind_assoc, bind_map_left]
            simp_rw [completedNativeSigning_monitored]
      · rw [Functor.map_map]
        exact id_map' _

theorem proposalStep_valid (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs)
    (hvalid : MonitoredValid inputs state.2)
    (result : Option ((OracleWorld + SigningSpec).Range input) × ProposalState inputs)
    (hresult : proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    MonitoredValid inputs result.2.2 := by
  have h := map_nonzero _ (Prod.map id Prod.snd) result hresult
  rw [proposalStep_erasure] at h
  exact monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter
    input state.2 hvalid _ h

theorem proposalStep_complete (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs)
    (hinputs : requestInputs key input ⊆ inputs) (hvalid : MonitoredValid inputs state.2) (total : Nat) :
    (proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state >>= fun result =>
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total result.2.1) : SPMF (List Index))) =
      (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1) : SPMF (List Index)) := by
  cases input with
  | inl input =>
      rw [proposalStep, bind_map_left]
      exact monitoredStep_bind_const key inputs hencoding words publicReplies selections rows budget required stopAfter
        (.inl input) state.2 hvalid.1 (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1))
  | inr message =>
      rw [proposalStep]
      split_ifs with hactive
      · rw [bind_map_left]
        have hbound : ProposalCacheBound key (monitorView state.2).1 (monitorView state.2).2.spent := hactive.2.1.2.1
        rw [originalRejectedProposal, dif_pos hbound]
        exact attachRejectedWord_complete _ Prod.snd
          (originalProposalRecord key (.inr message) (monitorView state.2).1) (fun record => record.index)
          (completedNativeSigning_index key inputs hencoding words publicReplies selections rows message state.2.1
            (digestInputs_of_request key inputs words selections message state.2.1.memory.routing.known hinputs)
            hvalid.1 hvalid.2)
          (originalProposalRecord_cap key message (monitorView state.2).1 (monitorView state.2).2.spent hbound) total state.1
      · rw [bind_map_left]
        exact monitoredStep_bind_const key inputs hencoding words publicReplies selections rows budget required stopAfter
          (.inr message) state.2 hvalid.1 (liftM (completeProposalWord (PMF.uniformOfFintype Index) total state.1))

theorem expected_proposalStep_terminalPotential (input : (OracleWorld + SigningSpec).Domain)
    (state : ProposalState inputs) (hinputs : requestInputs key input ⊆ inputs)
    (hvalid : MonitoredValid inputs state.2) (total : Nat) (payoff : List Index → ENNReal) :
    (∑' result, Pr[= result |
        proposalStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      terminalProposalPotential (PMF.uniformOfFintype Index) total payoff result.2.1) =
        terminalProposalPotential (PMF.uniformOfFintype Index) total payoff state.1 := by
  have h := congrArg (fun law : SPMF (List Index) => ∑' word, Pr[= word | law] * payoff word)
    (proposalStep_complete key inputs hencoding words publicReplies selections rows budget required stopAfter input state hinputs hvalid total)
  rw [tsum_probOutput_bind_mul] at h
  simpa only [terminalProposalPotential, SPMF.probOutput_liftM] using h

end SphincsSecurity.Concrete.RetainedResidual

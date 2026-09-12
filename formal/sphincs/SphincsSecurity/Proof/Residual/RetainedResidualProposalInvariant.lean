import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.CertificateProposalInvariant
import SphincsSecurity.Proof.Residual.RetainedResidualProposalStep
import SphincsSecurity.Proof.Residual.RetainedResidualProposalSupport
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  lazyRun environment signDigestLoop ResidualByteFrontend.jointSigningProgram
set_option backward.isDefEq.respectTransparency false

noncomputable def proposalStop (stopAfter : CertificateStopRule) : CertificateStopRule :=
  fun input state length record => proposalPrefixStop input state length record || stopAfter input state length record

theorem proposalStop_eq (stopAfter : CertificateStopRule) :
    proposalStop stopAfter = fun input state length record =>
      proposalPrefixStop input state length record || stopAfter input state length record := rfl

def ProposalInvariant {inputs : Finset HashInput} (key : SecretKey) (total : Nat) (state : ProposalState inputs) : Prop :=
  CertificateProposalInvariant key total (state.1, monitorView state.2)

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget total : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredWorldResult_proposalInvariant (input : OracleWorld.Domain) (state : ProposalState inputs)
    (hinputs : requestInputs key (.inl input) ⊆ inputs) (hvalid : MonitoredValid inputs state.2)
    (hinv : ProposalInvariant key total state) (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state.2.1 result ≠ 0) :
    ProposalInvariant key total (state.1,
      (monitoredWorldResult key budget required (proposalStop stopAfter) input state.2 result).2) := by
  rcases result with ⟨answer, after⟩
  cases answer with
  | none => intro hpost; cases hpost
  | some answer =>
      by_cases hactive : CertificateMonitorActive key budget (.inl input) (monitorView state.2)
      · have hbefore := hinv hactive.1
        have hstable := lazyWorld_observedViews key inputs hencoding words publicReplies selections rows input state.2.1
          hinputs hvalid.1 hvalid.2 state.2.2.log hactive.2.1.1 (some answer, after) hresult
        dsimp only at hstable
        have hafter := certificateProposalInvariant_advance key budget total required stopAfter (.inl input)
          (state.1, monitorView state.2) [] 0
          (proposalOfWorldResult key.parameter input (answer, after.memory.external.cache)) hinv hactive rfl
          (fun index => by
            change (signingSlotsAtIndex (observedOptionalSigningViews (messageAnswers key.parameter after.memory.external.cache)
              key.root (state.2.2.log ++ [])) index).card ≤ (state.1 ++ []).count index
            rw [List.append_nil, List.append_nil, hstable]
            exact hbefore.counts_le index)
        rw [← proposalStop_eq] at hafter
        simpa only [ProposalInvariant, monitorView, monitoredWorldResult, Option.elim_some,
          originalProposalAdvance, proposalOfWorldResult, List.append_nil] using hafter
      · intro hpost
        change (certificateMonitorUpdate key budget required (proposalStop stopAfter) (.inl input)
          (monitorView state.2) 0 (proposalOfWorldResult key.parameter input (answer, after.memory.external.cache))).stopped = false at hpost
        simp only [certificateMonitorUpdate, if_neg hactive, Bool.true_eq_false] at hpost

theorem completedSigning_proposalInvariant (message : Message) (state : ProposalState inputs)
    (hinputs : requestInputs key (.inr message) ⊆ inputs) (hvalid : MonitoredValid inputs state.2)
    (hinv : ProposalInvariant key total state)
    (hactive : CertificateMonitorActive key budget (.inr message) (monitorView state.2))
    (word : List Index) (result : (Option SigningRecord × State inputs) × Index)
    (hresult : completedNativeSigning key inputs hencoding words publicReplies selections rows message state.2.1 result ≠ 0) :
    ProposalInvariant key total (state.1 ++ (word ++ [result.2]),
      (monitoredSigningResult key budget required (proposalStop stopAfter) message
        (word.length + 1, result.2) state.2 result.1).2) := by
  have hraw := map_nonzero _ Prod.fst result hresult
  rw [completedNativeSigning_record] at hraw
  have hin := digestInputs_of_request key inputs words selections message state.2.1.memory.routing.known hinputs
  obtain ⟨record, hrecord⟩ := lazyRun_jointSigningProgram_some key.parameter inputs hencoding words publicReplies selections rows
    state.2.1.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin)
    state.2.1 hvalid.1 hvalid.2 result.1 hraw
  have heffective : record.1.2.elim result.2 Prod.fst = result.2 := by
    have h := completeRecordIndex_effective _ nativeSigningView result hresult
    simpa only [nativeSigningView, hrecord, Option.bind_some] using h
  have hbefore := hinv hactive.1
  have hafter := certificateProposalInvariant_advance key budget total required stopAfter (.inr message)
    (state.1, monitorView state.2) (word ++ [result.2]) (word.length + 1)
    (proposalOfSigningRecord message record result.1.2.memory.external.cache result.2) hinv hactive
    (by simp only [List.length_append, List.length_singleton]) (fun index => by
      have hc := completedNativeSigning_slots_le key inputs hencoding words publicReplies selections rows message state.2.1
        hin hvalid.1 hvalid.2 state.2.2.log hactive.2.1.1 result hresult record hrecord index
      calc
        _ ≤ _ := hc
        _ ≤ state.1.count index + if result.2 = index then 1 else 0 :=
          Nat.add_le_add_right (hbefore.counts_le index) _
        _ ≤ (state.1 ++ (word ++ [result.2])).count index := by
          simp only [List.count_append, List.count_cons, List.count_nil, beq_iff_eq]
          split_ifs <;> omega)
  rw [← proposalStop_eq] at hafter
  simpa only [ProposalInvariant, monitorView, monitoredSigningResult, hrecord, heffective,
    originalProposalAdvance, proposalOfSigningRecord, Memory.recordSigning] using hafter

theorem proposalStep_invariant (input : (OracleWorld + SigningSpec).Domain) (state : ProposalState inputs)
    (hinputs : requestInputs key input ⊆ inputs) (hvalid : MonitoredValid inputs state.2)
    (hinv : ProposalInvariant key total state)
    (result : Option ((OracleWorld + SigningSpec).Range input) × ProposalState inputs)
    (hresult : proposalStep key inputs hencoding words publicReplies selections rows budget required (proposalStop stopAfter) input state result ≠ 0) :
    ProposalInvariant key total result.2 := by
  cases input with
  | inl input =>
      rw [proposalStep] at hresult
      obtain ⟨middle, hmiddle, rfl⟩ := map_nonzero_source _ _ _ hresult
      rw [monitoredStep] at hmiddle
      obtain ⟨raw, hraw, rfl⟩ := map_nonzero_source _ _ _ hmiddle
      exact monitoredWorldResult_proposalInvariant key inputs hencoding words publicReplies selections rows budget total required stopAfter
        input state hinputs hvalid hinv raw hraw
  | inr message =>
      rw [proposalStep] at hresult
      split_ifs at hresult with hactive
      · obtain ⟨source, hsource, rfl⟩ := map_nonzero_source _ _ _ hresult
        have hrecord := map_nonzero _ Prod.snd source hsource
        rw [attachRejectedWord_record] at hrecord
        exact completedSigning_proposalInvariant key inputs hencoding words publicReplies selections rows budget total required stopAfter
          message state hinputs hvalid hinv hactive source.1 source.2 hrecord
      · obtain ⟨middle, hmiddle, rfl⟩ := map_nonzero_source _ _ _ hresult
        rw [monitoredStep, RetainedObservation.bind_nonzero] at hmiddle
        obtain ⟨annotation, _, hmiddle⟩ := hmiddle
        obtain ⟨raw, _, rfl⟩ := map_nonzero_source _ _ _ hmiddle
        rcases raw with ⟨answer, after⟩
        cases answer with
        | none => intro hpost; cases hpost
        | some record =>
            intro hpost
            change (certificateMonitorUpdate key budget required (proposalStop stopAfter) (.inr message)
              (monitorView state.2) annotation.1
              (proposalOfSigningRecord message record after.memory.external.cache (record.1.2.elim annotation.2 Prod.fst))).stopped = false at hpost
            simp only [certificateMonitorUpdate, if_neg hactive, Bool.true_eq_false] at hpost

end SphincsSecurity.Concrete.RetainedResidual

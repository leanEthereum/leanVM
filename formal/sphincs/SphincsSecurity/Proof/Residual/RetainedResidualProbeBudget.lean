import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualBoundaryCost
import SphincsSecurity.Proof.Residual.RetainedResidualMonitoredErasure
namespace SphincsSecurity.Concrete.ResidualByteFrontend

open CanonicalProbeRouting HiddenLabelObservation ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (actions : inputs → Action inputs)

theorem prepare_probes (input : inputs) (memory : ExternalMemory) :
    (prepare parameter inputs words disclosed known actions input memory).2.probes =
      (charge parameter words disclosed known input.val memory).probes := by
  unfold prepare
  cases memory.cache input.val with
  | some _ => rfl
  | none => cases actions input <;> rfl

theorem hashQueryResult_probes (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    (hashQueryResult parameter inputs words disclosed known actions actual seed input state).2.memory.probes =
      (charge parameter words disclosed known input.val state.memory).probes := by
  have h := prepare_probes parameter inputs words disclosed known actions input state.memory
  unfold hashQueryResult
  generalize hprepared : prepare parameter inputs words disclosed known actions input state.memory = prepared at h ⊢
  rcases prepared with ⟨action, memory⟩
  cases action with
  | known answer => exact h
  | read input => exact h
  | probe input test =>
      dsimp only [executeResult]
      cases hrow : state.rows input with
      | some answer => exact h
      | none => dsimp only; split <;> exact h

end SphincsSecurity.Concrete.ResidualByteFrontend

namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

def ProbeMessageBound (memory : Memory) : Prop :=
  memory.external.probes + memory.messageCalls.length ≤ memory.external.hashCalls

theorem afterReply_messageCount_le (parameter : PublicParameter) (memory : Memory) (input : HashInput)
    (answer : Option HashOutput) (external : ExternalMemory) :
    (memory.afterReply parameter input answer external).messageCalls.length ≤
      memory.messageCalls.length + if FtsProbeSimulation.MessageHashInput parameter input then 1 else 0 := by
  cases answer <;> by_cases hm : FtsProbeSimulation.MessageHashInput parameter input <;>
    simp [Memory.afterReply, Memory.observeMessage, hm]

theorem charge_message_probes (parameter : PublicParameter) (words : OtsReferenceWords) (routing : Routing)
    (input : HashInput) (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (memory : ExternalMemory) :
    (charge parameter words routing.disclosed routing.known input memory).probes = memory.probes := by
  have hdecode : decodePosition parameter input = none := by
    obtain ⟨payload, hinput⟩ := hmessage
    rw [← hinput]
    exact decodePosition_message parameter payload
  unfold charge
  cases memory.cache input with
  | some _ => rfl
  | none => simp only [route, hdecode, Option.elim_none, Nat.add_zero]

theorem applyBoundary_probeMessageBound (memory : Memory) (hbound : ProbeMessageBound memory) (trace : SigningBoundaryTrace) :
    ProbeMessageBound (memory.applyBoundary trace) := by
  have hlength : trace.messageCalls.length ≤ trace.hashCalls := List.length_filterMap_le _ _
  change memory.external.probes + (memory.messageCalls ++ trace.messageCalls).length ≤ memory.external.hashCalls + trace.hashCalls
  rw [List.length_append]
  change memory.external.probes + memory.messageCalls.length ≤ memory.external.hashCalls at hbound
  omega

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_probes (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) :
    (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.probes =
      (charge parameter words routing.disclosed routing.known input.val state.memory.external).probes := by
  have hproject := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => result.2.memory.probes)
    (hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  change (hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.probes = _
  exact hproject.trans (ResidualByteFrontend.hashQueryResult_probes parameter inputs words routing.disclosed routing.known
    (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows) actual seed input (project state))

theorem checkedHashResult_probeMessageBound (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hbound : ProbeMessageBound state.memory) :
    ProbeMessageBound (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory := by
  let result := checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hp := checkedHashResult_probes parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hh := checkedHashResult_hashCalls parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  have hm := afterReply_messageCount_le parameter state.memory input.val result.1 result.2.memory.external
  have hmemory := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  dsimp only at hmemory
  rw [← hmemory] at hm
  change ProbeMessageBound result.2.memory
  change result.2.memory.external.probes + result.2.memory.messageCalls.length ≤ result.2.memory.external.hashCalls
  dsimp only [result] at hm ⊢
  change state.memory.external.probes + state.memory.messageCalls.length ≤ state.memory.external.hashCalls at hbound
  by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input.val
  · rw [charge_message_probes parameter words routing input.val hmessage state.memory.external] at hp
    rw [if_pos hmessage] at hm
    omega
  · have hp' := charge_probes_le parameter words routing.disclosed routing.known input.val state.memory.external
    rw [if_neg hmessage] at hm
    omega

theorem lazyByteRun_world_probeMessageBound (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty) (hbound : ProbeMessageBound state.memory)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state result ≠ 0) : ProbeMessageBound result.2.memory := by
  cases input with
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [lazyByteRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbound
  | inr input =>
      have hin : input ∈ inputs := by
        apply hinputs
        rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
        exact mem_hashInputs_hash_bind input pure
      obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows routing input hin state ha result hresult
      exact checkedHashResult_probeMessageBound parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state hbound

omit parameter hencoding in
theorem lazyRun_signingProgram_probeMessageBound (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (message : Message)
    (hinputs : hashInputs (signWithView key message) ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : ProbeMessageBound state.memory)
    (result : Option (Option Signature) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (signingProgram inputs key.parameter key.root words selections message) state result ≠ 0) :
    ProbeMessageBound result.2.memory := by
  rw [lazyRun_signingProgram key inputs hencoding words publicReplies selections rows message state,
    map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨raw, hraw, hresult⟩ := hresult
  have hloop := (ResidualByteFrontend.hashInputs_publicSigningWork_subset_signWithView key state.memory.routing.known words selections message).trans hinputs
  rw [ResidualByteFrontend.hashInputs_publicSigningWork] at hloop
  obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
    state.memory.routing key.root message hloop state ha hcovered raw hraw
  simp only [Function.comp_def, hrecord, Option.elim_some, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  change ProbeMessageBound raw.2.memory
  rw [hmemory]
  exact applyBoundary_probeMessageBound state.memory hbound record.2

omit parameter hencoding in
theorem lazyRun_request_probeMessageBound (key : SecretKey)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (input : (OracleWorld + SigningSpec).Domain)
    (hinputs : requestInputs key input ⊆ inputs) (state : State inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hbound : ProbeMessageBound state.memory)
    (result : Option ((OracleWorld + SigningSpec).Range input) × State inputs)
    (hresult : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
      (adversaryImpl inputs key.parameter key.root words selections input) state result ≠ 0) : ProbeMessageBound result.2.memory := by
  cases input with
  | inl input =>
      change lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (externalProgram inputs key.parameter words selections (liftM (OracleWorld.query input))) state result ≠ 0 at hresult
      rw [lazyRun_externalProgram] at hresult
      exact lazyByteRun_world_probeMessageBound key.parameter inputs hencoding words publicReplies selections rows
        state.memory.routing input hinputs state ha hbound result hresult
  | inr message =>
      exact lazyRun_signingProgram_probeMessageBound inputs words publicReplies selections rows key hencoding message hinputs state
        ha hcovered hbound result hresult

variable (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
  (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
  (q : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule) (stopped : Bool)

end SphincsSecurity.Concrete.RetainedResidual

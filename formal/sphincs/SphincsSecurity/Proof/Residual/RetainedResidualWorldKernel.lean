import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualCheckedTrace
import SphincsSecurity.Proof.Residual.RetainedResidualDigestLaw
import SphincsSecurity.Proof.Residual.RetainedResidualProgram
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing)
open FtsProbeSimulation (messageAnswers MessageHashInput)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem checkedHashResult_cache_of_ne (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (other : HashInput) (hne : other ≠ input.val) :
    (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache other =
      state.memory.external.cache other := by
  have hp := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => result.2.memory.cache other)
    (hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  have hr := congrArg (fun result : Option HashOutput × ExternalMemory => result.2.cache other)
    (ResidualByteFrontend.hashQueryResult_project parameter inputs words routing.disclosed routing.known
      (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
      actual seed input (project state) hcovered
      (freshPrefix_local parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input))
  change (hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache other = _
  apply hp.trans
  apply hr.trans
  generalize ResidualByteFrontend.publicCachedReply inputs
    (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
    actual seed input (project state).memory = answer
  cases answer <;> simp only [ResidualByteFrontend.delivered, Option.elim_none, Option.elim_some,
    charge, storeReply, Function.update_of_ne hne, project]

theorem checkedHashResult_nonmessage (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmessage : ¬MessageHashInput parameter input.val) :
    messageAnswers parameter
      (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.cache =
      messageAnswers parameter state.memory.external.cache := by
  funext payload
  apply checkedHashResult_cache_of_ne parameter inputs hencoding words publicReplies selections rows routing actual seed input state hcovered
  intro heq
  exact hmessage ⟨payload, heq⟩

theorem lazyByteRun_hash_nonmessage (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hmessage : ¬MessageHashInput parameter input)
    (result : Option HashOutput × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query (.inr input))) state result ≠ 0) :
    messageAnswers parameter result.2.memory.external.cache = messageAnswers parameter state.memory.external.cache := by
  unfold lazyByteRun at hresult
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  simp only [simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin] at hresult
  rw [observedRun_checkedHashQuery parameter inputs hencoding words publicReplies selections rows routing actual seed
    ⟨input, hin⟩ state] at hresult
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  exact checkedHashResult_nonmessage parameter inputs hencoding words publicReplies selections rows routing actual seed
    ⟨input, hin⟩ state hcovered hmessage

theorem lazyByteRun_world_message_rom (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (hmessage : ∀ hash, input = .inr hash → MessageHashInput parameter hash)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) :
    cacheResult <$> lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state =
      Prod.map some id <$> 𝒟[(romImpl input).run state.memory.external.cache] := by
  have hm : ResidualByteFrontend.MessageOnly parameter (liftM (OracleWorld.query input)) := by
    rw [← bind_pure (liftM (OracleWorld.query input))]
    apply ResidualByteFrontend.messageOnly_query_bind
    · cases input with
      | inl _ => trivial
      | inr hash => exact hmessage hash rfl
    · intro answer
      exact ResidualByteFrontend.messageOnly_pure parameter answer
  simpa only [simulateQ_spec_query] using
    lazyByteRun_message_rom parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) hinputs hm state hcovered

theorem lazyRun_routing_bind {Result : Type} (next : Routing → OracleComp (World inputs) Result) (state : State inputs) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (currentRouting inputs >>= next) state =
      lazyRun (environment parameter inputs hencoding words publicReplies selections rows) (next state.memory.routing) state := by
  rw [currentRouting, lazyRun, runWith_query_bind]
  simp only [lazyImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind, Option.elim_some, lazyRun]

theorem lazyRun_externalProgram {Result : Type} (computation : OracleComp OracleWorld Result) (state : State inputs) :
    lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (externalProgram inputs parameter words selections computation) state =
      lazyByteRun parameter inputs hencoding words publicReplies selections rows state.memory.routing computation state := by
  rw [externalProgram, lazyRun_routing_bind]
  rfl

end SphincsSecurity.Concrete.RetainedResidual

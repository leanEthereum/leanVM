import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualByteRun
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def Memory.applyBoundary (memory : Memory) (trace : SigningBoundaryTrace) : Memory :=
  { memory with
    external := ResidualByteFrontend.applyBoundary memory.external trace
    messageCalls := memory.messageCalls ++ trace.messageCalls }

theorem applyBoundary_one (memory : Memory) : memory.applyBoundary 1 = memory := by
  simp only [Memory.applyBoundary, ResidualByteFrontend.applyBoundary_one,
    show SigningBoundaryTrace.messageCalls 1 = [] from rfl, List.append_nil]

theorem applyBoundary_mul (memory : Memory) (left right : SigningBoundaryTrace) :
    memory.applyBoundary (left * right) = (memory.applyBoundary left).applyBoundary right := by
  simp only [Memory.applyBoundary, ResidualByteFrontend.applyBoundary_mul, SigningBoundaryTrace.messageCalls_mul, List.append_assoc]

theorem fixedHashStep_message (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (memory : Memory) :
    fixedHashStep parameter words selections routing actual oracle input memory =
      (some (oracle input), memory.applyBoundary (signingBoundaryTrace parameter (.inr input) (oracle input))) := by
  rw [fixedHashStep, ResidualByteFrontend.checkedFixedStep_message parameter words routing.disclosed routing.known actual
    (knownEncodingMessage routing.known) selections oracle input hmessage memory.external]
  simp only [ResidualByteFrontend.messageStep, Memory.afterReply, Option.elim_some, Memory.observeMessage,
    Memory.applyBoundary,
    signingBoundaryTrace, if_pos hmessage]
  rfl

theorem fixedByteRun_message_trace {Result : Type} (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) (hmessage : ResidualByteFrontend.MessageOnly parameter computation) (memory : Memory) :
    fixedByteRun parameter words selections routing actual oracle computation memory =
      (fun result => (some result.1, memory.applyBoundary result.2)) <$> 𝒟[fixedBoundaryRun parameter oracle computation] := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure value => simp only [fixedByteRun_pure, fixedBoundaryRun_pure, evalDist_pure, map_pure, applyBoundary_one]
  | query_bind input next ih =>
      have hnext : ∀ answer, ResidualByteFrontend.MessageOnly parameter (next answer) :=
        fun answer row hrow => hmessage row ((hashInputs_next_subset input next answer) hrow)
      rw [fixedByteRun_query_bind, ResidualByteFrontend.fixedBoundaryRun_query_bind]
      cases input with
      | inl input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, fixedHashWorld, evalDist_bind,
            evalDist_query, signingBoundaryTrace, one_mul, evalDist_map, bind_assoc, pure_bind, Option.elim_some, map_bind]
          apply congrArg (_ >>= ·)
          funext answer
          simpa only [Functor.map_map, Function.comp_def] using ih answer (hnext answer) memory
      | inr input =>
          have hat := hmessage input (mem_hashInputs_hash_bind input next)
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk,
            fixedHashStep_message parameter words selections routing actual oracle input hat,
            fixedHashWorld, pure_bind, Option.elim_some, evalDist_map, Functor.map_map]
          rw [ih (oracle input) (hnext (oracle input))]
          congr 1
          funext result
          rw [applyBoundary_mul]

theorem byteRun_message_trace {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (oracle : QueryImpl HashSpec Id)
    (hfresh : ∀ input : inputs, ResidualByteAction.eval actual seed
      (ResidualByteAction.freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input) =
      ResidualByteFrontend.fixedAnswer parameter words routing.disclosed actual oracle input.val)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (hmessage : ResidualByteFrontend.MessageOnly parameter computation) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches oracle state.memory.external.cache)
    (hclean : CacheClean parameter words routing.disclosed actual state.memory.external.cache) :
    forgetState <$> byteRun parameter inputs hencoding words publicReplies selections rows routing actual seed computation state =
      (fun result => (some result.1, state.memory.applyBoundary result.2)) <$> 𝒟[fixedBoundaryRun parameter oracle computation] := by
  rw [byteRun_eq_fixed parameter inputs hencoding words publicReplies selections rows routing actual seed oracle hfresh
    computation hinputs state hcovered hmatches hclean, fixedByteRun_message_trace parameter words selections routing actual oracle computation hmessage]

end SphincsSecurity.Concrete.RetainedResidual

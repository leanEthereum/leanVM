import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualHashTrace
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem hashResult_project (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    projectResult (hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state) =
      ResidualByteFrontend.hashQueryResult parameter inputs words routing.disclosed routing.known
        (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
        actual seed input (project state) := by
  have h := observedRun_embed parameter inputs hencoding words publicReplies selections rows routing actual seed
    (ResidualByteFrontend.hashQuery input) state
  rw [observedRun_hashQuery, ResidualByteFrontend.observedRun_hashQuery, map_pure] at h
  have h := congrArg SPMF.support h
  simpa only [SPMF.support_pure, Set.singleton_eq_singleton_iff] using h

theorem observedRun_stop (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (embed inputs routing (.inl .stop)) state = pure (none, state) := by
  simp only [embed, observedRun, runWith, simulateQ_spec_query, observedImpl, environment,
    ResidualByteFrontend.environment, OptionT.run_mk, StateT.run_mk, PMF.pure_map, SPMF.lift_pure, pure_bind, afterControl, project]

noncomputable def checkedHashResult (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    Option HashOutput × State inputs :=
  ResidualByteFrontend.checkedResult (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
    input.val (hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state)

theorem observedRun_checkedHashQuery (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) (ResidualByteFrontend.checkedHashQuery
        (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input)) state =
      pure (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state) := by
  rw [ResidualByteFrontend.checkedHashQuery, simulateQ_bind, observedRun_bind, observedRun_hashQuery, pure_bind]
  unfold checkedHashResult
  generalize hresult : hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state = result
  rcases result with ⟨answer, after⟩
  cases answer with
  | none => rfl
  | some answer =>
      change _ = pure (ResidualByteFrontend.checkedResult _ input.val (some answer, after))
      dsimp only [Option.elim_some, ResidualByteFrontend.checkedResult, Option.bind_some]
      split
      · rw [simulateQ_spec_query, observedRun_stop]
      · rw [simulateQ_pure, observedRun, runWith_pure]

theorem checkedHashResult_memory (routing : Routing) (actual : Labels) (seed : inputs → HashOutput) (input : inputs) (state : State inputs) :
    let result := checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state
    result.2.memory = state.memory.afterReply parameter input.val result.1 result.2.memory.external := by
  have h := hashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed input state
  dsimp only at h ⊢
  unfold checkedHashResult
  generalize hresult : hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state = result at *
  rcases result with ⟨answer, after⟩
  cases answer with
  | none => exact h
  | some answer =>
      simp only [ResidualByteFrontend.checkedResult, Option.bind_some]
      split
      · rename_i hmatch
        have hnot : ¬FtsProbeSimulation.MessageHashInput parameter input.val := by
          intro hmessage
          obtain ⟨position, hat, _⟩ := hmatch
          exact ResidualByteFrontend.message_not_encoding parameter input.val hmessage position hat
        simpa only [Memory.afterReply, Option.elim_some, Option.elim_none, Memory.observeMessage, if_neg hnot] using h
      · exact h

noncomputable def fixedHashStep (routing : Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : Memory) :
    Option HashOutput × Memory :=
  let result := ResidualByteFrontend.checkedResult (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections)
    input (ResidualByteFrontend.fixedStep parameter words routing.disclosed routing.known actual oracle input memory.external)
  (result.1, memory.afterReply parameter input result.1 result.2)

theorem checkedHashResult_eq_fixed (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (oracle : QueryImpl HashSpec Id) (input : inputs) (state : State inputs)
    (hfresh : ResidualByteAction.eval actual seed
      (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input) =
      ResidualByteFrontend.fixedAnswer parameter words routing.disclosed actual oracle input.val)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hmatches : ResidualByteFrontend.CacheMatches oracle state.memory.external.cache)
    (hclean : CacheClean parameter words routing.disclosed actual state.memory.external.cache) :
    let result := checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state
    (result.1, result.2.memory) = fixedHashStep parameter words selections routing actual oracle input.val state.memory := by
  have hproject := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => (result.1, result.2.memory))
    (hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  have hfixed := ResidualByteFrontend.hashQueryResult_eq_fixed parameter inputs words routing.disclosed routing.known
    (freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
    actual seed oracle input (project state) hcovered
    (freshPrefix_local parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows input) hmatches hclean hfresh
  dsimp only [projectResult, project] at hproject
  have h := congrArg (ResidualByteFrontend.checkedResult
    (PublicEncodingMatch.Match parameter (knownEncodingMessage routing.known) words selections) input.val) (hproject.trans hfixed)
  change ((checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).1,
    (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external) = _ at h
  dsimp only
  rw [checkedHashResult_memory]
  exact congrArg (fun result => (result.1, state.memory.afterReply parameter input.val result.1 result.2)) h

end SphincsSecurity.Concrete.RetainedResidual

import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualProgram
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

def Memory.history (memory : Memory) := (memory.routing, memory.log, memory.records)

theorem observeMessage_history (parameter : PublicParameter) (memory : Memory) (input : HashInput) (answer : HashOutput) :
    (memory.observeMessage parameter input answer).history = memory.history := by
  unfold Memory.observeMessage
  split <;> rfl

theorem afterControl_history (parameter : PublicParameter) (inputs : Finset HashInput)
    (memory : Memory) (input : ResidualByteFrontend.Control inputs) (external : ExternalMemory) :
    (afterControl parameter inputs memory input external).history = memory.history := by
  cases input with
  | prepare input =>
      simp only [afterControl]
      cases memory.external.cache input.val with
      | none => rfl
      | some answer => exact observeMessage_history parameter _ _ _
  | random _ => rfl
  | account _ => rfl
  | stop => rfl

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem observedRun_embed_query_history (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : (ResidualByteFrontend.World inputs).Domain) (state : State inputs)
    (result : Option ((ResidualByteFrontend.World inputs).Range input) × State inputs)
    (hresult : observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (embed inputs routing input) state result ≠ 0) : result.2.memory.history = state.memory.history := by
  cases input with
  | inl input =>
      simp only [embed, observedRun, runWith, simulateQ_spec_query, observedImpl, environment,
        OptionT.run_mk, StateT.run_mk, ← PMF.monad_map_eq_map, liftM_map, bind_map_left] at hresult
      obtain ⟨after, _, hresult⟩ := (RetainedObservation.bind_nonzero _ _ _).mp hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact afterControl_history parameter inputs state.memory input after.2
  | inr input =>
      simp only [embed, observedRun, runWith, simulateQ_spec_query] at hresult
      cases input with
      | read input =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact observeMessage_history parameter _ _ _
      | probe input test =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk] at hresult
          cases hrow : state.rows input with
          | some answer =>
              simp only [hrow, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              subst result
              exact observeMessage_history parameter _ _ _
          | none =>
              simp only [hrow] at hresult
              split at hresult
              all_goals
                simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
                subst result
              · exact observeMessage_history parameter _ _ _
              · rfl
      | disclose coordinate =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          rfl

theorem observedRun_embed_history {Result : Type} (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp (ResidualByteFrontend.World inputs) Result) (state : State inputs)
    (result : Option Result × State inputs)
    (hresult : observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed
      (simulateQ (embed inputs routing) computation) state result ≠ 0) : result.2.memory.history = state.memory.history := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, observedRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, observedRun_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hafter, hresult⟩ := hresult
      have hhistory := observedRun_embed_query_history parameter inputs hencoding words publicReplies selections rows
        routing actual seed input state (answer, after) hafter
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hhistory
      | some answer => exact (ih answer after hresult).trans hhistory

end SphincsSecurity.Concrete.RetainedResidual

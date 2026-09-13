import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualSource
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

theorem fixedSourceRun_compatible {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (memory : Memory)
    (hcompatible : Compatible context memory) (value : Result) (after : Memory)
    (hresult : fixedSourceRun context computation memory (some value, after) ≠ 0) : Compatible context after := by
  induction computation using OracleComp.inductionOn generalizing memory value after with
  | pure value =>
      simp only [fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq] at hresult
      exact hresult.2 ▸ hcompatible
  | query_bind input next ih =>
      rw [fixedSourceRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, middle⟩, hmiddle, hresult⟩ := hresult
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, Prod.mk.injEq, Option.some_ne_none, false_and, not_not] at hresult
      | some answer =>
          exact ih answer middle (fixedSourceImpl_compatible context input memory hcompatible answer middle hmiddle) value after hresult

theorem observedRun_source_memory {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs context.key computation ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) :
    forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections) computation) state =
      fixedSourceRun context computation state.memory := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, observedRun, runWith_pure, map_pure, forgetState, fixedSourceRun_pure]
  | query_bind input next ih =>
      have hhead := (requestInputs_subset context.key input next).trans hinputs
      have hnext := fun answer => (sourceInputs_next_subset context.key input next answer).trans hinputs
      unfold Context.environment
      rw [simulateQ_bind, simulateQ_spec_query, observedRun_bind, map_bind, fixedSourceRun_query_bind,
        ← observedRun_request_memory context input hhead state hcovered hcompatible, bind_map_left]
      apply RetainedObservation.bind_congr
      rintro ⟨answer, after⟩ hafter
      cases answer with
      | none => simp only [Option.elim_none, map_pure, forgetState]
      | some answer =>
          have hcovered' := observedRun_rowsCovered context.key.parameter inputs context.encoding context.words context.publicReplies
            context.auxiliary.selections context.auxiliary.rows context.actual context.auxiliary.seed _ state hcovered (some answer, after) hafter
          have hcompatible' := observedRun_request_compatible context input hhead state hcovered hcompatible answer after hafter
          exact ih answer (hnext answer) after hcovered' hcompatible'

end SphincsSecurity.Concrete.RetainedResidual

import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.PrefixEncodingRisk
import SphincsSecurity.Proof.Residual.RetainedResidualExecution
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

theorem map_nonzero {A B : Type} (law : SPMF A) (f : A → B) (value : A) (hvalue : law value ≠ 0) :
    (f <$> law) (f value) ≠ 0 := by
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
  exact ⟨value, hvalue, by
    change (pure (f value) : SPMF B) (f value) ≠ 0
    rw [SPMF.pure_apply_self]
    exact one_ne_zero⟩

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem observedImpl_rowsCovered (actual : Labels) (seed : inputs → HashOutput)
    (input : (World inputs).Domain) (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option ((World inputs).Range input) × State inputs)
    (hresult : (observedImpl (environment parameter inputs hencoding words publicReplies selections rows) actual seed input).run.run state result ≠ 0) :
    ResidualByteFrontend.RowsCovered inputs (project result.2) := by
  cases input with
  | inl input =>
      cases input with
      | byte routing input =>
          have hproject := observedRun_embed_query parameter inputs hencoding words publicReplies selections rows routing actual seed (.inl input) state
          simp only [embed, observedRun, runWith, simulateQ_spec_query] at hproject
          have h := map_nonzero _ projectResult result hresult
          rw [hproject] at h
          exact ResidualByteFrontend.lazyImpl_rowsCovered parameter inputs words routing.disclosed routing.known
            (ResidualByteAction.freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
            (.inl input) (project state) hcovered (projectResult result) h
      | routing =>
          simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind,
            ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
      | transcript =>
          simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind,
            ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
      | record message record =>
          simp only [observedImpl, environment, OptionT.run_mk, StateT.run_mk, SPMF.lift_pure, pure_bind,
            ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered
  | inr input =>
      cases input with
      | read input =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          simpa only [project, readState, environment, observeMessage_external] using
            ResidualByteFrontend.rowsCovered_store inputs (project state) hcovered state.candidates input (seed input)
      | probe input test =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk] at hresult
          cases hrow : state.rows input with
          | some answer =>
              simp only [hrow, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
              subst result
              simpa only [project, readState, environment, observeMessage_external] using
                ResidualByteFrontend.rowsCovered_store inputs (project state) hcovered state.candidates input answer
          | none =>
              simp only [hrow] at hresult
              split at hresult
              all_goals
                simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
                subst result
              · simpa only [project, probeState, environment, observeMessage_external] using
                  ResidualByteFrontend.rowsCovered_store inputs (project state) hcovered (test.restrict state.candidates (seed input)) input (seed input)
              · exact hcovered
      | disclose coordinate =>
          simp only [observedImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered

theorem observedRun_rowsCovered {Result : Type} (actual : Labels) (seed : inputs → HashOutput)
    (computation : OracleComp (World inputs) Result) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (result : Option Result × State inputs)
    (hresult : observedRun (environment parameter inputs hencoding words publicReplies selections rows) actual seed computation state result ≠ 0) :
    ResidualByteFrontend.RowsCovered inputs (project result.2) := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [observedRun, runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hcovered
  | query_bind input next ih =>
      rw [observedRun, runWith_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hafter, hresult⟩ := hresult
      have hcovered' := observedImpl_rowsCovered parameter inputs hencoding words publicReplies selections rows
        actual seed input state hcovered (answer, after) hafter
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hcovered'
      | some answer => exact ih answer after hcovered' result hresult

end SphincsSecurity.Concrete.RetainedResidual

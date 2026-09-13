import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.Concrete.WeightedQuery

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {Index State : Type} {spec : OracleSpec Index}

noncomputable def implementation (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) : QueryImpl spec (StateT (State × ENNReal) SPMF) :=
  fun input => StateT.mk fun state =>
    (fun result => (result.1, (result.2, state.2 * factor state.1 input))) <$> (base input).run state.1

noncomputable def run {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (computation : OracleComp spec Result) (state : State × ENNReal) :=
  (simulateQ (implementation base factor) computation).run state

theorem run_forget {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (computation : OracleComp spec Result) (state : State × ENNReal) :
    (fun result => (result.1, result.2.1)) <$> run base factor computation state =
      (simulateQ base computation).run state.1 := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation,
        StateT.run_mk, bind_map_left, map_bind]
      exact congrArg ((base input).run state.1 >>= ·) (funext fun result => ih result.1 _)

theorem run_payoff {Result : Type} (left right : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal)
    (hstep : ∀ state input result, (left input).run state result = factor state input * (right input).run state result)
    (computation : OracleComp spec Result) (state : State) (weight : ENNReal) (payoff : Result × State → ENNReal) :
    weight * (∑' result, Pr[= result | (simulateQ left computation).run state] * payoff result) =
      ∑' result, Pr[= result | run right factor computation (state, weight)] *
        (result.2.2 * payoff (result.1, result.2.1)) := by
  induction computation using OracleComp.inductionOn generalizing state weight with
  | pure value => simp only [run, simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation,
        StateT.run_mk, bind_map_left, tsum_probOutput_bind_mul]
      simp only [run] at ih
      simp_rw [← ih]
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro result
      simp only [SPMF.probOutput_eq_apply, hstep]
      ring

theorem run_preserves {Result : Type} (base : QueryImpl spec (StateT State SPMF))
    (factor : State → spec.Domain → ENNReal) (invariant : State × ENNReal → Prop)
    (hstep : ∀ state, invariant state → ∀ input result, (base input).run state.1 result ≠ 0 →
      invariant (result.2, state.2 * factor state.1 input))
    (computation : OracleComp spec Result) (state : State × ENNReal) (hs : invariant state)
    (result : Result × State × ENNReal) (hr : run base factor computation state result ≠ 0) : invariant result.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [run, simulateQ_pure, StateT.run_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact hs
  | query_bind input next ih =>
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, implementation, StateT.run_mk,
        bind_map_left, RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hm, hr⟩ := hr
      exact ih middle.1 (middle.2, state.2 * factor state.1 input) (hstep state hs input middle hm) result hr

end SphincsSecurity.Concrete.WeightedQuery

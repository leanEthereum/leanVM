import SphincsSecurity.Proof.Base.QueryPause
namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index Memory Result : Type} {spec : OracleSpec Index}
  (stop : Memory → Prop) [DecidablePred stop]
  (step : (input : spec.Domain) → spec.Range input → Memory → Memory)

theorem run_invariant (invariant : Memory → Prop)
    (hstep : ∀ memory, invariant memory → ¬stop memory → ∀ input answer, invariant (step input answer memory))
    (computation : OracleComp spec Result) (memory : Memory) (hinitial : invariant memory)
    (result : Memory × OracleComp spec Result) (hresult : result ∈ support (run stop step computation memory)) :
    invariant result.1 := by
  induction computation using OracleComp.inductionOn generalizing memory result with
  | pure value =>
      rw [run_pure, mem_support_pure_iff] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : stop memory
      · rw [if_pos hs, mem_support_pure_iff] at hresult
        subst result
        exact hinitial
      · rw [if_neg hs, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        exact ih answer (step input answer memory) (hstep memory hinitial hs input answer) result hresult

theorem run_stopped_or_finished (computation : OracleComp spec Result) (memory : Memory)
    (result : Memory × OracleComp spec Result) (hresult : result ∈ support (run stop step computation memory)) :
    stop result.1 ∨ ∃ value, result.2 = pure value := by
  induction computation using OracleComp.inductionOn generalizing memory result with
  | pure value =>
      rw [run_pure, mem_support_pure_iff] at hresult
      subst result
      exact Or.inr ⟨value, rfl⟩
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : stop memory
      · rw [if_pos hs, mem_support_pure_iff] at hresult
        subst result
        exact Or.inl hs
      · rw [if_neg hs, mem_support_bind_iff] at hresult
        obtain ⟨answer, _, hresult⟩ := hresult
        exact ih answer (step input answer memory) result hresult

theorem run_simulation_invariant {State : Type} (impl : QueryImpl spec (StateT State PMF))
    (invariant : Memory → State → Prop)
    (hstep : ∀ memory state, invariant memory state → ¬stop memory → ∀ input,
      ∀ result ∈ ((impl input).run state).support, invariant (step input result.1 memory) result.2)
    (computation : OracleComp spec Result) (memory : Memory) (state : State) (hinitial : invariant memory state)
    (result : (Memory × OracleComp spec Result) × State)
    (hresult : result ∈ ((simulateQ impl (run stop step computation memory)).run state).support) :
    invariant result.1.1 result.2 := by
  induction computation using OracleComp.inductionOn generalizing memory state result with
  | pure value =>
      simp only [run_pure, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact hinitial
  | query_bind input next ih =>
      rw [run_query_bind] at hresult
      by_cases hs : stop memory
      · simp only [if_pos hs, simulateQ_pure, StateT.run_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hresult
        subst result
        exact hinitial
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
          PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hresult
        obtain ⟨middle, hmiddle, hresult⟩ := hresult
        exact ih middle.1 (step input middle.1 memory) middle.2
          (hstep memory state hinitial hs input middle hmiddle) result hresult

end SphincsSecurity.QueryPause

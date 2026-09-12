import SphincsSecurity.Proof.Base.QueryCapState
import SphincsSecurity.Proof.Chains.AdaptiveChainCountedRows
import SphincsSecurity.Proof.Base.QueryPause
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Memory : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) → result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
  (hsmall : budget < Fintype.card State)

include hcharge hreal hsmall

theorem lazyRun_counted_le_of_real (endpoint : State) (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support) :
    result.1.2 ≤ budget := by
  apply QueryCap.counted_state_le_of_cap_valid IsPrefixQuery (lazyImpl (auxiliary endpoint)) (computation endpoint) budget
    (fun _ _ => none) _ result hresult
  intro capped hcapped
  have hsource : (endpoint, capped) ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).support := by
    rw [idealRun, PMF.mem_support_bind_iff]
    refine ⟨endpoint, PMF.mem_support_uniformOfFintype endpoint, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨capped, hcapped, rfl⟩
  obtain ⟨finished, hfinished, _⟩ := idealRun_cap_valid auxiliary computation cost budget hcharge hreal hsmall (endpoint, capped) hsource
  change capped.1 = some finished at hfinished
  rw [hfinished]
  exact Option.some_ne_none finished

theorem lazyRun_pause_budget_of_real (endpoint : State) (stop : Memory → Prop) [DecidablePred stop]
    (step : (input : (auxSpec + PrefixSpec n State).Domain) → (auxSpec + PrefixSpec n State).Range input → Memory → Memory)
    (memory : Memory)
    (middle : ((Memory × OracleComp (auxSpec + PrefixSpec n State) Result) × Nat) × (Fin n → State → Option State))
    (hmiddle : middle ∈ (lazyRun (auxiliary endpoint)
      (QueryCap.counted IsPrefixQuery (QueryPause.run stop step (computation endpoint) memory)) (fun _ _ => none)).support)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery middle.1.1.2) middle.2).support) :
    queryCount middle.2 + result.1.2 ≤ budget ∧ queryCount result.2 ≤ budget := by
  have hfull : ((result.1.1, middle.1.2 + result.1.2), result.2) ∈
      (lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).support := by
    rw [← QueryPause.counted_resume stop step IsPrefixQuery (computation endpoint) memory]
    simp only [lazyRun, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    exact ⟨middle, hmiddle, result, hresult, rfl⟩
  have htotal := lazyRun_counted_le_of_real auxiliary computation cost budget hcharge hreal hsmall endpoint _ hfull
  have hpast := lazyRun_counted_queryCount_le (auxiliary endpoint) (QueryPause.run stop step (computation endpoint) memory)
    (fun _ _ => none) middle hmiddle
  simp only [queryCount_empty, Nat.zero_add] at hpast
  have hrows := lazyRun_counted_queryCount_le (auxiliary endpoint) middle.1.1.2 middle.2 result hresult
  exact ⟨(Nat.add_le_add_right hpast _).trans htotal, hrows.trans ((Nat.add_le_add_right hpast _).trans htotal)⟩

end SphincsSecurity.Concrete.PartialChainEndpoint

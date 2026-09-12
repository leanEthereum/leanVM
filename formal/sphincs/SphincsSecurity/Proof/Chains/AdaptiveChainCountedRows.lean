import SphincsSecurity.Proof.Chains.AdaptiveChainCapContact
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}

theorem lazyRun_counted_queryCount_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed).support) :
    queryCount result.2 ≤ queryCount observed + result.1.2 := by
  induction computation using OracleComp.inductionOn generalizing observed result with
  | pure value =>
      rw [QueryCap.counted_pure, lazyRun_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact le_rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
            lazyImpl, StateT.run_mk, PMF.bind_map, Function.comp_def, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, tail, htail, rfl⟩ := hresult
          simpa only [IsPrefixQuery, if_false, Nat.zero_add] using ih answer observed tail htail
      | inr query =>
          simp only [QueryCap.counted_query_bind, bind_pure_comp, lazyRun_query_bind, lazyRun_map,
            lazyImpl, StateT.run_mk, PMF.bind_map, Function.comp_def, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, tail, htail, rfl⟩ := hresult
          have ht := ih answer (record observed query answer) tail htail
          have hr := queryCount_record_le observed query answer
          simp only [IsPrefixQuery, if_true]
          omega

theorem lazyRun_counted_budget_le (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget)
    (result : (Result × Nat) × (Fin n → State → Option State))
    (hresult : result ∈ (lazyRun auxiliary (QueryCap.counted IsPrefixQuery computation) observed).support) :
    result.1.2 ≤ budget :=
  QueryCap.counted_le_of_queryBound IsPrefixQuery computation budget hbound result.1
    (lazyRun_result_mem auxiliary (QueryCap.counted IsPrefixQuery computation) observed result hresult)

end SphincsSecurity.Concrete.PartialChainEndpoint

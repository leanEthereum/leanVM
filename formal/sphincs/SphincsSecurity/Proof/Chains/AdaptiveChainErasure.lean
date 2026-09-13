import SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}

noncomputable def fixedImpl (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State) :
    QueryImpl (auxSpec + PrefixSpec n State) PMF :=
  auxiliary + (fun (query : Fin n × State) => PMF.pure (tables query.1 query.2) : QueryImpl (PrefixSpec n State) PMF)

omit [Fintype State] [Nonempty State] in
theorem observedRun_forget {Result : Type} (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (observedRun auxiliary tables computation observed).map Prod.fst = simulateQ (fixedImpl auxiliary tables) computation := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure result =>
      simp only [observedRun_pure, ← PMF.monad_map_eq_map, ← PMF.monad_pure_eq_pure, map_pure, simulateQ_pure]
  | query_bind input next ih =>
      rw [observedRun_query_bind, PMF.map_bind, simulateQ_bind, simulateQ_spec_query]
      cases input with
      | inl input =>
          simp only [observedImpl, StateT.run_mk, PMF.bind_map, PMF.monad_bind_eq_bind, fixedImpl, QueryImpl.add_apply_inl]
          exact congrArg (auxiliary input).bind (funext fun answer => ih answer observed)
      | inr query =>
          simp only [observedImpl, StateT.run_mk, PMF.pure_bind, fixedImpl, QueryImpl.add_apply_inr,
            PMF.monad_bind_eq_bind, PMF.pure_bind]
          exact ih (tables query.1 query.2) (record observed query (tables query.1 query.2))

theorem realRun_empty_forget {Result : Type} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) :
    (realRun auxiliary computation (fun _ _ => none)).map (fun result => result.2.1) =
      (PMF.uniformOfFintype (Fin n → State → State)).bind (fun tables =>
        (PMF.uniformOfFintype State).bind (fun secret =>
          simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables) (computation (evaluate tables secret)))) := by
  simp only [realRun, completeTables_empty, EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def, observedRun_forget]

theorem realRun_empty_result_mem {Result : Type} (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (tables : Fin n → State → State) (secret : State) (result : Result)
    (hresult : result ∈ (simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables)
      (computation (evaluate tables secret))).support) :
    result ∈ ((realRun auxiliary computation (fun _ _ => none)).map (fun result => result.2.1)).support := by
  rw [realRun_empty_forget, PMF.mem_support_bind_iff]
  refine ⟨tables, PMF.mem_support_uniformOfFintype tables, ?_⟩
  rw [PMF.mem_support_bind_iff]
  exact ⟨secret, PMF.mem_support_uniformOfFintype secret, hresult⟩

end SphincsSecurity.Concrete.PartialChainEndpoint

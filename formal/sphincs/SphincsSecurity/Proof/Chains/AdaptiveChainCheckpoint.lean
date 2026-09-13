import SphincsSecurity.Proof.Chains.AdaptiveChainRestart
import SphincsSecurity.Proof.Chains.AdaptiveChainCountedRows
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result : Type}

theorem run_posterior_payoff (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (payoff : (Fin n → State → State) → Result × (Fin n → State → Option State) → ENNReal) :
    (∑' tables, completeTables observed tables *
      ∑' result, observedRun auxiliary tables computation observed result * payoff tables result) =
    ∑' result, lazyRun auxiliary computation observed result *
      ∑' tables, completeTables result.2 tables * payoff tables result := by
  have h := congrArg (fun law : PMF ((Fin n → State → State) × (Result × (Fin n → State → Option State))) =>
    ∑' result, law result * payoff result.1 result.2) (run_posterior auxiliary computation observed)
  simpa only [expectation_bind, expectation_map] using h

theorem observedRun_supported_completion (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (tables : Fin n → State → State) (htables : tables ∈ (completeTables observed).support)
    (result : Result × (Fin n → State → Option State)) (hresult : result ∈ (observedRun auxiliary tables computation observed).support) :
    result ∈ (lazyRun auxiliary computation observed).support ∧ tables ∈ (completeTables result.2).support := by
  have hpair : (tables, result) ∈ ((completeTables observed).bind fun tables =>
      (observedRun auxiliary tables computation observed).map fun result => (tables, result)).support := by
    rw [PMF.mem_support_bind_iff]
    refine ⟨tables, htables, ?_⟩
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [run_posterior, PMF.mem_support_bind_iff] at hpair
  obtain ⟨middle, hmiddle, hpair⟩ := hpair
  rw [PMF.mem_support_map_iff] at hpair
  obtain ⟨completed, hcompleted, heq⟩ := hpair
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨rfl, rfl⟩
  exact ⟨hmiddle, hcompleted⟩

theorem realRun_support_lazy (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) (result : State × (Result × (Fin n → State → Option State)))
    (hr : result ∈ (realRun auxiliary computation observed).support) :
    result.2 ∈ (lazyRun (auxiliary result.1) (computation result.1) observed).support := by
  rw [realRun, PMF.mem_support_bind_iff] at hr
  obtain ⟨⟨tables, endpoint⟩, hsource, hr⟩ := hr
  rw [PMF.mem_support_map_iff] at hr
  obtain ⟨output, ho, rfl⟩ := hr
  have ht : tables ∈ (completeTables observed).support := by
    intro hz
    apply hsource
    simp only [EndpointPreimageDensity.real_apply, hz, zero_mul]
  exact (observedRun_supported_completion (auxiliary endpoint) (computation endpoint) observed tables ht output ho).1

noncomputable def checkpointObservedRun (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (before : OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    PMF ((Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State))) :=
  (observedRun auxiliary tables before observed).bind fun middle =>
    (observedRun auxiliary tables (QueryCap.counted IsPrefixQuery (after middle)) middle.2).map fun result => (middle, result)

noncomputable def realCheckpointRun (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    PMF (State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State))) :=
  (EndpointPreimageDensity.real (completeTables observed) evaluate).bind fun pair =>
    (checkpointObservedRun (auxiliary pair.2) pair.1 (before pair.2) (after pair.2) observed).map fun result => (pair.2, result)

theorem realCheckpointRun_support (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (result : State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (realCheckpointRun auxiliary before after observed).support) :
    result.2.1 ∈ (lazyRun (auxiliary result.1) (before result.1) observed).support ∧
      result.2.2 ∈ (lazyRun (auxiliary result.1) (QueryCap.counted IsPrefixQuery (after result.1 result.2.1)) result.2.1.2).support := by
  classical
  rw [realCheckpointRun, PMF.mem_support_bind_iff] at hresult
  obtain ⟨⟨tables, endpoint⟩, hsource, hresult⟩ := hresult
  rw [PMF.mem_support_map_iff] at hresult
  obtain ⟨pair, hpair, rfl⟩ := hresult
  rw [checkpointObservedRun, PMF.mem_support_bind_iff] at hpair
  obtain ⟨middle, hmiddle, hpair⟩ := hpair
  rw [PMF.mem_support_map_iff] at hpair
  obtain ⟨final, hfinal, rfl⟩ := hpair
  have ht : tables ∈ (completeTables observed).support := by
    intro hz
    apply hsource
    simp only [EndpointPreimageDensity.real_apply, hz, zero_mul]
  have hm := observedRun_supported_completion (auxiliary endpoint) (before endpoint) observed tables ht middle hmiddle
  exact ⟨hm.1, (observedRun_supported_completion (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (after endpoint middle))
    middle.2 tables hm.2 final hfinal).1⟩

theorem realCheckpointRun_before (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    (realCheckpointRun auxiliary before after observed).map (fun result => (result.1, result.2.1)) =
      realRun auxiliary before observed := by
  simp only [realCheckpointRun, checkpointObservedRun, realRun, PMF.map_bind, PMF.map_comp, Function.comp_def]
  simp only [PMF.map, Function.comp_def, PMF.bind_const]

theorem realCheckpointRun_expectation (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (payoff : State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State)) → ENNReal) :
    (∑' result, realCheckpointRun auxiliary before after observed result * payoff result) =
    ∑' endpoint, PMF.uniformOfFintype State endpoint * ∑' middle, lazyRun (auxiliary endpoint) (before endpoint) observed middle *
      ∑' tables, completeTables middle.2 tables *
        ∑' result, observedRun (auxiliary endpoint) tables (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 result *
          ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff (endpoint, middle, result)) := by
  classical
  simp only [realCheckpointRun, expectation_bind, expectation_map]
  rw [EndpointPreimageDensity.real_payoff, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [EndpointPreimageDensity.ideal_apply, div_eq_mul_inv, PMF.uniformOfFintype_apply,
    checkpointObservedRun, expectation_bind, expectation_map]
  apply tsum_congr
  intro endpoint
  rw [← run_posterior_payoff (auxiliary endpoint) (before endpoint) observed
    (fun tables middle => ∑' result,
      observedRun (auxiliary endpoint) tables (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 result *
        ((EndpointPreimageDensity.preimages evaluate tables endpoint : ENNReal) * payoff (endpoint, middle, result)))]
  simp only [expectation_scale]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro tables
  ring

theorem realCheckpointRun_density (auxiliary : State → QueryImpl auxSpec PMF)
    (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
    (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State)
    (payoff : State × (Checkpoint × (Fin n → State → Option State)) × ((Result × Nat) × (Fin n → State → Option State)) → ENNReal) :
    (∑' result, realCheckpointRun auxiliary before after observed result * payoff result) =
    ∑' endpoint, PMF.uniformOfFintype State endpoint * ∑' middle, lazyRun (auxiliary endpoint) (before endpoint) observed middle *
      ∑' result, lazyRun (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 result *
        (meanPreimages result.2 endpoint * payoff (endpoint, middle, result)) := by
  rw [realCheckpointRun_expectation]
  apply tsum_congr
  intro endpoint
  congr 1
  apply tsum_congr
  intro middle
  congr 1
  exact run_weighted_payoff (auxiliary endpoint) (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2 endpoint
    (fun result => payoff (endpoint, middle, result))

end SphincsSecurity.Concrete.PartialChainEndpoint

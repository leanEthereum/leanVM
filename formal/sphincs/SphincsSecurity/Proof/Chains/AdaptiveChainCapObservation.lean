import SphincsSecurity.Proof.Chains.AdaptiveChainCapContact
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

private theorem pmf_bind_eq_on_support {First Second : Type} (prior : PMF First) (first second : First → PMF Second)
    (h : ∀ input ∈ prior.support, first input = second input) : prior.bind first = prior.bind second := by
  apply PMF.ext
  intro result
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro input
  by_cases hi : input ∈ prior.support
  · rw [h input hi]
  · have hz : prior input = 0 := not_not.mp hi
    simp only [hz, zero_mul]

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}

omit [Fintype State] [Nonempty State] in
theorem observedRun_map (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (f : Result → Next)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (f <$> computation) observed =
      (observedRun auxiliary tables computation observed).map (fun result => (f result.1, result.2)) := by
  simp only [observedRun, simulateQ_map, StateT.run_map, PMF.monad_map_eq_map]

omit [Fintype State] [Nonempty State] in
theorem observedRun_cap_eq_counted (auxiliary : QueryImpl auxSpec PMF) (tables : Fin n → State → State)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ (fixedImpl auxiliary tables) (QueryCap.counted IsPrefixQuery computation)).support,
      result.2 ≤ budget) :
    observedRun auxiliary tables (QueryCap.run IsPrefixQuery computation budget) observed =
      (observedRun auxiliary tables (QueryCap.counted IsPrefixQuery computation) observed).map
        (fun result => (some (result.1.1, budget - result.1.2), result.2)) := by
  induction computation using OracleComp.inductionOn generalizing observed budget with
  | pure value =>
      simp only [QueryCap.run_pure, QueryCap.counted_pure, observedRun_pure, PMF.map, PMF.pure_bind, Function.comp_def, Nat.sub_zero]
  | query_bind input next ih =>
      rw [QueryCap.run_query_bind, QueryCap.counted_query_bind]
      simp only [bind_pure_comp, observedRun_query_bind, observedRun_map]
      cases input with
      | inl input =>
          simp only [IsPrefixQuery, if_false, observedRun_query_bind, observedImpl, StateT.run_mk,
            PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def, Nat.zero_add]
          apply pmf_bind_eq_on_support
          intro answer hanswer
          apply ih answer observed budget
          intro tail htail
          have h := QueryCap.counted_next_bound IsPrefixQuery (fixedImpl auxiliary tables) (.inl input) next budget hbound answer hanswer tail htail
          simpa only [IsPrefixQuery, if_false, Nat.zero_add] using h
      | inr query =>
          simp only [IsPrefixQuery, if_true]
          have hnext := fun tail htail => QueryCap.counted_next_bound IsPrefixQuery (fixedImpl auxiliary tables)
            (.inr query) next budget hbound (tables query.1 query.2) (by simp [fixedImpl]) tail htail
          cases budget with
          | zero =>
              obtain ⟨tail, htail⟩ := (simulateQ (fixedImpl auxiliary tables)
                (QueryCap.counted IsPrefixQuery (next (tables query.1 query.2)))).support_nonempty
              have h := hnext tail htail
              simp only [IsPrefixQuery, if_true] at h
              omega
          | succ budget =>
              simp only [observedRun_query_bind, observedImpl, StateT.run_mk, PMF.pure_bind,
                PMF.map_comp, Function.comp_def, Nat.add_comm 1, Nat.add_sub_add_right]
              apply ih (tables query.1 query.2) (record observed query (tables query.1 query.2)) budget
              intro tail htail
              have h := hnext tail htail
              simp only [IsPrefixQuery, if_true] at h
              omega

theorem realRun_map (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (f : State → Result → Next)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => f endpoint <$> computation endpoint) observed =
      (realRun auxiliary computation observed).map (fun result => (result.1, f result.1 result.2.1, result.2.2)) := by
  simp only [realRun, observedRun_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem realRun_counted_forget (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed).map
      (fun result => (result.1, result.2.1.1, result.2.2)) = realRun auxiliary computation observed := by
  simpa only [QueryCap.counted_forget] using
    (realRun_map auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ => Prod.fst) observed).symm

variable (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)

include hcharge hreal

theorem realRun_cap_eq_counted_observed :
    realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => (result.1, some (result.2.1.1, budget - result.2.1.2), result.2.2)) := by
  simp only [realRun, completeTables_empty, EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  rw [observedRun_cap_eq_counted (auxiliary (evaluate tables secret)) tables (computation (evaluate tables secret))
    (fun _ _ => none) budget (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret), PMF.map_comp]
  simp only [Function.comp_def]

theorem realRun_cap_erased_observed :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => (result.1, Option.map Prod.fst result.2.1, result.2.2)) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => (result.1, some result.2.1, result.2.2)) := by
  rw [realRun_cap_eq_counted_observed auxiliary computation cost budget hcharge hreal, PMF.map_comp]
  have h := congrArg (PMF.map (fun result : State × (Result × (Fin n → State → Option State)) =>
    (result.1, some result.2.1, result.2.2))) (realRun_counted_forget auxiliary computation (fun _ _ => none))
  simpa only [PMF.map_comp, Function.comp_def, Option.map_some] using h

theorem realRun_cap_contact_eq :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] =
        Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF (State × (Option Result × (Fin n → State → Option State))) =>
    Pr[fun result => Contact result.2.2 result.1 | law])
    (realRun_cap_erased_observed auxiliary computation cost budget hcharge hreal)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem realRun_contact_le_cap_cost (hsmall : budget < Fintype.card State) :
    Pr[fun result => Contact result.2.2 result.1 | realRun auxiliary computation (fun _ _ => none)] ≤
      (2 / Fintype.card State) * ∑' result,
        idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
          (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← realRun_cap_contact_eq auxiliary computation cost budget hcharge hreal]
  exact realRun_cap_contact_le auxiliary computation cost budget hcharge hreal hsmall

end SphincsSecurity.Concrete.PartialChainEndpoint

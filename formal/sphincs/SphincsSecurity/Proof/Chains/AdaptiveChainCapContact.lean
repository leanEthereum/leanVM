import SphincsSecurity.Proof.Chains.AdaptiveChainContact
import SphincsSecurity.Proof.Chains.AdaptiveChainCapCost
import SphincsSecurity.Proof.Base.QueryCapBalance
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result Next : Type}

theorem lazyRun_result_mem (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (result : Result × (Fin n → State → Option State)) (hresult : result ∈ (lazyRun auxiliary computation observed).support) :
    result.1 ∈ support computation := by
  induction computation using OracleComp.inductionOn generalizing observed with
  | pure value =>
      rw [lazyRun_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact (mem_support_pure_iff _ _).mpr rfl
  | query_bind input next ih =>
      rw [lazyRun_query_bind, PMF.mem_support_bind_iff] at hresult
      obtain ⟨middle, _, hresult⟩ := hresult
      rw [mem_support_bind_iff]
      exact ⟨middle.1, by simp only [support_query, Set.mem_univ], ih middle.1 middle.2 hresult⟩

theorem idealRun_result_mem (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (result : State × (Result × (Fin n → State → Option State))) (hresult : result ∈ (idealRun auxiliary computation observed).support) :
    result.2.1 ∈ support (computation result.1) := by
  rw [idealRun, PMF.mem_support_bind_iff] at hresult
  obtain ⟨endpoint, _, hresult⟩ := hresult
  rw [PMF.mem_support_map_iff] at hresult
  obtain ⟨output, houtput, rfl⟩ := hresult
  exact lazyRun_result_mem (auxiliary endpoint) (computation endpoint) observed output houtput

theorem idealRun_map (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (f : State → Result → Next)
    (observed : Fin n → State → Option State) :
    idealRun auxiliary (fun endpoint => f endpoint <$> computation endpoint) observed =
      (idealRun auxiliary computation observed).map (fun result => (result.1, f result.1 result.2.1, result.2.2)) := by
  simp only [idealRun, lazyRun_map, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem idealRun_counted_forget (auxiliary : State → QueryImpl auxSpec PMF)
    (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State) :
    (idealRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) observed).map
      (fun result => (result.1, result.2.1.1, result.2.2)) = idealRun auxiliary computation observed := by
  simpa only [QueryCap.counted_forget] using
    (idealRun_map auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ => Prod.fst) observed).symm

variable (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)
  (hsmall : budget < Fintype.card State)

include hcharge hreal hsmall

theorem idealRun_counted_cap_spent
    (result : State × ((Option (Result × Nat) × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none)).support) :
    result.2.1.2 = QueryCap.spent budget result.2.1.1 := by
  have hforget : (result.1, result.2.1.1, result.2.2) ∈
      (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).support := by
    rw [← idealRun_counted_forget auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  obtain ⟨finished, hfinished, _⟩ := idealRun_cap_valid auxiliary computation cost budget hcharge hreal hsmall _ hforget
  change result.2.1.1 = some finished at hfinished
  have hbalance := QueryCap.counted_run_balance IsPrefixQuery (computation result.1) budget result.2.1
    (idealRun_result_mem auxiliary _ (fun _ _ => none) result hresult)
  simp only [hfinished, Option.elim_some] at hbalance
  simp only [QueryCap.spent, hfinished, Option.elim_some]
  omega

theorem idealRun_cap_count_expectation :
    (∑' result, idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none) result *
          (result.2.1.2 : ENNReal)) =
      ∑' result, idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
        (QueryCap.spent budget result.2.1 : ENNReal) := by
  rw [← idealRun_counted_forget auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none), expectation_map]
  apply tsum_congr
  intro result
  by_cases hresult : result ∈ (idealRun auxiliary
      (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none)).support
  · rw [idealRun_counted_cap_spent auxiliary computation cost budget hcharge hreal hsmall result hresult]
  · have hzero : idealRun auxiliary
        (fun endpoint => QueryCap.counted IsPrefixQuery (QueryCap.run IsPrefixQuery (computation endpoint) budget)) (fun _ _ => none) result = 0 :=
      not_not.mp hresult
    simp only [hzero, zero_mul]

theorem realRun_cap_contact_le :
    Pr[fun result => Contact result.2.2 result.1 |
      realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)] ≤
        (2 / Fintype.card State) * ∑' result,
          idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none) result *
            (QueryCap.spent budget result.2.1 : ENNReal) := by
  have h := realRun_contact_le auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
  rwa [idealRun_cap_count_expectation auxiliary computation cost budget hcharge hreal hsmall] at h

end SphincsSecurity.Concrete.PartialChainEndpoint

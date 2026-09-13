import SphincsSecurity.Proof.Chains.AdaptiveChainErasure
import SphincsSecurity.Proof.Chains.AdaptiveChainSupport
import SphincsSecurity.Proof.Base.QueryCapErasure
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (computation : State → OracleComp (auxSpec + PrefixSpec n State) Result)
  (cost : Result → Nat) (budget : Nat)
  (hcharge : ∀ endpoint result, result ∈ support (QueryCap.counted IsPrefixQuery (computation endpoint)) →
    result.2 ≤ cost result.1)
  (hreal : ∀ result ∈ (realRun auxiliary computation (fun _ _ => none)).support, cost result.2.1 ≤ budget)

include hcharge hreal

theorem fixed_counted_le (tables : Fin n → State → State) (secret : State) (result : Result × Nat)
    (hresult : result ∈ (simulateQ (fixedImpl (auxiliary (evaluate tables secret)) tables)
      (QueryCap.counted IsPrefixQuery (computation (evaluate tables secret)))).support) : result.2 ≤ budget := by
  have hcount := hcharge (evaluate tables secret) result (QueryCap.simulate_mem_support _ _ result hresult)
  have houtput := QueryCap.counted_simulate_result_mem IsPrefixQuery _ _ result hresult
  have hsource := realRun_empty_result_mem auxiliary computation tables secret result.1 houtput
  rw [PMF.mem_support_map_iff] at hsource
  obtain ⟨source, hsource, hvalue⟩ := hsource
  exact hcount.trans (by simpa only [hvalue] using hreal source hsource)

theorem realRun_cap_erased :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map Prod.fst result.2.1) =
      (realRun auxiliary computation (fun _ _ => none)).map (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map Prod.fst ∘ (fun result => result.2.1)) =
    (realRun auxiliary computation (fun _ _ => none)).map (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_erased IsPrefixQuery _ _ budget
    (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret)

theorem realRun_cap_recover_count :
    (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
      (fun result => Option.map (fun finished => (finished.1, budget - finished.2)) result.2.1) =
      (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
        (fun result => some result.2.1) := by
  change (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
    (Option.map (fun finished => (finished.1, budget - finished.2)) ∘ (fun result => result.2.1)) =
    (realRun auxiliary (fun endpoint => QueryCap.counted IsPrefixQuery (computation endpoint)) (fun _ _ => none)).map
      (some ∘ (fun result => result.2.1))
  rw [← PMF.map_comp, ← PMF.map_comp, realRun_empty_forget, realRun_empty_forget]
  simp only [PMF.map_bind]
  apply congrArg (PMF.uniformOfFintype (Fin n → State → State)).bind
  funext tables
  apply congrArg (PMF.uniformOfFintype State).bind
  funext secret
  exact QueryCap.run_recover_count IsPrefixQuery _ _ budget
    (fixed_counted_le auxiliary computation cost budget hcharge hreal tables secret)

theorem realRun_cap_valid (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) :
    ∃ finished, result.2.1 = some finished ∧ cost finished.1 ≤ budget := by
  have hmap : Option.map Prod.fst result.2.1 ∈
      ((realRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget) (fun _ _ => none)).map
        (fun result => Option.map Prod.fst result.2.1)).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  rw [realRun_cap_erased auxiliary computation cost budget hcharge hreal, PMF.mem_support_map_iff] at hmap
  obtain ⟨source, hsource, hvalue⟩ := hmap
  cases hfinished : result.2.1 with
  | none => simp only [hfinished, Option.map_none, Option.some_ne_none] at hvalue
  | some finished =>
      refine ⟨finished, rfl, ?_⟩
      have heq : source.2.1 = finished.1 := by simpa only [hfinished, Option.map_some, Option.some.injEq] using hvalue
      rw [← heq]
      exact hreal source hsource

theorem idealRun_cap_valid (hsmall : budget < Fintype.card State)
    (result : State × (Option (Result × Nat) × (Fin n → State → Option State)))
    (hresult : result ∈ (idealRun auxiliary (fun endpoint => QueryCap.run IsPrefixQuery (computation endpoint) budget)
      (fun _ _ => none)).support) :
    ∃ finished, result.2.1 = some finished ∧ cost finished.1 ≤ budget := by
  apply realRun_cap_valid auxiliary computation cost budget hcharge hreal result
  exact idealRun_empty_support_subset auxiliary _ budget
    (fun endpoint => QueryCap.run_queryBound IsPrefixQuery (computation endpoint) budget) hsmall hresult

end SphincsSecurity.Concrete.PartialChainEndpoint

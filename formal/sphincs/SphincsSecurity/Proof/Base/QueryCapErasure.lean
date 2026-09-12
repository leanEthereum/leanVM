import SphincsSecurity.Proof.Base.QueryCapAccounting
namespace SphincsSecurity.QueryCap

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

private theorem map_eq_on_support {Result Output : Type} (law : PMF Result) (first second : Result → Output)
    (h : ∀ result ∈ law.support, first result = second result) : law.map first = law.map second := by
  classical
  apply PMF.ext
  intro output
  rw [PMF.map, PMF.map, PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro result
  simp only [Function.comp_apply]
  by_cases hresult : result ∈ law.support
  · rw [h result hresult]
  · have hzero : law result = 0 := by simpa only [PMF.mem_support_iff, not_not] using hresult
    simp only [hzero, zero_mul]

variable {Index : Type} {spec : OracleSpec Index} {Result : Type}
  (selected : Index → Prop) [DecidablePred selected]

theorem counted_simulate_result_mem (impl : QueryImpl spec PMF) (computation : OracleComp spec Result)
    (result : Result × Nat) (hresult : result ∈ (simulateQ impl (counted selected computation)).support) :
    result.1 ∈ (simulateQ impl computation).support := by
  have hmap : (simulateQ impl (counted selected computation)).map Prod.fst = simulateQ impl computation := by
    rw [← PMF.monad_map_eq_map, ← simulateQ_map, counted_forget]
  rw [← hmap, PMF.mem_support_map_iff]
  exact ⟨result, hresult, rfl⟩

theorem run_eq_some_counted (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    simulateQ impl (run selected computation budget) =
      (simulateQ impl (counted selected computation)).map (fun result => some (result.1, budget - result.2)) := by
  rw [run_eq_counted]
  apply map_eq_on_support
  intro result hresult
  exact if_pos (hbound result hresult)

theorem run_erased (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    (simulateQ impl (run selected computation budget)).map (Option.map Prod.fst) =
      (simulateQ impl computation).map some := by
  rw [run_eq_some_counted selected impl computation budget hbound, PMF.map_comp]
  change (simulateQ impl (counted selected computation)).map (some ∘ Prod.fst) = _
  rw [← PMF.map_comp]
  apply congrArg (PMF.map some)
  rw [← PMF.monad_map_eq_map, ← simulateQ_map, counted_forget]

theorem run_recover_count (impl : QueryImpl spec PMF) (computation : OracleComp spec Result) (budget : Nat)
    (hbound : ∀ result ∈ (simulateQ impl (counted selected computation)).support, result.2 ≤ budget) :
    (simulateQ impl (run selected computation budget)).map (Option.map (fun result => (result.1, budget - result.2))) =
      (simulateQ impl (counted selected computation)).map some := by
  rw [run_eq_some_counted selected impl computation budget hbound, PMF.map_comp]
  apply map_eq_on_support
  intro result hresult
  simp only [Function.comp_apply, Option.map_some]
  congr 2
  exact Nat.sub_sub_self (hbound result hresult)

end SphincsSecurity.QueryCap

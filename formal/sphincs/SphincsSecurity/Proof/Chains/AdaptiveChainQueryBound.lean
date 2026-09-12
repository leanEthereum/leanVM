import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Chains.AdaptiveChainObservation
import SphincsSecurity.Proof.Chains.PartialChainLikelihoodLower
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat}

omit [Nonempty State] in
theorem unqueried_update_some (observed : State → Option State) (input answer : State) :
    unqueried (Function.update observed input (some answer)) = (unqueried observed).erase input := by
  ext row
  by_cases hrow : row = input <;> simp [unqueried, Function.update_apply, hrow]

omit [Nonempty State] in
theorem queriedCount_update_le (observed : State → Option State) (input answer : State) :
    queriedCount (Function.update observed input (some answer)) ≤ queriedCount observed + 1 := by
  rw [queriedCount, unqueried_update_some, queriedCount]
  have h := Finset.pred_card_le_card_erase (s := unqueried observed) (a := input)
  omega

omit [Nonempty State] in
theorem queryCount_record_le (observed : Fin n → State → Option State) (query : Fin n × State) (answer : State) :
    queryCount (record observed query answer) ≤ queryCount observed + 1 := by
  have hfun : (fun step => queriedCount (record observed query answer step)) =
      Function.update (fun step => queriedCount (observed step)) query.1
        (queriedCount (Function.update (observed query.1) query.2 (some answer))) := by
    funext step
    by_cases hstep : step = query.1 <;> simp only [record, Function.update_apply, hstep, if_true, if_false]
  rw [queryCount, hfun, Finset.sum_update_of_mem (Finset.mem_univ query.1), Finset.sdiff_singleton_eq_erase,
    queryCount, ← Finset.add_sum_erase Finset.univ (fun step => queriedCount (observed step)) (Finset.mem_univ query.1)]
  have h := queriedCount_update_le (observed query.1) query.2 answer
  omega

omit [DecidableEq State] [Nonempty State] in
theorem queryCount_empty : queryCount (fun (_ : Fin n) (_ : State) => none) = 0 := by
  simp [queryCount, queriedCount, unqueried]

def IsPrefixQuery : AuxIndex ⊕ (Fin n × State) → Prop
  | .inl _ => False
  | .inr _ => True

instance instDecidableIsPrefixQuery (input : AuxIndex ⊕ (Fin n × State)) : Decidable (IsPrefixQuery input) := by
  cases input <;> unfold IsPrefixQuery <;> infer_instance

theorem lazyRun_queryCount_le {Result : Type} (auxiliary : QueryImpl auxSpec PMF)
    (computation : OracleComp (auxSpec + PrefixSpec n State) Result) (observed : Fin n → State → Option State)
    (budget : Nat) (hbound : computation.IsQueryBoundP IsPrefixQuery budget)
    (result : Result × (Fin n → State → Option State)) (hresult : result ∈ (lazyRun auxiliary computation observed).support) :
    queryCount result.2 ≤ queryCount observed + budget := by
  induction computation using OracleComp.inductionOn generalizing observed budget result with
  | pure value =>
      rw [lazyRun_pure, PMF.mem_support_pure_iff] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [lazyRun_query_bind] at hresult
      cases input with
      | inl input =>
          simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          exact ih answer observed budget (hbound.2 answer) result hresult
      | inr query =>
          simp only [lazyImpl, StateT.run_mk, PMF.bind_map, PMF.mem_support_bind_iff] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          have hpos : 0 < budget := by simpa only [IsPrefixQuery, not_true_eq_false, false_or] using hbound.1
          have hnext := ih answer (record observed query answer) (budget - 1) (hbound.2 answer) result hresult
          have hrecord := queryCount_record_le observed query answer
          omega

end SphincsSecurity.Concrete.PartialChainEndpoint

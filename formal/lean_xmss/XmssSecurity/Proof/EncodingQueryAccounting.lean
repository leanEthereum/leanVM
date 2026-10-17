import VCVio.OracleComp.QueryTracking.SubSpec

open OracleComp OracleSpec

namespace XmssSecurity

theorem OracleComp.IsQueryBoundP.bind_right_of_mem_support
    {index : Type} {spec : OracleSpec index} {α β : Type}
    {predicate : spec.Domain → Prop} [DecidablePred predicate]
    {head : OracleComp spec α} {next : α → OracleComp spec β}
    {fuel : Nat}
    (hbound : (head >>= next).IsQueryBoundP predicate fuel)
    (result : α) (hresult : result ∈ support head) :
    (next result).IsQueryBoundP predicate fuel := by
  induction head using OracleComp.inductionOn generalizing fuel result with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hresult
      subst result
      simpa only [pure_bind] using hbound
  | query_bind input rest ih =>
      rw [bind_assoc, OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hresult
      obtain ⟨response, _hquery, hrest⟩ := hresult
      exact (ih response (hbound.2 response) result hrest).mono (by
        split <;> omega)

end XmssSecurity

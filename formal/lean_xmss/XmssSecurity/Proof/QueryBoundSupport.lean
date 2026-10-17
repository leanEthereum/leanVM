import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec

namespace OracleComp

theorem IsQueryBoundP.of_bind_left
    {ι : Type} {spec : OracleSpec ι} {α β : Type}
    {p : ι → Prop} [DecidablePred p]
    {oa : OracleComp spec α} {ob : α → OracleComp spec β} {q : Nat}
    (hbound : IsQueryBoundP (oa >>= ob) p q) :
    IsQueryBoundP oa p q := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure value => simp
  | query_bind input next ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨hbound.1, fun output => ih output (hbound.2 output)⟩

theorem IsQueryBoundP.continuation_mono_of_mem_support
    {ι : Type} {spec : OracleSpec ι} {α β : Type}
    (p : ι → Prop) [DecidablePred p]
    (oa : OracleComp spec α) (ob : α → OracleComp spec β) (q : Nat)
    (hbound : IsQueryBoundP (oa >>= ob) p q)
    (x : α) (hx : x ∈ support oa) :
    IsQueryBoundP (ob x) p q := by
  induction oa using OracleComp.inductionOn generalizing q x with
  | pure value =>
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst x
      simpa using hbound
  | query_bind input next ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [mem_support_bind_iff] at hx
      obtain ⟨output, _houtput, hx⟩ := hx
      have hrest := ih output (if p input then q - 1 else q)
        (hbound.2 output) x hx
      apply hrest.mono
      split <;> omega

end OracleComp

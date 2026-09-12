import SphincsSecurity.Proof.Reference.QueryBound

namespace SphincsSecurity

open OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem countHashQueries_forget {α : Type} (computation : OracleComp OracleWorld α) :
    Prod.fst <$> countHashQueries computation = computation :=
  QueryCap.counted_forget _ computation

theorem countHashQueries_run_forget {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) :
    (fun result => (result.1.1, result.2)) <$>
      (simulateQ romImpl (countHashQueries computation)).run cache =
        (simulateQ romImpl computation).run cache := by
  have h := congrArg (fun c : OracleComp OracleWorld α => (simulateQ romImpl c).run cache)
    (countHashQueries_forget computation)
  simpa only [simulateQ_map, StateT.run_map] using h

theorem HashQueryBound.mono {α : Type} {computation : OracleComp OracleWorld α}
    {cache : QueryCache HashSpec} {q r : Nat} (hbound : HashQueryBound computation cache q)
    (hle : q ≤ r) : HashQueryBound computation cache r :=
  fun result hr => (hbound result hr).trans hle

theorem hashQueryBound_bind_run {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= next) cache q) (result : α × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl first).run cache)) :
    ∃ cost, cost ≤ q ∧ HashQueryBound (next result.1) result.2 (q - cost) := by
  rw [← countHashQueries_run_forget first cache, support_map] at hr
  obtain ⟨record, hrecord, rfl⟩ := hr
  exact ⟨record.1.2, hashQueryBound_bind first next cache q hbound record hrecord⟩

theorem hashQueryBound_bind_right {α β : Type} (first : OracleComp OracleWorld α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (first >>= next) cache q) (result : α × QueryCache HashSpec)
    (hr : result ∈ support ((simulateQ romImpl first).run cache)) :
    HashQueryBound (next result.1) result.2 q := by
  obtain ⟨cost, _, hnext⟩ := hashQueryBound_bind_run first next cache q hbound result hr
  exact hnext.mono (Nat.sub_le _ _)

theorem hashQueryBound_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound (liftM (OracleWorld.query input) >>= next) cache q)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hr : result ∈ support ((romImpl input).run cache)) :
    (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) ≤ q ∧
      HashQueryBound (next result.1) result.2 (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0)) := by
  apply hashQueryBound_bind _ next cache q hbound
    ((result.1, if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0), result.2)
  rw [← bind_pure (liftM (OracleWorld.query input)), countHashQueries_query_bind]
  simp only [countHashQueries_pure, map_pure, Nat.add_zero, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map]
  exact ⟨result, hr, by cases input <;> rfl⟩

end SphincsSecurity

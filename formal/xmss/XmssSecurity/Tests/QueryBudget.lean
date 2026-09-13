import XmssSecurity.Proof.Adversary.Embedding
open OracleComp OracleSpec XmssSecurity XmssSecurity.Security
set_option backward.isDefEq.respectTransparency false

namespace XmssSecurity.QueryBudgetChecks

private def inconsistentBranch : OracleComp HashSpec Unit := do
  let a ← liftM (HashSpec.query [])
  let b ← liftM (HashSpec.query [])
  if a = b then return ()
  else
    let _ ← liftM (HashSpec.query [1])
    return ()

example : ∀ result ∈ support ((simulateQ countedOracle inconsistentBranch).run.run' ∅), result.2 = (2 : Nat) := by
  have fresh : ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) []).run ∅ =
      (fun answer : HashOutput => (answer, (∅ : QueryCache HashSpec).cacheQuery [] answer)) <$>
        ($ᵗ HashOutput : ProbComp _) :=
    QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)
  have cached (answer : HashOutput) :
      ((randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) []).run ((∅ : QueryCache HashSpec).cacheQuery [] answer) =
        pure (answer, (∅ : QueryCache HashSpec).cacheQuery [] answer) :=
    QueryImpl.withCaching_run_some _ (by simp)
  intro result hr
  rw [← simulate_countAll] at hr
  simp only [inconsistentBranch, countAll, QueryCounting.counted_query_bind, simulateQ_bind,
    simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, fresh, bind_map_left, cached,
    pure_bind, ite_true, QueryCounting.counted_pure, simulateQ_pure, StateT.run_pure,
    map_bind, map_pure, Nat.add_zero, Nat.reduceAdd, bind_pure_comp,
    simulateQ_map, StateT.run_map, Functor.map_map] at hr
  rw [support_map] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  rfl

example : ¬ inconsistentBranch.IsQueryBoundP (fun _ : HashSpec.Domain => True) 2 := by
  intro h
  have h0 := (isQueryBoundP_query_bind_iff _ _ _ _).mp h
  have h1 := (isQueryBoundP_query_bind_iff _ _ _ _).mp (h0.2 (0 : HashOutput))
  have h2 := h1.2 (1 : HashOutput)
  have hne : (0 : HashOutput) ≠ 1 := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    change 0 = 1 at hn
    omega
  simp only [if_neg hne, if_true, Nat.reduceSub] at h2
  have h3 := (isQueryBoundP_query_bind_iff _ _ _ _).mp h2
  exact h3.1.elim (fun hfalse => hfalse (by decide)) (Nat.not_lt_zero _)

end XmssSecurity.QueryBudgetChecks

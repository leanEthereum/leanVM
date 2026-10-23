import XmssSecurity.Proof.EvalDistEq
import XmssSecurity.Proof.Seeded.StoppedRun
import XmssSecurity.Proof.ConsistentQueryBound

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem cacheQuery_comm (cache : QueryCache HashSpec) (left right : HashInput)
    (h : left ≠ right) (a b : HashOutput) :
    (cache.cacheQuery left a).cacheQuery right b = (cache.cacheQuery right b).cacheQuery left a := by
  ext input
  by_cases hl : input = left
  · subst input
    simp [QueryCache.cacheQuery_of_ne, h]
  · by_cases hr : input = right
    · subst input
      simp [QueryCache.cacheQuery_of_ne, hl]
    · simp [QueryCache.cacheQuery_of_ne, hl, hr]

/-- An unobserved query may be sampled early, whether or not the computation later uses it. -/
theorem evalDist_presample_fresh {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : HashInput) (hfresh : cache target = none) :
    ((simulateQ romImpl computation).run' cache) =ᵈ (do
      let output ← $ᵗ HashOutput
      (simulateQ romImpl computation).run' (cache.cacheQuery target output)) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind input next ih =>
      cases input with
      | inl input =>
          dsimp only [OracleWorld] at next ih ⊢
          have hrun (cache : QueryCache HashSpec) :
              (simulateQ romImpl (liftM (OracleWorld.query (.inl input)) >>= next)).run' cache =
                ((liftM (unifSpec.query input) : ProbComp _) >>= fun answer =>
                  (simulateQ romImpl (next answer)).run' cache) := by
            rw [run'_query_bind]
            change (((fun answer => (answer, cache)) <$> (liftM (unifSpec.query input) : ProbComp _)) >>= _) = _
            exact bind_map_left (m := ProbComp) (fun answer => (answer, cache))
              (liftM (unifSpec.query input) : ProbComp _)
              (fun result => (simulateQ romImpl (next result.1)).run' result.2)
          rw [hrun]
          refine EvalDistEq.trans (my := (do
            let answer ← (liftM (unifSpec.query input) : ProbComp _)
            let output ← $ᵗ HashOutput
            (simulateQ romImpl (next answer)).run' (cache.cacheQuery target output) : ProbComp _)) ?_ ?_
          · exact EvalDistEq.bind_right _ (fun answer => ih answer cache hfresh)
          · refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
            apply EvalDistEq.bind_right
            intro output
            rw [hrun]
      | inr input =>
          dsimp only [OracleWorld] at next ih ⊢
          have hrun (cache : QueryCache HashSpec) :
              (simulateQ romImpl (liftM (OracleWorld.query (.inr input)) >>= next)).run' cache =
                ((randomOracle (spec := HashSpec) input).run cache >>= fun result =>
                  (simulateQ romImpl (next result.1)).run' result.2) := run'_query_bind _ _ _
          by_cases heq : input = target
          · subst target
            rw [hrun, QueryImpl.withCaching_run_none _ hfresh, bind_map_left]
            apply EvalDistEq.bind_right
            intro output
            rw [hrun, QueryImpl.withCaching_run_some _ (QueryCache.cacheQuery_self _ _ _), pure_bind]
          · have hfresh' (output : HashOutput) : (cache.cacheQuery input output) target = none := by
              rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm heq), hfresh]
            cases hinput : cache input with
            | some answer =>
                rw [hrun, QueryImpl.withCaching_run_some _ hinput, pure_bind]
                refine (ih answer cache hfresh).trans ?_
                apply EvalDistEq.bind_right
                intro output
                rw [hrun, QueryImpl.withCaching_run_some _ (by
                  rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), pure_bind]
            | none =>
                rw [hrun, QueryImpl.withCaching_run_none _ hinput, bind_map_left]
                refine EvalDistEq.trans (my := (do
                  let answer ← $ᵗ HashOutput
                  let output ← $ᵗ HashOutput
                  (simulateQ romImpl (next answer)).run' ((cache.cacheQuery input answer).cacheQuery target output) : ProbComp _)) ?_ ?_
                · exact EvalDistEq.bind_right _ (fun answer => ih answer _ (hfresh' answer))
                · refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
                  apply EvalDistEq.bind_right
                  intro output
                  rw [hrun, QueryImpl.withCaching_run_none _ (by
                    rw [QueryCache.cacheQuery_of_ne _ _ heq, hinput]), bind_map_left]
                  apply EvalDistEq.bind_right
                  intro answer
                  rw [cacheQuery_comm cache input target heq]

theorem evalDist_presample_query {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (target : HashInput) :
    ((simulateQ romImpl computation).run' cache) =ᵈ ((randomOracle (spec := HashSpec) target).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) := by
  cases hc : cache target with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, bind_map_left]
      exact evalDist_presample_fresh computation cache target hc
  | some output =>
      rw [QueryImpl.withCaching_run_some _ hc, pure_bind]

theorem evalDist_presample_computation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    ((simulateQ romImpl computation).run' cache) =ᵈ ((simulateQ romImpl preparation).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2) := by
  induction preparation using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, bind_assoc]
      refine EvalDistEq.trans (my := ((romImpl input).run cache >>= fun result =>
        (simulateQ romImpl computation).run' result.2 : ProbComp _)) ?_ ?_
      · cases input with
        | inl input =>
            refine (OracleComp.EvalDistEq.bind_const
              (liftM (unifSpec.query input) : ProbComp _) _).symm.trans (EvalDistEq.of_eq ?_)
            simp [romImpl, unifFwdImpl]

        | inr input => exact evalDist_presample_query computation cache input
      · exact EvalDistEq.bind_right _ (fun result => ih result.1 result.2)

theorem hashQueryBound_after_preparation {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp OracleWorld β) (cache : QueryCache HashSpec) (q : Nat)
    (hbound : HashQueryBound computation cache q) (prepared : β × QueryCache HashSpec)
    (hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache)) :
    HashQueryBound computation prepared.2 q := by
  intro result hresult
  apply hbound result
  rw [OracleComp.support_eq_of_evalDistEq
    (evalDist_presample_computation (countHashQueries computation) preparation cache),
    mem_support_bind_iff]
  exact ⟨prepared, hprepared, hresult⟩

end XmssSecurity.Seeded

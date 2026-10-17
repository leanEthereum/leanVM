import XmssSecurity.Proof.CacheReplayEval
import VCVio.OracleComp.QueryTracking.QueryBound

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

/-- A computation making no query to an absent input leaves that input absent from the lazy-oracle cache. -/
theorem cache_none_of_zero_query_bound {α : Type}
    (computation : OracleComp HashSpec α) (target : HashInput)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hbound : computation.IsQueryBoundP (· = target) 0)
    (hnone : initialCache target = none)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    finalCache target = none := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.2 ▸ hnone
  | query_bind queried next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hne : queried ≠ target := by
        simpa using hbound.1
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache target = none := by
        cases hqueried : initialCache queried with
        | none =>
            rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
            obtain ⟨sampled, _hsampled, heq⟩ := hquery
            cases heq
            simpa only [QueryCache.cacheQuery_of_ne initialCache output hne.symm] using hnone
        | some cached =>
            rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
              Set.mem_singleton_iff] at hquery
            cases hquery
            exact hnone
      exact ih output middleCache finalCache result
        (by simpa [hne] using hbound.2 output) hmiddle hrest

/-- From an initially empty address class, one query to that class can cache at most one input in it. -/
theorem cache_unique_of_query_bound_one {α : Type}
    (computation : OracleComp HashSpec α) (p : HashInput → Prop) [DecidablePred p]
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hbound : computation.IsQueryBoundP p 1)
    (hinitial : ∀ input, p input → initialCache input = none)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : p left) (hrightP : p right)
    (hleft : finalCache left = some leftOutput)
    (hright : finalCache right = some rightOutput) :
    left = right := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [hmem.2, hinitial left hleftP] at hleft
      simp at hleft
  | query_bind queried next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      by_cases hqueriedP : p queried
      · have hcontinuation : (next output).IsQueryBoundP p 0 := by
          simpa [hqueriedP] using hbound.2 output
        have hentry_eq (input : HashInput) (inputOutput : HashOutput)
            (hinputP : p input) (hinput : finalCache input = some inputOutput) :
            input = queried := by
          by_contra hne
          have hmiddle : middleCache input = none := by
            cases hqueried : initialCache queried with
            | none =>
                rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
                obtain ⟨sampled, _hsampled, heq⟩ := hquery
                cases heq
                simpa only [QueryCache.cacheQuery_of_ne initialCache output hne] using
                  hinitial input hinputP
            | some cached =>
                rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
                  Set.mem_singleton_iff] at hquery
                cases hquery
                exact hinitial input hinputP
          have hexact : (next output).IsQueryBoundP (· = input) 0 :=
            OracleComp.IsQueryBoundP.of_imp
              (fun candidate heq => heq ▸ hinputP) hcontinuation
          have hnone := cache_none_of_zero_query_bound (next output) input
            middleCache finalCache result hexact hmiddle hrest
          rw [hinput] at hnone
          simp at hnone
        exact (hentry_eq left leftOutput hleftP hleft).trans
          (hentry_eq right rightOutput hrightP hright).symm
      · have hmiddle : ∀ input, p input → middleCache input = none := by
          intro input hinputP
          have hne : input ≠ queried := fun heq => hqueriedP (heq ▸ hinputP)
          cases hqueried : initialCache queried with
          | none =>
              rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
              obtain ⟨sampled, _hsampled, heq⟩ := hquery
              cases heq
              simpa only [QueryCache.cacheQuery_of_ne initialCache output hne] using
                hinitial input hinputP
          | some cached =>
              rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
                Set.mem_singleton_iff] at hquery
              cases hquery
              exact hinitial input hinputP
        exact ih output middleCache finalCache result
          (by simpa [hqueriedP] using hbound.2 output) hmiddle hrest hleft hright

end XmssSecurity.Concrete.CacheReplay

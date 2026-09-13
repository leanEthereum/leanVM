import SphincsSecurity.Proof.Forced.FtsGuessDeferredMessage
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def seedAllowed (inputs : Finset HashInput) (cache : QueryCache HashSpec) : inputs → Finset HashOutput :=
  fun input => (cache input.val).elim Finset.univ (fun answer => {answer})

theorem seedAllowed_cacheQuery (inputs : Finset HashInput) (cache : QueryCache HashSpec)
    (input : inputs) (answer : HashOutput) :
    seedAllowed inputs (cache.cacheQuery input.val answer) = discloseTableValue (seedAllowed inputs cache) input answer := by
  funext other
  by_cases he : other = input
  · subst other
    simp only [seedAllowed, QueryCache.cacheQuery, Function.update_self, Option.elim_some, discloseTableValue]
  · have hv : other.val ≠ input.val := fun hv => he (Subtype.ext hv)
    simp only [seedAllowed, QueryCache.cacheQuery, Function.update_of_ne hv, discloseTableValue, Function.update_of_ne he]

private theorem cell_singleton (answer : HashOutput) : cell {answer} = pure answer := by
  apply SPMF.ext
  intro value
  simp only [cell_apply, Finset.mem_singleton, Finset.card_singleton, Nat.cast_one, inv_one, SPMF.pure_apply]

noncomputable def cachedSeedImpl (inputs : Finset HashInput) :
    QueryImpl (ForcedSeedSpec inputs) (StateT (QueryCache HashSpec) SPMF)
  | .inl input => StateT.mk fun cache => (fun answer => (answer, cache)) <$> forcedSeedAuxiliary input
  | .inr input => StateT.mk fun cache => 𝒟[(randomOracle (spec := HashSpec) input.val).run cache]

noncomputable def cachedSeedRun {Result : Type} (inputs : Finset HashInput)
    (computation : OracleComp (ForcedSeedSpec inputs) Result) (cache : QueryCache HashSpec) :
    SPMF (Result × QueryCache HashSpec) := (simulateQ (cachedSeedImpl inputs) computation).run cache

theorem cachedSeedImpl_project (inputs : Finset HashInput) (input : (ForcedSeedSpec inputs).Domain)
    (cache : QueryCache HashSpec) :
    (Prod.map id (seedAllowed inputs)) <$> (cachedSeedImpl inputs input).run cache =
      (UniformTableObservation.lazyImpl forcedSeedAuxiliary input).run (seedAllowed inputs cache) := by
  cases input with
  | inl input => simp only [cachedSeedImpl, UniformTableObservation.lazyImpl, StateT.run_mk, Functor.map_map]; rfl
  | inr input =>
      cases hc : cache input.val with
      | none =>
          rw [cachedSeedImpl, StateT.run_mk, randomOracle, QueryImpl.withCaching_run_none _ hc]
          simp only [uniformSampleImpl, evalDist_map, evalDist_uniformSample, Functor.map_map,
            UniformTableObservation.lazyImpl, StateT.run_mk, seedAllowed, hc, Option.elim_none,
            cell, dif_pos Finset.univ_nonempty]
          congr 1
          funext answer
          exact Prod.ext rfl (seedAllowed_cacheQuery inputs cache input answer)
      | some answer =>
          rw [cachedSeedImpl, StateT.run_mk, randomOracle, QueryImpl.withCaching_run_some _ hc]
          simp only [evalDist_pure, map_pure, UniformTableObservation.lazyImpl, StateT.run_mk,
            seedAllowed, hc, Option.elim_some, Prod.map_apply, id_eq]
          change pure (answer, seedAllowed inputs cache) =
            ((fun value : HashOutput => (value, discloseTableValue (seedAllowed inputs cache) input value)) <$> cell {answer})
          rw [cell_singleton, map_pure]
          apply congrArg pure
          apply congrArg (fun allowed : inputs → Finset HashOutput => (answer, allowed))
          symm
          have ha : seedAllowed inputs cache input = {answer} := by simp only [seedAllowed, hc, Option.elim_some]
          rw [discloseTableValue, ← ha, Function.update_eq_self]

theorem cachedSeedRun_project {Result : Type} (inputs : Finset HashInput)
    (computation : OracleComp (ForcedSeedSpec inputs) Result) (cache : QueryCache HashSpec) :
    (Prod.map id (seedAllowed inputs)) <$> cachedSeedRun inputs computation cache =
      UniformTableObservation.lazyRun forcedSeedAuxiliary computation (seedAllowed inputs cache) := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [cachedSeedRun, simulateQ_pure, StateT.run_pure, map_pure, UniformTableObservation.lazyRun_pure]; rfl
  | query_bind input next ih =>
      simp only [cachedSeedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change ((cachedSeedImpl inputs input).run cache >>= fun result =>
        (Prod.map id (seedAllowed inputs)) <$> cachedSeedRun inputs (next result.1) result.2) = _
      simp only [ih]
      rw [UniformTableObservation.lazyRun_query_bind, ← cachedSeedImpl_project inputs input cache, bind_map_left]
      rfl

end SphincsSecurity.Concrete.FtsGuessHash

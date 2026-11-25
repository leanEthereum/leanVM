module

public import FORS.Seed.Model
public import FORS.Statement
public import FORS.Base.Prelude
public import Common.RomTable
public import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

@[expose] public section

/-! Finite fresh-table preparation: `PK.seed`, the secrets' parameter-dependent derivations and
`SK.prf`. Preparation explicitly performs oracle queries; later theorems relate it to independent
full-output material and its programmed cache. Preparation is not silently counted as part of an
adversary's existing query budget. -/

open OracleComp OracleSpec Common.QueryCount

namespace FORS.Security.SeedCoupling

variable [Params]

open SeedModel Completeness Common.RomTable

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- After the parameter response, the secrets' addresses are fixed independently of their own
answers: one derivation per secret. The complete 256-bit responses are stored. -/
def derivationInputs (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : HashInput :=
  keygenHashInput (truncateHash parameterOutput) (secretDomain position) seed

theorem derivationInputs_injective (seed : MasterSeed) (parameterOutput : HashOutput) :
    Function.Injective (derivationInputs seed parameterOutput) := by
  intro left right h
  exact secretDomain_injective (keygenInput_injective h).2.1

theorem derivationInputs_ne_parameter (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : derivationInputs seed parameterOutput position ≠ parameterInput seed :=
  fun h => keySeedInput_ne_keygenHashInput seed seed 0 _ _ h.symm

theorem derivationInputs_ne_prf (seed : MasterSeed) (parameterOutput : HashOutput)
    (position : SecretPosition) : derivationInputs seed parameterOutput position ≠ prfInput seed :=
  fun h => keySeedInput_ne_keygenHashInput seed seed 1 _ _ h.symm

/-- The sequential finite-cache construction implements exactly the candidate programming map. -/
theorem cacheTable_eq_programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) :
    (cacheTable (base.cacheQuery (parameterInput seed) (parameterOutput material))
      (derivationInputs seed (parameterOutput material)) material.2).cacheQuery (prfInput seed) (prf material) =
      programCache base seed material := by
  classical
  refine QueryCache.ext fun input => ?_
  by_cases hprf : input = prfInput seed
  · subst input
    rw [QueryCache.cacheQuery_self, programCache_prf]
  rw [QueryCache.cacheQuery_of_ne _ _ hprf]
  by_cases hp : input = parameterInput seed
  · subst input
    rw [cacheTable_apply_of_not_mem _ _ _ _
      (fun position => (derivationInputs_ne_parameter seed (parameterOutput material) position).symm)]
    rw [QueryCache.cacheQuery_self, programCache_parameter]
  · by_cases hs : ∃ position, input = derivationInputs seed (parameterOutput material) position
    · obtain ⟨position, rfl⟩ := hs
      rw [cacheTable_apply _ _ (derivationInputs_injective seed (parameterOutput material))]
      exact (programCache_secret base seed material position).symm
    · rw [cacheTable_apply_of_not_mem _ _ _ _ (by simpa only [not_exists] using hs),
        QueryCache.cacheQuery_of_ne _ _ hp, programCache_other _ _ _ _ hp hprf]
      intro position heq
      exact hs ⟨position, heq⟩

/-- Explicitly query `PK.seed`'s input, then every secret's derivation at that parameter, then
`SK.prf`'s input: the order of `sampleMaterial`. -/
noncomputable def prepareTable (seed : MasterSeed) : OracleComp HashSpec Material := do
  let parameterOutput ← liftM (HashSpec.query (parameterInput seed))
  let outputs ← queryTable (derivationInputs seed parameterOutput)
  let prf ← liftM (HashSpec.query (prfInput seed))
  return ((parameterOutput, prf), outputs)

attribute [local irreducible] cacheTable cacheFin programCache

/-- Exact joint distribution of the queried table and the cache: independently sampled material
and its full programmed cache.
No assertion about an arbitrary preexisting honest cache is needed: preparation starts empty. -/
theorem evalDist_prepareTable (seed : MasterSeed) :
    ((simulateQ randomOracle (prepareTable seed)).run ∅) =ᵈ
      ((fun material => (material, programCache ∅ seed material)) <$> sampleMaterial) := by
  unfold prepareTable
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [QueryImpl.withCaching_run_none _ (by rfl)]
  simp only [bind_map_left, simulateQ_pure, StateT.run_pure, bind_pure_comp,
    sampleMaterial, map_bind]
  refine EvalDistEq.bind_right _ fun parameterOutput => ?_
  have hfresh : ∀ position, ((∅ : QueryCache HashSpec).cacheQuery
      (parameterInput seed) parameterOutput) (derivationInputs seed parameterOutput position) = none := by
    intro position
    rw [QueryCache.cacheQuery_of_ne _ _ (derivationInputs_ne_parameter seed parameterOutput position)]
    rfl
  have htable := evalDist_queryTable_fresh (R := HashOutput)
    (derivationInputs seed parameterOutput) (derivationInputs_injective seed parameterOutput)
    ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed) parameterOutput) hfresh
  refine (htable.bind_left _).trans ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun outputs => ?_
  have hprf : (cacheTable ((∅ : QueryCache HashSpec).cacheQuery (parameterInput seed) parameterOutput)
      (derivationInputs seed parameterOutput) outputs) (prfInput seed) = none := by
    rw [cacheTable_apply_of_not_mem _ _ _ _
      (fun position => (derivationInputs_ne_prf seed parameterOutput position).symm),
      QueryCache.cacheQuery_of_ne _ _ (prfInput_ne_parameterInput seed)]
    rfl
  dsimp only
  rw [QueryImpl.withCaching_run_none _ hprf]
  simp only [Functor.map_map]
  convert EvalDistEq.refl (_ <$> ($ᵗ HashOutput)) using 2
  all_goals first
    | rfl
    | (funext prf
       exact congrArg (fun cache : QueryCache HashSpec => (((parameterOutput, prf), outputs), cache))
         (cacheTable_eq_programCache (∅ : QueryCache HashSpec) seed ((parameterOutput, prf), outputs)).symm)

/-- Every complete continuation has the same output distribution after table preparation.
The seed is fixed in this statement, so the continuation may perform actual seeded keygen,
signing, and verification. Its oracle state still contains the seed-addressed entries. -/
theorem evalDist_prepared_continuation {α : Type} (computation : OracleComp OracleWorld α)
    (seed : MasterSeed) :
    ((simulateQ romImpl computation).run' ∅) =ᵈ (sampleMaterial >>= fun material =>
        (simulateQ romImpl computation).run' (programCache ∅ seed material)) := by
  refine (evalDist_presample_computation romImpl computation
    (liftM (prepareTable seed) : OracleComp OracleWorld Material) ∅).trans ?_
  rw [simulate_lift_hash]
  refine EvalDistEq.trans (my := ((fun material => (material, programCache ∅ seed material)) <$>
      sampleMaterial) >>= fun result => (simulateQ romImpl computation).run' result.2) ?_ ?_
  · exact (evalDist_prepareTable seed).bind_left _
  · rw [bind_map_left]

/-- Pure instrumentation counts all hash calls, including cached calls, and no private draws. -/
noncomputable def countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    OracleComp OracleWorld (α × Nat) :=
  counted (fun input : OracleWorld.Domain => input matches .inr _) computation

theorem simulateQ_countHashQueries {α : Type} (computation : OracleComp OracleWorld α) :
    simulateQ romImpl (countHashQueries computation) = (simulateQ countedOracle computation).run := by
  rw [countHashQueries, simulate_withCost]
  congr 2
  funext input
  cases input <;> simp only [countedOracle, QueryImpl.withAddCost_apply] <;> rfl

/-- Uniform hidden seed sampling can be moved after seed-independent material sampling.
The oracle cache in the continuation remains programmed at the sampled seed's addresses. -/
theorem evalDist_seeded_prepared {α : Type} (next : MasterSeed → OracleComp OracleWorld α) :
    ((simulateQ romImpl ((liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= next)).run' ∅) =ᵈ (sampleMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_lift_prob,
    bind_map_left, map_bind]
  refine EvalDistEq.trans (my := sampleMasterSeed >>= fun seed => sampleMaterial >>= fun material =>
    (simulateQ romImpl (next seed)).run' (programCache ∅ seed material)) ?_ ?_
  · exact EvalDistEq.bind_right _ fun seed => evalDist_prepared_continuation (next seed) seed
  · exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

theorem countHashQueries_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    countHashQueries (liftM (OracleWorld.query input) >>= next) = (do
      let answer ← liftM (OracleWorld.query input)
      let result ← countHashQueries (next answer)
      pure (result.1, (if (fun query : OracleWorld.Domain => query matches .inr _) input then 1 else 0) + result.2)) := rfl

theorem countHashQueries_lift_prob {α : Type} (computation : ProbComp α) :
    countHashQueries (liftM computation : OracleComp OracleWorld α) =
      (fun value => (value, 0)) <$> (liftM computation : OracleComp OracleWorld α) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind]
      change countHashQueries (liftM (OracleWorld.query (.inl input)) >>= _) = _
      simp only [countHashQueries_query_bind, ih, map_bind, bind_pure_comp, Functor.map_map]
      rfl

end FORS.Security.SeedCoupling

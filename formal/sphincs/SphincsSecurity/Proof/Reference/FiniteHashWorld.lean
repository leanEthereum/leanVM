import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.FixedHashBoundary
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OracleComp.DeferredSampling
set_option backward.isDefEq.respectTransparency false

noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

noncomputable def sampleHashTable (inputs : Finset HashInput) : ProbComp (inputs → HashOutput) :=
  $ᵗ (inputs → HashOutput)

theorem evalDist_finiteHashTable_extract {α : Type} (inputs : Finset HashInput) (input : inputs)
    (next : (inputs → HashOutput) → HashOutput → ProbComp α) :
    𝒟[do let table ← ($ᵗ (inputs → HashOutput) : ProbComp _); next table (table input)] =
      𝒟[do
        let output ← ($ᵗ HashOutput : ProbComp _)
        let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        next (Function.update table input output) output] := by
  classical
  have h := congrArg (fun distribution : SPMF (inputs → HashOutput) =>
    distribution >>= fun table => 𝒟[next table (table input)])
    (evalDist_uniformSample_bind_update (R := HashOutput) input)
  simpa only [evalDist_bind, bind_assoc, evalDist_pure, pure_bind, Function.update_self] using h.symm

noncomputable def hashInputs {α : Type} (computation : OracleComp OracleWorld α) : Finset HashInput := by
  classical
  induction computation using OracleComp.construct with
  | pure _ => exact ∅
  | query_bind input _ tail =>
      exact (match input with | .inl _ => ∅ | .inr input => {input}) ∪ Finset.univ.biUnion tail

@[simp] theorem hashInputs_pure {α : Type} (value : α) :
    hashInputs (pure value) = ∅ := rfl

theorem hashInputs_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) :
    hashInputs (liftM (OracleWorld.query input) >>= next) =
      (match input with | .inl _ => ∅ | .inr input => {input}) ∪
        Finset.univ.biUnion (fun output => hashInputs (next output)) := by
  simp only [hashInputs, OracleComp.construct_query_bind]
  cases input <;> rfl

attribute [local irreducible] hashInputs

theorem hashInputs_next_subset {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (output : OracleWorld.Range input) :
    hashInputs (next output) ⊆ hashInputs (liftM (OracleWorld.query input) >>= next) := by
  intro row hrow
  rw [hashInputs_query_bind, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨output, Finset.mem_univ _, hrow⟩)

theorem mem_hashInputs_hash_bind {α : Type} (input : HashInput)
    (next : HashOutput → OracleComp OracleWorld α) :
    input ∈ hashInputs (liftM (OracleWorld.query (.inr input)) >>= next) := by
  rw [hashInputs_query_bind, Finset.mem_union]
  exact Or.inl (Finset.mem_singleton_self _)

noncomputable def finiteHashAnswer (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) : QueryImpl HashSpec Id :=
  fun input => (cache input).getD (if h : input ∈ inputs then table ⟨input, h⟩ else 0)

theorem finiteHashAnswer_some (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) (input : HashInput) (output : HashOutput) (h : cache input = some output) :
    finiteHashAnswer cache inputs table input = output := by
  simp only [finiteHashAnswer, h, Option.getD_some]

theorem finiteHashAnswer_none (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) (input : HashInput) (hin : input ∈ inputs) (h : cache input = none) :
    finiteHashAnswer cache inputs table input = table ⟨input, hin⟩ := by
  simp only [finiteHashAnswer, h, Option.getD_none, dif_pos hin]

theorem finiteHashAnswer_cacheQuery (cache : QueryCache HashSpec) (inputs : Finset HashInput)
    (table : inputs → HashOutput) (input : HashInput) (hin : input ∈ inputs)
    (h : cache input = none) (output : HashOutput) :
    finiteHashAnswer (cache.cacheQuery input output) inputs table =
      finiteHashAnswer cache inputs (Function.update table ⟨input, hin⟩ output) := by
  classical
  funext row
  by_cases heq : row = input
  · subst row
    simp [finiteHashAnswer, h, hin]
  · by_cases hrow : row ∈ inputs
    · have hne : (⟨row, hrow⟩ : inputs) ≠ ⟨input, hin⟩ := fun hsub => heq (congrArg Subtype.val hsub)
      simp [finiteHashAnswer, QueryCache.cacheQuery, heq, hrow, hne]
    · simp [finiteHashAnswer, QueryCache.cacheQuery, heq, hrow]

theorem romRun_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (liftM (OracleWorld.query input) >>= next)).run' cache =
      (romImpl input).run cache >>= fun result => (simulateQ romImpl (next result.1)).run' result.2 := by
  rw [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
  rfl

theorem evalDist_romRun_eq_finiteHash {α : Type} (computation : OracleComp OracleWorld α)
    (inputs : Finset HashInput) (hinputs : hashInputs computation ⊆ inputs) (cache : QueryCache HashSpec) :
    𝒟[(simulateQ romImpl computation).run' cache] =
      𝒟[do
        let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
        simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) computation] := by
  classical
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      exact (evalDist_bind_const_neverFails _ (by simp) (pure value)).symm
  | query_bind input next ih =>
      have hnext : ∀ output, hashInputs (next output) ⊆ inputs :=
        fun output => (hashInputs_next_subset input next output).trans hinputs
      rw [romRun_query_bind]
      cases input with
      | inl sample =>
          change 𝒟[(liftM (unifSpec.query sample) : ProbComp _) >>= fun output =>
            (simulateQ romImpl (next output)).run' cache] = _
          trans 𝒟[do
            let output ← (liftM (unifSpec.query sample) : ProbComp _)
            let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
            simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) (next output)]
          · exact evalDist_bind_congr_left _ _ _ (fun output => ih output (hnext output) cache)
          · rw [evalDist_bind_comm]
            apply evalDist_bind_congr_left
            intro table
            simp only [simulateQ_bind, simulateQ_spec_query, fixedHashWorld]
            rfl
      | inr input =>
          have hin : input ∈ inputs := hinputs (mem_hashInputs_hash_bind input next)
          rw [show romImpl (.inr input) = randomOracle (spec := HashSpec) input from rfl]
          cases hcache : cache input with
          | some output =>
              rw [QueryImpl.withCaching_run_some _ hcache, pure_bind, ih output (hnext output) cache]
              apply evalDist_bind_congr_left
              intro table
              simp only [simulateQ_bind, simulateQ_spec_query, fixedHashWorld,
                finiteHashAnswer_some cache inputs table input output hcache, pure_bind]
          | none =>
              rw [QueryImpl.withCaching_run_none _ hcache, map_eq_bind_pure_comp]
              simp only [Function.comp, bind_assoc, pure_bind]
              trans 𝒟[do
                let output ← ($ᵗ HashOutput : ProbComp _)
                let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
                simulateQ (fixedHashWorld (finiteHashAnswer (cache.cacheQuery input output) inputs table)) (next output)]
              · exact evalDist_bind_congr_left _ _ _ (fun output => ih output (hnext output) _)
              · simp_rw [finiteHashAnswer_cacheQuery cache inputs _ input hin hcache]
                rw [← evalDist_finiteHashTable_extract inputs (⟨input, hin⟩ : inputs)
                  (fun table output => simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) (next output))]
                apply evalDist_bind_congr_left
                intro table
                simp only [simulateQ_bind, simulateQ_spec_query, fixedHashWorld,
                  finiteHashAnswer_none cache inputs table input hin hcache, pure_bind]

end SphincsSecurity.Concrete

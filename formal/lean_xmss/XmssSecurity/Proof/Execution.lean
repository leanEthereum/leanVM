module

public import XmssSecurity.Proof.RandomizedStatement

@[expose] public section

/-!
# The security game with its final cache

Under `romImpl` a lifted probabilistic computation leaves the cache unchanged
(`xmssRom_lift_probComp_cache_eq`) and every computation's final cache extends its initial one
(`xmssRom_cache_le`). `gameWithCache` runs the security game from the empty cache and keeps its
final cache, with the same winning probability (`forgeAdvantage_eq_gameWithCache`).
-/

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem xmssRom_lift_probComp_cache_eq {α : Type} (computation : ProbComp α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support
      ((simulateQ romImpl (liftM computation)).run initialCache)) :
    result.2 = initialCache := by
  have hsupport := roSim.run_liftM_support
    (hashSpec := HashSpec)
    (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
    computation initialCache
  rw [show support ((simulateQ romImpl (liftM computation)).run initialCache) =
      (fun output => (output, initialCache)) '' support computation by
    simpa [romImpl] using hsupport] at hmem
  obtain ⟨output, _houtput, heq⟩ := hmem
  exact (congrArg Prod.snd heq).symm

theorem romImpl_query_cache_le
    (input : OracleWorld.Domain) (initialCache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hmem : result ∈ support ((romImpl input).run initialCache)) :
    initialCache ≤ result.2 := by
  cases input with
  | inl uniformInput =>
      obtain ⟨output, finalCache⟩ := result
      change unifSpec.Range uniformInput at output
      have hrun :
          (unifFwdImpl HashSpec uniformInput).run initialCache =
            (fun sample => (sample, initialCache)) <$>
              (liftM (unifSpec.query uniformInput) : ProbComp _) := by
        simpa [simulateQ_query] using
          (unifFwdImpl.simulateQ_run
            (hashSpec := HashSpec)
            (liftM (unifSpec.query uniformInput) : ProbComp _) initialCache)
      simp only [romImpl, QueryImpl.add_apply] at hmem
      have hmem' : (output, finalCache) ∈ support
          ((unifFwdImpl HashSpec uniformInput).run initialCache) := hmem
      rw [hrun, support_map] at hmem'
      obtain ⟨sample, _hsample, heq⟩ := hmem'
      exact le_of_eq (congrArg Prod.snd heq)
  | inr hashInput =>
      exact QueryImpl.withCaching_cache_le uniformSampleImpl hashInput initialCache
        result hmem

theorem xmssRom_cache_le {α : Type} (computation : OracleComp OracleWorld α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ romImpl computation).run initialCache)) :
    initialCache ≤ result.2 := by
  exact OracleComp.simulateQ_run_preservesInv romImpl
    (fun cache => initialCache ≤ cache)
    (by
      intro input cache hcache queryResult hquery
      exact hcache.trans (romImpl_query_cache_le input cache queryResult hquery))
    computation initialCache le_rfl result hmem

/-- The full security game with the final lazy random-oracle cache kept in its output. -/
noncomputable def gameWithCache (scheme : Scheme SecretKey) (adversary : Adversary) :
    ProbComp (Bool × QueryCache HashSpec) :=
  (simulateQ romImpl (gameCore scheme adversary)).run ∅

/-- Keeping the final cache does not change the winning probability. -/
theorem forgeAdvantage_eq_gameWithCache (scheme : Scheme SecretKey) (adversary : Adversary) :
    forgeAdvantage scheme adversary =
      Pr{let outcome ← gameWithCache scheme adversary}[outcome.1 = true] := by
  unfold forgeAdvantage gameWithCache
  rw [StateT.run'_eq, prEvent_map]

end XmssSecurity

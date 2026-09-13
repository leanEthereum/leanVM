import SphincsSecurity.Proof.Seeded.AdaptiveSeedGuessing

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem exists_seed_not_hit (inputs : List HashInput) (hsize : inputs.length < 2 ^ 256) :
    ∃ seed, ¬SeedHitLog inputs seed := by
  classical
  by_contra h
  have hall : ∀ seed, SeedHitLog inputs seed := by simpa using h
  have hone : Pr[SeedHitLog inputs | sampleMasterSeed] = 1 := by
    simp [hall]
  have hlt : (inputs.length : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) < 1 :=
    ENNReal.div_lt_of_lt_mul (by rw [one_mul]; exact_mod_cast hsize)
  exact (not_lt_of_ge (hone ▸ probEvent_seedHitLog_le inputs)) hlt

theorem hashQueryBound_query_bind_of {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (q : Nat)
    (hcost : (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) ≤ q)
    (hnext : ∀ result ∈ support ((romImpl input).run cache),
      HashQueryBound (next result.1) result.2
        (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0))) :
    HashQueryBound (liftM (OracleWorld.query input) >>= next) cache q := by
  intro result hresult
  rw [countHashQueries_query_bind, run'_query_bind, mem_support_bind_iff] at hresult
  obtain ⟨step, hstep, htail⟩ := hresult
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map,
    Functor.map_map, support_map] at htail
  obtain ⟨tail, htail, rfl⟩ := htail
  have h := hnext step hstep (tail.1.1,
    tail.1.2)
  have htail' : tail.1 ∈ support ((simulateQ romImpl
      (countHashQueries (next step.1))).run' step.2) := by
    rw [StateT.run'_eq, support_map]
    exact ⟨tail, htail, rfl⟩
  have := h htail'
  cases input <;> simp_all
  omega

noncomputable def cacheAfter (cache : QueryCache HashSpec) (input : OracleWorld.Domain)
    (answer : OracleWorld.Range input) : QueryCache HashSpec :=
  match input with
  | .inl _ => cache
  | .inr input => match cache input with
    | none => cache.cacheQuery input answer
    | some _ => cache

theorem romImpl_support_cacheAfter (input : OracleWorld.Domain) (cache : QueryCache HashSpec)
    (result : OracleWorld.Range input × QueryCache HashSpec)
    (hresult : result ∈ support ((romImpl input).run cache)) :
    result.2 = cacheAfter cache input result.1 := by
  cases input with
  | inl input =>
      change result ∈ support ((fun answer => (answer, cache)) <$>
        (liftM (unifSpec.query input) : ProbComp _)) at hresult
      rw [support_map] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      rfl
  | inr input =>
      change result ∈ support ((randomOracle input).run cache) at hresult
      cases hc : cache input with
      | none =>
          rw [QueryImpl.withCaching_run_none _ hc, support_map] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          simp [cacheAfter, hc]
      | some answer =>
          rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simp [cacheAfter, hc]

theorem romImpl_support_transfer (bad : HashInput → Prop) (left right : QueryCache HashSpec)
    (h : AgreeOutside bad left right) (input : OracleWorld.Domain) (hinput : ¬hashBad bad input)
    (answer : OracleWorld.Range input)
    (hanswer : (answer, cacheAfter right input answer) ∈ support ((romImpl input).run right)) :
    (answer, cacheAfter left input answer) ∈ support ((romImpl input).run left) ∧
      AgreeOutside bad (cacheAfter left input answer) (cacheAfter right input answer) := by
  cases input with
  | inl input =>
      dsimp [OracleWorld] at answer hanswer ⊢
      constructor
      · change (answer, left) ∈ support ((fun answer => (answer, left)) <$>
          (liftM (unifSpec.query input) : ProbComp _))
        rw [support_map]
        exact ⟨answer, mem_support_query input answer, rfl⟩
      · exact h
  | inr input =>
      have heq := h input hinput
      dsimp [cacheAfter] at hanswer ⊢
      change (answer, _) ∈ support ((randomOracle input).run right) at hanswer
      change (answer, _) ∈ support ((randomOracle input).run left) ∧ _
      cases hl : left input with
      | none =>
          have hr : right input = none := heq.symm.trans hl
          simp only [hr] at hanswer ⊢
          constructor
          · rw [QueryImpl.withCaching_run_none _ hl, support_map]
            exact ⟨answer, mem_support_uniformSample _, rfl⟩
          · exact h.cacheQuery input answer
      | some value =>
          have hr : right input = some value := heq.symm.trans hl
          simp only [hr] at hanswer ⊢
          rw [QueryImpl.withCaching_run_some _ hr, support_pure, Set.mem_singleton_iff] at hanswer
          have ha : answer = value := congrArg Prod.fst hanswer
          subst answer
          exact ⟨by rw [QueryImpl.withCaching_run_some _ hl]; simp, h⟩

/-- A budget valid for every unguessed seed also bounds the ordinary consistent oracle. -/
theorem hashQueryBound_of_seed_caches {α : Type} (computation : OracleComp OracleWorld α)
    (q : Nat) (inputs : List HashInput) (caches : MasterSeed → QueryCache HashSpec)
    (cache : QueryCache HashSpec) (hsize : inputs.length + q < 2 ^ 256)
    (hagree : ∀ seed, ¬SeedHitLog inputs seed →
      AgreeOutside (fun input => SeedHit input seed) (caches seed) cache)
    (hbound : ∀ seed, ¬SeedHitLog inputs seed → HashQueryBound computation (caches seed) q) :
    HashQueryBound computation cache q := by
  induction computation using OracleComp.inductionOn generalizing q inputs caches cache with
  | pure value =>
      intro result hresult
      simp only [countHashQueries_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure,
        map_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le q
  | query_bind input next ih =>
      obtain ⟨seed, hseed⟩ := exists_seed_not_hit inputs (by omega)
      obtain ⟨step, hstep⟩ := probComp_support_nonempty ((romImpl input).run (caches seed))
      have hcost := (hashQueryBound_query_bind input next (caches seed) q
        (hbound seed hseed) step hstep).1
      apply hashQueryBound_query_bind_of input next cache q hcost
      intro result hresult
      have hcache := romImpl_support_cacheAfter input cache result hresult
      rcases result with ⟨answer, nextCache⟩
      dsimp at hcache
      subst nextCache
      have havoid (seed : MasterSeed) (hseed : ¬SeedHitLog (prependHash input inputs) seed) :
          ¬hashBad (fun input => SeedHit input seed) input ∧ ¬SeedHitLog inputs seed := by
        change ¬TraceHits (fun input => SeedHit input seed) (prependHash input inputs) at hseed
        rw [traceHits_prepend] at hseed
        exact not_or.mp hseed
      have htransfer (seed : MasterSeed) (hseed : ¬SeedHitLog (prependHash input inputs) seed) :=
        romImpl_support_transfer (fun input => SeedHit input seed) (caches seed) cache
          (hagree seed (havoid seed hseed).2) input (havoid seed hseed).1 answer hresult
      apply ih answer
        (q - (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0))
        (prependHash input inputs) (fun seed => cacheAfter (caches seed) input answer)
        (cacheAfter cache input answer)
      · cases input <;> simp_all [prependHash]
      · intro seed hseed
        exact (htransfer seed hseed).2
      · intro seed hseed
        exact (hashQueryBound_query_bind input next (caches seed) q
          (hbound seed (havoid seed hseed).2) _ (htransfer seed hseed).1).2

end SphincsSecurity.Seeded

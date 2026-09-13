import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Extract
/-!
# From the run to an answer function

The extraction lemmas are facts about `evalWithAnswerFn f`, and the game runs under the lazy oracle.
The bridge is VCVio's support characterization: a value comes out of the lazy oracle exactly when some
total answer function agreeing with the cache evaluates the computation to it.

That characterization is stated for a computation over one spec, and the game's spec is
`unifSpec + HashSpec`. It applies anyway, because the part the extraction analyses is verification,
and verification samples nothing: it is an `OracleComp HashSpec Bool`, lifted into the sum.
-/

namespace SphincsSecurity

open OracleComp OracleSpec

/-- The inputs queried on the execution path selected by an answer function. -/
def queriedInputs {alpha : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) :
    List HashInput :=
  ((simulateQ (f.withLogging) oa).run).2.map Sigma.fst

@[simp] theorem queriedInputs_pure {alpha : Type} (f : QueryImpl HashSpec Id) (x : alpha) :
    queriedInputs f (pure x) = [] := by
  rfl

@[simp] theorem queriedInputs_query_bind {alpha : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec alpha) :
    queriedInputs f (liftM (HashSpec.query input) >>= next)
      = input :: queriedInputs f (next (f input)) := by
  rfl

theorem queriedInputs_bind {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta) :
    queriedInputs f (oa >>= next)
      = queriedInputs f oa ++ queriedInputs f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, queriedInputs_query_bind, queriedInputs_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

theorem queriedInputs_mono_bind_left {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta)
    {input : HashInput} (hinput : input ∈ queriedInputs f oa) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_left _ hinput

theorem queriedInputs_mono_bind_right {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta)
    {input : HashInput} (hinput : input ∈ queriedInputs f (next (evalWithAnswerFn f oa))) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_right _ hinput

@[simp] theorem queriedInputs_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    queriedInputs f (Concrete.tweakableHash parameter domain payload)
      = [tweakableHashInput parameter domain payload] := by
  change queriedInputs f
    (liftM (HashSpec.query (tweakableHashInput parameter domain payload)) >>=
      fun answer => pure (truncateHash answer)) = _
  rw [queriedInputs_query_bind, queriedInputs_pure]

/-- Every answer function agreeing with a run's final cache replays that run, and all inputs on the
replay path occur in the cache. -/
theorem replay_of_mem_support {alpha : Type} (oa : OracleComp HashSpec alpha)
    (cache : QueryCache HashSpec) (a : alpha) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    cache ≤ cache' ∧ evalWithAnswerFn f oa = a
      ∧ ∀ input, input ∈ queriedInputs f oa → cache' input ≠ none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      refine ⟨le_rfl, rfl, ?_⟩
      simp
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      change (answer, cacheMid) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : cacheMid input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
              Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      obtain ⟨hle, heval, hqueries⟩ := ih answer cacheMid a cache' hrest hf
      have hcached' : cache' input = some answer := hle hcached
      have hfinput : f input = answer := hf hcached'
      refine ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl input cache
        (answer, cacheMid) hquery).trans hle, ?_, ?_⟩
      · rw [evalWithAnswerFn_bind,
          show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
            simulateQ_spec_query f input, hfinput]
        exact heval
      · intro input₀ hqueried
        rw [queriedInputs_query_bind, List.mem_cons, hfinput] at hqueried
        rcases hqueried with rfl | hqueried
        · simp [hcached']
        · exact hqueries input₀ hqueried

theorem replay_of_mem_support_of_le {alpha : Type} (oa : OracleComp HashSpec alpha)
    (cache : QueryCache HashSpec) (a : alpha) (cache' finalCache : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (hle : cache' ≤ finalCache) (f : QueryImpl HashSpec Id) (hf : finalCache.AgreesWithFn f) :
    evalWithAnswerFn f oa = a
      ∧ ∀ input, input ∈ queriedInputs f oa → finalCache input ≠ none := by
  have hf' : cache'.AgreesWithFn f := fun _ _ hcached => hf (hle hcached)
  obtain ⟨_, heval, hqueries⟩ := replay_of_mem_support oa cache a cache' hmem f hf'
  refine ⟨heval, fun input hinput => ?_⟩
  obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp (hqueries input hinput)
  rw [hle hanswer]
  simp

/-- A cache entry absent initially stays absent when its input does not occur on the replay path. -/
theorem cache_eq_none_of_not_mem_queriedInputs {alpha : Type}
    (oa : OracleComp HashSpec alpha) (cache : QueryCache HashSpec)
    (a : alpha) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f)
    (target : HashInput) (hnone : cache target = none)
    (hnot : target ∉ queriedInputs f oa) : cache' target = none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hnone
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      change (answer, cacheMid) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : cacheMid input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache,
              support_pure, Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      have hle : cacheMid ≤ cache' :=
        (replay_of_mem_support (next answer) cacheMid a cache' hrest f hf).1
      have hfinput : f input = answer := hf (hle hcached)
      have htarget : target ≠ input := by
        intro heq
        apply hnot
        rw [queriedInputs_query_bind]
        exact List.mem_cons.2 (Or.inl heq)
      have hmid : cacheMid target = none := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache,
              support_pure, Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hnone
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            rwa [QueryCache.cacheQuery_of_ne _ _ htarget]
      apply ih answer cacheMid a cache' hrest hf hmid
      rw [queriedInputs_query_bind, List.mem_cons, hfinput] at hnot
      intro htail
      exact hnot (Or.inr htail)

/-- A random-oracle run can be replayed by an answer function agreeing with its final cache, and
every query on that replay path is present there. -/
theorem exists_answerFn_replay_of_mem_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache)) :
    cache ≤ cache' ∧
      ∃ f : QueryImpl HashSpec Id, cache'.AgreesWithFn f ∧ evalWithAnswerFn f oa = a
        ∧ ∀ input, input ∈ queriedInputs f oa → cache' input ≠ none := by
  classical
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) cache'
      refine ⟨le_rfl, f, hf, rfl, ?_⟩
      intro input hqueried
      simp at hqueried
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      change (answer, cacheMid) ∈ support ((randomOracle input).run cache) at hquery
      have hcached : cacheMid input = some answer := by
        cases hcache : cache input with
        | some old =>
            rw [QueryImpl.withCaching_run_some uniformSampleImpl hcache, support_pure,
              Set.mem_singleton_iff] at hquery
            obtain ⟨rfl, rfl⟩ := hquery
            exact hcache
        | none =>
            rw [QueryImpl.withCaching_run_none uniformSampleImpl hcache, support_map] at hquery
            obtain ⟨sample, _, heq⟩ := hquery
            obtain ⟨rfl, rfl⟩ := heq
            exact QueryCache.cacheQuery_self cache input answer
      obtain ⟨hle, f, hf, heval, hqueries⟩ := ih answer cacheMid a cache' hrest
      have hcached' : cache' input = some answer := hle hcached
      have hfinput : f input = answer := hf hcached'
      refine ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl input cache
        (answer, cacheMid) hquery).trans hle, f, hf, ?_, ?_⟩
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, hfinput]
      exact heval
      intro input₀ hqueried
      rw [queriedInputs_query_bind, List.mem_cons, hfinput] at hqueried
      rcases hqueried with rfl | hqueried
      · simp [hcached']
      · exact hqueries input₀ hqueried

/-- A random-oracle run can be replayed by an answer function agreeing with its final cache. -/
theorem exists_answerFn_agrees_final_of_mem_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache)) :
    cache ≤ cache' ∧
      ∃ f : QueryImpl HashSpec Id, cache'.AgreesWithFn f ∧ evalWithAnswerFn f oa = a := by
  obtain ⟨hle, f, hf, heval, _⟩ := exists_answerFn_replay_of_mem_support oa cache a cache' hmem
  exact ⟨hle, f, hf, heval⟩

/-- Simulating a lifted hash-only computation is simulating it under the random oracle. -/
theorem simulateQ_romImpl_liftM {α : Type} (oa : OracleComp HashSpec α) :
    simulateQ romImpl (liftM oa : OracleComp OracleWorld α)
      = simulateQ (randomOracle : QueryImpl HashSpec _) oa :=
  QueryImpl.simulateQ_add_liftM_right _ _ oa

/-! ### One layer of the walk, unpeeled

What the extraction consumes is the two facts of a single layer: that `Ots.leaf` returned something,
and that folding it reached what the layer above was handed. This peels them off `verifyLayers`.
-/

namespace Concrete

open OracleComp

theorem verifyLayers_succ_extract (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (remaining : Nat) (hlayer : remaining < numLayers)
    (message : Digest) (target : Digest)
    (hverify : evalWithAnswerFn f
        (verifyLayers parameter index signature (remaining + 1) message) = some target) :
    ∃ leafValue, evalWithAnswerFn f (otsLeaf parameter ⟨remaining, hlayer⟩
          (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
          (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩))
        = some leafValue
      ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining
          (foldValue f parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
            (leafIndexAt index ⟨remaining, hlayer⟩) (signaturePath signature ⟨remaining, hlayer⟩)
            leafValue (layerHeight ⟨remaining, hlayer⟩))) = some target := by
  rcases hleaf : evalWithAnswerFn f (otsLeaf parameter ⟨remaining, hlayer⟩
      (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
      (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩))
    with _ | leafValue
  · rw [verifyLayers_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simp at hverify
  · refine ⟨leafValue, rfl, ?_⟩
    rw [verifyLayers_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simpa [foldValue, evalWithAnswerFn_bind] using hverify

end Concrete

end SphincsSecurity

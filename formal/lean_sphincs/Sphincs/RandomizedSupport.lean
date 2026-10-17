import Sphincs.RandomizedCorrectness
import Sphincs.RandomizedDigest

/-!
Support-level correctness of the independently randomized signer in the lazy random-oracle model.
The replay argument is adapted from leanVM b7a107256, with the grinding loop handled separately
because its private uniform samples are outside the hash-oracle answer function.
-/

open OracleComp OracleSpec

namespace Sphincs.Completeness

open Concrete

/-- A lazy-oracle query records its answer and preserves all previous answers. -/
theorem query_support_cached (input : HashInput) (cache : QueryCache HashSpec)
    (answer : HashOutput) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((randomOracle (spec := HashSpec) input).run cache)) :
    cache ≤ cache' ∧ cache' input = some answer := by
  refine ⟨QueryImpl.withCaching_cache_le uniformSampleImpl input cache (answer, cache') hmem, ?_⟩
  cases hc : cache input with
  | some old =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact hc
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, support_map] at hmem
      obtain ⟨sample, _, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := heq
      exact QueryCache.cacheQuery_self cache input answer

/-- Any answer function extending a lazy-oracle run's cache replays that run. -/
theorem replay_hash_support {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support ((simulateQ randomOracle oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    cache ≤ cache' ∧ evalWithAnswerFn f oa = a := by
  induction oa using OracleComp.inductionOn generalizing cache a cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨le_rfl, rfl⟩
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      obtain ⟨hqueryLe, hcached⟩ := query_support_cached input cache answer cacheMid hquery
      obtain ⟨hrestLe, heval⟩ := ih answer cacheMid a cache' hrest hf
      have hfinput : f input = answer := hf (hrestLe hcached)
      refine ⟨hqueryLe.trans hrestLe, ?_⟩
      rw [evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, hfinput]
      exact heval

/-- Hash-only runs never delete or overwrite previous oracle answers. -/
theorem hash_support_cache_le {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (a : α) (cache' : QueryCache HashSpec)
    (hmem : (a, cache') ∈ support ((simulateQ randomOracle oa).run cache)) :
    cache ≤ cache' := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn cache'
  exact (replay_hash_support oa cache a cache' hmem f hf).1

variable [Params]

attribute [local irreducible] digestAttemptLimit encodingAttemptLimit Seeded.treeRoot
  Seeded.treeNode Seeded.subNode Seeded.topNode Seeded.spineNode Randomized.finishSign

/-- A successful scan leaves a cached answer certifying that it landed. -/
theorem scanLoop_support (sk : Seeded.SecretKey) (message : Message) :
    ∀ (n : Nat) (start : Randomness) (cache : QueryCache HashSpec) (result : Option Randomness)
      (cache' : QueryCache HashSpec),
      (result, cache') ∈ support ((simulateQ randomOracle
        (Randomized.scanLoop sk message n start)).run cache) →
      cache ≤ cache' ∧ ∀ ρ, result = some ρ → ∃ answer,
        cache' (msgInput sk message ρ) = some answer ∧
          Landed sk.parameter (blockIndex answer) := by
  intro n
  induction n with
  | zero =>
      intro start cache result cache' hmem
      simp only [Randomized.scanLoop, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨le_rfl, by simp⟩
  | succ n ih =>
      intro start cache result cache' hmem
      rw [run_randomizedDigest_succ, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, cacheMid⟩, hquery, hrest⟩ := hmem
      obtain ⟨hqueryLe, hcached⟩ := query_support_cached _ _ _ _ hquery
      split at hrest
      next hland =>
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hrest
        obtain ⟨rfl, rfl⟩ := hrest
        refine ⟨hqueryLe, ?_⟩
        intro ρ' heq
        cases Option.some.inj heq
        exact ⟨answer, hcached, hland⟩
      next =>
        obtain ⟨hrestLe, hresult⟩ := ih (start + 1) cacheMid result cache' hrest
        exact ⟨hqueryLe.trans hrestLe, hresult⟩

/-- A successful randomized grinding loop leaves a cached answer certifying that it landed. -/
theorem randomizedDigest_support (sk : Seeded.SecretKey) (message : Message)
    (n : Nat) (cache : QueryCache HashSpec) (result : Option Randomness)
    (cache' : QueryCache HashSpec)
    (hmem : (result, cache') ∈ support ((simulateQ romImpl
      (Randomized.signDigestLoop sk message n)).run cache)) :
    cache ≤ cache' ∧ ∀ ρ, result = some ρ → ∃ answer,
      cache' (msgInput sk message ρ) = some answer ∧
        Landed sk.parameter (blockIndex answer) := by
  rw [run_randomizedDigest_start, mem_support_bind_iff] at hmem
  obtain ⟨start, _, hmem⟩ := hmem
  exact scanLoop_support sk message n start cache result cache' hmem

/-- A successful randomized sign run replays as assembly with a landed randomizer. -/
theorem randomized_sign_replay (sk : Seeded.SecretKey) (message : Message)
    (signature : Signature) (cache cache' : QueryCache HashSpec)
    (hmem : (some signature, cache') ∈ support
      ((simulateQ romImpl (Randomized.sign sk message)).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f) :
    cache ≤ cache' ∧ ∃ ρ,
      Landed sk.parameter (digestIndex (digestValue f sk message ρ)) ∧
        evalWithAnswerFn f (Randomized.finishSign sk message ρ) = some signature := by
  rw [Randomized.sign, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨result, cacheMid⟩, hloop, hfinish⟩ := hmem
  obtain ⟨hloopLe, hland⟩ := randomizedDigest_support sk message _ _ _ _ hloop
  cases result with
  | none => simp at hfinish
  | some ρ =>
      rw [simulate_lift_hash] at hfinish
      obtain ⟨hfinishLe, heval⟩ := replay_hash_support _ _ _ _ hfinish f hf
      obtain ⟨answer, hcached, hland⟩ := hland ρ rfl
      refine ⟨hloopLe.trans hfinishLe, ρ, ?_, heval⟩
      rw [digestValue_index]
      have hanswer : f (msgInput sk message ρ) = answer := hf (hfinishLe hcached)
      change Landed sk.parameter (blockIndex (f (msgInput sk message ρ)))
      rwa [hanswer]

/-- Fixed-function correctness for the independent-randomizer assembly, with a generated key. -/
theorem correct_randomized_assembly (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (pk : PublicKey) (sk : Seeded.SecretKey) (message : Message)
    (ρ : Randomness) (signature : Signature)
    (hkey : evalWithAnswerFn f (Seeded.keygenFromMaster seed) = (pk, sk))
    (hland : Landed sk.parameter (digestIndex (digestValue f sk message ρ)))
    (hsign : evalWithAnswerFn f (Randomized.finishSign sk message ρ) = some signature) :
    evalWithAnswerFn f (Concrete.verify pk message signature : OracleComp HashSpec Bool) = true := by
  simp only [Seeded.keygenFromMaster, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    Prod.mk.injEq] at hkey
  generalize hparameter : evalWithAnswerFn f
    (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter at hkey
  generalize hrootval : evalWithAnswerFn f
    (Seeded.treeRoot parameter topLayer rootTree seed : OracleComp HashSpec Digest) = root at hkey
  obtain ⟨hpk, hsk⟩ := hkey
  subst pk
  subst sk
  exact verify_of_finishSign f ⟨seed, parameter, root⟩ message ρ hrootval.symm hland hsign

/-- Every successful honest signature verifies in the actual lazy random oracle, for any pruning
height and any initial cache. Private uniform randomizer sampling is included in the run. -/
theorem verify_of_keygen_sign_support (seed : MasterSeed) (pk : PublicKey)
    (sk : Seeded.SecretKey) (message : Message) (signature : Signature) (accepted : Bool)
    (cache₀ cacheK cacheS cacheV : QueryCache HashSpec)
    (hkey : ((pk, sk), cacheK) ∈ support
      ((simulateQ randomOracle (Seeded.keygenFromMaster seed)).run cache₀))
    (hsign : (some signature, cacheS) ∈ support
      ((simulateQ romImpl (Randomized.sign sk message)).run cacheK))
    (hverify : (accepted, cacheV) ∈ support
      ((simulateQ randomOracle (Concrete.verify pk message signature
        : OracleComp HashSpec Bool)).run cacheS)) : accepted = true := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn cacheV
  obtain ⟨hverifyLe, hevalVerify⟩ := replay_hash_support _ _ _ _ hverify f hf
  have hfS : cacheS.AgreesWithFn f := fun _ _ h => hf (hverifyLe h)
  obtain ⟨hsignLe, ρ, hland, hevalSign⟩ :=
    randomized_sign_replay sk message signature cacheK cacheS hsign f hfS
  have hfK : cacheK.AgreesWithFn f := fun _ _ h => hfS (hsignLe h)
  have hevalKey := (replay_hash_support _ _ _ _ hkey f hfK).2
  exact hevalVerify.symm.trans
    (correct_randomized_assembly f seed pk sk message ρ signature hevalKey hland hevalSign)

end Sphincs.Completeness

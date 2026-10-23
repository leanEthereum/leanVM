import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.EncodingOracleSimulation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

theorem simulate_chainHash_run_of_fresh
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) (cache : QueryCache HashSpec)
    (habsent : cache
      (Concrete.CacheView.keyChainInput parameter key chain step value) = none) :
    (simulateQ randomOracle
      (Concrete.keyChainHash parameter key chain step value :
        OracleComp HashSpec Digest)).run cache =
      (fun output => (truncateHash output,
        cache.cacheQuery
          (Concrete.CacheView.keyChainInput parameter key chain step value)
          output)) <$> uniformHashOutput := by
  let input := Concrete.CacheView.keyChainInput parameter key chain step value
  rw [Concrete.simulateQ_keyChainHash_run]
  change (fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run cache = _
  rw [randomOracle_run_none_eq_uniformHashOutput _ _ habsent]
  simp [Functor.map_map]

noncomputable def programmedChainExtension
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    ProbComp (Vector Digest ((n + 1) + 1) × QueryCache HashSpec) := do
  let sampled ← Rom.sampledHashOutputWithDigest
  pure (values.push sampled.1,
    cache.cacheQuery
      (Concrete.CacheView.keyChainInput parameter key chain step values.back)
      sampled.2)

set_option maxRecDepth 100000 in
theorem evalDist_chainExtension_eq_programmed
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec)
    (habsent : cache
      (Concrete.CacheView.keyChainInput parameter key chain step values.back) = none) :
    ((simulateQ randomOracle ((do
      let next ← Concrete.keyChainHash parameter key chain step values.back
      pure (values.push next)) :
        OracleComp HashSpec (Vector Digest ((n + 1) + 1)))).run
        cache) =ᵈ
    (programmedChainExtension parameter key chain step values cache) := by
  rw [simulateQ_bind, StateT.run_bind,
    simulate_chainHash_run_of_fresh parameter key chain step values.back
      cache habsent]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, simulateQ_pure, StateT.run_pure]
  unfold programmedChainExtension
  symm
  exact Rom.evalDist_sampledHashOutputWithDigest_bind_eq_uniform_bind
    (fun sampled => pure
      (values.push sampled.1,
        cache.cacheQuery
          (Concrete.CacheView.keyChainInput parameter key chain step values.back)
          sampled.2))

noncomputable def programmedChainTrajectory
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position : Nat) : (steps : Nat) → Digest → QueryCache HashSpec →
      ProbComp (Vector Digest (steps + 1) × QueryCache HashSpec)
  | 0, value, cache => pure (Vector.ofFn (fun _ => value), cache)
  | steps + 1, value, cache => do
      let prior ← programmedChainTrajectory parameter key chain position
        steps value cache
      if hvalid : position + steps < chainLength - 1 then
        programmedChainExtension parameter key chain ⟨position + steps, hvalid⟩
          prior.1 prior.2
      else
        pure (prior.1.push 0, prior.2)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_chainTrajectory_eq_programmed
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (value : Digest)
      (cache : QueryCache HashSpec),
      position + steps ≤ chainLength - 1 →
      (∀ step : ChainStep, ∀ input,
        AtHashAddress parameter (key.chainDomain chain step) input →
          cache input = none) →
      ((simulateQ randomOracle
        (Concrete.chainTrajectory parameter key chain position steps value)).run
          cache) =ᵈ
      (programmedChainTrajectory parameter key chain position steps
        value cache) := by
  intro steps
  induction steps with
  | zero =>
      intro value cache _hsteps _habsent
      simp [Concrete.chainTrajectory_zero, programmedChainTrajectory]
  | succ steps ih =>
      intro value cache hsteps habsent
      have hvalid : position + steps < chainLength - 1 := by
        omega
      rw [Concrete.chainTrajectory_succ, programmedChainTrajectory]
      simp only [hvalid, ↓reduceDIte, simulateQ_bind, StateT.run_bind,
        simulateQ_pure, StateT.run_pure]
      let actualPrior := (simulateQ randomOracle
        (Concrete.chainTrajectory parameter key chain position steps value)).run
          cache
      let programmedPrior := programmedChainTrajectory parameter key chain
        position steps value cache
      let actualExtension := fun prior :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        (simulateQ randomOracle
          (Concrete.keyChainHash parameter key chain
            ⟨position + steps, hvalid⟩ prior.1.back :
            OracleComp HashSpec Digest)).run prior.2 >>= fun hashed =>
          pure (prior.1.push hashed.1, hashed.2)
      let programmedExtension := fun prior :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        programmedChainExtension parameter key chain
          ⟨position + steps, hvalid⟩ prior.1 prior.2
      change (actualPrior >>= actualExtension) =ᵈ
        (programmedPrior >>= programmedExtension)
      calc
        (actualPrior >>= actualExtension) =ᵈ
            (programmedPrior >>= actualExtension) := by
          exact (ih value cache (by omega) habsent).bind_left _
        _ =ᵈ (programmedPrior >>= programmedExtension) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro prior hprior
          have hpriorActual : prior ∈ support actualPrior :=
            (OracleComp.support_eq_of_evalDistEq
              (ih value cache (by omega) habsent)).symm.subset hprior
          have hfresh : prior.2
              (Concrete.CacheView.keyChainInput parameter key chain
                ⟨position + steps, hvalid⟩ prior.1.back) = none := by
            apply Concrete.CacheReplay.cache_none_of_zero_query_bound
              (Concrete.chainTrajectory parameter key chain position steps value)
              (Concrete.CacheView.keyChainInput parameter key chain
                ⟨position + steps, hvalid⟩ prior.1.back)
              cache prior.2 prior.1
            · apply OracleComp.IsQueryBoundP.of_imp
                (p' := AtHashAddress parameter
                  (key.chainDomain chain ⟨position + steps, hvalid⟩))
              · intro input heq
                subst input
                exact (atHashAddress_tweakableHashInput_iff
                  parameter _ _ _).2 rfl
              · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
                intro offset hoffset hoffsetValid heq
                have hstep := (ChainKey.chainDomain_injective heq).2.2
                simp only [Fin.mk.injEq] at hstep
                omega
            · apply habsent ⟨position + steps, hvalid⟩
              exact (atHashAddress_tweakableHashInput_iff
                parameter _ _ _).2 rfl
            · exact hpriorActual
          simpa [actualExtension, programmedExtension, simulateQ_bind,
            StateT.run_bind, simulateQ_pure, StateT.run_pure] using
            (evalDist_chainExtension_eq_programmed parameter key chain
              ⟨position + steps, hvalid⟩ prior.1 prior.2 hfresh)

noncomputable def programmedFixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List ChainKey →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, key :: keys => do
      let first ← programmedChainTrajectory parameter key chain 0 steps
        (start key chain) cache
      let rest ← programmedFixedSeedChainTrajectoriesFromCache parameter start
        chain steps first.2 keys
      pure (first.1 :: rest.1, rest.2)

theorem programmedFixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (key : ChainKey) (keys : List ChainKey) :
    programmedFixedSeedChainTrajectoriesFromCache parameter start chain steps
      cache (key :: keys) = (do
        let first ← programmedChainTrajectory parameter key chain 0 steps
          (start key chain) cache
        let rest ← programmedFixedSeedChainTrajectoriesFromCache parameter start
          chain steps first.2 keys
        pure (first.1 :: rest.1, rest.2)) := rfl

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_fixedSeedChainTrajectories_eq_programmed
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    ∀ (keys : List ChainKey) (cache : QueryCache HashSpec),
      keys.Nodup →
      (∀ key ∈ keys, ∀ step : ChainStep, ∀ input,
        AtHashAddress parameter (key.chainDomain chain step) input →
          cache input = none) →
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter start
        chain steps cache keys) =ᵈ
      (programmedFixedSeedChainTrajectoriesFromCache parameter start
        chain steps cache keys) := by
  intro keys
  induction keys with
  | nil =>
      intro cache _hnodup _habsent
      rfl
  | cons key keys ih =>
      intro cache hnodup habsent
      have hnotMem : key ∉ keys := (List.nodup_cons.mp hnodup).1
      have htailNodup : keys.Nodup := (List.nodup_cons.mp hnodup).2
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        programmedFixedSeedChainTrajectoriesFromCache_cons]
      let actualFirst := (simulateQ randomOracle
        (Concrete.chainTrajectory parameter key chain 0 steps
          (start key chain))).run cache
      let programmedFirst := programmedChainTrajectory parameter key chain 0
        steps (start key chain) cache
      let actualRest := fun first :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain
          steps first.2 keys >>= fun rest =>
        pure (first.1 :: rest.1, rest.2)
      let programmedRest := fun first :
          Vector Digest (steps + 1) × QueryCache HashSpec =>
        programmedFixedSeedChainTrajectoriesFromCache parameter start chain
          steps first.2 keys >>= fun rest =>
        pure (first.1 :: rest.1, rest.2)
      change (actualFirst >>= actualRest) =ᵈ
        (programmedFirst >>= programmedRest)
      have hfirst : (actualFirst) =ᵈ (programmedFirst) := by
        apply evalDist_chainTrajectory_eq_programmed parameter key chain 0
          steps (start key chain) cache
        · simpa using hsteps
        · intro step input haddress
          exact habsent key (by simp) step input haddress
      calc
        (actualFirst >>= actualRest) =ᵈ
            (programmedFirst >>= actualRest) := by
          exact hfirst.bind_left _
        _ =ᵈ (programmedFirst >>= programmedRest) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro first hfirstProgrammed
          have hfirstActual : first ∈ support actualFirst :=
            (OracleComp.support_eq_of_evalDistEq hfirst).symm.subset hfirstProgrammed
          have htailAbsent : ∀ later ∈ keys, ∀ step : ChainStep, ∀ input,
              AtHashAddress parameter (later.chainDomain chain step) input →
                first.2 input = none := by
            intro later hlater step input haddress
            apply Concrete.CacheReplay.cache_none_of_zero_query_bound
              (Concrete.chainTrajectory parameter key chain 0 steps
                (start key chain)) input cache first.2 first.1
            · apply OracleComp.IsQueryBoundP.of_imp
                (p' := AtHashAddress parameter (later.chainDomain chain step))
              · intro candidate heq
                subst candidate
                exact haddress
              · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
                intro offset hoffset hoffsetValid heq
                exact hnotMem ((ChainKey.chainDomain_injective heq).1 ▸ hlater)
            · exact habsent later (by simp [hlater]) step input haddress
            · exact hfirstActual
          have hrest := ih first.2 htailNodup htailAbsent
          simp only [actualRest, programmedRest]
          exact hrest.bind_left _

end XmssSecurity

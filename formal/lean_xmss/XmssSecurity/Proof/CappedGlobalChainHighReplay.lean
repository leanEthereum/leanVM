import XmssSecurity.Proof.CappedGlobalChainHighLocalCoupling
import XmssSecurity.Proof.ObservedTraceMonitor

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalFilteredCausalAttackerHashPlan_eq_leafProbeThenFresh
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput secretKey.parameter leafIndex
      endpoints)
    (hcache : state.cache input = none)
    (hprobe : globalHiddenLeafProbe? state leafIndex endpoints =
      some (index, target)) :
    globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target := by
  subst input
  rw [globalFilteredCausalAttackerHashPlan, hcache,
    globalChainInputProbe?_keyLeafInput]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, globalLeafInputData?_leafInput]
  simp only
  rw [hprobe]

theorem globalFilteredCausalAttackerHashPlan_eq_leafRedirect
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest) (output : HashOutput)
    (hinput : input = Concrete.CacheView.keyLeafInput secretKey.parameter leafIndex
      endpoints)
    (hcache : state.cache input = none)
    (hhidden : globalHiddenLeafProbe? state leafIndex endpoints = none)
    (hmatch : GlobalLeafRevealsMatch state leafIndex endpoints)
    (hkeygen : state.keygenCache
      (keygenKeyLeafTargetInput secretKey state.keygenCache input) = some output) :
    globalFilteredCausalAttackerHashPlan secretKey input state =
      .redirect output := by
  subst input
  rw [globalFilteredCausalAttackerHashPlan, hcache,
    globalChainInputProbe?_keyLeafInput]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, globalLeafInputData?_leafInput]
  simp only
  rw [hhidden, ite_eq_left hmatch, hkeygen]

theorem globalFilteredCausalAttackerHashPlan_eq_leafFresh_of_mismatch
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput secretKey.parameter leafIndex
      endpoints)
    (hcache : state.cache input = none)
    (hhidden : globalHiddenLeafProbe? state leafIndex endpoints = none)
    (hmatch : ¬ GlobalLeafRevealsMatch state leafIndex endpoints) :
    globalFilteredCausalAttackerHashPlan secretKey input state = .fresh := by
  subst input
  rw [globalFilteredCausalAttackerHashPlan, hcache,
    globalChainInputProbe?_keyLeafInput]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, globalLeafInputData?_leafInput]
  simp only
  rw [hhidden, ite_eq_right hmatch]


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalLeaf_not_match_endpoint_miss
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalCausalHashState) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hreveals : GlobalSigningRevealsAgree table state)
    (hhidden : globalHiddenLeafProbe? state leafIndex endpoints = none)
    (hmatch : ¬ GlobalLeafRevealsMatch state leafIndex endpoints) :
    ∃ chain : ChainIndex,
      table (chain, leafIndex, chainEndpointDigit) ≠ endpoints chain := by
  classical
  have hall :=
    (globalHiddenLeafProbe?_eq_none_iff state leafIndex endpoints).mp hhidden
  unfold GlobalLeafRevealsMatch at hmatch
  push Not at hmatch
  obtain ⟨chain, hmismatch⟩ := hmatch
  cases hvalue : state.revealed (chain, leafIndex, chainEndpointDigit) with
  | none => exact (hall chain hvalue).elim
  | some value =>
      refine ⟨chain, ?_⟩
      have htable : table (chain, leafIndex, chainEndpointDigit) = value :=
        hreveals (chain, leafIndex, chainEndpointDigit) value hvalue
      intro heq
      apply hmismatch
      rw [hvalue, ← htable, heq]

theorem programmedGlobal_left_leaf_cache_none_of_hidden_probe_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState) (input : HashInput)
    (leafIndex : ChainKey) (endpoints : ChainIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput
      right.1.1.secretKey.parameter leafIndex endpoints)
    (hprobe : globalHiddenLeafProbe? state leafIndex endpoints =
      some (index, target))
    (hmiss : right.1.2 index ≠ target) :
    left.cache input = none := by
  obtain ⟨chain, hindex, htarget, _hhidden⟩ :=
    globalHiddenLeafProbe?_eq_some state leafIndex endpoints index target hprobe
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  rw [hinput, hparameter]
  apply programmedGlobal_left_leaf_cache_none_of_endpoint_miss left right hrel
    hleftSupport leafIndex endpoints chain
  simpa [hindex, htarget] using hmiss

theorem relTriple_programmed_globalFilteredLeafHashQuery_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput
      right.1.1.secretKey.parameter leafIndex endpoints) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
  cases hcache : rightState.cache input with
  | some output =>
      apply relTriple_post_mono
        (relTriple_programmed_globalFilteredHashQuery_cached left right
          leftCache rightState hstate input output hcache)
      intro _leftResult _rightResult hresult
      exact Or.inl hresult
  | none =>
      cases hprobe : globalHiddenLeafProbe? rightState leafIndex endpoints with
      | some probe =>
          obtain ⟨index, target⟩ := probe
          have hplan :=
            globalFilteredCausalAttackerHashPlan_eq_leafProbeThenFresh
              right.1.1.secretKey rightState input leafIndex endpoints index target
                hinput hcache hprobe
          obtain ⟨_chain, _hindex, _htarget, hhidden⟩ :=
            globalHiddenLeafProbe?_eq_some rightState leafIndex endpoints index
              target hprobe
          exact
            relTriple_programmed_globalFilteredHashQuery_probeThenFresh_until_hit
              left right leftCache rightState hstate monitor hmonitor input index
                target hhidden hplan
                  (programmedGlobal_left_leaf_cache_none_of_hidden_probe_miss
                    left right hrel hleftSupport hrightSupport rightState input
                      leafIndex endpoints index target hinput hprobe)
      | none =>
          by_cases hmatch : GlobalLeafRevealsMatch rightState leafIndex endpoints
          · obtain ⟨output, hleftBase, hrightBase⟩ :=
              programmedGlobal_leaf_cache_pair_of_reveals_match left right hrel
                hleftSupport hrightSupport rightState hstate.2.2.2.1
                  hstate.2.2.2.2 input leafIndex endpoints hinput hmatch
            have hplan :=
              globalFilteredCausalAttackerHashPlan_eq_leafRedirect
                right.1.1.secretKey rightState input leafIndex endpoints output
                  hinput hcache hprobe hmatch hrightBase
            have hparameter := programmedGlobal_secretKey_parameter_eq left
              right hrel hleftSupport hrightSupport
            have hnotSigning : ¬ GlobalSigningComparableHashInput
                left.secretKey.parameter input := by
              rw [hinput, hparameter]
              exact globalLeafInput_not_signingComparable left.secretKey.parameter
                leafIndex endpoints
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_redirect left right
                leftCache rightState hstate input output hleftBase hnotSigning
                  hplan)
            intro _leftResult _rightResult hresult
            exact Or.inl hresult
          · obtain ⟨chain, hmiss⟩ := globalLeaf_not_match_endpoint_miss
              right.1.2 rightState leafIndex endpoints hstate.2.2.2.2 hprobe hmatch
            have hparameter := programmedGlobal_secretKey_parameter_eq left
              right hrel hleftSupport hrightSupport
            have hbaseNone : left.cache input = none := by
              rw [hinput, hparameter]
              exact programmedGlobal_left_leaf_cache_none_of_endpoint_miss left
                right hrel hleftSupport leafIndex endpoints chain hmiss
            have hplan :=
              globalFilteredCausalAttackerHashPlan_eq_leafFresh_of_mismatch
                right.1.1.secretKey rightState input leafIndex endpoints hinput
                  hcache hprobe hmatch
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_fresh left right
                leftCache rightState hstate input hbaseNone hplan)
            intro _leftResult _rightResult hresult
            exact Or.inl hresult


set_option maxRecDepth 10000000
set_option maxHeartbeats 2000000

theorem Concrete.keygen_cache_none_at_global_chainAddress_of_probe_none
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep)
    (haddress : AtHashAddress keyResult.1.2.parameter
      (key.chainDomain chain step) input)
    (hprobe : globalChainInputProbe? keyResult.1.2.parameter input = none) :
    keyResult.2 input = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hmem key chain step
  cases hcached : keyResult.2 input with
  | none => rfl
  | some output =>
      have heq := Concrete.keygen_cache_unique_keyChainAddress keyResult hmem key chain
          step input _ output honestOutput haddress
          (Concrete.CacheView.keyChainInput_atHashAddress _ _ _ _ _) hcached hhonest
      rw [heq, globalChainInputProbe?_keyChainInput] at hprobe
      contradiction

theorem Concrete.keygen_cache_none_at_global_leafAddress_of_probe_none
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput) (key : ChainKey)
    (haddress : AtHashAddress keyResult.1.2.parameter key.leafDomain input)
    (hprobe : globalLeafInputData? keyResult.1.2.parameter input = none) :
    keyResult.2 input = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_keyLeafInput keyResult hmem key
  cases hcached : keyResult.2 input with
  | none => rfl
  | some output =>
      have heq := Concrete.keygen_cache_unique_keyLeafAddress keyResult hmem key input _
          output honestOutput haddress
          ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl) hcached hhonest
      rw [heq] at hprobe
      have hdata := globalLeafInputData?_leafInput keyResult.1.2.parameter key
        (Concrete.CacheReplay.keyOneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.keyChainStart key)
      exact absurd (hprobe.symm.trans hdata) (by simp)

theorem Concrete.keygen_cache_none_of_global_probes_none_not_merkle
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (input : HashInput)
    (hchain : globalChainInputProbe? keyResult.1.2.parameter input = none)
    (hleaf : globalLeafInputData? keyResult.1.2.parameter input = none)
    (hmerkle : ¬ MerkleHashInput keyResult.1.2.parameter input) :
    keyResult.2 input = none := by
  by_cases haddressed : KeygenAddressedHashInput
      keyResult.1.2.parameter input
  · obtain ⟨domain, hdomain⟩ := haddressed
    cases domain with
    | chain leafIndex chain step =>
        exact Concrete.keygen_cache_none_at_global_chainAddress_of_probe_none
          keyResult hmem input (.inl leafIndex) chain step hdomain hchain
    | topChain key chain step =>
        exact Concrete.keygen_cache_none_at_global_chainAddress_of_probe_none
          keyResult hmem input (.inr key) chain step hdomain hchain
    | leaf leafIndex =>
        exact Concrete.keygen_cache_none_at_global_leafAddress_of_probe_none
          keyResult hmem input (.inl leafIndex) hdomain hleaf
    | topLeaf key =>
        exact Concrete.keygen_cache_none_at_global_leafAddress_of_probe_none
          keyResult hmem input (.inr key) hdomain hleaf
    | merkle level node => exact (hmerkle ⟨.merkle level node, trivial, hdomain⟩).elim
    | topMerkle level node => exact (hmerkle ⟨.topMerkle level node, trivial, hdomain⟩).elim
    | topEncoding key => exact (hmerkle ⟨.topEncoding key, trivial, hdomain⟩).elim
    | encoding leafIndex =>
        exact Concrete.keygen_cache_none_at_encodingAddress keyResult hmem
          leafIndex input hdomain
  · exact Concrete.keygen_cache_none_unaddressed keyResult hmem input
      haddressed

theorem globalFilteredCausalAttackerHashPlan_eq_ordinaryFresh
    (secretKey : SecretKey) (state : GlobalCausalHashState)
    (input : HashInput)
    (hcache : state.cache input = none)
    (hchain : globalChainInputProbe? secretKey.parameter input = none)
    (hleaf : globalLeafInputData? secretKey.parameter input = none) :
    globalFilteredCausalAttackerHashPlan secretKey input state = .fresh := by
  rw [globalFilteredCausalAttackerHashPlan, hcache, hchain]
  simp only [globalFilteredCausalUncachedAttackerHashPlan]
  rw [globalFilteredCausalLeafHashPlan, hleaf]

theorem relTriple_programmed_globalFilteredOrdinaryHashQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput)
    (hcache : rightState.cache input = none)
    (hchain : globalChainInputProbe? right.1.1.secretKey.parameter input = none)
    (hleaf : globalLeafInputData? right.1.1.secretKey.parameter input = none)
    (hbaseNone : left.cache input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  apply relTriple_programmed_globalFilteredHashQuery_fresh left right leftCache
    rightState hstate input hbaseNone
  exact globalFilteredCausalAttackerHashPlan_eq_ordinaryFresh
    right.1.1.secretKey rightState input hcache hchain hleaf


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def GlobalMerkleKeygenCacheRetained
    (secretKey : SecretKey) (state : GlobalCausalHashState) : Prop :=
  ∀ input, MerkleHashInput secretKey.parameter input →
    ∀ output, state.keygenCache input = some output →
      state.cache input = some output

theorem globalFilteredCausalKeygenState_merkleRetained
    (view : ProgrammedGlobalChainKeygenView) :
    GlobalMerkleKeygenCacheRetained view.secretKey
      (globalFilteredCausalKeygenState view) := by
  intro input hmerkle output hkeygen
  simpa [globalFilteredCausalKeygenState, hmerkle] using hkeygen

theorem programmedGlobal_left_cache_none_of_retained_merkle_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState)
    (hkeygen : state.keygenCache = right.1.1.cache)
    (hretained : GlobalMerkleKeygenCacheRetained right.1.1.secretKey state)
    (input : HashInput)
    (hmerkle : MerkleHashInput right.1.1.secretKey.parameter input)
    (hcache : state.cache input = none) :
    left.cache input = none := by
  have hrightBase : right.1.1.cache input = none := by
    cases hbase : right.1.1.cache input with
    | none => rfl
    | some output =>
        have hcurrent := hretained input hmerkle output (by
          rw [hkeygen]
          exact hbase)
        rw [hcache] at hcurrent
        contradiction
  have hparameter := programmedGlobal_secretKey_parameter_eq left right hrel
    hleftSupport hrightSupport
  have hmerkleLeft : MerkleHashInput left.secretKey.parameter input := by
    rw [← hparameter]
    exact hmerkle
  obtain ⟨leftEndpoints, rightEndpoints, htree, _hleftReplay,
    _hrightReplay⟩ := hrel.1.2.2.2.2.2
  rw [htree.merkle input hmerkleLeft, hrightBase]

theorem relTriple_programmed_globalFilteredAttackerHashQuery_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (hretained : GlobalMerkleKeygenCacheRetained right.1.1.secretKey
      rightState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
  cases hcache : rightState.cache input with
  | some output =>
      apply relTriple_post_mono
        (relTriple_programmed_globalFilteredHashQuery_cached left right
          leftCache rightState hstate input output hcache)
      intro _leftResult _rightResult hresult
      exact Or.inl hresult
  | none =>
      have hparameter := programmedGlobal_secretKey_parameter_eq left right
        hrel hleftSupport hrightSupport
      cases hchain : globalChainInputProbe? right.1.1.secretKey.parameter input with
      | some probe =>
          obtain ⟨index, target⟩ := probe
          have hchainLeft : globalChainInputProbe? left.secretKey.parameter
              input = some (index, target) := by
            rw [← hparameter]
            exact hchain
          exact relTriple_programmed_globalFilteredChainHashQuery_until_hit
            left right hrel hleftSupport hrightSupport leftCache rightState
              hstate monitor hmonitor input index target hchainLeft
      | none =>
          cases hleaf : globalLeafInputData?
              right.1.1.secretKey.parameter input with
          | some data =>
              have hinput :=
                (globalLeafInputData?_eq_some_iff
                  right.1.1.secretKey.parameter input data).mp hleaf
              exact relTriple_programmed_globalFilteredLeafHashQuery_until_hit
                left right hrel hleftSupport hrightSupport leftCache rightState
                  hstate monitor hmonitor input data.leafIndex data.endpoints hinput
          | none =>
              have hbaseNone : left.cache input = none := by
                by_cases hmerkle : MerkleHashInput
                    right.1.1.secretKey.parameter input
                · exact programmedGlobal_left_cache_none_of_retained_merkle_miss
                    left right hrel hleftSupport hrightSupport rightState
                      hstate.2.2.2.1 hretained input hmerkle hcache
                · apply Concrete.keygen_cache_none_of_global_probes_none_not_merkle
                    left.keyResult
                    (trajectoryProgrammedGlobalChainKeygen_support_keyResult
                      left hleftSupport) input
                  · change globalChainInputProbe? left.secretKey.parameter
                      input = none
                    rw [← hparameter]
                    exact hchain
                  · change globalLeafInputData? left.secretKey.parameter
                      input = none
                    rw [← hparameter]
                    exact hleaf
                  · change ¬ MerkleHashInput left.secretKey.parameter input
                    rw [← hparameter]
                    exact hmerkle
              apply relTriple_post_mono
                (relTriple_programmed_globalFilteredOrdinaryHashQuery left right
                  leftCache rightState hstate input hcache hchain hleaf
                    hbaseNone)
              intro _leftResult _rightResult hresult
              exact Or.inl hresult


set_option maxRecDepth 10000000
set_option maxHeartbeats 2000000

theorem GlobalMerkleKeygenCacheRetained.recordedState
    {secretKey : SecretKey} {state : GlobalCausalHashState}
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (input : HashInput) :
    GlobalMerkleKeygenCacheRetained secretKey
      (globalCausalRecordedState secretKey input state) := by
  intro candidate hmerkle output hkeygen
  rw [globalCausalRecordedState_keygenCache] at hkeygen
  rw [globalCausalRecordedState_cache]
  exact hretained candidate hmerkle output hkeygen

theorem GlobalMerkleKeygenCacheRetained.cacheQuery_of_none
    {secretKey : SecretKey} {state : GlobalCausalHashState}
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (input : HashInput) (output : HashOutput)
    (hcache : state.cache input = none) :
    GlobalMerkleKeygenCacheRetained secretKey
      { state with cache := state.cache.cacheQuery input output } := by
  intro candidate hmerkle candidateOutput hkeygen
  change state.keygenCache candidate = some candidateOutput at hkeygen
  change state.cache.cacheQuery input output candidate = some candidateOutput
  by_cases heq : candidate = input
  · subst candidate
    have hcurrent := hretained input hmerkle candidateOutput hkeygen
    rw [hcache] at hcurrent
    contradiction
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    exact hretained candidate hmerkle candidateOutput hkeygen

theorem simulate_eagerTrace_globalCausalHashQuery_merkleRetained_of_cache_none
    (table : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (hcache : state.cache input = none)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalHashQuery input).run state)).run)) :
    GlobalMerkleKeygenCacheRetained secretKey result.1.2 := by
  rw [simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨raw, hraw, rfl⟩ := hresult
  rw [randomOracle, QueryImpl.withCaching_run_none _ hcache, support_map] at hraw
  obtain ⟨output, _houtput, rfl⟩ := hraw
  exact hretained.cacheQuery_of_none input output hcache

theorem globalFilteredCausalUncachedAttackerHashPlan_ne_cached
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest))
    (output : HashOutput) :
    globalFilteredCausalUncachedAttackerHashPlan secretKey input state probe ≠
      .cached output := by
  intro hplan
  unfold globalFilteredCausalUncachedAttackerHashPlan at hplan
  split at hplan
  · split at hplan
    · split at hplan
      · split at hplan <;> contradiction
      · contradiction
    · split at hplan <;> contradiction
  · unfold globalFilteredCausalLeafHashPlan at hplan
    split at hplan
    · contradiction
    · split at hplan
      · contradiction
      · split at hplan
        · split at hplan <;> contradiction
        · contradiction

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_merkleRetained
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hretained : GlobalMerkleKeygenCacheRetained secretKey state)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    GlobalMerkleKeygenCacheRetained secretKey result.1.2 := by
  cases hcache : state.cache input with
  | some cachedOutput =>
      have hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
          .cached cachedOutput := by
        simp [globalFilteredCausalAttackerHashPlan, hcache]
      rw [globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact hretained.recordedState input
  | none =>
      generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input
        state = plan
      cases plan with
      | cached output =>
          have huncached : globalFilteredCausalUncachedAttackerHashPlan
              secretKey input state
                (globalChainInputProbe? secretKey.parameter input) =
              .cached output := by
            rw [globalFilteredCausalAttackerHashPlan, hcache] at hplan
            exact hplan
          exact (globalFilteredCausalUncachedAttackerHashPlan_ne_cached
            secretKey input state
              (globalChainInputProbe? secretKey.parameter input) output
                huncached).elim
      | redirect output =>
          rw [globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
            WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simpa [globalFilteredCausalRedirectResultState] using
            (hretained.recordedState input).cacheQuery_of_none input output
              (by simpa using hcache)
      | probeThenFresh index target =>
          rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
            table high secretKey input state index target hplan, support_map]
              at hresult
          obtain ⟨raw, hraw, rfl⟩ := hresult
          rw [randomOracle, QueryImpl.withCaching_run_none _ hcache,
            support_map] at hraw
          obtain ⟨output, _houtput, rfl⟩ := hraw
          simpa [GlobalCausalHashState.setCache] using
            (hretained.recordedState input).cacheQuery_of_none input output
              (by simpa using hcache)
      | fresh =>
          rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
          exact simulate_eagerTrace_globalCausalHashQuery_merkleRetained_of_cache_none
            table secretKey input (globalCausalRecordedState secretKey input state)
              (hretained.recordedState input) (by simpa using hcache) result
                hresult
      | reveal index =>
          rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
            simulate_eagerTrace_globalCausalRevealHashQueryFromHigh,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          simpa [GlobalMerkleKeygenCacheRetained,
            globalFilteredCausalRevealResultState] using
            hretained.cacheQuery_of_none input
              (Rom.hashOutputEquivDigestPair.symm (high index, table index))
                hcache


def GlobalCausalSigningStateExtends
    (initial final : GlobalCausalHashState) : Prop :=
  initial.cache ≤ final.cache ∧ final.keygenCache = initial.keygenCache

theorem GlobalCausalSigningStateExtends.trans
    {first second third : GlobalCausalHashState}
    (hfirst : GlobalCausalSigningStateExtends first second)
    (hsecond : GlobalCausalSigningStateExtends second third) :
    GlobalCausalSigningStateExtends first third :=
  ⟨hfirst.1.trans hsecond.1, hsecond.2.trans hfirst.2⟩

theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_stateExtends
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request randomness state)).run)) :
    GlobalCausalSigningStateExtends state result.1.2 := by
  unfold globalFilteredCausalSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨encodedTrace, hencodedTrace, hresult⟩ := hresult
  rw [support_map] at hencodedTrace
  obtain ⟨encoded, hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  have hcacheLe : state.cache ≤ encoded.2 :=
    Concrete.CacheReplay.randomOracle_cache_le
      (Concrete.encodingHash keyView.secretKey.parameter request.leafIndex
        request.message randomness) state.cache encoded hencoded
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ⟨hcacheLe, rfl⟩
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignature] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      simp only [Prod.map, id_eq]
      constructor
      · rw [globalSignatureFullRevealResult_cache]
        exact hcacheLe
      · rw [globalSignatureFullRevealResult_keygenCache]

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
    (attempts trial : Nat) (base : Randomness) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts keyView request base attempts trial
          state)).run)) :
    GlobalCausalSigningStateExtends state result.1.2 := by
  induction attempts generalizing trial state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, rfl⟩
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hresult⟩ := hresult
      have hattemptExtends :=
        simulate_eagerTrace_globalFilteredCausalSigningAttempt_stateExtends
          table keyView request _ state attemptResult hattempt
      cases hoption : attemptResult.1.1 with
      | some signature =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hattemptExtends
      | none =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_map] at hresult
          obtain ⟨rest, hrest, rfl⟩ := hresult
          exact hattemptExtends.trans
            (ih (trial + 1) attemptResult.1.2 rest hrest)

theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalCausalSigningStateExtends state result.1.2 := by
  obtain ⟨base, attemptResult, hattempt, rfl⟩ :=
    mem_support_globalFilteredCausalSigningQuery hresult
  exact simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_stateExtends
    signingAttemptLimit 0 base table keyView request state attemptResult hattempt

theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_merkleRetained
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (hretained : GlobalMerkleKeygenCacheRetained keyView.secretKey state)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    GlobalMerkleKeygenCacheRetained keyView.secretKey result.1.2 := by
  have hextends :=
    simulate_eagerTrace_globalFilteredCausalSigningQuery_stateExtends
      table keyView request state result hresult
  intro input hmerkle output hkeygen
  rw [hextends.2] at hkeygen
  exact hextends.1 (hretained input hmerkle output hkeygen)


set_option maxRecDepth 1000000

structure GlobalMonitoredCausalState where
  causal : GlobalCausalHashState
  trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex

def GlobalMonitoredCausalState.observed
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState) :
    Option (AdaptiveRevealMonitor.State GlobalChainValueIndex) :=
  RevealProbeOracleSimulation.advanceObserved table
    AdaptiveRevealMonitor.State.empty state.trace

def GlobalMonitoredCausalState.bad
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState) : Prop :=
  state.observed table = none

def globalMonitoredCausalResult
    (initial : GlobalMonitoredCausalState)
    (result : (α × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    α × GlobalMonitoredCausalState :=
  (result.1.1, {
    causal := result.1.2
    trace := initial.trace ++ result.2
  })

theorem GlobalMonitoredCausalState.bad_implies_runObserved
    (table : GlobalChainValueIndex → Digest)
    (state : GlobalMonitoredCausalState)
    (hbad : state.bad table) :
    RevealProbeOracleSimulation.runObserved table
      AdaptiveRevealMonitor.State.empty state.trace = true := by
  apply (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
    table AdaptiveRevealMonitor.State.empty state.trace).1
  exact hbad

noncomputable def monitorGlobalCausalTrace
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)) :
    StateT GlobalMonitoredCausalState ProbComp α := fun state =>
  globalMonitoredCausalResult state <$> computation state.causal

theorem monitorGlobalCausalTrace_run
    (computation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (state : GlobalMonitoredCausalState) :
    (monitorGlobalCausalTrace computation).run state =
      globalMonitoredCausalResult state <$> computation state.causal :=
  rfl

def GlobalMonitoredFilteredStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState) : Prop :=
  ∃ monitor, rightState.observed right.2 = some monitor ∧
    RevealProbeOracleSimulation.StateAgrees right.2 monitor ∧
    monitor.revealed = rightState.causal.revealed ∧
    GlobalFilteredCausalStateRelation left right leftCache
      rightState.causal ∧
    GlobalMerkleKeygenCacheRetained right.1.secretKey rightState.causal

theorem globalMonitoredFilteredStateRelation_initial
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right leftCache
      rightState)
    (hretained : GlobalMerkleKeygenCacheRetained right.1.secretKey
      rightState)
    (hhidden : ∀ index, rightState.revealed index = none) :
    GlobalMonitoredFilteredStateRelation left right leftCache
      ⟨rightState, []⟩ := by
  have hnoHit : ¬ ∃ index, right.2 index ∈
      (AdaptiveRevealMonitor.State.empty :
        AdaptiveRevealMonitor.State GlobalChainValueIndex).pending index := by
    simp [AdaptiveRevealMonitor.State.empty]
  refine ⟨AdaptiveRevealMonitor.State.empty, ?_,
    RevealProbeOracleSimulation.stateAgrees_empty right.2, ?_, hstate,
      hretained⟩
  · simp [GlobalMonitoredCausalState.observed,
      RevealProbeOracleSimulation.advanceObserved,
      RevealProbeOracleSimulation.tableHits, hnoHit]
  funext index
  simp [AdaptiveRevealMonitor.State.empty, hhidden index]

theorem globalFilteredCausalRevealResultState_transition
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput) :
    CausalRevealTransition state.revealed index value
      (globalFilteredCausalRevealResultState secretKey input state index value
        output).revealed := by
  constructor
  · simp [globalFilteredCausalRevealResultState]
  · intro candidate hne
    simp [globalFilteredCausalRevealResultState,
      Function.update_of_ne hne]

theorem relTriple_monitorGlobalCausalTrace_of_filtered_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftComputation : ProbComp (α × QueryCache HashSpec))
    (rightComputation : GlobalCausalHashState → ProbComp
      ((α × GlobalCausalHashState) ×
        RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
    (rightState : GlobalMonitoredCausalState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : rightState.observed right.2 = some monitor)
    (hmonitorAgrees : RevealProbeOracleSimulation.StateAgrees right.2 monitor)
    (hrevealed : monitor.revealed = rightState.causal.revealed)
    (hcouple : RelTriple leftComputation
      (rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          GlobalFilteredCausalStateRelation left right leftResult.2
            rightResult.1.2) ∨
          RevealProbeOracleSimulation.runObserved right.2 monitor
            rightResult.2 = true))
    (htrace : ∀ result ∈ support (rightComputation rightState.causal),
      RevealProbeOracleSimulation.TraceAgrees right.2 result.2 ∧
        ReplaysCausalReveals rightState.causal.revealed result.2
          result.1.2.revealed)
    (hretainedStep : ∀ result ∈ support
      (rightComputation rightState.causal),
      GlobalMerkleKeygenCacheRetained right.1.secretKey result.1.2) :
    RelTriple leftComputation
      ((monitorGlobalCausalTrace rightComputation).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad right.2) := by
  rw [monitorGlobalCausalTrace_run]
  change RevealProbeOracleSimulation.advanceObserved right.2
    AdaptiveRevealMonitor.State.empty rightState.trace = some monitor
      at hmonitor
  have hmapped : RelTriple (id <$> leftComputation)
      (globalMonitoredCausalResult rightState <$>
        rightComputation rightState.causal)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right leftResult.2
            rightResult.2) ∨
          rightResult.2.bad right.2) :=
    relTriple_map (f := id)
      (g := globalMonitoredCausalResult rightState)
      (relTriple_post_mono (relTriple_with_support hcouple)
      (fun leftResult rightResult hresult => by
        have htraceResult := htrace rightResult hresult.2.2
        have hretainedResult := hretainedStep rightResult hresult.2.2
        rcases hresult.1 with hexact | hhit
        · cases hadvance : RevealProbeOracleSimulation.advanceObserved right.2
              monitor rightResult.2 with
          | none =>
              right
              change RevealProbeOracleSimulation.advanceObserved right.2
                AdaptiveRevealMonitor.State.empty
                  (rightState.trace ++ rightResult.2) = none
              rw [RevealProbeOracleSimulation.advanceObserved_append,
                hmonitor]
              exact hadvance
          | some finalMonitor =>
              left
              refine ⟨hexact.1, finalMonitor, ?_, ?_, ?_, hexact.2,
                hretainedResult⟩
              · change RevealProbeOracleSimulation.advanceObserved right.2
                    AdaptiveRevealMonitor.State.empty
                      (rightState.trace ++ rightResult.2) = some finalMonitor
                rw [RevealProbeOracleSimulation.advanceObserved_append,
                  hmonitor]
                exact hadvance
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_stateAgrees
                  right.2 monitor finalMonitor rightResult.2 hadvance
                    hmonitorAgrees
              · exact RevealProbeOracleSimulation.advanceObserved_preserves_replayed_reveals
                  right.2 monitor finalMonitor rightState.causal.revealed
                    rightResult.1.2.revealed rightResult.2 hadvance
                      hmonitorAgrees hrevealed htraceResult.1 htraceResult.2
        · right
          change RevealProbeOracleSimulation.advanceObserved right.2
            AdaptiveRevealMonitor.State.empty
              (rightState.trace ++ rightResult.2) = none
          rw [RevealProbeOracleSimulation.advanceObserved_append, hmonitor]
          exact (RevealProbeOracleSimulation.advanceObserved_eq_none_iff_runObserved_eq_true
            right.2 monitor rightResult.2).2 hhit))
  simpa only [id_map] using hmapped


theorem globalCausalAttackerHashQueryFromHigh_cached_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (output : HashOutput)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .cached output)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
  simp only [simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hresult
  subst result
  simpa [globalCausalRecordedState_revealed] using
    ReplaysCausalReveals.nil state.revealed

theorem globalCausalAttackerHashQueryFromHigh_redirect_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (output : HashOutput)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .redirect output)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan] at hresult
  simp only [simulateQ_pure, WriterT.run_pure', support_pure,
    Set.mem_singleton_iff] at hresult
  subst result
  simpa using ReplaysCausalReveals.nil state.revealed

theorem globalCausalAttackerHashQueryFromHigh_fresh_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .fresh)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalHashQuery, support_map] at hresult
  obtain ⟨sample, _hsample, rfl⟩ := hresult
  rw [GlobalCausalHashState.setCache_revealed,
    globalCausalRecordedState_revealed]
  exact ReplaysCausalReveals.nil state.revealed

theorem globalCausalAttackerHashQueryFromHigh_reveal_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .reveal index)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalRevealHashQueryFromHigh] at hresult
  simp only [support_pure, Set.mem_singleton_iff] at hresult
  subst result
  apply ReplaysCausalReveals.reveal state.revealed _ index (table index) []
    (globalFilteredCausalRevealResultState secretKey input state index
      (table index) (Rom.hashOutputEquivDigestPair.symm
        (high index, table index))).revealed
  · exact globalFilteredCausalRevealResultState_transition secretKey input state
      index (table index) _
  · exact ReplaysCausalReveals.nil _

theorem globalCausalAttackerHashQueryFromHigh_probeThenFresh_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (target : Digest)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
    table high secretKey input state index target hplan, support_map] at hresult
  obtain ⟨sample, _hsample, rfl⟩ := hresult
  apply ReplaysCausalReveals.probe state.revealed _ index target []
  rw [GlobalCausalHashState.setCache_revealed,
    globalCausalRecordedState_revealed]
  exact ReplaysCausalReveals.nil state.revealed

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_replays
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState)
    (result : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  generalize hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
    plan
  cases plan with
  | cached output =>
      exact globalCausalAttackerHashQueryFromHigh_cached_replays table high
        secretKey input state output hplan result hresult
  | redirect output =>
      exact globalCausalAttackerHashQueryFromHigh_redirect_replays table high
        secretKey input state output hplan result hresult
  | fresh =>
      exact globalCausalAttackerHashQueryFromHigh_fresh_replays table high
        secretKey input state hplan result hresult
  | reveal index =>
      exact globalCausalAttackerHashQueryFromHigh_reveal_replays table high
        secretKey input state index hplan result hresult
  | probeThenFresh index target =>
      exact globalCausalAttackerHashQueryFromHigh_probeThenFresh_replays table
        high secretKey input state index target hplan result hresult

theorem relTriple_programmed_monitoredGlobalAttackerHashQuery_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2)
              right.1.1.secretKey input).run causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.1.2) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right.1
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · exact relTriple_programmed_globalFilteredAttackerHashQuery_until_hit left
      right hrel hleftSupport hrightSupport leftCache rightState.causal
        hcausal hretained monitor hrevealed input
  · intro result hresult
    constructor
    · exact RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.1.2 _ result hresult
    · exact
        simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_support_replays
          right.1.2 (globalChainValueHighTableOfEdges right.2)
            right.1.1.secretKey input rightState.causal result hresult
  · intro result hresult
    exact simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_merkleRetained
      right.1.2 (globalChainValueHighTableOfEdges right.2)
        right.1.1.secretKey input rightState.causal hretained result hresult


theorem GlobalCausalHashState.recordReveal_transition
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) :
    CausalRevealTransition state.revealed index value
      (state.recordReveal index value).revealed := by
  constructor
  · simp [GlobalCausalHashState.recordReveal]
  · intro candidate hne
    simp [GlobalCausalHashState.recordReveal, Function.update_of_ne hne]

theorem globalSignatureRevealResult_replays
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    ReplaysCausalReveals state.revealed
      (globalSignatureRevealTrace table request encoding chains)
      (globalSignatureRevealResult table request encoding chains signature
        state).2.revealed := by
  induction chains generalizing signature state with
  | nil => exact ReplaysCausalReveals.nil state.revealed
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, .inl request.leafIndex, encoding chain)
      rw [globalSignatureRevealTrace, globalSignatureRevealResult]
      apply ReplaysCausalReveals.reveal state.revealed _ index (table index) _
        (state.recordReveal index (table index)).revealed
      · exact state.recordReveal_transition index (table index)
      · exact ih _ _

theorem globalSignatureTopRevealResult_replays
    (table : GlobalChainValueIndex → Digest)
    (request : SignRequest) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature)
    (state : GlobalCausalHashState) :
    ReplaysCausalReveals state.revealed
      (globalSignatureTopRevealTrace table request encoding chains)
      (globalSignatureTopRevealResult table request encoding chains signature
        state).2.revealed := by
  induction chains generalizing signature state with
  | nil => exact ReplaysCausalReveals.nil state.revealed
  | cons chain chains ih =>
      let index : GlobalChainValueIndex :=
        (chain, .inr (topKeyOf request.leafIndex), encoding chain)
      rw [globalSignatureTopRevealTrace, globalSignatureTopRevealResult]
      apply ReplaysCausalReveals.reveal state.revealed _ index (table index) _
        (state.recordReveal index (table index)).revealed
      · exact state.recordReveal_transition index (table index)
      · exact ih _ _

theorem globalSignatureFullRevealResult_replays
    (table : GlobalChainValueIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) :
    ReplaysCausalReveals state.revealed
      (globalSignatureFullRevealTrace table topSigned request encoding)
      (globalSignatureFullRevealResult table topSigned request encoding signature
        state).2.revealed := by
  unfold globalSignatureFullRevealTrace globalSignatureFullRevealResult
  cases topSigned (topKeyOf request.leafIndex) with
  | none => exact ReplaysCausalReveals.nil state.revealed
  | some signed =>
      exact (globalSignatureRevealResult_replays table request encoding allChains signature
        state).append (globalSignatureTopRevealResult_replays table request signed.2 allChains _ _)

theorem simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_replays
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request randomness state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  unfold globalFilteredCausalSigningAttempt at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨encodedTrace, hencodedTrace, hresult⟩ := hresult
  rw [support_map] at hencodedTrace
  obtain ⟨encoded, _hencoded, rfl⟩ := hencodedTrace
  simp only [List.nil_append] at hresult
  cases hdecode : TargetSum.decodeDigest encoded.1 with
  | none =>
      simp only [hdecode, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      exact ReplaysCausalReveals.nil state.revealed
  | some encoding =>
      rw [hdecode, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignature] at hresult
      simp only [pure_bind, simulateQ_pure, WriterT.run_pure] at hresult
      subst result
      simpa using globalSignatureFullRevealResult_replays table keyView.secretKey.topSigned
        request encoding
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.leafIndex randomness encoding)
        ({ state with cache := encoded.2 } : GlobalCausalHashState)

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_replays
    (attempts trial : Nat) (base : Randomness) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts keyView request base attempts trial
          state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  induction attempts generalizing trial state result with
  | zero =>
      simp only [globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        WriterT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ReplaysCausalReveals.nil state.revealed
  | succ attempts ih =>
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ,
        mem_support_bind_iff] at hresult
      obtain ⟨attemptResult, hattempt, hresult⟩ := hresult
      have hattemptReplay :=
        simulate_eagerTrace_globalFilteredCausalSigningAttempt_support_replays
          table keyView request _ state attemptResult hattempt
      cases hoption : attemptResult.1.1 with
      | some signature =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_pure, Set.mem_singleton_iff] at hresult
          subst result
          exact hattemptReplay
      | none =>
          simp only [globalFilteredCausalSignTraceContinuation, hoption,
            support_map] at hresult
          obtain ⟨rest, hrest, rfl⟩ := hresult
          exact hattemptReplay.append (ih (trial + 1) attemptResult.1.2 rest hrest)

theorem simulate_eagerTrace_globalFilteredCausalSigningQuery_support_replays
    (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    ReplaysCausalReveals state.revealed result.2 result.1.2.revealed := by
  obtain ⟨base, attemptResult, hattempt, rfl⟩ :=
    mem_support_globalFilteredCausalSigningQuery hresult
  exact
    simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_support_replays
      signingAttemptLimit 0 base table keyView request state attemptResult hattempt

theorem relTriple_programmed_monitoredGlobalSigningQuery
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalMonitoredCausalState)
    (hstate : GlobalMonitoredFilteredStateRelation left right.1 leftCache
      rightState)
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.scheme.sign
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.leafIndex request.message)).run leftCache)
      ((monitorGlobalCausalTrace fun causalState =>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          (globalFilteredCausalSigningQuery right.1.1 request
            causalState)).run).run rightState)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1 ∧
          GlobalMonitoredFilteredStateRelation left right.1 leftResult.2
            rightResult.2) ∨ rightResult.2.bad right.1.2) := by
  rcases hstate with
    ⟨monitor, hmonitor, hmonitorAgrees, hrevealed, hcausal, hretained⟩
  apply relTriple_monitorGlobalCausalTrace_of_filtered_until_hit left right.1
    _ _ rightState monitor hmonitor hmonitorAgrees hrevealed
  · apply relTriple_post_mono
      (relTriple_programmed_globalFilteredCausalSigningQuery left right hrel
        hleftSupport hrightSupport leftCache rightState.causal hcausal request)
    intro leftResult rightResult hresult
    exact Or.inl hresult
  · intro result hresult
    constructor
    · exact RevealProbeOracleSimulation.simulate_eagerTrace_support_traceAgrees
        right.1.2 _ result hresult
    · exact
        simulate_eagerTrace_globalFilteredCausalSigningQuery_support_replays
          right.1.2 right.1.1 request rightState.causal result hresult
  · intro result hresult
    exact simulate_eagerTrace_globalFilteredCausalSigningQuery_merkleRetained
      right.1.2 right.1.1 request rightState.causal hretained result hresult

end XmssSecurity.CappedChain

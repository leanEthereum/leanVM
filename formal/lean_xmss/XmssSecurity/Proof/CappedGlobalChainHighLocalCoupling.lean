import VCVio.ProgramLogic.Relational.FromUnary
import XmssSecurity.Proof.CappedGlobalChainHighSetup
import XmssSecurity.Proof.CappedChain.KeygenUnaddressedCache
import XmssSecurity.Proof.RunObservedAppend

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

inductive GlobalFilteredCausalHashPlan where
  | cached (output : HashOutput)
  | reveal (index : GlobalChainValueIndex)
  | probeThenFresh (index : GlobalChainValueIndex) (target : Digest)
  | redirect (output : HashOutput)
  | fresh

structure GlobalLeafInputData where
  leafIndex : ChainKey
  endpoints : ChainIndex → Digest

noncomputable def globalLeafInputData?
    (parameter : PublicParameter) (input : HashInput) :
    Option GlobalLeafInputData := by
  classical
  exact
  if h : ∃ data : GlobalLeafInputData,
      input = Concrete.CacheView.keyLeafInput parameter data.leafIndex data.endpoints then
    some h.choose
  else none

theorem globalLeafInputData?_eq_some_iff
    (parameter : PublicParameter) (input : HashInput)
    (data : GlobalLeafInputData) :
    globalLeafInputData? parameter input = some data ↔
      input = Concrete.CacheView.keyLeafInput parameter data.leafIndex data.endpoints := by
  constructor
  · intro hdata
    unfold globalLeafInputData? at hdata
    split at hdata
    · rename_i hexists
      have heq : hexists.choose = data := by simpa using hdata
      rw [← heq]
      exact hexists.choose_spec
    · simp at hdata
  · intro hinput
    unfold globalLeafInputData?
    split
    · rename_i hexists
      have hchosen := hexists.choose_spec
      have heq := (Concrete.CacheView.keyLeafInput_eq_iff parameter
        hexists.choose.leafIndex data.leafIndex hexists.choose.endpoints
          data.endpoints).mp (hchosen.symm.trans hinput)
      apply congrArg some
      cases hchosenData : hexists.choose with
      | mk chosenLeafIndex chosenEndpoints =>
          cases hdata : data with
          | mk leafIndex endpoints =>
              simp only [hchosenData, hdata] at heq ⊢
              obtain ⟨rfl, rfl⟩ := heq
              rfl
    · rename_i hnone
      exact (hnone ⟨data, hinput⟩).elim

@[simp]
theorem globalLeafInputData?_leafInput
    (parameter : PublicParameter) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest) :
    globalLeafInputData? parameter
        (Concrete.CacheView.keyLeafInput parameter leafIndex endpoints) =
      some ⟨leafIndex, endpoints⟩ := by
  rw [globalLeafInputData?_eq_some_iff]

noncomputable def globalHiddenLeafProbe?
    (state : GlobalCausalHashState) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest) :
    Option (GlobalChainValueIndex × Digest) :=
  if h : ∃ chain : ChainIndex,
      state.revealed (chain, leafIndex, chainEndpointDigit) = none then
    let chain := h.choose
    some ((chain, leafIndex, chainEndpointDigit), endpoints chain)
  else none

theorem globalHiddenLeafProbe?_eq_some
    (state : GlobalCausalHashState) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest) :
    globalHiddenLeafProbe? state leafIndex endpoints = some (index, target) →
      ∃ chain : ChainIndex,
        index = (chain, leafIndex, chainEndpointDigit) ∧
        target = endpoints chain ∧
        state.revealed index = none := by
  intro hprobe
  unfold globalHiddenLeafProbe? at hprobe
  split at hprobe
  · rename_i hexists
    simp only [Option.some.injEq, Prod.mk.injEq] at hprobe
    refine ⟨hexists.choose, hprobe.1.symm, hprobe.2.symm, ?_⟩
    simpa [hprobe.1] using hexists.choose_spec
  · simp at hprobe

theorem globalHiddenLeafProbe?_eq_none_iff
    (state : GlobalCausalHashState) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest) :
    globalHiddenLeafProbe? state leafIndex endpoints = none ↔
      ∀ chain : ChainIndex,
        state.revealed (chain, leafIndex, chainEndpointDigit) ≠ none := by
  unfold globalHiddenLeafProbe?
  split
  · rename_i hexists
    constructor
    · intro himpossible
      simp at himpossible
    · intro hall
      exact (hall hexists.choose hexists.choose_spec).elim
  · rename_i hnone
    constructor
    · intro _ chain hhidden
      exact hnone ⟨chain, hhidden⟩
    · intro _
      rfl

def GlobalLeafRevealsMatch
    (state : GlobalCausalHashState) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest) : Prop :=
  ∀ chain : ChainIndex,
    state.revealed (chain, leafIndex, chainEndpointDigit) = some (endpoints chain)

noncomputable def globalFilteredCausalLeafHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalFilteredCausalHashPlan := by
  classical
  exact
  match globalLeafInputData? secretKey.parameter input with
  | none => .fresh
  | some data =>
      match globalHiddenLeafProbe? state data.leafIndex data.endpoints with
      | some (index, target) => .probeThenFresh index target
      | none =>
          if GlobalLeafRevealsMatch state data.leafIndex data.endpoints then
            match state.keygenCache
                (keygenKeyLeafTargetInput secretKey state.keygenCache input) with
            | some output => .redirect output
            | none => .fresh
          else .fresh


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalFilteredCausalUncachedAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    Option (GlobalChainValueIndex × Digest) → GlobalFilteredCausalHashPlan
  | some (index, target) =>
      match state.revealed index with
      | some value =>
          if value = target then
            if hnext : index.2.2.val + 1 < chainLength then
              .reveal (index.1, index.2.1,
                ⟨index.2.2.val + 1, hnext⟩)
            else .fresh
          else .fresh
      | none =>
          if _hnext : index.2.2.val + 1 < chainLength then
            .probeThenFresh index target
          else .fresh
  | none => globalFilteredCausalLeafHashPlan secretKey input state

noncomputable def globalFilteredCausalAttackerHashPlan
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalFilteredCausalHashPlan :=
  match state.cache input with
  | some output => .cached output
  | none => globalFilteredCausalUncachedAttackerHashPlan secretKey input state
      (globalChainInputProbe? secretKey.parameter input)

theorem globalFilteredCausalUncachedAttackerHashPlan_eq_reveal
    (secretKey : SecretKey) (_input : HashInput)
    (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) (target : Digest)
    (hvalue : state.revealed index = some target)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalUncachedAttackerHashPlan secretKey _input state
        (some (index, target)) =
      .reveal (index.1, index.2.1, ⟨index.2.2.val + 1, hnext⟩) := by
  simp [globalFilteredCausalUncachedAttackerHashPlan, hvalue, hnext]

theorem globalFilteredCausalUncachedAttackerHashPlan_eq_probeThenFresh
    (secretKey : SecretKey) (_input : HashInput)
    (state : GlobalCausalHashState)
    (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : state.revealed index = none)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalUncachedAttackerHashPlan secretKey _input state
        (some (index, target)) =
      .probeThenFresh index target := by
  simp [globalFilteredCausalUncachedAttackerHashPlan, hhidden, hnext]

theorem globalFilteredCausalAttackerHashPlan_eq_probeThenFresh
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (target : Digest)
    (hcache : state.cache input = none)
    (hprobe : globalChainInputProbe? secretKey.parameter input =
      some (index, target))
    (hhidden : state.revealed index = none)
    (hnext : index.2.2.val + 1 < chainLength) :
    globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target := by
  rw [globalFilteredCausalAttackerHashPlan, hcache, hprobe]
  exact globalFilteredCausalUncachedAttackerHashPlan_eq_probeThenFresh
    secretKey input state index target hhidden hnext

@[simp]
theorem globalChainInputProbe?_globalChainTableEdgeInput
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    globalChainInputProbe? parameter
        (globalChainTableEdgeInput parameter table edge) =
      some ((edge.1, edge.2.1, chainStepDigit edge.2.2),
        table (edge.1, edge.2.1, chainStepDigit edge.2.2)) := by
  exact globalChainInputProbe?_keyChainInput parameter edge.2.1 edge.1 edge.2.2
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2))

theorem globalFilteredCausalAttackerHashPlan_eq_reveal_globalEdge
    (secretKey : SecretKey)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (state : GlobalCausalHashState)
    (hcache : state.cache
      (globalChainTableEdgeInput secretKey.parameter table edge) = none)
    (hrevealed : state.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) =
        some (table (edge.1, edge.2.1, chainStepDigit edge.2.2))) :
    globalFilteredCausalAttackerHashPlan secretKey
        (globalChainTableEdgeInput secretKey.parameter table edge) state =
      .reveal (edge.1, edge.2.1, chainStepNextDigit edge.2.2) := by
  rw [globalFilteredCausalAttackerHashPlan, hcache]
  rw [globalChainInputProbe?_globalChainTableEdgeInput]
  have hnext :
      (⟨(chainStepDigit edge.2.2).val + 1,
        (chainStepNextDigit edge.2.2).isLt⟩ : Digit) =
        chainStepNextDigit edge.2.2 := by
    apply Fin.ext
    rfl
  rw [← hnext]
  exact globalFilteredCausalUncachedAttackerHashPlan_eq_reveal
    secretKey
    (globalChainTableEdgeInput secretKey.parameter table edge) state
    (edge.1, edge.2.1, chainStepDigit edge.2.2)
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2)) hrevealed
    (chainStepNextDigit edge.2.2).isLt

noncomputable def globalFilteredCausalRedirectResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (output : HashOutput) :
    GlobalCausalHashState :=
  let recorded := globalCausalRecordedState secretKey input state
  { recorded with cache := recorded.cache.cacheQuery input output }

@[simp]
theorem globalFilteredCausalRedirectResultState_revealed
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (output : HashOutput) :
    (globalFilteredCausalRedirectResultState secretKey input state
      output).revealed = state.revealed := by
  simp [globalFilteredCausalRedirectResultState,
    globalCausalRecordedState_revealed]

noncomputable def globalCausalAttackerHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  let recorded := globalCausalRecordedState secretKey input state
  match globalFilteredCausalAttackerHashPlan secretKey input state with
  | .cached output => pure (output, recorded)
  | .redirect output =>
      pure (output,
        globalFilteredCausalRedirectResultState secretKey input state output)
  | .probeThenFresh index target => do
      let _ ← RevealProbeOracleSimulation.probeQuery index target
      (globalCausalHashQuery input).run recorded
  | .fresh => (globalCausalHashQuery input).run recorded
  | .reveal index =>
      globalCausalRevealHashQueryFromHigh high secretKey input state index

theorem globalCausalAttackerHashQueryFromHigh_run
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state =
      (let recorded := globalCausalRecordedState secretKey input state
       match globalFilteredCausalAttackerHashPlan secretKey input state with
       | .cached output => pure (output, recorded)
       | .redirect output =>
           pure (output,
             globalFilteredCausalRedirectResultState secretKey input state
               output)
       | .probeThenFresh index target => do
           let _ ← RevealProbeOracleSimulation.probeQuery index target
           (globalCausalHashQuery input).run recorded
       | .fresh => (globalCausalHashQuery input).run recorded
       | .reveal index =>
           globalCausalRevealHashQueryFromHigh high secretKey input state
             index) := rfl


theorem globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (globalCausalRevealHashQueryFromHigh high secretKey input state index)
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalRevealHashQueryFromHigh
  apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
    (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP index 0)
  intro value _hvalue
  exact OracleComp.isQueryBoundP_pure
    (p := RevealProbeOracleSimulation.IsProbeQuery) _ 0

theorem globalCausalAttackerHashQueryFromHigh_isProbeQueryBoundP
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalAttackerHashQueryFromHigh high secretKey input).run state
      |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 1 := by
  rw [globalCausalAttackerHashQueryFromHigh_run]
  generalize hplan :
    globalFilteredCausalAttackerHashPlan secretKey input state = plan
  cases plan with
  | cached output => simp
  | redirect output => simp
  | fresh =>
      exact (globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)).mono (by omega)
  | reveal index =>
      exact (globalCausalRevealHashQueryFromHigh_isProbeQueryBoundP high
        secretKey input state index).mono (by omega)
  | probeThenFresh index target =>
      apply OracleComp.isQueryBoundP_bind (n := 1) (m := 0)
        (RevealProbeOracleSimulation.probeQuery_isProbeQueryBoundP index target)
      intro _ _
      exact globalCausalHashQuery_run_isProbeQueryBoundP input
        (globalCausalRecordedState secretKey input state)


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem relTriple_programmed_globalFilteredHashQuery_cached
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (output : HashOutput)
    (hright : rightState.cache input = some output) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleft : leftCache input = some output :=
    hstate.2.1.right_le_left hright
  have hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .cached output := by
    simp [globalFilteredCausalAttackerHashPlan, hright]
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
    WriterT.run_pure]
  apply relTriple_pure_pure
  exact ⟨rfl, hstate.recordedState right.1.1.secretKey input⟩

theorem relTriple_programmed_globalFilteredHashQuery_fresh
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput)
    (hbaseNone : left.cache input = none)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .fresh) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hcurrent : leftCache input = rightState.cache input := by
    rcases hstate.2.1 input with hagree | ⟨hleft, hright⟩
    · exact hagree
    · rw [hleft, hbaseNone, hright]
  have hcouple := relTriple_randomOracle_run_of_current_eq_filtered
    (GlobalSigningComparableHashInput left.secretKey.parameter) left.cache
      leftCache rightState.cache input hcurrent hstate.1 hstate.2.1
  let recorded :=
    globalCausalRecordedState right.1.1.secretKey input rightState
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1, recorded.setCache result.2),
      ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))
  have hprepared : RelTriple ((randomOracle input).run leftCache)
      ((randomOracle input).run rightState.cache)
      (fun leftResult rightResult =>
        GlobalFilteredHashResultRelation left right.1 leftResult
          (wrap rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    refine ⟨hresult.1, ?_⟩
    exact hstate.recordedStateSetCache right.1.1.secretKey input
      leftResult.2 rightResult.2 hresult.2.1 hresult.2.2.2.2
        hresult.2.2.1
  have hmapped := relTriple_map
    (R := GlobalFilteredHashResultRelation left right.1)
    (f := id) (g := wrap) hprepared
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalHashQuery]
  simpa [wrap, recorded, GlobalCausalHashState.setCache] using hmapped

theorem relTriple_programmed_globalFilteredHashQuery_redirect
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (output : HashOutput)
    (hbase : left.cache input = some output)
    (hinput : ¬ GlobalSigningComparableHashInput left.secretKey.parameter input)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .redirect output) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleft : leftCache input = some output := hstate.2.2.1 hbase
  have hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter) leftCache
      ((globalCausalRecordedState right.1.1.secretKey input rightState).cache
        |>.cacheQuery input output) := by
    intro candidate hcandidate
    have hne : candidate ≠ input := by
      intro heq
      subst candidate
      exact hinput hcandidate
    rw [QueryCache.cacheQuery_of_ne _ _ hne,
      globalCausalRecordedState_cache]
    exact hstate.1 candidate hcandidate
  have hfiltered : FilteredCacheExtensionRelation left.cache leftCache
      ((globalCausalRecordedState right.1.1.secretKey input rightState).cache
        |>.cacheQuery input output) := by
    intro candidate
    by_cases heq : candidate = input
    · subst candidate
      left
      simp [hleft]
    · rw [QueryCache.cacheQuery_of_ne _ _ heq,
        globalCausalRecordedState_cache]
      exact hstate.2.1 candidate
  have hnext := hstate.recordedStateSetCache right.1.1.secretKey input
    leftCache
    ((globalCausalRecordedState right.1.1.secretKey input rightState).cache
      |>.cacheQuery input output)
    hagrees hfiltered le_rfl
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_pure,
    WriterT.run_pure]
  exact relTriple_pure_pure ⟨rfl, hnext⟩


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem relTriple_programmed_globalFilteredHashQuery_revealEdge
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
    (edge : GlobalChainEdgeIndex)
    (hrightCache : rightState.cache
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge) =
        none)
    (hrevealed : rightState.revealed
      (edge.1, edge.2.1, chainStepDigit edge.2.2) =
        some (right.1.2
          (edge.1, edge.2.1, chainStepDigit edge.2.2))) :
    RelTriple
      ((randomOracle
        (globalChainTableEdgeInput left.secretKey.parameter left.table edge)).run
          leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            (globalChainTableEdgeInput left.secretKey.parameter left.table
              edge)).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  have htable : left.table = right.1.2 := hrel.1.toStable.1.1
  have hedgeInput :
      globalChainTableEdgeInput left.secretKey.parameter left.table edge =
        globalChainTableEdgeInput right.1.1.secretKey.parameter right.1.2
          edge := by
    rw [hparameter, htable]
  have hrightCanonical : rightState.cache
      (globalChainTableEdgeInput right.1.1.secretKey.parameter right.1.2
        edge) = none := by
    rw [← hedgeInput]
    exact hrightCache
  have hplanCanonical := globalFilteredCausalAttackerHashPlan_eq_reveal_globalEdge
    right.1.1.secretKey right.1.2 edge rightState hrightCanonical hrevealed
  have hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge)
        rightState =
      .reveal (edge.1, edge.2.1, chainStepNextDigit edge.2.2) := by
    rw [hedgeInput]
    exact hplanCanonical
  obtain ⟨output, hbase, htruncate⟩ := hrel.2.2 edge
  have hleft : leftCache
      (globalChainTableEdgeInput left.secretKey.parameter left.table edge) =
        some output := hstate.2.2.1 hbase
  rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
    globalCausalAttackerHashQueryFromHigh_run, hplan,
    simulate_eagerTrace_globalCausalRevealHashQueryFromHigh]
  apply relTriple_pure_pure
  have hconstructed :
      Rom.hashOutputEquivDigestPair.symm
          (globalChainValueHighTableOfEdges right.2
            (edge.1, edge.2.1, chainStepNextDigit edge.2.2),
            right.1.2
              (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) =
        output := by
    calc
      _ = globalChainEdgeOutputFromHigh right.2 right.1.2 edge :=
        globalChainEdgeOutputFromHigh_eq_revealOutput right.2 right.1.2 edge
      _ = globalChainEdgeOutputFromHigh
          (globalChainEdgeHighTableOfCache left.cache
            left.secretKey.parameter left.table) left.table edge := by
        rw [hrel.2.1, htable]
      _ = output := globalChainEdgeOutputFromHigh_eq_cached left.cache
        left.secretKey.parameter left.table edge output hbase htruncate
  refine ⟨hconstructed.symm, ?_⟩
  rw [hconstructed]
  apply hstate.revealResultState right.1.1.secretKey
    (globalChainTableEdgeInput left.secretKey.parameter left.table edge)
    (edge.1, edge.2.1, chainStepNextDigit edge.2.2)
    (right.1.2 (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) output
  · exact globalChainTableEdgeInput_not_signingComparable
      left.secretKey.parameter left.table edge
  · exact hleft
  · rfl


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def GlobalFilteredHashUntilHitRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalFilteredHashResultRelation left right leftResult rightResult ∨
    RevealProbeOracleSimulation.runObserved right.2 monitor rightResult.2 = true

theorem simulate_eagerTrace_globalProbeQuery
    (table : GlobalChainValueIndex → Digest)
    (index : GlobalChainValueIndex) (target : Digest) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (RevealProbeOracleSimulation.probeQuery index target)).run =
        pure ((), [RevealProbeOracleSimulation.ObservedAction.probe
          index target]) := by
  simp [RevealProbeOracleSimulation.probeQuery,
    RevealProbeOracleSimulation.eagerTraceImpl,
    RevealProbeOracleSimulation.eagerImpl,
    RevealProbeOracleSimulation.traceFragment,
    WriterT.run_tell]

theorem globalRunObserved_probe_hit_hidden
    (table : GlobalChainValueIndex → Digest)
    (state : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (index : GlobalChainValueIndex) (target : Digest)
    (suffix : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex)
    (hhidden : state.revealed index = none)
    (hhit : table index = target) :
    RevealProbeOracleSimulation.runObserved table state
      (RevealProbeOracleSimulation.ObservedAction.probe index target :: suffix) =
        true := by
  rw [RevealProbeOracleSimulation.runObserved, hhidden]
  apply RevealProbeOracleSimulation.runObserved_eq_true_of_initial_tableHit
  unfold RevealProbeOracleSimulation.tableHits
  simp only [decide_eq_true_eq]
  refine ⟨index, ?_⟩
  simp [AdaptiveRevealMonitor.State.addPending, hhit]

theorem simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (target : Digest)
    (hplan : globalFilteredCausalAttackerHashPlan secretKey input state =
      .probeThenFresh index target) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalAttackerHashQueryFromHigh high secretKey input).run
        state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1,
          (globalCausalRecordedState secretKey input state).setCache result.2),
          [RevealProbeOracleSimulation.ObservedAction.probe index target])) <$>
        ((randomOracle input).run state.cache) := by
  rw [globalCausalAttackerHashQueryFromHigh_run, hplan, simulateQ_bind,
    WriterT.run_bind', simulate_eagerTrace_globalProbeQuery]
  simp only [map_eq_bind_pure_comp]
  rw [simulate_eagerTrace_globalCausalHashQuery]
  rw [map_eq_bind_pure_comp]
  simp [Function.comp_def]

theorem relTriple_programmed_globalFilteredHashQuery_probeThenFresh_of_baseNone
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hbaseNone : left.cache input = none)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .probeThenFresh index target) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashResultRelation left right.1) := by
  have hcurrent : leftCache input = rightState.cache input := by
    rcases hstate.2.1 input with hagree | ⟨hleft, hright⟩
    · exact hagree
    · rw [hleft, hbaseNone, hright]
  have hcouple := relTriple_randomOracle_run_of_current_eq_filtered
    (GlobalSigningComparableHashInput left.secretKey.parameter) left.cache
      leftCache rightState.cache input hcurrent hstate.1 hstate.2.1
  let recorded :=
    globalCausalRecordedState right.1.1.secretKey input rightState
  let trace : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
    [RevealProbeOracleSimulation.ObservedAction.probe index target]
  let wrap := fun result : HashOutput × QueryCache HashSpec =>
    ((result.1, recorded.setCache result.2), trace)
  have hprepared : RelTriple ((randomOracle input).run leftCache)
      ((randomOracle input).run rightState.cache)
      (fun leftResult rightResult =>
        GlobalFilteredHashResultRelation left right.1 leftResult
          (wrap rightResult)) := by
    apply relTriple_post_mono hcouple
    intro leftResult rightResult hresult
    refine ⟨hresult.1, ?_⟩
    exact hstate.recordedStateSetCache right.1.1.secretKey input
      leftResult.2 rightResult.2 hresult.2.1 hresult.2.2.2.2
        hresult.2.2.1
  have hmapped := relTriple_map
    (R := GlobalFilteredHashResultRelation left right.1)
    (f := id) (g := wrap) hprepared
  rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
    right.1.2 (globalChainValueHighTableOfEdges right.2)
      right.1.1.secretKey input rightState index target hplan]
  simpa [wrap, trace, recorded, GlobalCausalHashState.setCache] using hmapped

theorem relTriple_programmed_globalFilteredHashQuery_probeThenFresh_until_hit
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (leftCache : QueryCache HashSpec) (rightState : GlobalCausalHashState)
    (hstate : GlobalFilteredCausalStateRelation left right.1 leftCache
      rightState)
    (monitor : AdaptiveRevealMonitor.State GlobalChainValueIndex)
    (hmonitor : monitor.revealed = rightState.revealed)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hhidden : rightState.revealed index = none)
    (hplan : globalFilteredCausalAttackerHashPlan right.1.1.secretKey input
      rightState = .probeThenFresh index target)
    (hbaseNone : right.1.2 index ≠ target → left.cache input = none) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
  by_cases hhit : right.1.2 index = target
  · have hmonitorHidden : monitor.revealed index = none := by
      rw [hmonitor, hhidden]
    have hright : ∀ result ∈ support
        ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
          ((globalCausalAttackerHashQueryFromHigh
            (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
              input).run rightState)).run),
        RevealProbeOracleSimulation.runObserved right.1.2 monitor result.2 =
          true := by
      intro result hresult
      rw [simulate_eagerTrace_globalCausalAttackerHashQueryFromHigh_probeThenFresh
        right.1.2 (globalChainValueHighTableOfEdges right.2)
          right.1.1.secretKey input rightState index target hplan,
        support_map] at hresult
      obtain ⟨raw, _hraw, rfl⟩ := hresult
      exact globalRunObserved_probe_hit_hidden
        right.1.2 monitor index target [] hmonitorHidden hhit
    have hproduct := relTriple_prod
      (oa := (randomOracle input).run leftCache)
      (ob := (simulateQ
        (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (P := fun _ => True)
      (Q := fun result => RevealProbeOracleSimulation.runObserved
        right.1.2 monitor result.2 = true)
      (fun _ _ => True.intro) hright
    apply relTriple_post_mono hproduct
    intro _leftResult _rightResult hresult
    exact Or.inr hresult.2
  · apply relTriple_post_mono
      (relTriple_programmed_globalFilteredHashQuery_probeThenFresh_of_baseNone
        left right leftCache rightState hstate input index target
          (hbaseNone hhit) hplan)
    intro _leftResult _rightResult hresult
    exact Or.inl hresult

theorem globalChainInputProbe?_eq_some_iff
    (parameter : PublicParameter) (input : HashInput)
    (index : GlobalChainValueIndex) (target : Digest) :
    globalChainInputProbe? parameter input = some (index, target) ↔
      ∃ step : ChainStep,
        input = Concrete.CacheView.keyChainInput parameter index.2.1 index.1
          step target ∧ index.2.2 = chainStepDigit step := by
  constructor
  · intro hprobe
    unfold globalChainInputProbe? at hprobe
    split at hprobe
    · rename_i hexists
      let data := hexists.choose
      have hdata := hexists.choose_spec
      simp only [Option.some.injEq, Prod.mk.injEq] at hprobe
      obtain ⟨hindex, htarget⟩ := hprobe
      refine ⟨data.2.2.1, ?_, ?_⟩
      · rw [hdata]
        rw [← congrArg (fun value : GlobalChainValueIndex => value.2.1) hindex,
          ← congrArg (fun value : GlobalChainValueIndex => value.1) hindex,
          ← htarget]
      · exact (congrArg (fun value : GlobalChainValueIndex => value.2.2)
          hindex).symm
    · simp at hprobe
  · rintro ⟨step, rfl, hindex⟩
    rw [globalChainInputProbe?_keyChainInput]
    rw [← hindex]

theorem programmedGlobal_left_chainValue_eq_table
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (index : GlobalChainValueIndex) :
    Wots.walk
        (Concrete.CacheView.keyChainStep left.cache left.secretKey.parameter
          index.2.1 index.1)
        0 index.2.2.val (left.secretKey.keyChainStart index.2.1 index.1) =
      right.1.2 index := by
  change globalKeygenChainValueTable left.cache left.secretKey index =
    right.1.2 index
  rw [trajectoryProgrammedGlobalChainKeygen_support_table left hleftSupport]
  exact congrFun hrel.1.toStable.1.1 index

theorem programmedGlobal_left_cache_chainInput_eq_none_of_probe_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hprobe : globalChainInputProbe? left.secretKey.parameter input =
      some (index, target))
    (hmiss : right.1.2 index ≠ target) :
    left.cache input = none := by
  obtain ⟨step, hinput, hindex⟩ :=
    (globalChainInputProbe?_eq_some_iff left.secretKey.parameter input index
      target).mp hprobe
  rw [hinput]
  apply Concrete.keygen_cache_chainInput_eq_none_of_ne left.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport)
  intro heq
  apply hmiss
  rw [← programmedGlobal_left_chainValue_eq_table left right hrel
    hleftSupport index]
  rw [hindex]
  simpa [ProgrammedGlobalChainKeygenView.keyResult, chainStepDigit] using
    heq.symm

theorem relTriple_programmed_globalFilteredChainHashQuery_until_hit
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
    (input : HashInput) (index : GlobalChainValueIndex) (target : Digest)
    (hprobe : globalChainInputProbe? left.secretKey.parameter input =
      some (index, target)) :
    RelTriple
      ((randomOracle input).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        ((globalCausalAttackerHashQueryFromHigh
          (globalChainValueHighTableOfEdges right.2) right.1.1.secretKey
            input).run rightState)).run)
      (GlobalFilteredHashUntilHitRelation left right.1 monitor) := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hrel.1.toStable.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  have hprobeRight : globalChainInputProbe?
      right.1.1.secretKey.parameter input = some (index, target) := by
    rw [← hparameter]
    exact hprobe
  cases hcache : rightState.cache input with
  | some output =>
      apply relTriple_post_mono
        (relTriple_programmed_globalFilteredHashQuery_cached left right
          leftCache rightState hstate input output hcache)
      intro _leftResult _rightResult hresult
      exact Or.inl hresult
  | none =>
      obtain ⟨step, hinput, hindex⟩ :=
        (globalChainInputProbe?_eq_some_iff left.secretKey.parameter input
          index target).mp hprobe
      have hnext : index.2.2.val + 1 < chainLength := by
        rw [hindex]
        exact (chainStepNextDigit step).isLt
      cases hhidden : rightState.revealed index with
      | none =>
          have hplan := globalFilteredCausalAttackerHashPlan_eq_probeThenFresh
            right.1.1.secretKey input rightState index target hcache hprobeRight
              hhidden hnext
          exact
            relTriple_programmed_globalFilteredHashQuery_probeThenFresh_until_hit
              left right leftCache rightState hstate monitor hmonitor input index
                target hhidden hplan
                  (programmedGlobal_left_cache_chainInput_eq_none_of_probe_miss
                    left right hrel hleftSupport input index target hprobe)
      | some value =>
          by_cases hvalue : value = target
          · subst value
            have hhit : right.1.2 index = target :=
              hstate.2.2.2.2 index target hhidden
            have htable : left.table = right.1.2 := hrel.1.toStable.1.1
            have htarget : left.table index = target :=
              (congrFun htable index).trans hhit
            have hedgeInput : input = globalChainTableEdgeInput
                left.secretKey.parameter left.table
                  (index.1, index.2.1, step) := by
              unfold globalChainTableEdgeInput
              rw [hinput]
              rw [← hindex, htarget]
            rw [hedgeInput] at hcache ⊢
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_revealEdge left
                right hrel hleftSupport hrightSupport leftCache rightState
                  hstate (index.1, index.2.1, step) hcache ?_)
            · intro _leftResult _rightResult hresult
              exact Or.inl hresult
            · rw [← hindex, hhit]
              exact hhidden
          · have hmiss : right.1.2 index ≠ target := by
              intro hhit
              exact hvalue ((hstate.2.2.2.2 index value hhidden).symm.trans
                hhit)
            have hbaseNone :=
              programmedGlobal_left_cache_chainInput_eq_none_of_probe_miss
                left right hrel hleftSupport input index target hprobe hmiss
            have hplan : globalFilteredCausalAttackerHashPlan
                right.1.1.secretKey input rightState = .fresh := by
              rw [globalFilteredCausalAttackerHashPlan, hcache, hprobeRight]
              simp [globalFilteredCausalUncachedAttackerHashPlan, hhidden,
                hvalue]
            apply relTriple_post_mono
              (relTriple_programmed_globalFilteredHashQuery_fresh left right
                leftCache rightState hstate input hbaseNone hplan)
            intro _leftResult _rightResult hresult
            exact Or.inl hresult


theorem globalLeafInput_not_signingComparable
    (parameter : PublicParameter) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest) :
    ¬ GlobalSigningComparableHashInput parameter
      (Concrete.CacheView.keyLeafInput parameter leafIndex endpoints) := by
  rintro ⟨encodingLeafIndex, message, randomness, hencoding⟩
  have hdomain := domain_eq_of_tweakableHashInput_eq parameter hencoding
  cases leafIndex <;> simp [ChainKey.leafDomain] at hdomain

theorem programmedGlobal_left_endpoint_eq_table
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leafIndex : ChainKey) (chain : ChainIndex) :
    Concrete.CacheReplay.keyOneTimePublicKey left.cache
        left.secretKey.parameter left.secretKey.keyChainStart leafIndex chain =
      right.1.2 (chain, leafIndex, chainEndpointDigit) := by
  exact programmedGlobal_left_chainValue_eq_table left right hrel hleftSupport
    (chain, leafIndex, chainEndpointDigit)

theorem programmedGlobal_left_leaf_cache_none_of_endpoint_miss
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leafIndex : ChainKey) (endpoints : ChainIndex → Digest)
    (chain : ChainIndex)
    (hmiss : right.1.2 (chain, leafIndex, chainEndpointDigit) ≠ endpoints chain) :
    left.cache (Concrete.CacheView.keyLeafInput left.secretKey.parameter leafIndex
      endpoints) = none := by
  apply Concrete.keygen_cache_keyLeafInput_eq_none_of_ne left.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult left hleftSupport)
      leafIndex endpoints
  intro heq
  apply hmiss
  rw [← programmedGlobal_left_endpoint_eq_table left right hrel hleftSupport
    leafIndex chain]
  exact congrFun heq.symm chain

theorem globalLeafRevealsMatch_endpoints_eq_leftReplay
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hreveals : GlobalSigningRevealsAgree right.1.2 state)
    (hmatch : GlobalLeafRevealsMatch state leafIndex endpoints) :
    endpoints = Concrete.CacheReplay.keyOneTimePublicKey left.cache
      left.secretKey.parameter left.secretKey.keyChainStart leafIndex := by
  funext chain
  have htable : right.1.2 (chain, leafIndex, chainEndpointDigit) =
      endpoints chain :=
    hreveals (chain, leafIndex, chainEndpointDigit) (endpoints chain)
      (hmatch chain)
  rw [← htable]
  exact (programmedGlobal_left_endpoint_eq_table left right hrel hleftSupport
    leafIndex chain).symm

theorem programmedGlobal_secretKey_parameter_eq
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    right.1.1.secretKey.parameter = left.secretKey.parameter := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    right.1.1 hrightSupport
  calc
    right.1.1.secretKey.parameter = right.1.1.publicKey.parameter :=
      (keygen_parameter_eq right.1.1.keyResult hrightKey).symm
    _ = left.publicKey.parameter :=
      congrArg PublicKey.parameter hrel.1.toStable.1.2.1.symm
    _ = left.secretKey.parameter := keygen_parameter_eq left.keyResult hleftKey

theorem leafBaseCachePair_of_treeCorrespondence
    (parameter : PublicParameter)
    (leftSecret : ChainKey → ChainIndex → Digest)
    (rightSecret : SecretKey)
    (leftCache rightCache : QueryCache HashSpec)
    (leftEndpoints rightEndpoints : ChainKey → ChainIndex → Digest)
    (htree : GlobalTreeCacheCorrespondence parameter leftEndpoints
      rightEndpoints leftCache rightCache)
    (hleftReplay : ReplayEndpointsMatch parameter leftSecret leftEndpoints
      leftCache)
    (hrightReplay : ReplayEndpointsMatch parameter rightSecret.keyChainStart
      rightEndpoints rightCache)
    (hparameter : rightSecret.parameter = parameter)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput rightSecret.parameter leafIndex
      endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.keyOneTimePublicKey leftCache
      parameter leftSecret leafIndex)
    (hcached : ∃ output : HashOutput, leftCache
      (Concrete.CacheView.keyLeafInput parameter leafIndex
        (Concrete.CacheReplay.keyOneTimePublicKey leftCache parameter leftSecret
          leafIndex)) = some output) :
    ∃ output : HashOutput,
      leftCache input = some output ∧
      rightCache (keygenKeyLeafTargetInput rightSecret rightCache input) =
        some output := by
  have hreplay := GlobalTreeCacheCorrespondence.replayLeaves parameter leftSecret
    rightSecret.keyChainStart leftCache rightCache leftEndpoints rightEndpoints
      htree hleftReplay hrightReplay
  obtain ⟨output, hleftHonest⟩ := hcached
  have hleftInput : input = Concrete.CacheView.keyLeafInput parameter leafIndex
      (Concrete.CacheReplay.keyOneTimePublicKey leftCache parameter leftSecret
        leafIndex) := by
    calc
      input = Concrete.CacheView.keyLeafInput rightSecret.parameter leafIndex
          endpoints := hinput
      _ = Concrete.CacheView.keyLeafInput parameter leafIndex endpoints :=
        congrArg (fun p => Concrete.CacheView.keyLeafInput p leafIndex endpoints)
          hparameter
      _ = Concrete.CacheView.keyLeafInput parameter leafIndex
          (Concrete.CacheReplay.keyOneTimePublicKey leftCache parameter leftSecret
            leafIndex) :=
        congrArg (Concrete.CacheView.keyLeafInput parameter leafIndex) hendpoints
  have htarget : keygenKeyLeafTargetInput rightSecret rightCache input =
      Concrete.CacheView.keyLeafInput parameter leafIndex
        (Concrete.CacheReplay.keyOneTimePublicKey rightCache parameter
          rightSecret.keyChainStart leafIndex) := by
    calc
      keygenKeyLeafTargetInput rightSecret rightCache input =
          keygenKeyLeafTargetInput rightSecret rightCache
            (Concrete.CacheView.keyLeafInput rightSecret.parameter leafIndex
              endpoints) :=
        congrArg (keygenKeyLeafTargetInput rightSecret rightCache) hinput
      _ = Concrete.CacheView.keyLeafInput rightSecret.parameter leafIndex
          (Concrete.CacheReplay.keyOneTimePublicKey rightCache
            rightSecret.parameter rightSecret.keyChainStart leafIndex) :=
        keygenKeyLeafTargetInput_keyLeafInput rightSecret rightCache leafIndex endpoints
      _ = Concrete.CacheView.keyLeafInput parameter leafIndex
          (Concrete.CacheReplay.keyOneTimePublicKey rightCache parameter
            rightSecret.keyChainStart leafIndex) :=
        congrArg (fun p => Concrete.CacheView.keyLeafInput p leafIndex
          (Concrete.CacheReplay.keyOneTimePublicKey rightCache p
            rightSecret.keyChainStart leafIndex)) hparameter
  have hcorrespond : hashCacheLookup leftCache
      (Concrete.CacheView.keyLeafInput parameter leafIndex
        (Concrete.CacheReplay.keyOneTimePublicKey leftCache parameter leftSecret
          leafIndex)) = hashCacheLookup rightCache
      (Concrete.CacheView.keyLeafInput parameter leafIndex
        (Concrete.CacheReplay.keyOneTimePublicKey rightCache parameter
          rightSecret.keyChainStart leafIndex)) :=
    hreplay leafIndex
  refine ⟨output, ?_, ?_⟩
  · show hashCacheLookup leftCache input = some output
    rw [hleftInput]
    exact hleftHonest
  · show hashCacheLookup rightCache
      (keygenKeyLeafTargetInput rightSecret rightCache input) = some output
    rw [htarget]
    exact hcorrespond.symm.trans hleftHonest

theorem programmedGlobal_leaf_base_cache_pair
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput
      right.1.1.secretKey.parameter leafIndex endpoints)
    (hendpoints : endpoints = Concrete.CacheReplay.keyOneTimePublicKey left.cache
      left.secretKey.parameter left.secretKey.keyChainStart leafIndex) :
    ∃ output : HashOutput,
      left.cache input = some output ∧
      right.1.1.cache
        (keygenKeyLeafTargetInput right.1.1.secretKey right.1.1.cache input) =
          some output := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hparameter : right.1.1.secretKey.parameter =
      left.secretKey.parameter :=
    programmedGlobal_secretKey_parameter_eq left right hrel hleftSupport
      hrightSupport
  obtain ⟨leftEndpoints, rightEndpoints, htree, hleftReplay, hrightReplay⟩ :=
    hrel.1.2.2.2.2.2
  apply leafBaseCachePair_of_treeCorrespondence left.secretKey.parameter
    left.secretKey.keyChainStart right.1.1.secretKey left.cache right.1.1.cache
      leftEndpoints rightEndpoints htree hleftReplay hrightReplay hparameter
        input leafIndex endpoints hinput hendpoints
  exact Concrete.keygen_cache_has_keyLeafInput left.keyResult hleftKey leafIndex

theorem programmedGlobal_leaf_cache_pair_of_reveals_match
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen)
    (state : GlobalCausalHashState)
    (hkeygenCache : state.keygenCache = right.1.1.cache)
    (hreveals : GlobalSigningRevealsAgree right.1.2 state)
    (input : HashInput) (leafIndex : ChainKey)
    (endpoints : ChainIndex → Digest)
    (hinput : input = Concrete.CacheView.keyLeafInput
      right.1.1.secretKey.parameter leafIndex endpoints)
    (hmatch : GlobalLeafRevealsMatch state leafIndex endpoints) :
    ∃ output : HashOutput,
      left.cache input = some output ∧
      state.keygenCache
        (keygenKeyLeafTargetInput right.1.1.secretKey state.keygenCache input) =
          some output := by
  have hendpoints := globalLeafRevealsMatch_endpoints_eq_leftReplay left right
    hrel hleftSupport state leafIndex endpoints hreveals hmatch
  obtain ⟨output, hleft, hright⟩ := programmedGlobal_leaf_base_cache_pair
    left right hrel hleftSupport hrightSupport input leafIndex endpoints hinput
      hendpoints
  refine ⟨output, hleft, ?_⟩
  rw [hkeygenCache]
  exact hright

end XmssSecurity.CappedChain

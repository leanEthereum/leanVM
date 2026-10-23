import XmssSecurity.Proof.CappedGlobalChainOutputUniformity
import XmssSecurity.Proof.CappedGlobalCausalSetup
import XmssSecurity.Proof.MarginalCoupling
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

set_option maxHeartbeats 2000000
set_option maxRecDepth 1000000
set_option linter.constructorNameAsVariable false

noncomputable def programmedGlobalChainTrajectoryMaterialWithBaseHigh
    (parameter : PublicParameter) :
    ProbComp ((GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let materialBase ←
    programmedGlobalChainTrajectoryMaterialWithBase parameter
  let high ← independentGlobalChainHigh
  pure (materialBase, high)

def programmedGlobalChainMaterialBaseHighView
    (result : (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest) :=
  (result.1.2, result.2)

theorem evalDist_programmedGlobalChainMaterialBaseHighView_eq_independent
    (parameter : PublicParameter) :
    (programmedGlobalChainMaterialBaseHighView <$>
      programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter) =ᵈ
    independentGlobalChainTableHigh := by
  unfold programmedGlobalChainTrajectoryMaterialWithBaseHigh
    programmedGlobalChainMaterialBaseHighView
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  calc
    _ =ᵈ ((globalChainTrajectoryMaterialBase <$>
          programmedGlobalChainTrajectoryMaterialWithBase parameter) >>=
        fun table => independentGlobalChainHigh >>= fun high =>
          pure (table, high)) := by
      simp [globalChainTrajectoryMaterialBase, map_eq_bind_pure_comp,
        bind_assoc]
    _ =ᵈ ((globalChainTrajectoryMaterialTable <$>
          programmedGlobalChainTrajectoryMaterial parameter) >>=
        fun table => independentGlobalChainHigh >>= fun high =>
          pure (table, high)) :=
      (evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base
        parameter).symm.bind_left _
    _ =ᵈ (independentGlobalChainValueTable >>= fun table =>
        independentGlobalChainHigh >>= fun high => pure (table, high)) := by
      rw [independentGlobalChainValueTable_eq_uniform]
      exact (evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
        parameter).bind_left _
    _ = _ := by rfl

def ProgrammedGlobalChainMaterialBaseHighRelation
    (parameter : PublicParameter)
    (left : GlobalChainTrajectoryMaterial)
    (right : (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  globalChainTrajectoryMaterialTable left = right.1.2 ∧
    globalChainEdgeHighTableOfCache left.2.2 parameter
      (globalChainTrajectoryMaterialTable left) = right.2

theorem relTriple_programmedGlobalChainTrajectoryMaterial_withBaseHigh
    (parameter : PublicParameter) :
    RelTriple
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter)
      (ProgrammedGlobalChainMaterialBaseHighRelation parameter) := by
  classical
  let : DecidableEq ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) := Classical.decEq _
  have hprojection :
      ((fun material : GlobalChainTrajectoryMaterial =>
        (globalChainTrajectoryMaterialTable material,
          globalChainEdgeHighTableOfCache material.2.2 parameter
            (globalChainTrajectoryMaterialTable material))) <$>
        programmedGlobalChainTrajectoryMaterial parameter) =ᵈ
      (programmedGlobalChainMaterialBaseHighView <$>
        programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter) := by
    calc
      _ =ᵈ (globalChainTableHighViewOfMaterial parameter <$>
          outputGlobalChainTrajectoryMaterial parameter) := by
        have hfunction : (fun material : GlobalChainTrajectoryMaterial =>
            (globalChainTrajectoryMaterialTable material,
              globalChainEdgeHighTableOfCache material.2.2 parameter
                (globalChainTrajectoryMaterialTable material))) =
            globalChainTableHighViewOfMaterial parameter := by
          funext material
          rfl
        rw [hfunction]
        exact (evalDist_programmedGlobalChainTrajectoryMaterial_eq_output parameter).map _
      _ =ᵈ (globalChainKeygenRandomnessView <$>
          (globalChainRandomnessOfMaterial parameter <$>
            outputGlobalChainTrajectoryMaterial parameter)) := by
        simp only [Functor.map_map]
        have hview : (fun material => globalChainKeygenRandomnessView
            (globalChainRandomnessOfMaterial parameter material)) =
            globalChainTableHighViewOfMaterial parameter := by
          funext material
          exact globalChainKeygenRandomnessView_ofView
            (globalChainTableHighViewOfMaterial parameter material)
        rw [hview]
      _ =ᵈ (globalChainKeygenRandomnessView <$>
          uniformGlobalChainKeygenRandomness) :=
        (evalDist_outputGlobalChainRandomness_eq_uniform parameter).map _
      _ =ᵈ independentGlobalChainTableHigh :=
        evalDist_globalChainKeygenRandomnessView_eq_independent
      _ =ᵈ _ :=
        (evalDist_programmedGlobalChainMaterialBaseHighView_eq_independent
          parameter).symm
  apply relTriple_post_mono
    (relTriple_of_evalDist_map_eq_general
      (programmedGlobalChainTrajectoryMaterial parameter)
      (programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter)
      (fun material =>
        (globalChainTrajectoryMaterialTable material,
          globalChainEdgeHighTableOfCache material.2.2 parameter
            (globalChainTrajectoryMaterialTable material)))
      programmedGlobalChainMaterialBaseHighView hprojection)
  intro left right hrelation
  exact ⟨congrArg Prod.fst hrelation, congrArg Prod.snd hrelation⟩

noncomputable def coupledGlobalChainKeygenWithBaseHigh
    (parameter : PublicParameter) :
    ProbComp ((CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let materialBaseHigh ←
    programmedGlobalChainTrajectoryMaterialWithBaseHigh parameter
  let material := materialBaseHigh.1.1
  let topBase ← Concrete.sampleTopBase
  let run ← (simulateQ randomOracle (Concrete.honestKeygenFrom parameter material.1 topBase)).run
    material.2.2
  pure ((({
    start := material.1
    table := globalChainTrajectoryMaterialTable material
    run := run
  } : CoupledGlobalChainKeygenView), materialBaseHigh.1.2),
    materialBaseHigh.2)

/-- Two coupled key generations: equal outputs, the left table is the base, and the caches extend
warm chain caches with corresponding trees. -/
def CoupledGlobalChainKeygenRunRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧ left.run.1 = right.1.run.1 ∧
    ∃ leftWarm rightWarm, ChainsWarm parameter left.start leftWarm ∧
      ChainsWarm parameter right.1.start rightWarm ∧
      KeygenRunRelation parameter left.start right.1.start leftWarm rightWarm
        left.run.2 right.1.run.2

def CoupledGlobalChainKeygenBaseHighRelation
    (parameter : PublicParameter)
    (left : CoupledGlobalChainKeygenView)
    (right : (CoupledGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  CoupledGlobalChainKeygenRunRelation parameter left right.1 ∧
    globalChainEdgeHighTableOfCache left.run.2 parameter left.table = right.2 ∧
    GlobalChainTableEdgesMatch left.run.2 parameter left.table

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
theorem relTriple_coupledGlobalChainKeygen_withBaseHigh
    (parameter : PublicParameter) :
    RelTriple
      (coupledGlobalChainKeygenExperiment parameter)
      (coupledGlobalChainKeygenWithBaseHigh parameter)
      (CoupledGlobalChainKeygenBaseHighRelation parameter) := by
  unfold coupledGlobalChainKeygenExperiment
    coupledGlobalChainKeygenWithBaseHigh
  apply relTriple_bind (relTriple_with_support
    (relTriple_programmedGlobalChainTrajectoryMaterial_withBaseHigh parameter))
  intro leftMaterial rightMaterialBaseHigh hmaterial
  rcases hmaterial with ⟨⟨htable, hhigh⟩, hleftSupport,
    hrightSupport⟩
  have hrightMaterialSupport : rightMaterialBaseHigh.1.1 ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter) := by
    unfold programmedGlobalChainTrajectoryMaterialWithBaseHigh at hrightSupport
    rw [mem_support_bind_iff] at hrightSupport
    obtain ⟨materialBase, hmaterialBase, hhighBind⟩ := hrightSupport
    rw [mem_support_bind_iff] at hhighBind
    obtain ⟨sampledHigh, _hsampledHigh, hpure⟩ := hhighBind
    simp only [support_pure, Set.mem_singleton_iff] at hpure
    rw [hpure]
    unfold programmedGlobalChainTrajectoryMaterialWithBase at hmaterialBase
    rw [mem_support_bind_iff] at hmaterialBase
    obtain ⟨base, _hbase, hmaterialBind⟩ := hmaterialBase
    rw [mem_support_bind_iff] at hmaterialBind
    obtain ⟨material, hmaterial, hpureMaterial⟩ := hmaterialBind
    simp only [support_pure, Set.mem_singleton_iff] at hpureMaterial
    rw [hpureMaterial]
    exact hmaterial
  apply relTriple_bind (relTriple_refl Concrete.sampleTopBase)
  intro leftTopBase rightTopBase htopBase
  have htopBase' : leftTopBase = rightTopBase := htopBase
  subst htopBase'
  apply relTriple_bind
    (relTriple_with_support
      (relTriple_programmedMaterial_honestKeygenFrom_run parameter leftMaterial
        rightMaterialBaseHigh.1.1 hleftSupport hrightMaterialSupport leftTopBase))
  intro leftRun rightRun hrun
  obtain ⟨⟨hrunEq, hrunRel⟩, hleftRunSupport, _⟩ := hrun
  have hmatches := programmedGlobalChainTrajectoryMaterial_edgesMatch
    parameter leftMaterial hleftSupport
  have hcacheLe := Concrete.CacheReplay.randomOracle_cache_le _ _ _ hleftRunSupport
  have hhighFinal :=
    (globalChainEdgeHighTableOfCache_mono leftMaterial.2.2 leftRun.2
      parameter (globalChainTrajectoryMaterialTable leftMaterial)
      hmatches hcacheLe).symm.trans hhigh
  apply relTriple_pure_pure
  refine ⟨⟨htable, hrunEq, leftMaterial.2.2, rightMaterialBaseHigh.1.1.2.2,
    programmedGlobalChainTrajectoryMaterial_chainsWarm parameter leftMaterial hleftSupport,
    programmedGlobalChainTrajectoryMaterial_chainsWarm parameter rightMaterialBaseHigh.1.1
      hrightMaterialSupport, hrunRel⟩, hhighFinal, hmatches.mono hcacheLe⟩


set_option maxRecDepth 2000000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable def coupledGlobalChainKeygenWithBaseHighFull :
    ProbComp ((ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let parameter ← Concrete.samplePublicParameter
  let result ← coupledGlobalChainKeygenWithBaseHigh parameter
  pure ((result.1.1.toProgrammedView parameter, result.1.2), result.2)

def ProgrammedGlobalChainKeygenBaseHighFullRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheRelation left right.1 ∧
    globalChainEdgeHighTableOfCache left.cache left.secretKey.parameter
      left.table = right.2 ∧
    GlobalChainTableEdgesMatch left.cache left.secretKey.parameter left.table

theorem relTriple_coupledGlobalChainKeygenWithBaseHighFull :
    RelTriple coupledGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseHighFull
      ProgrammedGlobalChainKeygenBaseHighFullRelation := by
  unfold coupledGlobalChainKeygen coupledGlobalChainKeygenWithBaseHighFull
  apply relTriple_bind (relTriple_refl Concrete.samplePublicParameter)
  intro leftParameter rightParameter hparameter
  subst rightParameter
  apply relTriple_bind
    (relTriple_coupledGlobalChainKeygen_withBaseHigh leftParameter)
  intro leftView rightView hview
  apply relTriple_pure_pure
  obtain ⟨⟨htable, hrunEq, leftWarm, rightWarm, hleftWarm, hrightWarm, hrunRel⟩,
    hhigh, hedges⟩ := hview
  have hleftStart : (leftView.toProgrammedView leftParameter).secretKey.keyChainStart =
      leftView.start := startSecretKey_keyChainStart _ _ _
  have hrightStart : (rightView.1.1.toProgrammedView leftParameter).secretKey.keyChainStart =
      rightView.1.1.start := startSecretKey_keyChainStart _ _ _
  refine ⟨⟨⟨htable, ?_, ?_, ?_, ?_⟩, _, _, hrunRel.2.2,
      ?_, ?_⟩, hhigh, hedges⟩
  · change PublicKey.mk leftView.run.1.1 leftParameter =
      PublicKey.mk rightView.1.1.run.1.1 leftParameter
    rw [hrunEq]
  · change leftView.run.1.2 = rightView.1.1.run.1.2
    rw [hrunEq]
  · intro leafIndex
    change Concrete.CacheReplay.authenticationPath leftView.run.2
        (startSecretKey leftParameter leftView.start leftView.run.1.2) leafIndex =
      Concrete.CacheReplay.authenticationPath rightView.1.1.run.2
        (startSecretKey leftParameter rightView.1.1.start rightView.1.1.run.1.2) leafIndex
    exact KeygenRunRelation.authenticationPath_eq hleftWarm hrightWarm hrunRel _ _ leafIndex
  · intro key level
    change Concrete.honestTopPath leftView.run.2
        (startSecretKey leftParameter leftView.start leftView.run.1.2) key level =
      Concrete.honestTopPath rightView.1.1.run.2
        (startSecretKey leftParameter rightView.1.1.start rightView.1.1.run.1.2) key level
    exact KeygenRunRelation.honestTopPath_eq hleftWarm hrightWarm hrunRel _ _ key level
  · rw [hleftStart]
    exact KeygenRunRelation.leftReplayEndpoints hleftWarm hrunRel
  · rw [hrightStart]
    exact KeygenRunRelation.rightReplayEndpoints hrightWarm hrunRel

theorem coupledGlobalChainKeygenWithBaseHighFull_support_keyView
    (result : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hresult : result ∈ support
      coupledGlobalChainKeygenWithBaseHighFull) :
    result.1.1 ∈ support trajectoryProgrammedGlobalChainKeygen := by
  unfold coupledGlobalChainKeygenWithBaseHighFull at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨parameter, hparameter, hparameterBind⟩ := hresult
  rw [mem_support_bind_iff] at hparameterBind
  obtain ⟨viewBaseHigh, hviewBaseHigh, hpureView⟩ := hparameterBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureView
  unfold coupledGlobalChainKeygenWithBaseHigh at hviewBaseHigh
  rw [mem_support_bind_iff] at hviewBaseHigh
  obtain ⟨materialBaseHigh, hmaterialBaseHigh, htopBaseBind⟩ := hviewBaseHigh
  rw [mem_support_bind_iff] at htopBaseBind
  obtain ⟨topBase, htopBase, hrunBind⟩ := htopBaseBind
  rw [mem_support_bind_iff] at hrunBind
  obtain ⟨run, hrun, hpureRun⟩ := hrunBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureRun
  unfold programmedGlobalChainTrajectoryMaterialWithBaseHigh at hmaterialBaseHigh
  rw [mem_support_bind_iff] at hmaterialBaseHigh
  obtain ⟨materialBase, hmaterialBase, hhighBind⟩ := hmaterialBaseHigh
  rw [mem_support_bind_iff] at hhighBind
  obtain ⟨high, _hhigh, hpureHigh⟩ := hhighBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureHigh
  unfold programmedGlobalChainTrajectoryMaterialWithBase at hmaterialBase
  rw [mem_support_bind_iff] at hmaterialBase
  obtain ⟨base, _hbase, hmaterialBind⟩ := hmaterialBase
  rw [mem_support_bind_iff] at hmaterialBind
  obtain ⟨material, hmaterial, hpureMaterial⟩ := hmaterialBind
  simp only [support_pure, Set.mem_singleton_iff] at hpureMaterial
  subst hpureMaterial
  subst hpureHigh
  let expectedCoupled : CoupledGlobalChainKeygenView := {
    start := material.1
    table := globalChainTrajectoryMaterialTable material
    run := run
  }
  have hparameterView : expectedCoupled ∈ support
      (coupledGlobalChainKeygenExperiment parameter) := by
    unfold coupledGlobalChainKeygenExperiment
    rw [mem_support_bind_iff]
    refine ⟨material, hmaterial, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨topBase, htopBase, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨run, hrun, by simp [expectedCoupled]⟩
  have hcoupled : expectedCoupled.toProgrammedView parameter ∈
      support coupledGlobalChainKeygen := by
    unfold coupledGlobalChainKeygen
    rw [mem_support_bind_iff]
    refine ⟨parameter, hparameter, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨expectedCoupled, hparameterView, by simp⟩
  have hexpected : expectedCoupled.toProgrammedView parameter ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    (OracleComp.support_eq_of_evalDistEq
      evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed).subset hcoupled
  rw [hpureView, hpureRun]
  exact hexpected

def ProgrammedGlobalChainKeygenBaseHighStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest)) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheStableRelation left right.1 ∧
    globalChainEdgeHighTableOfCache left.cache left.secretKey.parameter
      left.table = right.2 ∧
    GlobalChainTableEdgesMatch left.cache left.secretKey.parameter left.table

theorem relTriple_coupledGlobalChainKeygen_withBaseHigh_fullCacheStable :
    RelTriple coupledGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseHighFull
      ProgrammedGlobalChainKeygenBaseHighStableRelation := by
  apply relTriple_post_mono
    (relTriple_with_support
      relTriple_coupledGlobalChainKeygenWithBaseHighFull)
  intro left right hrel
  obtain ⟨hbaseHigh, hleftCoupledSupport, hrightSupport⟩ := hrel
  have hleftSupport : left ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    (OracleComp.support_eq_of_evalDistEq
      evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed).subset
        hleftCoupledSupport

  have hrightViewSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen :=
    coupledGlobalChainKeygenWithBaseHighFull_support_keyView right
      hrightSupport
  have hparameter : left.secretKey.parameter =
      right.1.1.secretKey.parameter := by
    have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
      left hleftSupport
    have hrightKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
      right.1.1 hrightViewSupport
    calc
      left.secretKey.parameter = left.publicKey.parameter :=
        (keygen_parameter_eq left.keyResult hleftKey).symm
      _ = right.1.1.publicKey.parameter :=
        congrArg PublicKey.parameter hbaseHigh.1.1.2.1
      _ = right.1.1.secretKey.parameter :=
        keygen_parameter_eq right.1.1.keyResult hrightKey
  obtain ⟨leftEndpoints, rightEndpoints, hcache, hleftReplay,
    hrightReplay⟩ := hbaseHigh.1.2
  refine ⟨?_, hbaseHigh.2.1, hbaseHigh.2.2⟩
  refine ⟨hbaseHigh.1,
    trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable left
      hleftSupport,
    trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable right.1.1
      hrightViewSupport,
    trajectoryProgrammedGlobalChainKeygen_support_topCacheStable left hleftSupport,
    trajectoryProgrammedGlobalChainKeygen_support_topCacheStable right.1.1 hrightViewSupport,
    leftEndpoints, rightEndpoints, hcache, hleftReplay, ?_⟩
  rw [hparameter]
  exact hrightReplay

theorem relTriple_trajectoryProgrammedGlobalChainKeygen_withBaseHigh_stable :
    RelTriple trajectoryProgrammedGlobalChainKeygen
      coupledGlobalChainKeygenWithBaseHighFull
      ProgrammedGlobalChainKeygenBaseHighStableRelation := by
  exact relTriple_of_evalDistEq_left
    evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed.symm
    relTriple_coupledGlobalChainKeygen_withBaseHigh_fullCacheStable


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalFilteredCausalKeygenState
    (view : ProgrammedGlobalChainKeygenView) : GlobalCausalHashState := by
  classical
  exact {
    cache := QueryCache.ofFn fun input =>
      if MerkleHashInput view.secretKey.parameter input then view.cache input
      else none
    keygenCache := view.cache
    revealed := fun _ => none
    probes := []
  }

@[simp]
theorem globalChainInputProbe?_encodingInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (input : Message × Randomness) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.encodingInput parameter leafIndex input) = none := by
  apply globalChainInputProbe?_eq_none_of_tweakableHashInput
  intro key chain step
  cases key <;> simp [ChainKey.chainDomain]

@[simp]
theorem globalChainInputProbe?_leafInput
    (parameter : PublicParameter) (leafIndex : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.leafInput parameter leafIndex endpoints) = none := by
  apply globalChainInputProbe?_eq_none_of_tweakableHashInput
  intro key chain step
  cases key <;> simp [ChainKey.chainDomain]

@[simp]
theorem globalChainInputProbe?_keyLeafInput
    (parameter : PublicParameter) (key : ChainKey)
    (endpoints : ChainIndex → Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.keyLeafInput parameter key endpoints) = none := by
  apply globalChainInputProbe?_eq_none_of_tweakableHashInput
  intro chainKey chain step
  cases chainKey <;> cases key <;> simp [ChainKey.chainDomain, ChainKey.leafDomain]

theorem globalChainInputProbe?_merkleHashInput
    (parameter : PublicParameter) (input : HashInput)
    (hinput : MerkleHashInput parameter input) :
    globalChainInputProbe? parameter input = none := by
  obtain ⟨domain, hretained, haddress⟩ := hinput
  apply globalChainInputProbe?_eq_none_of_atHashAddress parameter domain input haddress
  intro key chain step heq
  subst domain
  cases key <;> exact hretained

def FilteredCacheExtensionRelation
    (leftBase left right : QueryCache HashSpec) : Prop :=
  ∀ input,
    left input = right input ∨
      (left input = leftBase input ∧ right input = none)

theorem FilteredCacheExtensionRelation.right_le_left
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right) :
    right ≤ left := by
  intro input output hright
  rcases hrel input with hagrees | ⟨_hbase, hnone⟩
  · rw [hagrees]
    exact hright
  · rw [hnone] at hright
    simp at hright

theorem FilteredCacheExtensionRelation.cacheQuery
    {leftBase left right : QueryCache HashSpec}
    (hrel : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput) (output : HashOutput) :
    FilteredCacheExtensionRelation leftBase
      (left.cacheQuery input output) (right.cacheQuery input output) := by
  intro candidate
  by_cases heq : candidate = input
  · subst candidate
    simp
  · rw [QueryCache.cacheQuery_of_ne left output heq,
      QueryCache.cacheQuery_of_ne right output heq]
    exact hrel candidate

theorem relTriple_randomOracle_run_of_current_eq_filtered
    (inputs : HashInput → Prop)
    (leftBase left right : QueryCache HashSpec)
    (input : HashInput) (hcurrent : left input = right input)
    (hagrees : HashCachesAgreeOn inputs left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right) :
    RelTriple
      ((randomOracle input).run left)
      ((randomOracle input).run right)
      (fun leftResult rightResult =>
        leftResult.1 = rightResult.1 ∧
          HashCachesAgreeOn inputs leftResult.2 rightResult.2 ∧
          left ≤ leftResult.2 ∧ right ≤ rightResult.2 ∧
          FilteredCacheExtensionRelation leftBase
            leftResult.2 rightResult.2) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        HashCachesAgreeOn.cacheQuery inputs left right hagrees
          input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hcurrent]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

theorem simulate_eagerTrace_globalCausalHashQuery
    (table : GlobalChainValueIndex → Digest) (input : HashInput)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      ((globalCausalHashQuery input).run state)).run =
      (fun result : HashOutput × QueryCache HashSpec =>
        ((result.1, state.setCache result.2),
          ([] : RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex))) <$>
        ((randomOracle input).run state.cache) := by
  rw [globalCausalHashQuery_run, simulateQ_map, WriterT.run_map',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp [Functor.map_map]

def GlobalFilteredCausalStateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftCache : QueryCache HashSpec)
    (rightState : GlobalCausalHashState) : Prop :=
  HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      leftCache rightState.cache ∧
    FilteredCacheExtensionRelation left.cache leftCache rightState.cache ∧
    left.cache ≤ leftCache ∧
    rightState.keygenCache = right.1.cache ∧
    GlobalSigningRevealsAgree right.2 rightState

theorem GlobalSigningRevealsAgree.globalCausalRecordedState
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalSigningRevealsAgree table
      (globalCausalRecordedState secretKey input state) := by
  intro index value hvalue
  rw [globalCausalRecordedState_revealed] at hvalue
  exact hagrees index value hvalue

theorem GlobalFilteredCausalStateRelation.recordedStateSetCache
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (newLeft newRight : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput left.secretKey.parameter)
      newLeft newRight)
    (hfiltered : FilteredCacheExtensionRelation left.cache newLeft newRight)
    (hle : leftCache ≤ newLeft) :
    GlobalFilteredCausalStateRelation left right newLeft
      { (globalCausalRecordedState secretKey input rightState) with
        cache := newRight } := by
  refine ⟨hagrees, hfiltered, hstate.2.2.1.trans hle, ?_, ?_⟩
  · simpa using hstate.2.2.2.1
  · exact ((hstate.2.2.2.2.globalCausalRecordedState secretKey input).setCache
      newRight)

theorem GlobalFilteredCausalStateRelation.recordedState
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput) :
    GlobalFilteredCausalStateRelation left right leftCache
      (globalCausalRecordedState secretKey input rightState) := by
  refine ⟨?_, ?_, hstate.2.2.1, ?_, ?_⟩
  · simpa using hstate.1
  · simpa using hstate.2.1
  · simpa using hstate.2.2.2.1
  · exact hstate.2.2.2.2.globalCausalRecordedState secretKey input

noncomputable def globalFilteredCausalRevealResultState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) (output : HashOutput) : GlobalCausalHashState :=
  {
    cache := state.cache.cacheQuery input output
    keygenCache := state.keygenCache
    revealed := Function.update state.revealed index (some value)
    probes := (globalCausalRecordedState secretKey input state).probes
  }

theorem hashCachesAgreeOn_globalFilteredCausalRevealResultState
    {parameter : PublicParameter}
    {leftCache : QueryCache HashSpec} {rightState : GlobalCausalHashState}
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) leftCache rightState.cache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hinput : ¬ GlobalSigningComparableHashInput parameter input) :
    HashCachesAgreeOn (GlobalSigningComparableHashInput parameter) leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index value
        output).cache := by
  intro candidate hcandidate
  have hne : candidate ≠ input := by
    intro heq
    subst candidate
    exact hinput hcandidate
  unfold globalFilteredCausalRevealResultState
  change leftCache candidate =
    rightState.cache.cacheQuery input output candidate
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hagrees candidate hcandidate

theorem filteredCacheExtension_globalFilteredCausalRevealResultState
    {leftBase leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hfiltered : FilteredCacheExtensionRelation leftBase leftCache
      rightState.cache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hleft : leftCache input = some output) :
    FilteredCacheExtensionRelation leftBase leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index value
      output).cache := by
  intro candidate
  change leftCache candidate =
      rightState.cache.cacheQuery input output candidate ∨
    (leftCache candidate = leftBase candidate ∧
      rightState.cache.cacheQuery input output candidate = none)
  by_cases heq : candidate = input
  · subst candidate
    left
    simp [hleft]
  · rw [QueryCache.cacheQuery_of_ne _ _ heq]
    exact hfiltered candidate

theorem globalFilteredCausalRevealResultState_keygenCache_eq
    {rightState : GlobalCausalHashState} {keygenCache : QueryCache HashSpec}
    (hkeygen : rightState.keygenCache = keygenCache)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput) :
    (globalFilteredCausalRevealResultState secretKey input rightState index value
      output).keygenCache = keygenCache := by
  unfold globalFilteredCausalRevealResultState
  exact hkeygen

theorem GlobalSigningRevealsAgree.globalFilteredCausalRevealResultState
    {table : GlobalChainValueIndex → Digest}
    {rightState : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hvalue : table index = value) :
    GlobalSigningRevealsAgree table
      (globalFilteredCausalRevealResultState secretKey input rightState index value
        output) := by
  intro candidate candidateValue hcand
  by_cases heq : candidate = index
  · subst candidate
    simp only [XmssSecurity.CappedChain.globalFilteredCausalRevealResultState,
      Function.update_self, Option.some.injEq] at hcand
    exact hvalue.trans hcand
  · have hright : rightState.revealed candidate = some candidateValue := by
      simpa only [XmssSecurity.CappedChain.globalFilteredCausalRevealResultState,
        Function.update_of_ne heq] using hcand
    exact hagrees candidate candidateValue hright

theorem GlobalFilteredCausalStateRelation.revealResultState
    {left : ProgrammedGlobalChainKeygenView}
    {right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)}
    {leftCache : QueryCache HashSpec}
    {rightState : GlobalCausalHashState}
    (hstate : GlobalFilteredCausalStateRelation left right leftCache rightState)
    (secretKey : SecretKey) (input : HashInput)
    (index : GlobalChainValueIndex) (value : Digest) (output : HashOutput)
    (hinput : ¬ GlobalSigningComparableHashInput
      left.secretKey.parameter input)
    (hleft : leftCache input = some output)
    (hvalue : right.2 index = value) :
    GlobalFilteredCausalStateRelation left right leftCache
      (globalFilteredCausalRevealResultState secretKey input rightState index value
        output) := by
  exact ⟨
    hashCachesAgreeOn_globalFilteredCausalRevealResultState hstate.1 secretKey input
      index value output hinput,
    filteredCacheExtension_globalFilteredCausalRevealResultState hstate.2.1 secretKey
      input index value output hleft,
    hstate.2.2.1,
    globalFilteredCausalRevealResultState_keygenCache_eq hstate.2.2.2.1 secretKey input
      index value output,
    hstate.2.2.2.2.globalFilteredCausalRevealResultState secretKey input index value
      output hvalue⟩

def GlobalFilteredHashResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : HashOutput × QueryCache HashSpec)
    (rightResult : (HashOutput × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

structure GlobalFilteredResultRelation (Output : Type)
    (parameter : PublicParameter)
    (leftBase initialLeft initialRight : QueryCache HashSpec)
    (leftResult rightResult : Output × QueryCache HashSpec) : Prop where
  output_eq : leftResult.1 = rightResult.1
  caches_agree : HashCachesAgreeOn
    (GlobalSigningComparableHashInput parameter) leftResult.2 rightResult.2
  left_le : initialLeft ≤ leftResult.2
  right_le : initialRight ≤ rightResult.2
  filtered : FilteredCacheExtensionRelation leftBase leftResult.2 rightResult.2

theorem relTriple_globalRawHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (input : HashInput)
    (hinput : GlobalSigningComparableHashInput parameter input) :
    RelTriple ((randomOracle input).run left) ((randomOracle input).run right)
      (GlobalFilteredResultRelation HashOutput parameter leftBase left right) := by
  cases hleft : left input with
  | none =>
      have hright : right input = none := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_none _ hleft,
        QueryImpl.withCaching_run_none _ hright,
        map_eq_bind_pure_comp, map_eq_bind_pure_comp]
      apply relTriple_bind (relTriple_refl ($ᵗ HashOutput))
      intro leftOutput rightOutput houtput
      subst rightOutput
      exact relTriple_pure_pure ⟨rfl,
        hagrees.cacheQuery (GlobalSigningComparableHashInput parameter)
          left right input leftOutput,
        QueryCache.le_cacheQuery left hleft,
        QueryCache.le_cacheQuery right hright,
        hfiltered.cacheQuery input leftOutput⟩
  | some output =>
      have hright : right input = some output := by
        rw [← hagrees input hinput]
        exact hleft
      rw [randomOracle, QueryImpl.withCaching_run_some _ hleft,
        QueryImpl.withCaching_run_some _ hright]
      exact relTriple_pure_pure ⟨rfl, hagrees, le_rfl, le_rfl, hfiltered⟩

theorem relTriple_globalEncodingHash_run_filtered
    (parameter : PublicParameter)
    (leftBase left right : QueryCache HashSpec)
    (hagrees : HashCachesAgreeOn
      (GlobalSigningComparableHashInput parameter) left right)
    (hfiltered : FilteredCacheExtensionRelation leftBase left right)
    (leafIndex : LeafIndex) (message : Message) (randomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run left)
      ((simulateQ randomOracle
        (Concrete.encodingHash parameter leafIndex message randomness)).run right)
      (GlobalFilteredResultRelation Digest parameter leftBase left right) := by
  let input := Concrete.CacheView.encodingInput parameter leafIndex
    (message, randomness)
  rw [Concrete.simulateQ_encodingHash_run, Concrete.simulateQ_encodingHash_run]
  change RelTriple
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run left)
    ((fun result : HashOutput × QueryCache HashSpec =>
      (truncateHash result.1, result.2)) <$> (randomOracle input).run right)
    (GlobalFilteredResultRelation Digest parameter leftBase left right)
  apply relTriple_map
  apply relTriple_post_mono
    (relTriple_globalRawHash_run_filtered parameter leftBase left right hagrees
      hfiltered input ⟨leafIndex, message, randomness, rfl⟩)
  intro leftResult rightResult hresult
  exact ⟨congrArg truncateHash hresult.output_eq, hresult.caches_agree,
    hresult.left_le, hresult.right_le, hresult.filtered⟩


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem programmedGlobal_filteredKeygen_stateRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : (ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) ×
      (GlobalChainEdgeIndex → Digest))
    (hrel : ProgrammedGlobalChainKeygenBaseHighStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (hrightSupport : right.1.1 ∈ support
      trajectoryProgrammedGlobalChainKeygen) :
    GlobalFilteredCausalStateRelation left right.1 left.cache
      (globalFilteredCausalKeygenState right.1.1) := by
  classical
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
  obtain ⟨leftEndpoints, rightEndpoints, htree, _hleftReplay,
    _hrightReplay⟩ := hrel.1.1.2
  refine ⟨?_, ?_, le_rfl, rfl, ?_⟩
  · intro input hinput
    obtain ⟨leafIndex, message, randomness, rfl⟩ := hinput
    have hleftNone := Concrete.keygen_cache_none_encodingInput
      left.keyResult hleftKey leafIndex (message, randomness)
    change left.cache (Concrete.CacheView.encodingInput
      left.secretKey.parameter leafIndex (message, randomness)) = none at hleftNone
    have hnotMerkle : ¬ MerkleHashInput right.1.1.secretKey.parameter
        (Concrete.CacheView.encodingInput left.secretKey.parameter leafIndex
          (message, randomness)) := by
      rw [← hparameter]
      exact not_merkleHashInput_of_atHashAddress _ (.encoding leafIndex) _
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl) id
    simpa [globalFilteredCausalKeygenState, hnotMerkle] using hleftNone
  · intro input
    by_cases hmerkle : MerkleHashInput right.1.1.secretKey.parameter input
    · left
      have hmerkleLeft : MerkleHashInput left.secretKey.parameter input := by
        rw [hparameter]
        exact hmerkle
      simpa [globalFilteredCausalKeygenState, hmerkle] using
        htree.merkle input hmerkleLeft
    · right
      exact ⟨rfl, by simp [globalFilteredCausalKeygenState, hmerkle]⟩
  · intro index value hvalue
    simp [globalFilteredCausalKeygenState] at hvalue


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

noncomputable def globalChainValueHighTableOfEdges
    (high : GlobalChainEdgeIndex → Digest) :
    GlobalChainValueIndex → Digest := fun index =>
  if hzero : index.2.2.val = 0 then
    0
  else
    high (index.1, index.2.1, ⟨index.2.2.val - 1, by omega⟩)

@[simp]
theorem globalChainValueHighTableOfEdges_next
    (high : GlobalChainEdgeIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    globalChainValueHighTableOfEdges high
        (edge.1, edge.2.1, chainStepNextDigit edge.2.2) =
      high edge := by
  unfold globalChainValueHighTableOfEdges
  split
  · rename_i hzero
    simp [chainStepNextDigit] at hzero
  · simp only [chainStepNextDigit]
    congr 3

noncomputable def globalCausalRevealHashQueryFromHigh
    (high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (HashOutput × GlobalCausalHashState) := do
  let value ← RevealProbeOracleSimulation.revealQuery index
  let output := Rom.hashOutputEquivDigestPair.symm (high index, value)
  pure (output, globalFilteredCausalRevealResultState secretKey input state
    index value output)

theorem simulate_eagerTrace_globalCausalRevealHashQueryFromHigh
    (table high : GlobalChainValueIndex → Digest)
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalCausalRevealHashQueryFromHigh high secretKey input state
        index)).run =
      pure ((Rom.hashOutputEquivDigestPair.symm
          (high index, table index),
        globalFilteredCausalRevealResultState secretKey input state index
          (table index) (Rom.hashOutputEquivDigestPair.symm
            (high index, table index))),
        [RevealProbeOracleSimulation.ObservedAction.reveal
          index (table index)]) := by
  unfold globalCausalRevealHashQueryFromHigh
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
  simp

theorem globalChainEdgeOutputFromHigh_eq_revealOutput
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    Rom.hashOutputEquivDigestPair.symm
        (globalChainValueHighTableOfEdges high
          (edge.1, edge.2.1, chainStepNextDigit edge.2.2),
          table (edge.1, edge.2.1, chainStepNextDigit edge.2.2)) =
      globalChainEdgeOutputFromHigh high table edge := by
  unfold globalChainEdgeOutputFromHigh globalChainTableEdgeTarget
  rw [globalChainValueHighTableOfEdges_next]


theorem Concrete.keygen_signWithEncoding_eq_base
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (hstable : TreeCacheStable keyResult.1.2.parameter
      keyResult.1.2.chainStart keyResult.2)
    (htopStable : TopCacheStable keyResult.1.2 keyResult.2)
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (leafIndex : LeafIndex) (randomness : Randomness) (encoding : Encoding) :
    Concrete.CacheReplay.signWithEncoding largerCache keyResult.1.2
        leafIndex randomness encoding =
      Concrete.CacheReplay.signWithEncoding keyResult.2 keyResult.1.2
        leafIndex randomness encoding := by
  unfold Concrete.CacheReplay.signWithEncoding
  congr 1
  · funext chain
    calc
      Concrete.CacheReplay.signedChainValues largerCache keyResult.1.2
          leafIndex encoding chain =
        keygenChainValueTable keyResult.2 keyResult.1.2 chain
          (.inl leafIndex, encoding chain) :=
        Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult largerCache hle leafIndex randomness encoding chain
      _ = Concrete.CacheReplay.signedChainValues keyResult.2 keyResult.1.2
          leafIndex encoding chain :=
        (Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
          keyResult hkeyResult keyResult.2 le_rfl leafIndex randomness encoding
            chain).symm
  · exact (TreeCacheStable.authenticationPath_eq keyResult.1.2 keyResult.2
      hstable largerCache hle leafIndex).symm
  · exact (htopStable largerCache hle (topKeyOf leafIndex)).symm

noncomputable def globalFilteredCausalSigningAttempt
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (randomness : Randomness) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let encoded ← RevealProbeOracleSimulation.liftProbComp
    ((simulateQ randomOracle
      (Concrete.encodingHash keyView.secretKey.parameter request.leafIndex
        request.message randomness)).run state.cache)
  let encodedState := { state with cache := encoded.2 }
  match TargetSum.decodeDigest encoded.1 with
  | none => pure (none, encodedState)
  | some encoding => do
      let result ← (revealGlobalSignature keyView.secretKey.topSigned request encoding
        (Concrete.CacheReplay.signWithEncoding keyView.cache keyView.secretKey
          request.leafIndex randomness encoding)).run encodedState
      pure (some result.1, result.2)

noncomputable def globalFilteredCausalSignBoundedAttempts
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest) (base : Randomness) :
    Nat → Nat → GlobalCausalHashState →
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState)
  | 0, _trial, state => pure (none, state)
  | attempts + 1, trial, state => do
      let result ← globalFilteredCausalSigningAttempt keyView request
        (base + BitVec.ofNat randomnessBits trial) state
      match result.1 with
      | some signature => pure (some signature, result.2)
      | none =>
          globalFilteredCausalSignBoundedAttempts keyView request base attempts (trial + 1)
            result.2

/-- The signer's answer: no signature when the request's bottom tree has no top signature. -/
def topSignedResult (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (result : Option Signature × GlobalCausalHashState) :
    Option Signature × GlobalCausalHashState :=
  (if Concrete.topSignedAt keyView.secretKey request.leafIndex then result.1 else none, result.2)

noncomputable def globalFilteredCausalSigningQuery
    (keyView : ProgrammedGlobalChainKeygenView)
    (request : SignRequest) (state : GlobalCausalHashState) :
    OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)
      (Option Signature × GlobalCausalHashState) := do
  let base ← RevealProbeOracleSimulation.liftProbComp Concrete.signingRandomness
  let result ← globalFilteredCausalSignBoundedAttempts keyView request base signingAttemptLimit 0
    state
  pure (topSignedResult keyView request result)

noncomputable def globalFilteredCausalSignTraceContinuation
    (attempts trial : Nat) (base : Randomness) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :
    ProbComp ((Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) :=
  match result.1.1 with
  | some _signature => pure result
  | none =>
      (fun rest => (rest.1, result.2 ++ rest.2)) <$>
        (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
          (globalFilteredCausalSignBoundedAttempts keyView request base attempts trial
            result.1.2)).run

theorem simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ
    (attempts trial : Nat) (base : Randomness) (table : GlobalChainValueIndex → Digest)
    (keyView : ProgrammedGlobalChainKeygenView) (request : SignRequest)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
      (globalFilteredCausalSignBoundedAttempts keyView request base (attempts + 1) trial
        state)).run =
      (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningAttempt keyView request
          (base + BitVec.ofNat randomnessBits trial) state)).run >>=
          globalFilteredCausalSignTraceContinuation attempts (trial + 1) base table keyView
            request := by
  rw [globalFilteredCausalSignBoundedAttempts, simulateQ_bind,
    WriterT.run_bind']
  apply bind_congr
  intro result
  rcases result with ⟨⟨signatureOption, resultState⟩, trace⟩
  cases signatureOption with
  | none =>
      simp only [globalFilteredCausalSignTraceContinuation]
      congr 1
  | some signature =>
      simp [globalFilteredCausalSignTraceContinuation]

theorem mem_support_globalFilteredCausalSigningQuery
    {table : GlobalChainValueIndex → Digest} {keyView : ProgrammedGlobalChainKeygenView}
    {request : SignRequest} {state : GlobalCausalHashState}
    {result : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex}
    (hresult : result ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSigningQuery keyView request state)).run)) :
    ∃ base attemptResult, attemptResult ∈ support
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        (globalFilteredCausalSignBoundedAttempts keyView request base signingAttemptLimit 0
          state)).run) ∧
      result = (topSignedResult keyView request attemptResult.1, attemptResult.2) := by
  unfold globalFilteredCausalSigningQuery at hresult
  rw [simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp,
    mem_support_bind_iff] at hresult
  obtain ⟨baseTrace, hbaseTrace, hresult⟩ := hresult
  rw [support_map] at hbaseTrace
  obtain ⟨base, _hbase, rfl⟩ := hbaseTrace
  simp only [List.nil_append] at hresult
  rw [support_map] at hresult
  obtain ⟨attemptTrace, hattempt, rfl⟩ := hresult
  rw [simulateQ_bind, WriterT.run_bind', mem_support_bind_iff] at hattempt
  obtain ⟨attempt, hattemptMem, hpure⟩ := hattempt
  simp only [simulateQ_pure, WriterT.run_pure, support_map, support_pure,
    Set.image_singleton, Set.mem_singleton_iff] at hpure
  subst hpure
  exact ⟨base, attempt, hattemptMem, by simp⟩

def GlobalFilteredSigningResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest))
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1 = rightResult.1.1 ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

/-- Signing attempts agree on whether they succeed, and on the signature itself when the request's
bottom tree has a top signature: otherwise the signer discards it. -/
def GlobalFilteredSigningLoopRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) (request : SignRequest)
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  leftResult.1.isSome = rightResult.1.1.isSome ∧
    (Concrete.topSignedAt left.secretKey request.leafIndex = true →
      leftResult.1 = rightResult.1.1) ∧
    GlobalFilteredCausalStateRelation left right leftResult.2 rightResult.1.2

def GlobalFilteredSigningAttemptResultRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) (request : SignRequest)
    (leftResult : Option Signature × QueryCache HashSpec)
    (rightResult : (Option Signature × GlobalCausalHashState) ×
      RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex) : Prop :=
  GlobalFilteredSigningLoopRelation left right request leftResult rightResult ∧
    (leftResult.1 = none → rightResult.2 = [])

theorem relTriple_programmed_globalFilteredCausalSigningAttempt
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
    (request : SignRequest) (leftRandomness : Randomness) :
    RelTriple
      ((simulateQ randomOracle
        (Concrete.signAttempt left.secretKey request.leafIndex request.message leftRandomness :
          OracleComp HashSpec (Option Signature))).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSigningAttempt right.1.1 request leftRandomness
          rightState)).run)
      (GlobalFilteredSigningAttemptResultRelation left right.1 request) := by
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
  unfold globalFilteredCausalSigningAttempt
  unfold Concrete.signAttempt
  simp only [simulateQ_bind, StateT.run_bind]
  rw [WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  rw [← hparameter]
  apply relTriple_bind
    (relTriple_globalEncodingHash_run_filtered
      left.secretKey.parameter left.cache leftCache rightState.cache
        hstate.1 hstate.2.1 request.leafIndex request.message leftRandomness)
  intro leftEncoded rightEncoded hencoded
  have hdigestEq : leftEncoded.1 = rightEncoded.1 := hencoded.output_eq
  rw [← hdigestEq]
  cases hdecode : TargetSum.decodeDigest leftEncoded.1 with
  | none =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningLoopRelation
        GlobalFilteredCausalStateRelation
      refine ⟨⟨rfl, fun _ => rfl, hencoded.caches_agree, hencoded.filtered,
        hstate.2.2.1.trans hencoded.left_le, hstate.2.2.2.1, ?_⟩,
        fun _ => rfl⟩
      exact hstate.2.2.2.2.setCache rightEncoded.2
  | some encoding =>
      have hleftRun :
          (simulateQ randomOracle
            (Concrete.signWithEncoding left.secretKey request.leafIndex
              leftRandomness encoding)).run leftEncoded.2 =
            pure (Concrete.CacheReplay.signWithEncoding leftEncoded.2
              left.secretKey request.leafIndex leftRandomness encoding,
                leftEncoded.2) := by
        simpa [ProgrammedGlobalChainKeygenView.keyResult] using
          (Concrete.keygen_signWithEncoding_run_eq_pure left.keyResult hleftKey
            hrel.1.toStable.2.1 leftEncoded.2
            (hstate.2.2.1.trans hencoded.left_le) request.leafIndex
              leftRandomness encoding)
      rw [simulateQ_bind, StateT.run_bind, hleftRun]
      simp only [pure_bind, Function.comp_apply, simulateQ_pure,
        StateT.run_pure]
      rw [simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignature]
      simp [Prod.map]
      unfold GlobalFilteredSigningAttemptResultRelation
        GlobalFilteredSigningLoopRelation
        GlobalFilteredCausalStateRelation
      let encodedState : GlobalCausalHashState :=
        { rightState with cache := rightEncoded.2 }
      let rightSignature := Concrete.CacheReplay.signWithEncoding
        right.1.1.cache right.1.1.secretKey request.leafIndex leftRandomness
          encoding
      have hleftStable := Concrete.keygen_signWithEncoding_eq_base
        left.keyResult hleftKey hrel.1.toStable.2.1 hrel.1.toStable.2.2.2.1 leftEncoded.2
          (hstate.2.2.1.trans hencoded.left_le) request.leafIndex
            leftRandomness encoding
      have hcachesFinal : HashCachesAgreeOn
          (GlobalSigningComparableHashInput left.secretKey.parameter)
          leftEncoded.2
          (globalSignatureFullRevealResult right.1.2 right.1.1.secretKey.topSigned request
            encoding rightSignature encodedState).2.cache := by
        rw [globalSignatureFullRevealResult_cache]
        exact hencoded.caches_agree
      have hfilteredFinal : FilteredCacheExtensionRelation left.cache
          leftEncoded.2
          (globalSignatureFullRevealResult right.1.2 right.1.1.secretKey.topSigned request
            encoding rightSignature encodedState).2.cache := by
        rw [globalSignatureFullRevealResult_cache]
        exact hencoded.filtered
      refine ⟨⟨rfl, ?_, hcachesFinal, hfilteredFinal,
        hstate.2.2.1.trans hencoded.left_le, ?_, ?_⟩, ?_⟩
      · intro htopSigned
        unfold Concrete.topSignedAt at htopSigned
        obtain ⟨⟨topRandomness, topEncoding⟩, htop⟩ := Option.isSome_iff_exists.mp htopSigned
        have hbase := keygenViews_signWithEncoding_eq_globalReveal
          left right.1 hrel.1.toStable hleftSupport hrightSupport left.cache
            right.1.1.cache le_rfl le_rfl request leftRandomness encoding
              encodedState topRandomness topEncoding htop
        exact congrArg some (hleftStable.trans hbase)
      · rw [globalSignatureFullRevealResult_keygenCache]
        exact hstate.2.2.2.1
      · have hagrees := hstate.2.2.2.2.setCache rightEncoded.2
        exact hagrees.globalSignatureFullRevealResult right.1.1.secretKey.topSigned request
          encoding rightSignature
      · intro hnone
        simp at hnone

theorem relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    (attempts trial : Nat) (base : Randomness)
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
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.signBoundedAttempts left.secretKey
          request.leafIndex request.message base attempts trial)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSignBoundedAttempts right.1.1 request base attempts trial
          rightState)).run)
      (GlobalFilteredSigningLoopRelation left right.1 request) := by
  induction attempts generalizing trial leftCache rightState with
  | zero =>
      simp only [Concrete.signBoundedAttempts,
        globalFilteredCausalSignBoundedAttempts, simulateQ_pure,
        StateT.run_pure, WriterT.run_pure]
      apply relTriple_pure_pure
      exact ⟨rfl, fun _ => rfl, hstate⟩
  | succ attempts ih =>
      rw [Concrete.signBoundedAttempts_run_succ_eq attempts trial left.secretKey
        request.leafIndex request.message base leftCache]
      rw [simulate_eagerTrace_globalFilteredCausalSignBoundedAttempts_succ]
      apply relTriple_bind
        (relTriple_programmed_globalFilteredCausalSigningAttempt left right
          hrel hleftSupport hrightSupport leftCache rightState hstate request
          (base + BitVec.ofNat randomnessBits trial))
      intro leftAttempt rightAttempt hattempt
      rcases hattempt with ⟨⟨hsome, hequal, hstate'⟩, hnil⟩
      cases hleft : leftAttempt.1 with
      | none =>
          have hright : rightAttempt.1.1 = none := by
            rw [hleft] at hsome
            exact Option.not_isSome_iff_eq_none.mp (by simpa using hsome.symm)
          have htrace : rightAttempt.2 = [] := hnil hleft
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright, htrace]
          simpa using ih (trial + 1) leftAttempt.2 rightAttempt.1.2 hstate'
      | some signature =>
          obtain ⟨rightSignature, hright⟩ : ∃ rightSignature,
              rightAttempt.1.1 = some rightSignature := by
            rw [hleft] at hsome
            exact Option.isSome_iff_exists.mp (by simpa using hsome.symm)
          unfold Concrete.signBoundedAttemptsContinuation
          unfold globalFilteredCausalSignTraceContinuation
          rw [hleft, hright]
          apply relTriple_pure_pure
          refine ⟨by simp [hright], fun htop => ?_, hstate'⟩
          have := hequal htop
          rw [hleft, hright] at this
          simpa [hright] using this

theorem relTriple_programmed_globalFilteredCausalSigningQuery
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
    (request : SignRequest) :
    RelTriple
      ((simulateQ romImpl
        (Concrete.scheme.sign
          (Concrete.materializePrecomputation left.cache left.secretKey)
          request.leafIndex request.message)).run leftCache)
      ((simulateQ (RevealProbeOracleSimulation.eagerTraceImpl right.1.2)
        (globalFilteredCausalSigningQuery right.1.1 request
          rightState)).run)
      (GlobalFilteredSigningResultRelation left right.1) := by
  simp only [Concrete.scheme, globalFilteredCausalSigningQuery]
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have htopSigned : left.secretKey.topSigned = right.1.1.secretKey.topSigned :=
    hrel.1.toStable.1.2.2.1
  apply relTriple_of_evalDistEq_left
    (Concrete.evalDist_precomputedCappedSign_materialized_eq_cappedSign
      left.keyResult hleftKey hrel.1.2.1 leftCache hstate.2.2.1
        request.leafIndex request.message)
  rw [Concrete.cappedSign_eq, simulateQ_bind, StateT.run_bind]
  have hsample :
      (simulateQ romImpl (liftM Concrete.signingRandomness)).run leftCache =
        (fun base => (base, leftCache)) <$> Concrete.signingRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.signingRandomness)).run leftCache = _
    exact roSim.run_liftM (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.signingRandomness leftCache
  rw [hsample, simulateQ_bind, WriterT.run_bind',
    RevealProbeOracleSimulation.simulate_eagerTrace_liftProbComp]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply, List.nil_append]
  apply relTriple_bind (relTriple_refl Concrete.signingRandomness)
  intro leftBase rightBase hbase
  subst rightBase
  rw [simulateQ_bind, StateT.run_bind, simulateQ_bind, WriterT.run_bind', bind_assoc]
  apply relTriple_bind (relTriple_programmed_globalFilteredCausalSignBoundedAttempts
    signingAttemptLimit 0 leftBase left right hrel hleftSupport hrightSupport leftCache
      rightState hstate request)
  rintro leftResult ⟨⟨rightSignature, rightResultState⟩, rightTrace⟩ hresult
  obtain ⟨hsome, hequal, hstate'⟩ := hresult
  simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure, Prod.map, map_pure, pure_bind,
    Function.comp_apply, id_eq]
  apply relTriple_pure_pure
  refine ⟨?_, hstate'⟩
  change (if Concrete.topSignedAt left.secretKey request.leafIndex = true then leftResult.1
      else none) =
    (if Concrete.topSignedAt right.1.1.secretKey request.leafIndex = true then rightSignature
      else none)
  have htopAt : Concrete.topSignedAt right.1.1.secretKey request.leafIndex =
      Concrete.topSignedAt left.secretKey request.leafIndex := by
    unfold Concrete.topSignedAt
    rw [htopSigned]
  rw [htopAt]
  split
  · exact hequal (by assumption)
  · rfl


set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

theorem globalChainTableEdgeInput_not_signingComparable
    (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) :
    ¬ GlobalSigningComparableHashInput parameter
      (globalChainTableEdgeInput parameter table edge) := by
  rintro ⟨leafIndex, message, randomness, hencoding⟩
  have hprobe : globalChainInputProbe? parameter
      (Concrete.CacheView.keyChainInput parameter edge.2.1 edge.1 edge.2.2
        (table (edge.1, edge.2.1, chainStepDigit edge.2.2))) =
        some ((edge.1, edge.2.1, chainStepDigit edge.2.2),
          table (edge.1, edge.2.1, chainStepDigit edge.2.2)) := by
    exact globalChainInputProbe?_keyChainInput parameter edge.2.1 edge.1 edge.2.2
      (table (edge.1, edge.2.1, chainStepDigit edge.2.2))
  unfold globalChainTableEdgeInput at hencoding
  rw [hencoding, globalChainInputProbe?_encodingInput] at hprobe
  simp at hprobe

end XmssSecurity.CappedChain

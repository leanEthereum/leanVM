import XmssSecurity.Proof.CappedChain.ChainRevealFiltering
import XmssSecurity.Proof.ChainOraclePresampling
import XmssSecurity.Proof.HashOutputHigh
import XmssSecurity.Proof.UniformFiniteTable
import XmssSecurity.Proof.CausalKeygenCoupling
import XmssSecurity.Proof.CausalTreeCoupling
import XmssSecurity.Proof.TopKeygenFacts

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

/-- A uniform pair is the applicative pair of independent uniform coordinates. -/
private theorem uniformSample_prod_evalDistEq_seq {A B : Type} [SampleableType A]
    [SampleableType B] :
    ($ᵗ (A × B)) =ᵈ (Prod.mk <$> ($ᵗ A) <*> ($ᵗ B)) :=
  .of_eq (by
    rw [SampleableType.uniformSample_prod_eq_bind, seq_eq_bind_map, bind_map_left]
    simp only [map_eq_bind_pure_comp, Function.comp_def])

/-- An applicative pair is congruent in its first coordinate. -/
private theorem prod_seq_evalDistEq_left {A B : Type} {a a' : ProbComp A} (h : a =ᵈ a')
    (b : ProbComp B) : (Prod.mk <$> a <*> b) =ᵈ (Prod.mk <$> a' <*> b) := by
  have hseq : ∀ x : ProbComp A, (Prod.mk <$> x <*> b) = (x >>= fun u => Prod.mk u <$> b) := by
    intro x
    rw [seq_eq_bind_map, bind_map_left]
  rw [hseq, hseq]
  exact h.bind_left _

/-- Every uniform sampler of a type is equal in distribution to every other. -/
private theorem uniformSample_evalDistEq_inst {A : Type} (i₁ i₂ : SampleableType A) :
    (@uniformSample A i₁) =ᵈ (@uniformSample A i₂) :=
  EvalDistEq.of_forall_prEvent_eq fun p =>
    SampleableType.prEvent_uniformSample_inst_irrel i₁ i₂ p

abbrev GlobalChainValueIndex := ChainIndex × ChainValueIndex

noncomputable def globalKeygenChainValueTable
    (keygenCache : QueryCache HashSpec) (secretKey : SecretKey) :
    GlobalChainValueIndex → Digest := fun index =>
  keygenChainValueTable keygenCache secretKey index.1 index.2

noncomputable def globalChainInputProbe?
    (parameter : PublicParameter) (input : HashInput) :
    Option (GlobalChainValueIndex × Digest) :=
  if h : ∃ data : ChainKey × ChainIndex × ChainStep × Digest,
      input = Concrete.CacheView.keyChainInput parameter data.1 data.2.1
        data.2.2.1 data.2.2.2 then
    let data := h.choose
    some ((data.2.1, data.1, chainStepDigit data.2.2.1), data.2.2.2)
  else
    none

@[simp]
theorem globalChainInputProbe?_keyChainInput
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.keyChainInput parameter key chain step value) =
      some ((chain, key, chainStepDigit step), value) := by
  unfold globalChainInputProbe?
  split
  · rename_i h
    let chosen := h.choose
    have hchosen := h.choose_spec
    have heq := (Concrete.CacheView.keyChainInput_eq_iff parameter
      chosen.1 key chosen.2.1 chain chosen.2.2.1 step
        chosen.2.2.2 value).mp hchosen.symm
    obtain ⟨hkey, hchain, hstep, hvalue⟩ := heq
    simp only
    rw [hkey, hchain, hstep, hvalue]
  · rename_i h
    exact (h ⟨(key, chain, step, value), rfl⟩).elim

@[simp]
theorem globalChainInputProbe?_chainInput
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.chainInput parameter leafIndex chain step value) =
      some ((chain, .inl leafIndex, chainStepDigit step), value) :=
  globalChainInputProbe?_keyChainInput parameter (.inl leafIndex) chain step value

@[simp]
theorem globalChainInputProbe?_topChainInput
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (step : ChainStep) (value : Digest) :
    globalChainInputProbe? parameter
      (Concrete.CacheView.topChainInput parameter key chain step value) =
      some ((chain, .inr key, chainStepDigit step), value) :=
  globalChainInputProbe?_keyChainInput parameter (.inr key) chain step value


theorem globalChainInputProbe?_eq_none_of_atHashAddress
    (parameter : PublicParameter) (domain : HashDomain) (input : HashInput)
    (haddress : AtHashAddress parameter domain input)
    (hdomain : ∀ (key : ChainKey) chain step, key.chainDomain chain step ≠ domain) :
    globalChainInputProbe? parameter input = none := by
  unfold globalChainInputProbe?
  split
  · rename_i hexists
    obtain ⟨data, hdata⟩ := hexists
    exfalso
    apply hdomain data.1 data.2.1 data.2.2.1
    apply atHashAddress_unique parameter _ _ input _ haddress
    rw [hdata]
    exact Concrete.CacheView.keyChainInput_atHashAddress _ _ _ _ _
  · rfl

theorem globalChainInputProbe?_eq_none_of_tweakableHashInput
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hdomain : ∀ (key : ChainKey) chain step, key.chainDomain chain step ≠ domain) :
    globalChainInputProbe? parameter (tweakableHashInput parameter domain payload) = none :=
  globalChainInputProbe?_eq_none_of_atHashAddress parameter domain _
    ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl) hdomain

abbrev GlobalChainEdgeIndex := ChainIndex × ChainEdgeIndex

noncomputable local instance globalPresamplingSampleableTable :
    SampleableType (GlobalChainValueIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainValueIndex → Digest)

noncomputable local instance globalPresamplingSampleableSeeds :
    SampleableType (ChainKey → ChainIndex → Digest) :=
  SampleableType.ofFintype (ChainKey → ChainIndex → Digest)

noncomputable local instance globalPresamplingSampleableEdges :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

structure ProgrammedGlobalChainKeygenView where
  publicKey : PublicKey
  secretKey : SecretKey
  cache : QueryCache HashSpec
  table : GlobalChainValueIndex → Digest

def globalChainTableEdgeInput
    (parameter : PublicParameter) (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : HashInput :=
  Concrete.CacheView.keyChainInput parameter edge.2.1 edge.1 edge.2.2
    (table (edge.1, edge.2.1, chainStepDigit edge.2.2))

def globalChainTableEdgeTarget
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : Digest :=
  table (edge.1, edge.2.1, chainStepNextDigit edge.2.2)

def GlobalChainTableSeedsMatch
    (secretKey : SecretKey) (table : GlobalChainValueIndex → Digest) : Prop :=
  ∀ key chain,
    secretKey.keyChainStart key chain =
      table (chain, key, ⟨0, by simp [chainLength]⟩)

def GlobalChainTableEdgesMatch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) : Prop :=
  ∀ edge, ∃ output,
    cache (globalChainTableEdgeInput parameter table edge) = some output ∧
      truncateHash output = globalChainTableEdgeTarget table edge

theorem GlobalChainTableEdgesMatch.mono
    {cache larger : QueryCache HashSpec} {parameter : PublicParameter}
    {table : GlobalChainValueIndex → Digest}
    (hmatch : GlobalChainTableEdgesMatch cache parameter table)
    (hle : cache ≤ larger) :
    GlobalChainTableEdgesMatch larger parameter table := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatch edge
  exact ⟨output, hle hcached, htarget⟩

def globalChainTableSeedTargets
    (table : GlobalChainValueIndex → Digest) : ChainKey → ChainIndex → Digest :=
  fun key chain => table (chain, key, ⟨0, by simp [chainLength]⟩)

/-- A global chain table is equivalently all chain seeds and all positive edge coordinates. -/
def globalChainTableMaterialEquiv :
    (GlobalChainValueIndex → Digest) ≃
      ((ChainKey → ChainIndex → Digest) × (GlobalChainEdgeIndex → Digest)) where
  toFun table := (globalChainTableSeedTargets table, globalChainTableEdgeTarget table)
  invFun material index :=
    if hzero : index.2.2.val = 0 then
      material.1 index.2.1 index.1
    else
      material.2
        (index.1, index.2.1, ⟨index.2.2.val - 1, by
          have hdigit := index.2.2.isLt
          omega⟩)
  left_inv table := by
    funext index
    by_cases hzero : index.2.2.val = 0
    · simp only [hzero, ↓reduceDIte, globalChainTableSeedTargets]
      apply congrArg table
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      exact Fin.ext hzero.symm
    · simp only [hzero, ↓reduceDIte, globalChainTableEdgeTarget]
      apply congrArg table
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Fin.ext
      simp [chainStepNextDigit]
      omega
  right_inv material := by
    apply Prod.ext
    · funext key chain
      simp [globalChainTableSeedTargets]
    · funext edge
      simp only [globalChainTableEdgeTarget]
      have hpositive : (chainStepNextDigit edge.2.2).val ≠ 0 := by
        simp [chainStepNextDigit]
      simp only [hpositive, ↓reduceDIte]
      apply congrArg material.2
      apply Prod.ext
      · rfl
      apply Prod.ext
      · rfl
      apply Fin.ext
      simp [chainStepNextDigit]

noncomputable def independentGlobalChainTableMaterial :
    ProbComp ((ChainKey → ChainIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :=
  Prod.mk <$> ($ᵗ (ChainKey → ChainIndex → Digest)) <*>
    ($ᵗ (GlobalChainEdgeIndex → Digest))

theorem evalDist_split_uniformGlobalChainTable_eq_independent :
    (globalChainTableMaterialEquiv <$>
        ($ᵗ (GlobalChainValueIndex → Digest))) =ᵈ independentGlobalChainTableMaterial := by
  calc
    (globalChainTableMaterialEquiv <$> ($ᵗ (GlobalChainValueIndex → Digest))) =ᵈ
        ($ᵗ ((ChainKey → ChainIndex → Digest) × (GlobalChainEdgeIndex → Digest))) :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective
        globalChainTableMaterialEquiv.bijective
    _ =ᵈ independentGlobalChainTableMaterial := uniformSample_prod_evalDistEq_seq

noncomputable def allChains : List ChainIndex :=
  Finset.univ.toList

theorem allChains_nodup : allChains.Nodup := by
  exact Finset.nodup_toList _

theorem mem_allChains (chain : ChainIndex) : chain ∈ allChains := by
  simp [allChains]

noncomputable local instance : SampleableType (TopIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (TopIndex → ChainIndex → Digest)

/-- Both layers' chain starts, as one table. -/
noncomputable def Concrete.sampleChainStarts : ProbComp (ChainKey → ChainIndex → Digest) := do
  let secret ← Concrete.sampleSecret
  let topSecret ← Concrete.sampleTopSecret
  pure (Sum.elim secret topSecret)

attribute [local semireducible] Concrete.sampleTopSecret in
theorem Concrete.sampleTopSecret_eq :
    Concrete.sampleTopSecret = $ᵗ (TopIndex → ChainIndex → Digest) := rfl

set_option maxRecDepth 100000 in
theorem Concrete.evalDist_sampleChainStarts_eq_uniform :
    Concrete.sampleChainStarts =ᵈ ($ᵗ (ChainKey → ChainIndex → Digest)) := by
  have hmap : Concrete.sampleChainStarts =
      (fun pair : (LeafIndex → ChainIndex → Digest) × (TopIndex → ChainIndex → Digest) =>
        Sum.elim pair.1 pair.2) <$>
        (Prod.mk <$> Concrete.sampleSecret <*> ($ᵗ (TopIndex → ChainIndex → Digest))) := by
    rw [← Concrete.sampleTopSecret_eq]
    simp [Concrete.sampleChainStarts, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]
  have hsecret : Concrete.sampleSecret =ᵈ ($ᵗ (LeafIndex → ChainIndex → Digest)) :=
    (EvalDistEq.of_eq Concrete.sampleSecret_eq).trans (uniformSample_evalDistEq_inst _ _)
  rw [hmap]
  exact ((((prod_seq_evalDistEq_left hsecret _).trans uniformSample_prod_evalDistEq_seq.symm).map
    _).trans (SampleableType.map_uniformSample_evalDistEq_of_bijective
      (Equiv.sumArrowEquivProdArrow LeafIndex TopIndex (ChainIndex → Digest)).symm.bijective)).trans
    (uniformSample_evalDistEq_inst _ _)

/-- The secret key of key generation with chain starts `start` and top signatures `topSigned`. -/
def startSecretKey (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) : SecretKey :=
  SecretKey.withoutPrecomputation parameter (fun leafIndex => start (.inl leafIndex))
    (fun key => start (.inr key)) topSigned

@[simp] theorem startSecretKey_keyChainStart (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) :
    (startSecretKey parameter start topSigned).keyChainStart = start := by
  funext key
  cases key <;> rfl

@[simp] theorem startSecretKey_keyChainStart_apply (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) (key : ChainKey) (chain : ChainIndex) :
    (startSecretKey parameter start topSigned).keyChainStart key chain = start key chain := by
  cases key <;> rfl

@[simp] theorem startSecretKey_parameter (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest)
    (topSigned : TopIndex → Option (Randomness × Encoding)) :
    (startSecretKey parameter start topSigned).parameter = parameter := rfl

noncomputable def actualGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let keyResult ← (simulateQ romImpl Concrete.keygen).run ∅
  return {
    publicKey := keyResult.1.1
    secretKey := keyResult.1.2
    cache := keyResult.2
    table := globalKeygenChainValueTable keyResult.2 keyResult.1.2
  }

theorem actualGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support actualGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  unfold actualGlobalChainKeygen at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨keyResult, _hkeyResult, hpure⟩ := hresult
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst result
  rfl

/-- The key generation view of a run of key generation's honest computation. -/
noncomputable def keygenViewOfRun (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest)
    (run : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryCache HashSpec) :
    ProgrammedGlobalChainKeygenView where
  publicKey := ⟨run.1.1, parameter⟩
  secretKey := startSecretKey parameter start run.1.2
  cache := run.2
  table := globalKeygenChainValueTable run.2 (startSecretKey parameter start run.1.2)

noncomputable def explicitGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let start ← Concrete.sampleChainStarts
  let topBase ← Concrete.sampleTopBase
  let run ← (simulateQ randomOracle (Concrete.honestKeygenFrom parameter start topBase)).run ∅
  pure (keygenViewOfRun parameter start run)

theorem evalDist_actualGlobalChainKeygen_eq_explicit :
    actualGlobalChainKeygen =ᵈ explicitGlobalChainKeygen := by
  have hlift : ∀ {α : Type} (computation : ProbComp α),
      (simulateQ romImpl (liftM computation)).run ∅ =
        (fun value => (value, ∅)) <$> computation := fun computation => by
    simpa only [romImpl] using
      (roSim.run_liftM (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)) computation ∅)
  unfold actualGlobalChainKeygen explicitGlobalChainKeygen Concrete.keygen
    Concrete.sampleChainStarts
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, bind_assoc,
    pure_bind, hlift, map_eq_bind_pure_comp, Function.comp_apply]
  apply EvalDistEq.bind_right
  intro parameter
  apply EvalDistEq.bind_right
  intro secret
  apply EvalDistEq.bind_right
  intro topSecret
  apply EvalDistEq.bind_right
  intro topBase
  have hhonest :
      simulateQ romImpl
          (liftM (Concrete.honestKeygen parameter secret topSecret
            (fun key _ => pure (topBase key)) : OracleComp HashSpec _)) =
        simulateQ (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
          (Concrete.honestKeygen parameter secret topSecret
            (fun key _ => pure (topBase key)) : OracleComp HashSpec _) := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) _
  rw [hhonest]
  rfl

noncomputable def globalChainEdgeHighTableOfCache
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest) :
    GlobalChainEdgeIndex → Digest := fun edge =>
  match cache (globalChainTableEdgeInput parameter table edge) with
  | none => 0
  | some output => XmssSecurity.hashOutputHigh output

def globalChainEdgeOutputFromHigh
    (high : GlobalChainEdgeIndex → Digest)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) : HashOutput :=
  Rom.hashOutputEquivDigestPair.symm
    (high edge, globalChainTableEdgeTarget table edge)

theorem globalChainEdgeOutputFromHigh_eq_cached
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (edge : GlobalChainEdgeIndex) (output : HashOutput)
    (hcache : cache (globalChainTableEdgeInput parameter table edge) =
      some output)
    (htarget : truncateHash output = globalChainTableEdgeTarget table edge) :
    globalChainEdgeOutputFromHigh
        (globalChainEdgeHighTableOfCache cache parameter table) table edge =
      output := by
  simp [globalChainEdgeOutputFromHigh, globalChainEdgeHighTableOfCache,
    hcache, XmssSecurity.hashOutputHigh, ← htarget]
  exact Rom.hashOutputEquivDigestPair.symm_apply_apply output

theorem globalChainEdgeHighTableOfCache_mono
    (cache larger : QueryCache HashSpec) (parameter : PublicParameter)
    (table : GlobalChainValueIndex → Digest)
    (hmatches : GlobalChainTableEdgesMatch cache parameter table)
    (hle : cache ≤ larger) :
    globalChainEdgeHighTableOfCache cache parameter table =
      globalChainEdgeHighTableOfCache larger parameter table := by
  funext edge
  obtain ⟨output, hcache, _htarget⟩ := hmatches edge
  have hlarger := hle hcache
  simp [globalChainEdgeHighTableOfCache, hcache, hlarger]


abbrev GlobalChainEdgeOutputTable := GlobalChainEdgeIndex → HashOutput

def outputChainSteps : List ChainStep :=
  List.ofFn (id : ChainStep → ChainStep)

theorem outputChainSteps_nodup : outputChainSteps.Nodup :=
  List.nodup_ofFn.mpr Function.injective_id

theorem mem_outputChainSteps (step : ChainStep) :
    step ∈ outputChainSteps := by
  simp [outputChainSteps]

theorem outputChainSteps_length :
    outputChainSteps.length = chainLength - 1 := by
  simp [outputChainSteps, ChainStep]

noncomputable def globalOutputEdgeOrder : List GlobalChainEdgeIndex :=
  allChains ×ˢ (allChainKeys ×ˢ outputChainSteps)

theorem globalOutputEdgeOrder_nodup : globalOutputEdgeOrder.Nodup :=
  allChains_nodup.product (allChainKeys_nodup.product outputChainSteps_nodup)

theorem mem_globalOutputEdgeOrder (edge : GlobalChainEdgeIndex) :
    edge ∈ globalOutputEdgeOrder := by
  rcases edge with ⟨chain, key, step⟩
  exact List.mem_product.mpr ⟨mem_allChains chain,
    List.mem_product.mpr ⟨mem_allChainKeys key,
      mem_outputChainSteps step⟩⟩

theorem globalOutputEdgeOrder_length :
    globalOutputEdgeOrder.length =
      allChains.length * (allChainKeys.length * (chainLength - 1)) := by
  rw [globalOutputEdgeOrder, List.length_product,
    List.length_product, outputChainSteps_length]

noncomputable def globalChainEdgeOutputTableOfOutputTape
    (outputs : List HashOutput) : GlobalChainEdgeOutputTable :=
  finiteTableOfTape globalOutputEdgeOrder globalOutputEdgeOrder_nodup
    mem_globalOutputEdgeOrder outputs

@[simp]
theorem globalChainEdgeOutputTableOfOutputTape_map
    (table : GlobalChainEdgeOutputTable) :
    globalChainEdgeOutputTableOfOutputTape
      (globalOutputEdgeOrder.map table) = table :=
  finiteTableOfTape_map globalOutputEdgeOrder globalOutputEdgeOrder_nodup
    mem_globalOutputEdgeOrder table

theorem evalDist_globalChainEdgeOutputTableOfOutputTape_uniformSnoc_eq_uniform :
    (globalChainEdgeOutputTableOfOutputTape <$>
      uniformSnocList HashOutput globalOutputEdgeOrder.length) =ᵈ
    ($ᵗ GlobalChainEdgeOutputTable) :=
  (evalDist_finiteTableOfTape_uniformSnoc_eq_uniform globalOutputEdgeOrder
    globalOutputEdgeOrder_nodup mem_globalOutputEdgeOrder).trans
    (uniformSample_evalDistEq_inst _ _)

def trajectoryChainSteps : List ChainStep :=
  (List.ofFn (id : ChainStep → ChainStep)).reverse

theorem trajectoryChainSteps_nodup : trajectoryChainSteps.Nodup := by
  unfold trajectoryChainSteps
  rw [List.nodup_reverse]
  exact List.nodup_ofFn.mpr Function.injective_id

theorem mem_trajectoryChainSteps (step : ChainStep) :
    step ∈ trajectoryChainSteps := by
  simp [trajectoryChainSteps]

theorem trajectoryChainSteps_length :
    trajectoryChainSteps.length = chainLength - 1 := by
  simp [trajectoryChainSteps, ChainStep]

noncomputable def globalTrajectoryEdgeOrder : List GlobalChainEdgeIndex :=
  allChains ×ˢ (allChainKeys ×ˢ trajectoryChainSteps)

theorem globalTrajectoryEdgeOrder_nodup :
    globalTrajectoryEdgeOrder.Nodup := by
  exact allChains_nodup.product
    (allChainKeys_nodup.product trajectoryChainSteps_nodup)

theorem mem_globalTrajectoryEdgeOrder (edge : GlobalChainEdgeIndex) :
    edge ∈ globalTrajectoryEdgeOrder := by
  rcases edge with ⟨chain, key, step⟩
  exact List.mem_product.mpr ⟨mem_allChains chain,
    List.mem_product.mpr ⟨mem_allChainKeys key,
      mem_trajectoryChainSteps step⟩⟩

theorem globalTrajectoryEdgeOrder_length :
    globalTrajectoryEdgeOrder.length =
      allChains.length * (allChainKeys.length * (chainLength - 1)) := by
  rw [globalTrajectoryEdgeOrder, List.length_product,
    List.length_product, trajectoryChainSteps_length]

noncomputable def globalChainEdgeOutputTableOfTape
    (outputs : List HashOutput) : GlobalChainEdgeOutputTable :=
  finiteTableOfTape globalTrajectoryEdgeOrder
    globalTrajectoryEdgeOrder_nodup mem_globalTrajectoryEdgeOrder outputs

@[simp]
theorem globalChainEdgeOutputTableOfTape_map
    (table : GlobalChainEdgeOutputTable) :
    globalChainEdgeOutputTableOfTape
      (globalTrajectoryEdgeOrder.map table) = table :=
  finiteTableOfTape_map globalTrajectoryEdgeOrder
    globalTrajectoryEdgeOrder_nodup mem_globalTrajectoryEdgeOrder table

theorem evalDist_globalChainEdgeOutputTableOfTape_drawList_eq_uniform :
    (globalChainEdgeOutputTableOfTape <$>
      OracleComp.drawList ($ᵗ HashOutput)
        globalTrajectoryEdgeOrder.length) =ᵈ
    ($ᵗ GlobalChainEdgeOutputTable) :=
  (evalDist_finiteTableOfTape_drawList_eq_uniform globalTrajectoryEdgeOrder
    globalTrajectoryEdgeOrder_nodup mem_globalTrajectoryEdgeOrder).trans
    (uniformSample_evalDistEq_inst _ _)


noncomputable local instance outputTableSampleable :
    SampleableType GlobalChainEdgeOutputTable :=
  SampleableType.ofFintype GlobalChainEdgeOutputTable

noncomputable local instance secretTableSampleable :
    SampleableType (ChainKey → ChainIndex → Digest) :=
  SampleableType.ofFintype (ChainKey → ChainIndex → Digest)

noncomputable local instance highTableSampleable :
    SampleableType (GlobalChainEdgeIndex → Digest) :=
  SampleableType.ofFintype (GlobalChainEdgeIndex → Digest)

noncomputable def globalChainValueTableOfRandomness
    (randomness : (ChainKey → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    GlobalChainValueIndex → Digest :=
  globalChainTableMaterialEquiv.symm
    (randomness.1, fun edge => truncateHash (randomness.2 edge))

def globalChainHighTableOfRandomness
    (randomness : (ChainKey → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    GlobalChainEdgeIndex → Digest :=
  fun edge => hashOutputHigh (randomness.2 edge)

noncomputable def globalChainKeygenRandomnessView
    (randomness : (ChainKey → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest) :=
  (globalChainValueTableOfRandomness randomness,
    globalChainHighTableOfRandomness randomness)

noncomputable def globalChainKeygenRandomnessOfView
    (view : (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :
    (ChainKey → ChainIndex → Digest) × GlobalChainEdgeOutputTable :=
  let material := globalChainTableMaterialEquiv view.1
  (material.1, fun edge =>
    Rom.hashOutputEquivDigestPair.symm (view.2 edge, material.2 edge))

theorem globalChainKeygenRandomnessOfView_view
    (randomness : (ChainKey → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :
    globalChainKeygenRandomnessOfView
      (globalChainKeygenRandomnessView randomness) = randomness := by
  apply Prod.ext
  · change (globalChainTableMaterialEquiv
        (globalChainTableMaterialEquiv.symm
          (randomness.1, fun edge => truncateHash (randomness.2 edge)))).1 =
      randomness.1
    exact congrArg Prod.fst (globalChainTableMaterialEquiv.apply_symm_apply
      (randomness.1, fun edge => truncateHash (randomness.2 edge)))
  · funext edge
    have hmaterial := globalChainTableMaterialEquiv.apply_symm_apply
      (randomness.1, fun edge => truncateHash (randomness.2 edge))
    have hlow := congrFun (congrArg Prod.snd hmaterial) edge
    change Rom.hashOutputEquivDigestPair.symm
        (hashOutputHigh (randomness.2 edge),
          (globalChainTableMaterialEquiv
            (globalChainTableMaterialEquiv.symm
              (randomness.1, fun edge => truncateHash (randomness.2 edge)))).2
                edge) = randomness.2 edge
    rw [hlow]
    exact Rom.hashOutputEquivDigestPair.symm_apply_apply (randomness.2 edge)

theorem globalChainKeygenRandomnessView_ofView
    (view : (GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :
    globalChainKeygenRandomnessView
      (globalChainKeygenRandomnessOfView view) = view := by
  apply Prod.ext
  · change globalChainTableMaterialEquiv.symm
        ((globalChainTableMaterialEquiv view.1).1, fun edge =>
          truncateHash (Rom.hashOutputEquivDigestPair.symm
            (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))) = view.1
    have hlow : (fun edge =>
        truncateHash (Rom.hashOutputEquivDigestPair.symm
          (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))) =
        (globalChainTableMaterialEquiv view.1).2 := by
      funext edge
      exact congrArg Prod.snd
        (Rom.hashOutputEquivDigestPair.apply_symm_apply
          (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))
    rw [hlow, globalChainTableMaterialEquiv.symm_apply_apply]
  · funext edge
    exact congrArg Prod.fst
      (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (view.2 edge, (globalChainTableMaterialEquiv view.1).2 edge))

theorem globalChainKeygenRandomnessView_bijective :
    Function.Bijective globalChainKeygenRandomnessView := by
  constructor
  · intro left right heq
    rw [← globalChainKeygenRandomnessOfView_view left,
      ← globalChainKeygenRandomnessOfView_view right, heq]
  · intro view
    exact ⟨globalChainKeygenRandomnessOfView view,
      globalChainKeygenRandomnessView_ofView view⟩

noncomputable def independentGlobalChainValueTable :
    ProbComp (GlobalChainValueIndex → Digest) :=
  $ᵗ (GlobalChainValueIndex → Digest)

noncomputable def independentGlobalChainHigh :
    ProbComp (GlobalChainEdgeIndex → Digest) :=
  $ᵗ (GlobalChainEdgeIndex → Digest)

theorem independentGlobalChainValueTable_eq_uniform :
    independentGlobalChainValueTable =
      ($ᵗ (GlobalChainValueIndex → Digest)) := rfl

theorem evalDist_independentGlobalChainValueTable_eq_uniformMeasure :
    independentGlobalChainValueTable =ᵈ ($ᵗ (GlobalChainValueIndex → Digest)) :=
  .of_eq independentGlobalChainValueTable_eq_uniform

noncomputable def independentGlobalChainTableHigh :
    ProbComp ((GlobalChainValueIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) := do
  let table ← independentGlobalChainValueTable
  let high ← independentGlobalChainHigh
  pure (table, high)

noncomputable def uniformGlobalChainKeygenRandomness :
    ProbComp ((ChainKey → ChainIndex → Digest) ×
      GlobalChainEdgeOutputTable) :=
  Prod.mk <$> Concrete.sampleChainStarts <*>
    ($ᵗ GlobalChainEdgeOutputTable)

set_option maxRecDepth 100000 in
theorem evalDist_uniformGlobalChainKeygenRandomness_eq_uniform :
    uniformGlobalChainKeygenRandomness =ᵈ
      ($ᵗ ((ChainKey → ChainIndex → Digest) × GlobalChainEdgeOutputTable)) := by
  rw [uniformGlobalChainKeygenRandomness]
  exact (prod_seq_evalDistEq_left Concrete.evalDist_sampleChainStarts_eq_uniform _).trans
    uniformSample_prod_evalDistEq_seq.symm

theorem evalDist_uniformGlobalChainKeygenRandomness_eq_uniformMeasure :
    uniformGlobalChainKeygenRandomness =ᵈ
      ($ᵗ ((ChainKey → ChainIndex → Digest) × GlobalChainEdgeOutputTable)) :=
  evalDist_uniformGlobalChainKeygenRandomness_eq_uniform

set_option maxRecDepth 100000 in
theorem evalDist_uniformGlobalChainKeygenRandomness_eq_independent :
    (globalChainKeygenRandomnessView <$>
      ($ᵗ ((ChainKey → ChainIndex → Digest) ×
        GlobalChainEdgeOutputTable))) =ᵈ
    independentGlobalChainTableHigh := by
  calc
    (globalChainKeygenRandomnessView <$>
        ($ᵗ ((ChainKey → ChainIndex → Digest) × GlobalChainEdgeOutputTable))) =ᵈ
        ($ᵗ ((GlobalChainValueIndex → Digest) × (GlobalChainEdgeIndex → Digest))) :=
      SampleableType.map_uniformSample_evalDistEq_of_bijective
        globalChainKeygenRandomnessView_bijective
    _ =ᵈ independentGlobalChainTableHigh := by
      unfold independentGlobalChainTableHigh independentGlobalChainValueTable
        independentGlobalChainHigh
      rw [SampleableType.uniformSample_prod_eq_bind]

theorem evalDist_globalChainKeygenRandomnessView_eq_independent :
    (globalChainKeygenRandomnessView <$>
      uniformGlobalChainKeygenRandomness) =ᵈ
    independentGlobalChainTableHigh := by
  calc
    _ =ᵈ (globalChainKeygenRandomnessView <$>
          ($ᵗ ((ChainKey → ChainIndex → Digest) ×
            GlobalChainEdgeOutputTable))) := by
      exact evalDist_uniformGlobalChainKeygenRandomness_eq_uniform.map _
    _ =ᵈ _ := evalDist_uniformGlobalChainKeygenRandomness_eq_independent


abbrev AllChainTrajectories := ChainIndex → List FullChainTrajectory

noncomputable def globalChainValueTableOfTrajectories
    (trajectories : AllChainTrajectories) :
    GlobalChainValueIndex → Digest := fun index =>
  chainValueTableOfList (trajectories index.1) index.2

noncomputable def Concrete.allChainTrajectoriesFromCache
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex →
      ProbComp (AllChainTrajectories × QueryCache HashSpec)
  | cache, [] => pure (fun _ => [], cache)
  | cache, chain :: chains => do
      let first ← Concrete.fixedSeedChainTrajectoriesFromCache parameter start
        chain (chainLength - 1) cache allChainKeys
      let rest ← Concrete.allChainTrajectoriesFromCache parameter start
        first.2 chains
      pure (Function.update rest.1 chain first.1, rest.2)

@[simp]
theorem Concrete.allChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (cache : QueryCache HashSpec) :
    Concrete.allChainTrajectoriesFromCache parameter start cache [] =
      pure (fun _ => [], cache) := rfl

theorem Concrete.allChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (chain : ChainIndex)
    (chains : List ChainIndex) :
    Concrete.allChainTrajectoriesFromCache parameter start cache
      (chain :: chains) = (do
        let first ← Concrete.fixedSeedChainTrajectoriesFromCache parameter start
          chain (chainLength - 1) cache allChainKeys
        let rest ← Concrete.allChainTrajectoriesFromCache parameter start
          first.2 chains
        pure (Function.update rest.1 chain first.1, rest.2)) := rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.allChainTrajectoriesFromCache_support_info
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      chains.Nodup →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter start cache chains) →
      cache ≤ result.2 ∧
        ∀ chain ∈ chains,
          (result.1 chain).length = Fintype.card ChainKey ∧
            ∀ largerCache : QueryCache HashSpec, result.2 ≤ largerCache →
            List.Forall₂
              (fun key trajectory =>
                evalWithAnswerFn (Concrete.CacheReplay.answerFn largerCache)
                  (Concrete.chainTrajectory parameter key chain 0
                    (chainLength - 1) (start key chain)) = trajectory)
              allChainKeys (result.1 chain) := by
  intro chains
  induction chains with
  | nil =>
      intro cache result _hnodup hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, by simp⟩
  | cons chain chains ih =>
      intro cache result hnodup hresult
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hfirstInfo :=
        Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
          start chain (chainLength - 1) allChainKeys cache first hfirst
      have hrestInfo := ih first.2 rest htailNodup hrest
      constructor
      · exact hfirstInfo.1.trans hrestInfo.1
      · intro selected hselected
        by_cases heq : selected = chain
        · subst selected
          simp only [Function.update_self]
          constructor
          · simpa [allChainKeys_length] using hfirstInfo.2.1
          · intro largerCache hlarger
            exact
              Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
                parameter start chain (chainLength - 1) allChainKeys cache first
                  largerCache hfirst (hrestInfo.1.trans hlarger)
        · have htail : selected ∈ chains := by
            simpa [heq] using hselected
          simp only [Function.update_of_ne heq]
          exact hrestInfo.2 selected htail

theorem chainValueTableOfList_eq_keygenChainValueTable_of_replay
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (cache : QueryCache HashSpec)
    (trajectories : List FullChainTrajectory)
    (hlength : trajectories.length = Fintype.card ChainKey)
    (hreplay : List.Forall₂
      (fun key trajectory =>
        evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
          (Concrete.chainTrajectory parameter key chain 0
            (chainLength - 1) (start key chain)) = trajectory)
      allChainKeys trajectories)
    (secretKey : SecretKey) (hparameter : secretKey.parameter = parameter)
    (hstart : secretKey.keyChainStart = start) :
    chainValueTableOfList trajectories = keygenChainValueTable cache secretKey chain := by
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := chainKeyPosition index.1
    have htrajectoryPosition : position.val < trajectories.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hreplay.get position.isLt htrajectoryPosition
    have hkey : allChainKeys.get position = index.1 :=
      allChainKeys_get_chainKeyPosition index.1
    rw [hkey] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    rw [keygenChainValueTable, hparameter, hstart]
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength (allChainKeys_length.trans hlength.symm)).elim

theorem Concrete.allChainTrajectoriesFromCache_globalTable_eq
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (largerCache : QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter start ∅ allChains))
    (hle : result.2 ≤ largerCache)
    (secretKey : SecretKey) (hparameter : secretKey.parameter = parameter)
    (hstart : secretKey.keyChainStart = start) :
    globalChainValueTableOfTrajectories result.1 =
      globalKeygenChainValueTable largerCache secretKey := by
  have hinfo := Concrete.allChainTrajectoriesFromCache_support_info parameter
    start allChains ∅ result allChains_nodup hresult
  funext index
  have hchainInfo := hinfo.2 index.1 (mem_allChains index.1)
  have hlocal := chainValueTableOfList_eq_keygenChainValueTable_of_replay
    parameter start index.1 largerCache (result.1 index.1) hchainInfo.1
      (hchainInfo.2 largerCache hle) secretKey hparameter hstart
  exact congrFun hlocal index.2

def AllChainAddressesAbsent
    (parameter : PublicParameter) (chains : List ChainIndex)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ chain ∈ chains, ∀ (key : ChainKey) step input,
    AtHashAddress parameter (key.chainDomain chain step) input →
      cache input = none

set_option maxRecDepth 100000 in
theorem Concrete.fixedSeedChainTrajectories_preserves_otherChain_none
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (selected other : ChainIndex) (hne : selected ≠ other)
    (steps : Nat) (keys : List ChainKey) (cache : QueryCache HashSpec)
    (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter start selected
        steps cache keys))
    (key : ChainKey) (step : ChainStep) (input : HashInput)
    (haddress : AtHashAddress parameter (key.chainDomain other step) input)
    (habsent : cache input = none) :
    result.2 input = none := by
  induction keys generalizing cache result with
  | nil =>
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact habsent
  | cons firstKey keys ih =>
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      apply ih first.2 rest hrest
      apply Concrete.CacheReplay.cache_none_of_zero_query_bound
        (Concrete.chainTrajectory parameter firstKey selected 0 steps
          (start firstKey selected)) input cache first.2 first.1
      · apply OracleComp.IsQueryBoundP.of_imp
          (p' := AtHashAddress parameter (key.chainDomain other step))
        · intro candidate heq
          subst candidate
          exact haddress
        · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
          intro offset hoffset hvalid heq
          exact hne (ChainKey.chainDomain_injective heq).2.1
      · exact habsent
      · exact hfirst

noncomputable def programmedAllChainTrajectoriesFromCache
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest) :
    QueryCache HashSpec → List ChainIndex →
      ProbComp (AllChainTrajectories × QueryCache HashSpec)
  | cache, [] => pure (fun _ => [], cache)
  | cache, chain :: chains => do
      let first ← programmedFixedSeedChainTrajectoriesFromCache parameter start
        chain (chainLength - 1) cache allChainKeys
      let rest ← programmedAllChainTrajectoriesFromCache parameter start
        first.2 chains
      pure (Function.update rest.1 chain first.1, rest.2)

@[simp]
theorem programmedAllChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (cache : QueryCache HashSpec) :
    programmedAllChainTrajectoriesFromCache parameter start cache [] =
      pure (fun _ => [], cache) := rfl

theorem programmedAllChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (cache : QueryCache HashSpec) (chain : ChainIndex)
    (chains : List ChainIndex) :
    programmedAllChainTrajectoriesFromCache parameter start cache
      (chain :: chains) = (do
        let first ← programmedFixedSeedChainTrajectoriesFromCache parameter
          start chain (chainLength - 1) cache allChainKeys
        let rest ← programmedAllChainTrajectoriesFromCache parameter start
          first.2 chains
        pure (Function.update rest.1 chain first.1, rest.2)) := rfl

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 100000 in
theorem evalDist_allChainTrajectories_eq_programmed
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
      chains.Nodup → AllChainAddressesAbsent parameter chains cache →
      (Concrete.allChainTrajectoriesFromCache parameter start cache
        chains) =ᵈ
      (programmedAllChainTrajectoriesFromCache parameter start cache
        chains) := by
  intro chains
  induction chains with
  | nil =>
      intro cache _hnodup _habsent
      simp
  | cons chain chains ih =>
      intro cache hnodup habsent
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        programmedAllChainTrajectoriesFromCache_cons]
      let actualFirst := Concrete.fixedSeedChainTrajectoriesFromCache parameter
        start chain (chainLength - 1) cache allChainKeys
      let programmedFirst := programmedFixedSeedChainTrajectoriesFromCache
        parameter start chain (chainLength - 1) cache allChainKeys
      have hfirst : actualFirst =ᵈ programmedFirst := by
        apply evalDist_fixedSeedChainTrajectories_eq_programmed parameter start
          chain (chainLength - 1) le_rfl allChainKeys cache allChainKeys_nodup
        intro key _hleafIndex step input haddress
        exact habsent chain (by simp) key step input haddress
      calc
        _ =ᵈ (programmedFirst >>= fun first =>
              Concrete.allChainTrajectoriesFromCache parameter start first.2
                chains >>= fun rest =>
              pure (Function.update rest.1 chain first.1, rest.2)) := by
          exact hfirst.bind_left _
        _ =ᵈ (programmedFirst >>= fun first =>
              programmedAllChainTrajectoriesFromCache parameter start first.2
                chains >>= fun rest =>
              pure (Function.update rest.1 chain first.1, rest.2)) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro first hfirstProgrammed
          have hfirstActual : first ∈ support actualFirst := by
            rw [OracleComp.support_eq_of_evalDistEq hfirst]
            exact hfirstProgrammed
          have htailAbsent : AllChainAddressesAbsent parameter chains first.2 := by
            intro later hlater key step input haddress
            apply Concrete.fixedSeedChainTrajectories_preserves_otherChain_none
              parameter start chain later
            · intro heq
              subst later
              exact hnotMem hlater
            · exact hfirstActual
            · exact haddress
            · exact habsent later (by simp [hlater]) key step input haddress
          have hrest := ih first.2 htailNodup htailAbsent
          exact hrest.bind_left _

noncomputable def uniformTrajectoryFromSeed :
    (steps : Nat) → Digest → ProbComp (Vector Digest (steps + 1))
  | 0, seed => pure (Vector.ofFn fun _ => seed)
  | steps + 1, seed => do
      let prior ← uniformTrajectoryFromSeed steps seed
      let next ← $ᵗ Digest
      pure (prior.push next)

@[simp]
theorem uniformTrajectoryFromSeed_zero (seed : Digest) :
    uniformTrajectoryFromSeed 0 seed =
      pure (Vector.ofFn fun _ => seed) := rfl

theorem uniformTrajectoryFromSeed_succ (steps : Nat) (seed : Digest) :
    uniformTrajectoryFromSeed (steps + 1) seed = (do
      let prior ← uniformTrajectoryFromSeed steps seed
      let next ← $ᵗ Digest
      pure (prior.push next)) := rfl

def trajectoryTailTape {steps : Nat}
    (trajectory : Vector Digest (steps + 1)) : List Digest :=
  trajectory.toList.drop 1

@[simp]
theorem trajectoryTailTape_ofFn_seed (seed : Digest) :
    trajectoryTailTape (Vector.ofFn fun _ : Fin 1 => seed) = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [trajectoryTailTape]

theorem trajectoryTailTape_push {steps : Nat}
    (trajectory : Vector Digest (steps + 1)) (next : Digest) :
    trajectoryTailTape (trajectory.push next) =
      trajectoryTailTape trajectory ++ [next] := by
  unfold trajectoryTailTape
  rw [Vector.toList_push, List.drop_append_of_le_length]
  simp

theorem evalDist_uniformTrajectoryFromSeed_tailTape
    (steps : Nat) (seed : Digest) :
    (trajectoryTailTape <$>
      uniformTrajectoryFromSeed steps seed) =ᵈ
      (uniformSnocList Digest steps) := by
  induction steps with
  | zero => simp [uniformSnocList]
  | succ steps ih =>
      rw [uniformTrajectoryFromSeed_succ, uniformSnocList]
      simp only [map_bind, bind_pure_comp]
      calc
        _ =ᵈ (uniformTrajectoryFromSeed steps seed >>= fun prior =>
              ($ᵗ Digest) >>= fun next =>
              pure (trajectoryTailTape prior ++ [next])) := by
          apply EvalDistEq.bind_right
          intro prior
          simp [trajectoryTailTape_push]
        _ =ᵈ (uniformSnocList Digest steps >>= fun prior =>
              ($ᵗ Digest) >>= fun next =>
              pure (prior ++ [next])) := by
          calc
            _ =ᵈ ((trajectoryTailTape <$>
                  uniformTrajectoryFromSeed steps seed) >>= fun prior =>
                ($ᵗ Digest) >>= fun next =>
                pure (prior ++ [next])) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ =ᵈ _ := by
              exact ih.bind_left _

def trajectoryDrawTape {steps : Nat}
    (trajectory : Vector Digest (steps + 1)) : List Digest :=
  (trajectoryTailTape trajectory).reverse

theorem trajectoryDrawTape_ofDigitTable (values : Digit → Digest) :
    trajectoryDrawTape (FullChainTrajectory.ofDigitTable values) =
      trajectoryChainSteps.map
        (fun step => values (chainStepNextDigit step)) := by
  unfold trajectoryDrawTape trajectoryTailTape trajectoryChainSteps
    FullChainTrajectory.ofDigitTable
  rw [Vector.toList_ofFn, List.ofFn_succ]
  simp only [List.drop]
  rw [List.map_reverse]
  congr 1

theorem evalDist_uniformTrajectoryFromSeed_drawTape
    (steps : Nat) (seed : Digest) :
    (trajectoryDrawTape <$>
      uniformTrajectoryFromSeed steps seed) =ᵈ
      (OracleComp.drawList ($ᵗ Digest) steps) := by
  calc
    _ =ᵈ (List.reverse <$>
          (trajectoryTailTape <$>
            uniformTrajectoryFromSeed steps seed)) := by
      rw [Functor.map_map]
      rfl
    _ =ᵈ (List.reverse <$>
          uniformSnocList Digest steps) := by
      exact (evalDist_uniformTrajectoryFromSeed_tailTape steps seed).map _
    _ =ᵈ (List.reverse <$>
          (List.reverse <$>
            OracleComp.drawList ($ᵗ Digest) steps)) := by
      exact (evalDist_uniformSnocList_eq_reverse_drawList Digest steps).map _
    _ =ᵈ (OracleComp.drawList ($ᵗ Digest) steps) := by
      simp [Functor.map_map]

theorem drawList_append (firstLength secondLength : Nat) :
    (do
      let first ← OracleComp.drawList ($ᵗ Digest) firstLength
      let second ← OracleComp.drawList ($ᵗ Digest) secondLength
      pure (first ++ second)) =
      OracleComp.drawList ($ᵗ Digest) (firstLength + secondLength) := by
  induction firstLength with
  | zero => simp [OracleComp.drawList]
  | succ firstLength ih =>
      calc
        (do
            let first ← OracleComp.drawList ($ᵗ Digest) (firstLength + 1)
            let second ← OracleComp.drawList ($ᵗ Digest) secondLength
            pure (first ++ second)) =
            (do
              let head ← $ᵗ Digest
              let tail ← (do
                let first ← OracleComp.drawList ($ᵗ Digest) firstLength
                let second ← OracleComp.drawList ($ᵗ Digest) secondLength
                pure (first ++ second))
              pure (head :: tail)) := by
          simp [OracleComp.drawList, bind_assoc]
        _ = (do
              let head ← $ᵗ Digest
              let tail ← OracleComp.drawList ($ᵗ Digest)
                (firstLength + secondLength)
              pure (head :: tail)) := by
          rw [ih]
        _ = OracleComp.drawList ($ᵗ Digest)
              ((firstLength + secondLength) + 1) := rfl
        _ = OracleComp.drawList ($ᵗ Digest)
              ((firstLength + 1) + secondLength) := by
          congr 1
          omega

theorem evalDist_sampledHashOutputWithDigest_fst_eq_uniform :
    (Prod.fst <$> Rom.sampledHashOutputWithDigest) =ᵈ
      ($ᵗ Digest) := by
  calc
    _ =ᵈ (truncateHash <$> ($ᵗ HashOutput)) := by
      refine (Rom.evalDist_sampledHashOutputWithDigest_eq_uniform.map _).trans (.of_eq ?_)
      simp [Functor.map_map]
    _ =ᵈ ($ᵗ Digest) := Rom.evalDist_truncate_uniformHashOutput

theorem evalDist_programmedChainExtension_fst
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (step : ChainStep) (values : Vector Digest (n + 1))
    (cache : QueryCache HashSpec) :
    (Prod.fst <$>
      programmedChainExtension parameter key chain step values cache) =ᵈ
      ((fun next : Digest => values.push next) <$> ($ᵗ Digest)) := by
  unfold programmedChainExtension
  simp only [bind_pure_comp]
  calc
    _ =ᵈ ((fun next : Digest => values.push next) <$>
          (Prod.fst <$> Rom.sampledHashOutputWithDigest)) := by
      simp [Functor.map_map]
    _ =ᵈ ((fun next : Digest => values.push next) <$>
          ($ᵗ Digest)) := by
      exact evalDist_sampledHashOutputWithDigest_fst_eq_uniform.map _

set_option maxRecDepth 100000 in
theorem evalDist_programmedChainTrajectory_fst_eq_uniform
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position : Nat) : ∀ (steps : Nat) (seed : Digest)
      (cache : QueryCache HashSpec),
      position + steps ≤ chainLength - 1 →
      (Prod.fst <$>
        programmedChainTrajectory parameter key chain position steps seed
          cache) =ᵈ
      (uniformTrajectoryFromSeed steps seed) := by
  intro steps
  induction steps with
  | zero =>
      intro seed cache _hsteps
      simp [programmedChainTrajectory]
  | succ steps ih =>
      intro seed cache hsteps
      have hvalid : position + steps < chainLength - 1 := by omega
      simp only [programmedChainTrajectory, hvalid, ↓reduceDIte, map_bind]
      let prior := programmedChainTrajectory parameter key chain position
        steps seed cache
      calc
        _ =ᵈ (prior >>= fun priorResult =>
              (fun next : Digest => priorResult.1.push next) <$>
                ($ᵗ Digest)) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro priorResult _hpriorResult
          exact evalDist_programmedChainExtension_fst parameter key chain
            ⟨position + steps, hvalid⟩ priorResult.1 priorResult.2
        _ =ᵈ ((Prod.fst <$> prior) >>= fun priorValues =>
              (fun next : Digest => priorValues.push next) <$>
                ($ᵗ Digest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (uniformTrajectoryFromSeed steps seed >>=
              fun priorValues =>
              (fun next : Digest => priorValues.push next) <$>
                ($ᵗ Digest)) := by
          exact (ih seed cache (by omega)).bind_left _
        _ =ᵈ (uniformTrajectoryFromSeed (steps + 1) seed) := by
          simp [uniformTrajectoryFromSeed_succ, map_eq_bind_pure_comp]

noncomputable def uniformFixedChainTrajectories
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : List ChainKey →
      ProbComp (List (Vector Digest (steps + 1)))
  | [] => pure []
  | key :: keys => do
      let first ← uniformTrajectoryFromSeed steps (start key chain)
      let rest ← uniformFixedChainTrajectories start chain steps keys
      pure (first :: rest)

@[simp]
theorem uniformFixedChainTrajectories_nil
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) :
    uniformFixedChainTrajectories start chain steps [] = pure [] := rfl

theorem uniformFixedChainTrajectories_cons
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) (key : ChainKey) (keys : List ChainKey) :
    uniformFixedChainTrajectories start chain steps (key :: keys) = (do
      let first ← uniformTrajectoryFromSeed steps (start key chain)
      let rest ← uniformFixedChainTrajectories start chain steps keys
      pure (first :: rest)) := rfl

def fixedChainTrajectoryDrawTape {steps : Nat}
    (trajectories : List (Vector Digest (steps + 1))) : List Digest :=
  trajectories.flatMap trajectoryDrawTape

theorem evalDist_uniformFixedChainTrajectories_drawTape
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : ∀ keys : List ChainKey,
    (fixedChainTrajectoryDrawTape <$>
      uniformFixedChainTrajectories start chain steps keys) =ᵈ
      (OracleComp.drawList ($ᵗ Digest)
        (keys.length * steps)) := by
  intro keys
  induction keys with
  | nil => simp [fixedChainTrajectoryDrawTape, OracleComp.drawList]
  | cons key keys ih =>
      rw [uniformFixedChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      calc
        _ =ᵈ (uniformTrajectoryFromSeed steps
              (start key chain) >>= fun first =>
            uniformFixedChainTrajectories start chain steps keys >>=
              fun rest =>
            pure (trajectoryDrawTape first ++
              fixedChainTrajectoryDrawTape rest)) := by
          simp [fixedChainTrajectoryDrawTape]
        _ =ᵈ ((trajectoryDrawTape <$>
              uniformTrajectoryFromSeed steps (start key chain)) >>=
            fun first =>
            (fixedChainTrajectoryDrawTape <$>
              uniformFixedChainTrajectories start chain steps keys) >>=
            fun rest => pure (first ++ rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (OracleComp.drawList ($ᵗ Digest) steps >>= fun first =>
            OracleComp.drawList ($ᵗ Digest) (keys.length * steps) >>=
              fun rest => pure (first ++ rest)) := by
          exact ((evalDist_uniformTrajectoryFromSeed_drawTape steps
              (start key chain)).bind_left _).trans
            (EvalDistEq.bind_right _ fun _ => ih.bind_left _)
        _ =ᵈ (OracleComp.drawList ($ᵗ Digest)
              (steps + keys.length * steps)) := by
          rw [drawList_append]
        _ =ᵈ (OracleComp.drawList ($ᵗ Digest)
              ((key :: keys).length * steps)) := by
          refine .of_eq ?_
          congr 2
          simp only [List.length_cons]
          simp [Nat.add_mul, Nat.add_comm]

set_option maxRecDepth 100000 in
theorem evalDist_programmedFixedChainTrajectories_fst_eq_uniform
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    ∀ (keys : List ChainKey) (cache : QueryCache HashSpec),
      (Prod.fst <$>
        programmedFixedSeedChainTrajectoriesFromCache parameter start chain
          steps cache keys) =ᵈ
      (uniformFixedChainTrajectories start chain steps keys) := by
  intro keys
  induction keys with
  | nil =>
      intro cache
      rfl
  | cons key keys ih =>
      intro cache
      rw [programmedFixedSeedChainTrajectoriesFromCache_cons,
        uniformFixedChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      let firstProgram := programmedChainTrajectory parameter key chain 0
        steps (start key chain) cache
      calc
        _ =ᵈ (firstProgram >>= fun first =>
              uniformFixedChainTrajectories start chain steps keys >>=
                fun rest =>
              pure (first.1 :: rest)) := by
          apply EvalDistEq.bind_right
          intro first
          calc
            _ =ᵈ ((fun rest => first.1 :: rest) <$>
                  (Prod.fst <$>
                    programmedFixedSeedChainTrajectoriesFromCache parameter
                      start chain steps first.2 keys)) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ =ᵈ ((fun rest => first.1 :: rest) <$>
                  uniformFixedChainTrajectories start chain steps keys) := by
              exact (ih first.2).map _
            _ = _ := by
              simp [map_eq_bind_pure_comp]
        _ =ᵈ ((Prod.fst <$> firstProgram) >>= fun first =>
              uniformFixedChainTrajectories start chain steps keys >>=
                fun rest =>
              pure (first :: rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (uniformTrajectoryFromSeed steps (start key chain) >>=
              fun first =>
              uniformFixedChainTrajectories start chain steps keys >>=
                fun rest =>
              pure (first :: rest)) := by
          exact (evalDist_programmedChainTrajectory_fst_eq_uniform parameter key
              chain 0 steps (start key chain) cache (by simpa using hsteps)).bind_left _
        _ = _ := by
          simp only [bind_pure_comp]

noncomputable def uniformAllChainTrajectories
    (start : ChainKey → ChainIndex → Digest) :
    List ChainIndex → ProbComp AllChainTrajectories
  | [] => pure (fun _ => [])
  | chain :: chains => do
      let first ← uniformFixedChainTrajectories start chain
        (chainLength - 1) allChainKeys
      let rest ← uniformAllChainTrajectories start chains
      pure (Function.update rest chain first)

@[simp]
theorem uniformAllChainTrajectories_nil
    (start : ChainKey → ChainIndex → Digest) :
    uniformAllChainTrajectories start [] = pure (fun _ => []) := rfl

theorem uniformAllChainTrajectories_cons
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (chains : List ChainIndex) :
    uniformAllChainTrajectories start (chain :: chains) = (do
      let first ← uniformFixedChainTrajectories start chain
        (chainLength - 1) allChainKeys
      let rest ← uniformAllChainTrajectories start chains
      pure (Function.update rest chain first)) := rfl

theorem uniformTrajectoryFromSeed_support_first :
    ∀ (steps : Nat) (seed : Digest)
      (trajectory : Vector Digest (steps + 1)),
      trajectory ∈ support (uniformTrajectoryFromSeed steps seed) →
      trajectory[0]'(by omega) = seed := by
  intro steps
  induction steps with
  | zero =>
      intro seed trajectory htrajectory
      simp only [uniformTrajectoryFromSeed_zero, support_pure,
        Set.mem_singleton_iff] at htrajectory
      subst trajectory
      rw [Vector.getElem_ofFn]
  | succ steps ih =>
      intro seed trajectory htrajectory
      rw [uniformTrajectoryFromSeed_succ, mem_support_bind_iff] at htrajectory
      obtain ⟨prior, hprior, hnext⟩ := htrajectory
      rw [mem_support_bind_iff] at hnext
      obtain ⟨next, _hnext, hpure⟩ := hnext
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst trajectory
      rw [Vector.getElem_push_lt (by omega)]
      exact ih seed prior hprior

theorem uniformFixedChainTrajectories_support_info
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (steps : Nat) : ∀ (keys : List ChainKey)
      (trajectories : List (Vector Digest (steps + 1))),
      trajectories ∈ support
        (uniformFixedChainTrajectories start chain steps keys) →
      trajectories.length = keys.length ∧
        List.Forall₂
          (fun key trajectory =>
            trajectory[0]'(by omega) = start key chain)
          keys trajectories := by
  intro keys
  induction keys with
  | nil =>
      intro trajectories htrajectories
      simp only [uniformFixedChainTrajectories_nil, support_pure,
        Set.mem_singleton_iff] at htrajectories
      subst trajectories
      exact ⟨rfl, List.Forall₂.nil⟩
  | cons key keys ih =>
      intro trajectories htrajectories
      rw [uniformFixedChainTrajectories_cons,
        mem_support_bind_iff] at htrajectories
      obtain ⟨first, hfirst, hrest⟩ := htrajectories
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst trajectories
      have hrestInfo := ih rest hrest
      constructor
      · simp [hrestInfo.1]
      · exact List.Forall₂.cons
          (uniformTrajectoryFromSeed_support_first steps
            (start key chain) first hfirst)
          hrestInfo.2

theorem uniformAllChainTrajectories_support_info
    (start : ChainKey → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (trajectories : AllChainTrajectories),
      chains.Nodup →
      trajectories ∈ support (uniformAllChainTrajectories start chains) →
      ∀ chain ∈ chains,
        (trajectories chain).length = Fintype.card ChainKey ∧
          List.Forall₂
            (fun key trajectory =>
              trajectory[0]'(by omega) = start key chain)
            allChainKeys (trajectories chain) := by
  intro chains
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      intro trajectories hnodup htrajectories
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [uniformAllChainTrajectories_cons,
        mem_support_bind_iff] at htrajectories
      obtain ⟨first, hfirst, hrest⟩ := htrajectories
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst trajectories
      have hfirstInfo := uniformFixedChainTrajectories_support_info start
        chain (chainLength - 1) allChainKeys first hfirst
      have hrestInfo := ih rest htailNodup hrest
      intro selected hselected
      by_cases heq : selected = chain
      · subst selected
        simp only [Function.update_self]
        exact ⟨by simpa [allChainKeys_length] using hfirstInfo.1,
          hfirstInfo.2⟩
      · have htail : selected ∈ chains := by
          simpa [heq] using hselected
        simp only [Function.update_of_ne heq]
        exact hrestInfo selected htail

theorem chainValueTableOfList_zero_eq_of_forall₂
    (start : ChainKey → ChainIndex → Digest) (chain : ChainIndex)
    (trajectories : List FullChainTrajectory)
    (hlength : trajectories.length = Fintype.card ChainKey)
    (hseeds : List.Forall₂
      (fun key trajectory =>
        trajectory[0]'(by simp [chainLength]) = start key chain)
      allChainKeys trajectories) (key : ChainKey) :
    chainValueTableOfList trajectories
        (key, ⟨0, by simp [chainLength]⟩) =
      start key chain := by
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := chainKeyPosition key
    have htrajectoryPosition : position.val < trajectories.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hseeds.get position.isLt htrajectoryPosition
    have hkey : allChainKeys.get position = key :=
      allChainKeys_get_chainKeyPosition key
    rw [hkey] at hpair
    simpa [FullChainTrajectory.toDigitTable] using hpair
  · rename_i htableLength
    exact (htableLength (allChainKeys_length.trans hlength.symm)).elim

theorem uniformAllChainTrajectories_support_seeds
    (start : ChainKey → ChainIndex → Digest)
    (trajectories : AllChainTrajectories)
    (htrajectories : trajectories ∈ support
      (uniformAllChainTrajectories start allChains)) :
    globalChainTableSeedTargets
        (globalChainValueTableOfTrajectories trajectories) = start := by
  have hinfo := uniformAllChainTrajectories_support_info start allChains
    trajectories allChains_nodup htrajectories
  funext key chain
  have hchain := hinfo chain (mem_allChains chain)
  exact chainValueTableOfList_zero_eq_of_forall₂ start chain
    (trajectories chain) hchain.1 hchain.2 key

def allChainTrajectoryDrawTape
    (trajectories : AllChainTrajectories) :
    List ChainIndex → List Digest
  | [] => []
  | chain :: chains =>
      fixedChainTrajectoryDrawTape (trajectories chain) ++
        allChainTrajectoryDrawTape trajectories chains

@[simp]
theorem allChainTrajectoryDrawTape_nil
    (trajectories : AllChainTrajectories) :
    allChainTrajectoryDrawTape trajectories [] = [] := rfl

theorem allChainTrajectoryDrawTape_update_of_not_mem
    (trajectories : AllChainTrajectories) (chain : ChainIndex)
    (values : List FullChainTrajectory) : ∀ chains : List ChainIndex,
    chain ∉ chains →
    allChainTrajectoryDrawTape (Function.update trajectories chain values)
        chains =
      allChainTrajectoryDrawTape trajectories chains := by
  intro chains
  induction chains with
  | nil => simp
  | cons current chains ih =>
      intro hnotMem
      have hne : current ≠ chain := by
        intro heq
        subst current
        exact hnotMem (by simp)
      have htail : chain ∉ chains := by
        intro hmem
        exact hnotMem (by simp [hmem])
      simp [allChainTrajectoryDrawTape, Function.update_of_ne hne, ih htail]

theorem allChainTrajectoryDrawTape_update_cons
    (trajectories : AllChainTrajectories) (chain : ChainIndex)
    (values : List FullChainTrajectory) (chains : List ChainIndex)
    (hnotMem : chain ∉ chains) :
    allChainTrajectoryDrawTape
        (Function.update trajectories chain values) (chain :: chains) =
      fixedChainTrajectoryDrawTape values ++
        allChainTrajectoryDrawTape trajectories chains := by
  simp [allChainTrajectoryDrawTape,
    allChainTrajectoryDrawTape_update_of_not_mem trajectories chain values
      chains hnotMem]

theorem evalDist_uniformAllChainTrajectories_drawTape
    (start : ChainKey → ChainIndex → Digest) :
    ∀ chains : List ChainIndex, chains.Nodup →
    ((fun trajectories =>
      allChainTrajectoryDrawTape trajectories chains) <$>
        uniformAllChainTrajectories start chains) =ᵈ
      (OracleComp.drawList ($ᵗ Digest)
        (chains.length * (allChainKeys.length * (chainLength - 1)))) := by
  intro chains
  induction chains with
  | nil =>
      intro _hnodup
      simp [OracleComp.drawList]
  | cons chain chains ih =>
      intro hnodup
      obtain ⟨hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [uniformAllChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      let blockSize := allChainKeys.length * (chainLength - 1)
      calc
        _ =ᵈ (uniformFixedChainTrajectories start chain
              (chainLength - 1) allChainKeys >>= fun first =>
            uniformAllChainTrajectories start chains >>= fun rest =>
            pure (fixedChainTrajectoryDrawTape first ++
              allChainTrajectoryDrawTape rest chains)) := by
          apply EvalDistEq.bind_right
          intro first
          calc
            _ =ᵈ ((fun rest => allChainTrajectoryDrawTape
                  (Function.update rest chain first) (chain :: chains)) <$>
                uniformAllChainTrajectories start chains) := by
              rw [Functor.map_map]
            _ =ᵈ ((fun rest => fixedChainTrajectoryDrawTape first ++
                  allChainTrajectoryDrawTape rest chains) <$>
                uniformAllChainTrajectories start chains) := by
              refine .of_eq ?_
              congr 1
              funext rest
              exact allChainTrajectoryDrawTape_update_cons rest chain first
                chains hnotMem
            _ = _ := by
              simp [map_eq_bind_pure_comp]
        _ =ᵈ ((fixedChainTrajectoryDrawTape <$>
              uniformFixedChainTrajectories start chain
                (chainLength - 1) allChainKeys) >>= fun first =>
            ((fun rest => allChainTrajectoryDrawTape rest chains) <$>
              uniformAllChainTrajectories start chains) >>= fun rest =>
            pure (first ++ rest)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (OracleComp.drawList ($ᵗ Digest) blockSize >>=
            fun first =>
            OracleComp.drawList ($ᵗ Digest)
              (chains.length * blockSize) >>= fun rest =>
            pure (first ++ rest)) := by
          exact ((evalDist_uniformFixedChainTrajectories_drawTape start chain
              (chainLength - 1) allChainKeys).bind_left _).trans
            (EvalDistEq.bind_right _ fun _ => (ih htailNodup).bind_left _)
        _ =ᵈ (OracleComp.drawList ($ᵗ Digest)
              (blockSize + chains.length * blockSize)) := by
          rw [drawList_append]
        _ =ᵈ (OracleComp.drawList ($ᵗ Digest)
              ((chain :: chains).length *
                (allChainKeys.length * (chainLength - 1)))) := by
          refine .of_eq ?_
          congr 2
          dsimp only [blockSize]
          simp [Nat.add_mul, Nat.add_comm]

noncomputable def globalTrajectoryEdgeTableTapeEquiv :
    (GlobalChainEdgeIndex → Digest) ≃
      (Fin globalTrajectoryEdgeOrder.length → Digest) :=
  (Equiv.piCongrLeft (fun _ : GlobalChainEdgeIndex => Digest)
    (globalTrajectoryEdgeOrder_nodup.getEquivOfForallMemList
      globalTrajectoryEdgeOrder mem_globalTrajectoryEdgeOrder)).symm

theorem listOfFn_globalTrajectoryEdgeTableTapeEquiv
    (table : GlobalChainEdgeIndex → Digest) :
    List.ofFn (globalTrajectoryEdgeTableTapeEquiv table) =
      globalTrajectoryEdgeOrder.map table := by
  rw [← List.ofFn_get (globalTrajectoryEdgeOrder.map table)]
  apply List.ext_get
  · simp
  · intro index hleft hright
    simp [globalTrajectoryEdgeTableTapeEquiv]

noncomputable def globalTrajectoryEdgeTableOfTape
    (targets : List Digest) : GlobalChainEdgeIndex → Digest :=
  if hlength : targets.length = globalTrajectoryEdgeOrder.length then
    globalTrajectoryEdgeTableTapeEquiv.symm fun index =>
      targets.get (Fin.cast hlength.symm index)
  else
    fun _ => 0

@[simp]
theorem globalTrajectoryEdgeTableOfTape_map
    (table : GlobalChainEdgeIndex → Digest) :
    globalTrajectoryEdgeTableOfTape
      (globalTrajectoryEdgeOrder.map table) = table := by
  unfold globalTrajectoryEdgeTableOfTape
  split
  · rename_i hlength
    apply globalTrajectoryEdgeTableTapeEquiv.injective
    rw [globalTrajectoryEdgeTableTapeEquiv.apply_symm_apply]
    funext index
    simp [globalTrajectoryEdgeTableTapeEquiv]
  · rename_i hlength
    exact (hlength (by simp)).elim

theorem evalDist_uniformGlobalTrajectoryEdgeTableTape_eq_drawList :
    ((fun table : GlobalChainEdgeIndex → Digest =>
      globalTrajectoryEdgeOrder.map table) <$>
        ($ᵗ (GlobalChainEdgeIndex → Digest))) =ᵈ
      (OracleComp.drawList ($ᵗ Digest)
        globalTrajectoryEdgeOrder.length) := by
  calc
    _ =ᵈ (List.ofFn <$>
        (globalTrajectoryEdgeTableTapeEquiv <$>
          ($ᵗ (GlobalChainEdgeIndex → Digest)))) := by
      simp only [Functor.map_map]
      refine .of_eq ?_
      congr 1
      funext table
      exact (listOfFn_globalTrajectoryEdgeTableTapeEquiv table).symm
    _ =ᵈ (List.ofFn <$>
        ($ᵗ (Fin globalTrajectoryEdgeOrder.length → Digest))) :=
      (SampleableType.map_uniformSample_evalDistEq_of_bijective
        globalTrajectoryEdgeTableTapeEquiv.bijective).map _
    _ =ᵈ (OracleComp.drawList ($ᵗ Digest)
        globalTrajectoryEdgeOrder.length) :=
      evalDist_listOfFn_uniform_eq_drawList
        globalTrajectoryEdgeOrder.length

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_globalTrajectoryEdgeTableOfTape_drawList_eq_uniform :
    (globalTrajectoryEdgeTableOfTape <$>
      OracleComp.drawList ($ᵗ Digest)
        globalTrajectoryEdgeOrder.length) =ᵈ
      ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ =ᵈ (globalTrajectoryEdgeTableOfTape <$>
        ((fun table : GlobalChainEdgeIndex → Digest =>
          globalTrajectoryEdgeOrder.map table) <$>
            ($ᵗ (GlobalChainEdgeIndex → Digest)))) :=
      evalDist_uniformGlobalTrajectoryEdgeTableTape_eq_drawList.symm.map _
    _ =ᵈ ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
      simp [Functor.map_map]

noncomputable def globalChainEdgeTableOfTrajectories
    (trajectories : AllChainTrajectories) :
    GlobalChainEdgeIndex → Digest := fun edge =>
  chainValueTableOfList (trajectories edge.1)
    (edge.2.1, chainStepNextDigit edge.2.2)

theorem fixedChainTrajectoryDrawTape_eq_edgeMap
    (trajectories : List FullChainTrajectory)
    (hlength : trajectories.length = Fintype.card ChainKey) :
    fixedChainTrajectoryDrawTape trajectories =
      (allChainKeys ×ˢ trajectoryChainSteps).map fun edge =>
        chainValueTableOfList trajectories
          (edge.1, chainStepNextDigit edge.2) := by
  let table := chainValueTableOfList trajectories
  have hinverse : listOfChainValueTable table = trajectories :=
    listOfChainValueTable_chainValueTableOfList trajectories hlength
  conv_lhs => rw [← hinverse]
  change List.flatMap trajectoryDrawTape (allChainKeys.map fun key =>
      FullChainTrajectory.ofDigitTable fun digit => table (key, digit)) =
    (allChainKeys ×ˢ trajectoryChainSteps).map fun edge =>
      table (edge.1, chainStepNextDigit edge.2)
  have hgeneral : ∀ keys : List ChainKey,
      List.flatMap trajectoryDrawTape (keys.map fun key =>
        FullChainTrajectory.ofDigitTable fun digit => table (key, digit)) =
      (keys ×ˢ trajectoryChainSteps).map fun edge =>
        table (edge.1, chainStepNextDigit edge.2) := by
    intro keys
    induction keys with
    | nil => simp
    | cons key keys ih =>
        rw [List.map_cons, List.flatMap_cons, List.product_cons,
          List.map_append, ih]
        rw [trajectoryDrawTape_ofDigitTable]
        simp
  exact hgeneral allChainKeys

theorem allChainTrajectoryDrawTape_eq_edgeMap
    (trajectories : AllChainTrajectories) :
    ∀ chains : List ChainIndex,
      (∀ chain ∈ chains, (trajectories chain).length = Fintype.card ChainKey) →
      allChainTrajectoryDrawTape trajectories chains =
        (chains ×ˢ (allChainKeys ×ˢ trajectoryChainSteps)).map
          (globalChainEdgeTableOfTrajectories trajectories) := by
  intro chains
  induction chains with
  | nil => simp
  | cons chain chains ih =>
      intro hlength
      have hhead := hlength chain (by simp)
      have htail : ∀ selected ∈ chains,
          (trajectories selected).length = Fintype.card ChainKey := by
        intro selected hselected
        exact hlength selected (by simp [hselected])
      rw [allChainTrajectoryDrawTape, List.product_cons, List.map_append, ih htail]
      rw [fixedChainTrajectoryDrawTape_eq_edgeMap (trajectories chain) hhead]
      simp [globalChainEdgeTableOfTrajectories]

theorem globalTrajectoryEdgeTableOfTape_drawTape
    (trajectories : AllChainTrajectories)
    (hlength : ∀ chain, (trajectories chain).length = Fintype.card ChainKey) :
    globalTrajectoryEdgeTableOfTape
        (allChainTrajectoryDrawTape trajectories allChains) =
      globalChainEdgeTableOfTrajectories trajectories := by
  rw [allChainTrajectoryDrawTape_eq_edgeMap trajectories allChains
    (fun chain _hchain => hlength chain)]
  exact globalTrajectoryEdgeTableOfTape_map
    (globalChainEdgeTableOfTrajectories trajectories)

set_option maxRecDepth 100000 in
theorem evalDist_uniformAllChainTrajectories_edgeTable_eq_uniform
    (start : ChainKey → ChainIndex → Digest) :
    (globalChainEdgeTableOfTrajectories <$>
      uniformAllChainTrajectories start allChains) =ᵈ
      ($ᵗ (GlobalChainEdgeIndex → Digest)) := by
  calc
    _ =ᵈ (globalTrajectoryEdgeTableOfTape <$>
          ((fun trajectories =>
            allChainTrajectoryDrawTape trajectories allChains) <$>
              uniformAllChainTrajectories start allChains)) := by
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind,
        Function.comp_apply]
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro trajectories htrajectories
      have hinfo := uniformAllChainTrajectories_support_info start allChains
        trajectories allChains_nodup htrajectories
      rw [globalTrajectoryEdgeTableOfTape_drawTape trajectories
        (fun chain => (hinfo chain (mem_allChains chain)).1)]
      simp
    _ =ᵈ (globalTrajectoryEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest)
            (allChains.length *
              (allChainKeys.length * (chainLength - 1)))) := by
      exact (evalDist_uniformAllChainTrajectories_drawTape start allChains
          allChains_nodup).map _
    _ =ᵈ (globalTrajectoryEdgeTableOfTape <$>
          OracleComp.drawList ($ᵗ Digest)
            globalTrajectoryEdgeOrder.length) := by
      rw [globalTrajectoryEdgeOrder_length]
    _ =ᵈ ($ᵗ (GlobalChainEdgeIndex → Digest)) :=
      evalDist_globalTrajectoryEdgeTableOfTape_drawList_eq_uniform

theorem globalChainTableMaterialEquiv_trajectories
    (start : ChainKey → ChainIndex → Digest)
    (trajectories : AllChainTrajectories)
    (htrajectories : trajectories ∈ support
      (uniformAllChainTrajectories start allChains)) :
    globalChainTableMaterialEquiv
        (globalChainValueTableOfTrajectories trajectories) =
      (start, globalChainEdgeTableOfTrajectories trajectories) := by
  apply Prod.ext
  · exact uniformAllChainTrajectories_support_seeds start trajectories
      htrajectories
  · rfl

noncomputable def uniformGlobalChainTableFromTrajectories :
    ProbComp (GlobalChainValueIndex → Digest) := do
  let start ← Concrete.sampleChainStarts
  let trajectories ← uniformAllChainTrajectories start allChains
  pure (globalChainValueTableOfTrajectories trajectories)

noncomputable def sampleSecretGlobalChainMaterial :
    ProbComp ((ChainKey → ChainIndex → Digest) ×
      (GlobalChainEdgeIndex → Digest)) :=
  Prod.mk <$> Concrete.sampleChainStarts <*>
    ($ᵗ (GlobalChainEdgeIndex → Digest))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem evalDist_sampleSecretGlobalChainMaterial_eq_independent :
    sampleSecretGlobalChainMaterial =ᵈ independentGlobalChainTableMaterial := by
  rw [sampleSecretGlobalChainMaterial, independentGlobalChainTableMaterial]
  exact prod_seq_evalDistEq_left Concrete.evalDist_sampleChainStarts_eq_uniform _

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 2000000 in
theorem evalDist_uniformGlobalChainTableFromTrajectories_eq_uniform :
    uniformGlobalChainTableFromTrajectories =ᵈ ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold uniformGlobalChainTableFromTrajectories
  calc
    _ =ᵈ (Concrete.sampleChainStarts >>= fun start =>
          uniformAllChainTrajectories start allChains >>= fun trajectories =>
          pure (globalChainTableMaterialEquiv.symm
            (start, globalChainEdgeTableOfTrajectories trajectories))) := by
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro start _hsecret
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro trajectories htrajectories
      rw [← globalChainTableMaterialEquiv_trajectories start trajectories
        htrajectories, globalChainTableMaterialEquiv.symm_apply_apply]
    _ =ᵈ (Concrete.sampleChainStarts >>= fun start =>
          (globalChainEdgeTableOfTrajectories <$>
            uniformAllChainTrajectories start allChains) >>= fun edges =>
          pure (globalChainTableMaterialEquiv.symm (start, edges))) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ =ᵈ (Concrete.sampleChainStarts >>= fun start =>
          ($ᵗ (GlobalChainEdgeIndex → Digest)) >>= fun edges =>
          pure (globalChainTableMaterialEquiv.symm (start, edges))) := by
      apply EvalDistEq.bind_right
      intro start
      exact (evalDist_uniformAllChainTrajectories_edgeTable_eq_uniform start).bind_left _
    _ =ᵈ (globalChainTableMaterialEquiv.symm <$>
          sampleSecretGlobalChainMaterial) := by
      simp [sampleSecretGlobalChainMaterial, monad_norm]
    _ =ᵈ (globalChainTableMaterialEquiv.symm <$>
          independentGlobalChainTableMaterial) := by
      exact EvalDistEq.map
        evalDist_sampleSecretGlobalChainMaterial_eq_independent
        globalChainTableMaterialEquiv.symm
    _ =ᵈ ($ᵗ (GlobalChainValueIndex → Digest)) := by
      have h := EvalDistEq.map
        evalDist_split_uniformGlobalChainTable_eq_independent
        globalChainTableMaterialEquiv.symm
      simpa [Functor.map_map] using h.symm

set_option maxRecDepth 100000 in
theorem evalDist_programmedAllChainTrajectories_fst_eq_uniform
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec),
      (Prod.fst <$>
        programmedAllChainTrajectoriesFromCache parameter start cache chains) =ᵈ
      (uniformAllChainTrajectories start chains) := by
  intro chains
  induction chains with
  | nil =>
      intro cache
      simp
  | cons chain chains ih =>
      intro cache
      rw [programmedAllChainTrajectoriesFromCache_cons,
        uniformAllChainTrajectories_cons]
      simp only [map_bind, bind_pure_comp]
      let firstProgram := programmedFixedSeedChainTrajectoriesFromCache
        parameter start chain (chainLength - 1) cache allChainKeys
      calc
        _ =ᵈ (firstProgram >>= fun first =>
              uniformAllChainTrajectories start chains >>= fun rest =>
              pure (Function.update rest chain first.1)) := by
          apply EvalDistEq.bind_right
          intro first
          calc
            _ =ᵈ ((fun rest => Function.update rest chain first.1) <$>
                  (Prod.fst <$>
                    programmedAllChainTrajectoriesFromCache parameter start
                      first.2 chains)) := by
              simp [map_eq_bind_pure_comp, bind_assoc]
            _ =ᵈ ((fun rest => Function.update rest chain first.1) <$>
                  uniformAllChainTrajectories start chains) := by
              exact (ih first.2).map _
            _ = _ := by
              simp [map_eq_bind_pure_comp]
        _ =ᵈ ((Prod.fst <$> firstProgram) >>= fun first =>
              uniformAllChainTrajectories start chains >>= fun rest =>
              pure (Function.update rest chain first)) := by
          simp [map_eq_bind_pure_comp, bind_assoc]
        _ =ᵈ (uniformFixedChainTrajectories start chain
              (chainLength - 1) allChainKeys >>= fun first =>
              uniformAllChainTrajectories start chains >>= fun rest =>
              pure (Function.update rest chain first)) := by
          exact (evalDist_programmedFixedChainTrajectories_fst_eq_uniform parameter
              start chain (chainLength - 1) le_rfl allChainKeys cache).bind_left _
        _ = _ := by
          simp only [bind_pure_comp]

theorem evalDist_run_eq_allChainTrajectories_then {α : Type} (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (computation : OracleComp HashSpec α)
    (hcovers : CoversKeyChains parameter start computation)
    (chains : List ChainIndex) (initialCache : QueryCache HashSpec) :
    ((simulateQ randomOracle computation).run initialCache) =ᵈ
      (Concrete.allChainTrajectoriesFromCache parameter start initialCache chains >>=
        fun trajectoryResult => (simulateQ randomOracle computation).run trajectoryResult.2) := by
  induction chains generalizing initialCache with
  | nil => simp
  | cons chain chains ih =>
      calc
        _ =ᵈ (Concrete.fixedSeedChainTrajectoriesFromCache parameter start
              chain (chainLength - 1) initialCache allChainKeys >>= fun first =>
            (simulateQ randomOracle computation).run first.2) :=
          evalDist_run_eq_fixedSeedTrajectories_then parameter start computation hcovers
            chain (chainLength - 1) le_rfl allChainKeys initialCache
        _ =ᵈ (Concrete.fixedSeedChainTrajectoriesFromCache parameter
              start chain (chainLength - 1) initialCache allChainKeys >>= fun first =>
            Concrete.allChainTrajectoriesFromCache parameter start first.2
              chains >>= fun rest =>
            (simulateQ randomOracle computation).run rest.2) := by
          apply EvalDistEq.bind_right
          intro first
          exact ih first.2
        _ =ᵈ _ := by
          rw [Concrete.allChainTrajectoriesFromCache_cons]
          simp only [bind_assoc, pure_bind, EvalDistEq.refl]

noncomputable def allChainTrajectoryKeygen :
    ProbComp (ProgrammedGlobalChainKeygenView × AllChainTrajectories) := do
  let parameter ← Concrete.samplePublicParameter
  let start ← Concrete.sampleChainStarts
  let topBase ← Concrete.sampleTopBase
  let trajectoryResult ← Concrete.allChainTrajectoriesFromCache parameter start ∅ allChains
  let run ← (simulateQ randomOracle (Concrete.honestKeygenFrom parameter start topBase)).run
    trajectoryResult.2
  pure (keygenViewOfRun parameter start run, trajectoryResult.1)

noncomputable def programmedAllChainTrajectoryKeygen :
    ProbComp (ProgrammedGlobalChainKeygenView × AllChainTrajectories) := do
  let parameter ← Concrete.samplePublicParameter
  let start ← Concrete.sampleChainStarts
  let trajectoryResult ← programmedAllChainTrajectoriesFromCache parameter start ∅ allChains
  let topBase ← Concrete.sampleTopBase
  let run ← (simulateQ randomOracle (Concrete.honestKeygenFrom parameter start topBase)).run
    trajectoryResult.2
  pure (keygenViewOfRun parameter start run, trajectoryResult.1)

theorem evalDist_allChainTrajectoryKeygen_eq_programmed :
    allChainTrajectoryKeygen =ᵈ programmedAllChainTrajectoryKeygen := by
  unfold allChainTrajectoryKeygen programmedAllChainTrajectoryKeygen
  apply EvalDistEq.bind_right
  intro parameter
  apply EvalDistEq.bind_right
  intro start
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  exact (evalDist_allChainTrajectories_eq_programmed parameter start allChains ∅
    allChains_nodup (by simp [AllChainAddressesAbsent])).bind_left _

def eraseAllChainTrajectories
    (result : ProgrammedGlobalChainKeygenView × AllChainTrajectories) :
    ProgrammedGlobalChainKeygenView := result.1

theorem evalDist_explicitGlobalChainKeygen_eq_allChainTrajectoryKeygen :
    explicitGlobalChainKeygen =ᵈ (eraseAllChainTrajectories <$> allChainTrajectoryKeygen) := by
  unfold explicitGlobalChainKeygen allChainTrajectoryKeygen
    eraseAllChainTrajectories
  simp only [map_bind, map_pure]
  apply EvalDistEq.bind_right
  intro parameter
  apply EvalDistEq.bind_right
  intro start
  apply EvalDistEq.bind_right
  intro topBase
  refine ((evalDist_run_eq_allChainTrajectories_then parameter start _
    (honestKeygenFrom_coversKeyChains parameter start topBase) allChains ∅).bind_left _).trans
      (.of_eq ?_)
  simp only [bind_assoc]

theorem evalDist_actualGlobalChainKeygen_eq_allChainTrajectoryKeygen :
    actualGlobalChainKeygen =ᵈ (eraseAllChainTrajectories <$> allChainTrajectoryKeygen) :=
  evalDist_actualGlobalChainKeygen_eq_explicit.trans
    evalDist_explicitGlobalChainKeygen_eq_allChainTrajectoryKeygen

theorem evalDist_actualGlobalChainKeygen_eq_programmedAllChainTrajectories :
    actualGlobalChainKeygen =ᵈ (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
  calc
    _ =ᵈ (eraseAllChainTrajectories <$>
        allChainTrajectoryKeygen) :=
      evalDist_actualGlobalChainKeygen_eq_allChainTrajectoryKeygen
    _ =ᵈ (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
      exact evalDist_allChainTrajectoryKeygen_eq_programmed.map _

theorem Concrete.fixedSeedChainTrajectoriesFromCache_component_support
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (keys : List ChainKey) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (target : ChainKey),
      target ∈ keys →
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain
          steps cache keys) →
      ∃ before after trajectory,
        (trajectory, after) ∈ support
          ((simulateQ randomOracle
            (Concrete.chainTrajectory parameter target chain 0 steps
              (start target chain))).run before) ∧
        after ≤ result.2 := by
  intro keys
  induction keys with
  | nil =>
      intro _cache _result target htarget _hresult
      simp at htarget
  | cons key keys ih =>
      intro cache result target htarget hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      rw [List.mem_cons] at htarget
      rcases htarget with rfl | htarget
      · have hrestInfo :=
          Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
            start chain steps keys first.2 rest hrest
        exact ⟨cache, first.2, first.1, hfirst, hrestInfo.1⟩
      · exact ih first.2 rest target htarget hrest

theorem Concrete.allChainTrajectoriesFromCache_chain_component_support
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec)
      (selected : ChainIndex),
      chains.Nodup →
      selected ∈ chains →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter start cache chains) →
      ∃ before after trajectories,
        (trajectories, after) ∈ support
          (Concrete.fixedSeedChainTrajectoriesFromCache parameter start
            selected (chainLength - 1) before allChainKeys) ∧
        after ≤ result.2 := by
  intro chains
  induction chains with
  | nil =>
      intro _cache _result selected _hnodup hselected _hresult
      simp at hselected
  | cons chain chains ih =>
      intro cache result selected hnodup hselected hresult
      obtain ⟨_hnotMem, htailNodup⟩ := List.nodup_cons.mp hnodup
      rw [Concrete.allChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      rw [List.mem_cons] at hselected
      rcases hselected with rfl | hselected
      · have hrestInfo :=
          Concrete.allChainTrajectoriesFromCache_support_info parameter start
            chains first.2 rest htailNodup hrest
        exact ⟨cache, first.2, first.1, hfirst, hrestInfo.1⟩
      · exact ih first.2 rest selected htailNodup hselected hrest

/-- The chain trajectories warm every chain of both layers. -/
theorem Concrete.allChainTrajectoriesFromCache_chainsWarm
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (initialCache : QueryCache HashSpec)
    (result : AllChainTrajectories × QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter start initialCache allChains)) :
    ChainsWarm parameter start result.2 := by
  intro key chain steps hsteps
  obtain ⟨before, after, trajectories, htrajectories, hafter⟩ :=
    Concrete.allChainTrajectoriesFromCache_chain_component_support
      parameter start allChains initialCache result chain allChains_nodup
        (mem_allChains chain) hresult
  obtain ⟨walkBefore, walkAfter, trajectory, htrajectory, hwalkAfter⟩ :=
    Concrete.fixedSeedChainTrajectoriesFromCache_component_support
      parameter start chain (chainLength - 1) allChainKeys before
        (trajectories, after) key (mem_allChainKeys key) htrajectories
  have hmapped : (trajectory.back, walkAfter) ∈ support
      ((fun value : FullChainTrajectory × QueryCache HashSpec =>
        (value.1.back, value.2)) <$>
          (simulateQ randomOracle
            (Concrete.chainTrajectory parameter key chain 0
              (chainLength - 1) (start key chain))).run walkBefore) := by
    rw [support_map]
    exact ⟨(trajectory, walkAfter), htrajectory, rfl⟩
  have hwalk : (trajectory.back, walkAfter) ∈ support
      ((simulateQ randomOracle
        (Concrete.keyChainWalk parameter key chain 0 (chainLength - 1)
          (start key chain) : OracleComp HashSpec Digest)).run walkBefore) :=
    (OracleComp.support_eq_of_evalDistEq
      (evalDist_chainTrajectory_run_cache_eq_keyChainWalk_run_cache
        parameter key chain 0 (chainLength - 1) (start key chain)
          walkBefore)).subset hmapped
  exact Concrete.CacheReplay.RunsBelow.keyChainWalk_prefix steps hsteps
    ⟨walkBefore, walkAfter, trajectory.back, hwalk, hwalkAfter.trans hafter⟩

/-- The chain trajectories query nothing outside the chain addresses. -/
theorem Concrete.allChainTrajectoriesFromCache_none_of_notChain
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (domain : HashDomain)
    (hdomain : ∀ (key : ChainKey) chain step, key.chainDomain chain step ≠ domain)
    (input : HashInput) (haddress : AtHashAddress parameter domain input) :
    ∀ (chains : List ChainIndex) (cache : QueryCache HashSpec)
      (result : AllChainTrajectories × QueryCache HashSpec),
      cache input = none →
      result ∈ support
        (Concrete.allChainTrajectoriesFromCache parameter start cache chains) →
      result.2 input = none := by
  have hfixed : ∀ (chain : ChainIndex) (keys : List ChainKey) (cache : QueryCache HashSpec)
      (result : List FullChainTrajectory × QueryCache HashSpec),
      cache input = none →
      result ∈ support (Concrete.fixedSeedChainTrajectoriesFromCache parameter start
        chain (chainLength - 1) cache keys) →
      result.2 input = none := by
    intro chain keys
    induction keys with
    | nil =>
        intro cache result habsent hresult
        simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
          support_pure, Set.mem_singleton_iff] at hresult
        subst result
        exact habsent
    | cons key keys ih =>
        intro cache result habsent hresult
        rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
          mem_support_bind_iff] at hresult
        obtain ⟨first, hfirst, hrest⟩ := hresult
        rw [mem_support_bind_iff] at hrest
        obtain ⟨rest, hrest, hpure⟩ := hrest
        simp only [support_pure, Set.mem_singleton_iff] at hpure
        subst result
        apply ih first.2 rest _ hrest
        apply Concrete.CacheReplay.cache_none_of_zero_query_bound
          (Concrete.chainTrajectory parameter key chain 0 (chainLength - 1)
            (start key chain)) input cache first.2 first.1
        · apply OracleComp.IsQueryBoundP.of_imp
            (p' := AtHashAddress parameter domain)
          · intro candidate heq
            subst candidate
            exact haddress
          · apply Concrete.chainTrajectory_queryBound_zero_of_avoids
            intro offset _ hvalid
            exact hdomain key chain _
        · exact habsent
        · exact hfirst
  intro chains
  induction chains with
  | nil =>
      intro cache result habsent hresult
      simp only [Concrete.allChainTrajectoriesFromCache_nil, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      exact habsent
  | cons chain chains ih =>
      intro cache result habsent hresult
      rw [Concrete.allChainTrajectoriesFromCache_cons, mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      exact ih first.2 rest (hfixed chain allChainKeys cache first habsent hfirst) hrest

abbrev GlobalChainTrajectoryMaterial :=
  (ChainKey → ChainIndex → Digest) ×
    (AllChainTrajectories × QueryCache HashSpec)

noncomputable def globalChainTrajectoryMaterialTable
    (material : GlobalChainTrajectoryMaterial) :
    GlobalChainValueIndex → Digest :=
  globalChainValueTableOfTrajectories material.2.1

noncomputable def programmedGlobalChainTrajectoryMaterial
    (parameter : PublicParameter) : ProbComp GlobalChainTrajectoryMaterial := do
  let start ← Concrete.sampleChainStarts
  let trajectories ← programmedAllChainTrajectoriesFromCache parameter
    start ∅ allChains
  pure (start, trajectories)

noncomputable def programmedGlobalChainTrajectoryMaterialWithBase
    (parameter : PublicParameter) :
    ProbComp (GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) := do
  let base ← $ᵗ (GlobalChainValueIndex → Digest)
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  pure (material, base)

theorem programmedGlobalChainTrajectoryMaterial_support_trajectories
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    material.2 ∈ support
      (programmedAllChainTrajectoriesFromCache parameter material.1 ∅
        allChains) := by
  unfold programmedGlobalChainTrajectoryMaterial at hmaterial
  rw [mem_support_bind_iff] at hmaterial
  obtain ⟨start, _hsecret, htrajectories⟩ := hmaterial
  rw [mem_support_bind_iff] at htrajectories
  obtain ⟨trajectories, htrajectories, hpure⟩ := htrajectories
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst material
  exact htrajectories

theorem evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
    (parameter : PublicParameter) :
    (globalChainTrajectoryMaterialTable <$>
      programmedGlobalChainTrajectoryMaterial parameter) =ᵈ
      ($ᵗ (GlobalChainValueIndex → Digest)) := by
  unfold programmedGlobalChainTrajectoryMaterial
    globalChainTrajectoryMaterialTable
  simp only [map_eq_bind_pure_comp, bind_assoc]
  calc
    _ =ᵈ (Concrete.sampleChainStarts >>= fun start =>
          globalChainValueTableOfTrajectories <$>
            (Prod.fst <$> programmedAllChainTrajectoriesFromCache parameter
              start ∅ allChains)) := by
      apply EvalDistEq.bind_right
      intro start
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ =ᵈ (Concrete.sampleChainStarts >>= fun start =>
          globalChainValueTableOfTrajectories <$>
            uniformAllChainTrajectories start allChains) := by
      apply EvalDistEq.bind_right
      intro start
      exact (evalDist_programmedAllChainTrajectories_fst_eq_uniform parameter
          start allChains ∅).map _
    _ = uniformGlobalChainTableFromTrajectories := by
      simp only [uniformGlobalChainTableFromTrajectories, bind_pure_comp]
    _ =ᵈ ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_uniformGlobalChainTableFromTrajectories_eq_uniform

def globalChainTrajectoryMaterialBase
    (result : GlobalChainTrajectoryMaterial ×
      (GlobalChainValueIndex → Digest)) :
    GlobalChainValueIndex → Digest := result.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
set_option linter.constructorNameAsVariable false in
theorem evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_base
    (parameter : PublicParameter) :
    (globalChainTrajectoryMaterialTable <$>
        programmedGlobalChainTrajectoryMaterial parameter) =ᵈ
      (globalChainTrajectoryMaterialBase <$>
        programmedGlobalChainTrajectoryMaterialWithBase parameter) := by
  calc
    _ =ᵈ ($ᵗ (GlobalChainValueIndex → Digest)) :=
      evalDist_programmedGlobalChainTrajectoryMaterial_table_eq_uniform
        parameter
    _ =ᵈ (globalChainTrajectoryMaterialBase <$>
        programmedGlobalChainTrajectoryMaterialWithBase parameter) := by
      unfold programmedGlobalChainTrajectoryMaterialWithBase
        globalChainTrajectoryMaterialBase
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
      symm
      calc
        _ =ᵈ ($ᵗ (GlobalChainValueIndex → Digest) >>= fun base =>
              pure base) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro base _hbase
          exact OracleComp.EvalDistEq.bind_const
            (programmedGlobalChainTrajectoryMaterial parameter) (pure base)
        _ = _ := by simp

theorem programmedGlobalChainTrajectoryMaterial_support_as_actual
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    material.2 ∈ support
      (Concrete.allChainTrajectoriesFromCache parameter material.1 ∅ allChains) := by
  apply (OracleComp.support_eq_of_evalDistEq
    (evalDist_allChainTrajectories_eq_programmed parameter material.1
      allChains ∅ allChains_nodup (by
        simp [AllChainAddressesAbsent]))).symm.subset
  exact programmedGlobalChainTrajectoryMaterial_support_trajectories
    parameter material hmaterial

theorem programmedGlobalChainTrajectoryMaterial_chainsWarm
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter)) :
    ChainsWarm parameter material.1 material.2.2 :=
  Concrete.allChainTrajectoriesFromCache_chainsWarm parameter material.1 ∅ material.2
    (programmedGlobalChainTrajectoryMaterial_support_as_actual parameter material hmaterial)

theorem programmedGlobalChainTrajectoryMaterial_none_of_notChain
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (domain : HashDomain)
    (hdomain : ∀ (key : ChainKey) chain step, key.chainDomain chain step ≠ domain)
    (input : HashInput) (haddress : AtHashAddress parameter domain input) :
    material.2.2 input = none :=
  Concrete.allChainTrajectoriesFromCache_none_of_notChain parameter material.1 domain hdomain
    input haddress allChains ∅ material.2 rfl
    (programmedGlobalChainTrajectoryMaterial_support_as_actual parameter material hmaterial)

/-- Key generation runs from the warm caches of two trajectory materials start related. -/
theorem programmedGlobalChainTrajectoryMaterial_initialRelation
    (parameter : PublicParameter) (left right : GlobalChainTrajectoryMaterial)
    (hleft : left ∈ support (programmedGlobalChainTrajectoryMaterial parameter))
    (hright : right ∈ support (programmedGlobalChainTrajectoryMaterial parameter)) :
    KeygenRunRelation parameter left.1 right.1 left.2.2 right.2.2 left.2.2 right.2.2 := by
  refine ⟨le_rfl, le_rfl, ?_, ?_⟩
  · intro input hinput
    obtain ⟨domain, hretained, haddress⟩ := hinput
    have hdomain : ∀ (key : ChainKey) chain step, key.chainDomain chain step ≠ domain := by
      intro key chain step heq
      subst domain
      cases key <;> exact hretained
    rw [programmedGlobalChainTrajectoryMaterial_none_of_notChain parameter left hleft domain
        hdomain input haddress,
      programmedGlobalChainTrajectoryMaterial_none_of_notChain parameter right hright domain
        hdomain input haddress]
  · intro key
    have hdomain : ∀ (chainKey : ChainKey) chain step,
        chainKey.chainDomain chain step ≠ key.leafDomain := by
      intro chainKey chain step heq
      cases chainKey <;> cases key <;> simp [ChainKey.chainDomain, ChainKey.leafDomain] at heq
    unfold hashCacheLookup
    rw [programmedGlobalChainTrajectoryMaterial_none_of_notChain parameter left hleft
        key.leafDomain hdomain (Concrete.CacheView.keyLeafInput parameter key
          (Concrete.CacheReplay.keyOneTimePublicKey left.2.2 parameter left.1 key))
          ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl),
      programmedGlobalChainTrajectoryMaterial_none_of_notChain parameter right hright
        key.leafDomain hdomain (Concrete.CacheView.keyLeafInput parameter key
          (Concrete.CacheReplay.keyOneTimePublicKey right.2.2 parameter right.1 key))
          ((atHashAddress_tweakableHashInput_iff parameter _ _ _).2 rfl)]

structure CoupledGlobalChainKeygenView where
  start : ChainKey → ChainIndex → Digest
  table : GlobalChainValueIndex → Digest
  run : (Digest × (TopIndex → Option (Randomness × Encoding))) × QueryCache HashSpec

def CoupledGlobalChainKeygenView.toProgrammedView
    (parameter : PublicParameter) (view : CoupledGlobalChainKeygenView) :
    ProgrammedGlobalChainKeygenView where
  publicKey := ⟨view.run.1.1, parameter⟩
  secretKey := startSecretKey parameter view.start view.run.1.2
  cache := view.run.2
  table := view.table

noncomputable def coupledGlobalChainKeygenExperiment
    (parameter : PublicParameter) : ProbComp CoupledGlobalChainKeygenView := do
  let material ← programmedGlobalChainTrajectoryMaterial parameter
  let topBase ← Concrete.sampleTopBase
  let run ← (simulateQ randomOracle (Concrete.honestKeygenFrom parameter material.1 topBase)).run
    material.2.2
  pure { start := material.1, table := globalChainTrajectoryMaterialTable material, run }

theorem programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable
    (parameter : PublicParameter) (material : GlobalChainTrajectoryMaterial)
    (hmaterial : material ∈ support
      (programmedGlobalChainTrajectoryMaterial parameter))
    (cache : QueryCache HashSpec) (hle : material.2.2 ≤ cache)
    (topSigned : TopIndex → Option (Randomness × Encoding)) :
    globalChainTrajectoryMaterialTable material =
      globalKeygenChainValueTable cache (startSecretKey parameter material.1 topSigned) :=
  Concrete.allChainTrajectoriesFromCache_globalTable_eq parameter material.1 material.2 cache
    (programmedGlobalChainTrajectoryMaterial_support_as_actual parameter material hmaterial)
    hle _ rfl (startSecretKey_keyChainStart parameter material.1 topSigned)

noncomputable def coupledGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView := do
  let parameter ← Concrete.samplePublicParameter
  let view ← coupledGlobalChainKeygenExperiment parameter
  pure (view.toProgrammedView parameter)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 1000000 in
theorem evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories :
    coupledGlobalChainKeygen =ᵈ (eraseAllChainTrajectories <$>
        programmedAllChainTrajectoryKeygen) := by
  unfold coupledGlobalChainKeygen programmedAllChainTrajectoryKeygen
    eraseAllChainTrajectories coupledGlobalChainKeygenExperiment
  simp only [map_bind, map_pure, bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro parameter
  have hmaterial : ∀ material ∈ support (programmedGlobalChainTrajectoryMaterial parameter),
      ∀ topBase, ∀ run ∈ support ((simulateQ randomOracle
        (Concrete.honestKeygenFrom parameter material.1 topBase)).run material.2.2),
      ({ start := material.1, table := globalChainTrajectoryMaterialTable material, run } :
        CoupledGlobalChainKeygenView).toProgrammedView parameter =
        keygenViewOfRun parameter material.1 run := by
    intro material hmaterial topBase run hrun
    unfold CoupledGlobalChainKeygenView.toProgrammedView keygenViewOfRun
    rw [programmedGlobalChainTrajectoryMaterial_table_eq_keygenTable parameter material
      hmaterial run.2 (Concrete.CacheReplay.randomOracle_cache_le _ _ _ hrun) run.1.2]
  calc
    _ =ᵈ (programmedGlobalChainTrajectoryMaterial parameter >>= fun material =>
          Concrete.sampleTopBase >>= fun topBase =>
          (simulateQ randomOracle (Concrete.honestKeygenFrom parameter material.1
            topBase)).run material.2.2 >>= fun run =>
          pure (keygenViewOfRun parameter material.1 run)) := by
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro material hmaterialSupport
      apply EvalDistEq.bind_right
      intro topBase
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro run hrun
      rw [hmaterial material hmaterialSupport topBase run hrun]
    _ = _ := by
      unfold programmedGlobalChainTrajectoryMaterial
      simp only [bind_assoc, pure_bind]


def ProgrammedGlobalChainKeygenRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : ProgrammedGlobalChainKeygenView ×
      (GlobalChainValueIndex → Digest)) : Prop :=
  left.table = right.2 ∧
    left.publicKey = right.1.publicKey ∧
    left.secretKey.topSigned = right.1.secretKey.topSigned ∧
    (∀ leafIndex,
      Concrete.CacheReplay.authenticationPath left.cache left.secretKey leafIndex =
        Concrete.CacheReplay.authenticationPath right.1.cache
          right.1.secretKey leafIndex) ∧
    (∀ key level,
      Concrete.honestTopPath left.cache left.secretKey key level =
        Concrete.honestTopPath right.1.cache right.1.secretKey key level)

end XmssSecurity.CappedChain

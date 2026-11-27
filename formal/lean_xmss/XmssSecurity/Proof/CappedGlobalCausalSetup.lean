module

public import XmssSecurity.Proof.CappedChain.SignatureChainValue
public import XmssSecurity.Proof.RevealProbeOracleSimulation
public import XmssSecurity.Proof.CappedChain.ChainInputTrace
public import XmssSecurity.Proof.CappedChain.TreeCacheStable
public import XmssSecurity.Proof.CappedGlobalKeygen
public import XmssSecurity.Proof.PrecomputedKeygenCache

@[expose] public section

/-!
# The causal hash state and the signer's reveals

The causal simulation reads every chain value of key generation (`GlobalChainValueIndex`) as a
hidden value of `RevealProbeOracleSimulation`. Its state, `GlobalCausalHashState`, holds the random
oracle's cache, key generation's cache, the values revealed so far and the chain probes the hash
queries made (`globalCausalRecordedState`). `revealGlobalSignature` reveals the chain values a
returned signature sends at both layers and writes them into the signature, one layer at a time by
the side of the chain key (`revealGlobalSignatureChains`,
`globalSignatureRevealResult_allChains_chainValue`). `keygenViews_signWithEncoding_eq_globalReveal`
shows that a signature replayed from one key generation is the other's with the revealed table
values written in, under the relations defined here (`ProgrammedGlobalChainKeygenStableRelation`,
`ProgrammedGlobalChainKeygenFullCacheStableRelation`). Key generation with presampled trajectories
(`trajectoryProgrammedGlobalChainKeygen`) equals both the actual and the coupled key generation in
distribution.
-/

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.CappedChain

variable (table : GlobalChainValueIndex → Digest) (keyView : ProgrammedGlobalChainKeygenView)
  (edgeHigh : GlobalChainEdgeIndex → Digest)

noncomputable def trajectoryProgrammedGlobalChainKeygen :
    ProbComp ProgrammedGlobalChainKeygenView :=
  eraseAllChainTrajectories <$> programmedAllChainTrajectoryKeygen

theorem evalDist_coupledGlobalChainKeygen_eq_trajectoryProgrammed :
    (coupledGlobalChainKeygen) =ᵈ
      (trajectoryProgrammedGlobalChainKeygen) :=
  evalDist_coupledGlobalChainKeygen_eq_programmedTrajectories

theorem evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed :
    (actualGlobalChainKeygen) =ᵈ
      (trajectoryProgrammedGlobalChainKeygen) :=
  evalDist_actualGlobalChainKeygen_eq_programmedAllChainTrajectories

theorem trajectoryProgrammedGlobalChainKeygen_support_table
    (result : ProgrammedGlobalChainKeygenView)
    (hresult : result ∈ support trajectoryProgrammedGlobalChainKeygen) :
    globalKeygenChainValueTable result.cache result.secretKey = result.table := by
  apply actualGlobalChainKeygen_support_table result
  exact (OracleComp.support_eq_of_evalDistEq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed).symm.subset hresult

abbrev GlobalChainActionTracedResult :=
  ((ProgrammedGlobalChainKeygenView × (GameOutcome × QueryCache HashSpec)) ×
    AttackerActionTrace)

def eraseGlobalChainKeygenView
    (result : GlobalChainActionTracedResult) :
    ((((PublicKey × SecretKey) × QueryCache HashSpec) ×
      (GameOutcome × QueryCache HashSpec)) × AttackerActionTrace) :=
  ((((result.1.1.publicKey, Concrete.materializePrecomputation
      result.1.1.cache result.1.1.secretKey), result.1.1.cache),
    result.1.2), result.2)

structure GlobalCausalHashState where
  cache : QueryCache HashSpec
  keygenCache : QueryCache HashSpec
  revealed : GlobalChainValueIndex → Option Digest
  probes : List (GlobalChainValueIndex × Digest)

def GlobalCausalHashState.recordProbe
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    GlobalCausalHashState :=
  { state with probes :=
      match probe with
      | none => state.probes
      | some value => state.probes ++ [value] }

@[simp]
theorem GlobalCausalHashState.recordProbe_cache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).cache = state.cache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_keygenCache
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).keygenCache = state.keygenCache := rfl

@[simp]
theorem GlobalCausalHashState.recordProbe_revealed
    (state : GlobalCausalHashState)
    (probe : Option (GlobalChainValueIndex × Digest)) :
    (state.recordProbe probe).revealed = state.revealed := rfl

def GlobalCausalHashState.recordReveal
    (state : GlobalCausalHashState) (index : GlobalChainValueIndex)
    (value : Digest) : GlobalCausalHashState :=
  { state with revealed := Function.update state.revealed index (some value) }

def GlobalCausalHashState.setCache
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    GlobalCausalHashState :=
  { state with cache := cache }

@[simp]
theorem GlobalCausalHashState.setCache_revealed
    (state : GlobalCausalHashState) (cache : QueryCache HashSpec) :
    (state.setCache cache).revealed = state.revealed := rfl

noncomputable def globalCausalHashQuery
    (input : HashInput) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex))
      HashOutput := fun state =>
  (fun result : HashOutput × QueryCache HashSpec =>
    (result.1, state.setCache result.2)) <$>
      RevealProbeOracleSimulation.liftProbComp
        ((randomOracle input).run state.cache)

theorem globalCausalHashQuery_run
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state =
      (fun result : HashOutput × QueryCache HashSpec =>
        (result.1, state.setCache result.2)) <$>
          RevealProbeOracleSimulation.liftProbComp
            ((randomOracle input).run state.cache) := rfl

noncomputable def globalCausalRecordedState
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) : GlobalCausalHashState :=
  state.recordProbe (globalChainInputProbe? secretKey.parameter input)

@[simp]
theorem globalCausalRecordedState_cache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).cache = state.cache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_cache state _

@[simp]
theorem globalCausalRecordedState_keygenCache
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).keygenCache =
      state.keygenCache := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_keygenCache state _

@[simp]
theorem globalCausalRecordedState_revealed
    (secretKey : SecretKey) (input : HashInput)
    (state : GlobalCausalHashState) :
    (globalCausalRecordedState secretKey input state).revealed =
      state.revealed := by
  rw [globalCausalRecordedState]
  exact GlobalCausalHashState.recordProbe_revealed state _

def globalCausalUniformImpl :
    QueryImpl unifSpec
      (StateT GlobalCausalHashState
        (OracleComp
          (RevealProbeOracleSimulation.World GlobalChainValueIndex))) :=
  fun n => liftM (RevealProbeOracleSimulation.uniformQuery
    (Index := GlobalChainValueIndex) n)

theorem globalCausalHashQuery_run_isProbeQueryBoundP
    (input : HashInput) (state : GlobalCausalHashState) :
    (globalCausalHashQuery input).run state |>.IsQueryBoundP
      RevealProbeOracleSimulation.IsProbeQuery 0 := by
  unfold globalCausalHashQuery
  apply (OracleComp.isQueryBoundP_map_iff _ _ 0).2
  exact RevealProbeOracleSimulation.liftProbComp_isProbeQueryBoundP
    ((randomOracle input).run state.cache) 0

section Reveal

variable (table : GlobalChainValueIndex → Digest) (key : ChainKey) (encoding : ChainIndex → Digit)
  (chains : List ChainIndex) (signature : Signature) (state : GlobalCausalHashState)

/-- Reveal the chain values of `chains` at key `key`'s layer and write them into the signature. -/
noncomputable def revealGlobalSignatureChains (key : ChainKey) (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature →
      StateT GlobalCausalHashState
        (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)) Signature
  | [], signature => pure signature
  | chain :: chains, signature => fun state => do
      let index : GlobalChainValueIndex := (chain, key, encoding chain)
      let value ← RevealProbeOracleSimulation.revealQuery index
      (revealGlobalSignatureChains key encoding chains
        (replaceSignatureChainValue key signature chain value)).run
          (state.recordReveal index value)

/-- `revealGlobalSignatureChains` answered from `table`. -/
def globalSignatureRevealResult (table : GlobalChainValueIndex → Digest) (key : ChainKey)
    (encoding : ChainIndex → Digit) :
    List ChainIndex → Signature → GlobalCausalHashState → Signature × GlobalCausalHashState
  | [], signature, state => (signature, state)
  | chain :: chains, signature, state =>
      let index : GlobalChainValueIndex := (chain, key, encoding chain)
      globalSignatureRevealResult table key encoding chains
        (replaceSignatureChainValue key signature chain (table index))
        (state.recordReveal index (table index))

/-- The reveals `revealGlobalSignatureChains` makes. -/
def globalSignatureRevealTrace (table : GlobalChainValueIndex → Digest) (key : ChainKey)
    (encoding : ChainIndex → Digit) :
    List ChainIndex → RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex
  | [] => []
  | chain :: chains =>
      let index : GlobalChainValueIndex := (chain, key, encoding chain)
      .reveal index (table index) :: globalSignatureRevealTrace table key encoding chains

theorem simulate_eagerTrace_revealGlobalSignatureChains :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignatureChains key encoding chains signature).run state)).run =
      pure (globalSignatureRevealResult table key encoding chains signature state,
        globalSignatureRevealTrace table key encoding chains) := by
  induction chains generalizing signature state with
  | nil => simp [revealGlobalSignatureChains, globalSignatureRevealResult, globalSignatureRevealTrace]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      change (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table) (do
          let value ← RevealProbeOracleSimulation.revealQuery (chain, key, encoding chain)
          (revealGlobalSignatureChains key encoding chains
            (replaceSignatureChainValue key signature chain value)).run
              (state.recordReveal (chain, key, encoding chain) value))).run = _
      rw [simulateQ_bind, WriterT.run_bind',
        RevealProbeOracleSimulation.simulate_eagerTrace_revealQuery]
      simp only [pure_bind]
      rw [ih]
      simp [globalSignatureRevealResult, globalSignatureRevealTrace]

theorem globalSignatureRevealResult_chainValue_of_not_mem (candidate : ChainIndex)
    (hnotmem : candidate ∉ chains) :
    (globalSignatureRevealResult table key encoding chains signature state).1.keyChainValue key
      candidate = signature.keyChainValue key candidate := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      simp only [List.mem_cons, not_or] at hnotmem
      rw [globalSignatureRevealResult, ih _ _ hnotmem.2]
      exact replaceSignatureChainValue_other key signature chain candidate _ hnotmem.1

theorem globalSignatureRevealResult_chainValue_of_mem (candidate : ChainIndex)
    (hnodup : chains.Nodup) (hmem : candidate ∈ chains) :
    (globalSignatureRevealResult table key encoding chains signature state).1.keyChainValue key
      candidate = table (candidate, key, encoding candidate) := by
  induction chains generalizing signature state with
  | nil => simp at hmem
  | cons chain chains ih =>
      rw [List.nodup_cons] at hnodup
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · rw [globalSignatureRevealResult, globalSignatureRevealResult_chainValue_of_not_mem _ _ _ _ _ _
          _ hnodup.1]
        exact replaceSignatureChainValue_same key signature _ _
      · rw [globalSignatureRevealResult]
        exact ih _ _ hnodup.2 hmem

theorem globalSignatureRevealResult_allChains_chainValue (chain : ChainIndex) :
    (globalSignatureRevealResult table key encoding allChains signature state).1.keyChainValue key
      chain = table (chain, key, encoding chain) :=
  globalSignatureRevealResult_chainValue_of_mem _ _ _ _ _ _ _ allChains_nodup (by simp [allChains])

theorem revealGlobalSignatureChains_run_isProbeQueryBoundP :
    (revealGlobalSignatureChains key encoding chains signature).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  induction chains generalizing signature state with
  | nil => simp [revealGlobalSignatureChains]
  | cons chain chains ih =>
      rw [revealGlobalSignatureChains]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (RevealProbeOracleSimulation.revealQuery_isProbeQueryBoundP (chain, key, encoding chain) 0)
      intro value _hvalue
      exact ih _ _

theorem Signature.eq_of_fields
    (left right : Signature)
    (hrandomness : left.randomness = right.randomness)
    (hchainValue : left.chainValue = right.chainValue)
    (hauthPath : left.authPath = right.authPath)
    (htop : left.top = right.top) :
    left = right := by
  cases left
  cases right
  simp_all

/-- What a reveal leaves alone: `field` reads no chain value of key `key`'s layer. -/
theorem globalSignatureRevealResult_field {α : Type} (field : Signature → α)
    (hfield : ∀ signature chain value,
      field (replaceSignatureChainValue key signature chain value) = field signature) :
    field (globalSignatureRevealResult table key encoding chains signature state).1 =
      field signature := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih =>
      rw [globalSignatureRevealResult, ih, hfield]

theorem globalSignatureRevealResult_randomness :
    (globalSignatureRevealResult table key encoding chains signature state).1.randomness =
      signature.randomness :=
  globalSignatureRevealResult_field table key encoding chains signature state Signature.randomness (by cases key <;> intros <;> rfl)

theorem globalSignatureRevealResult_authPath :
    (globalSignatureRevealResult table key encoding chains signature state).1.authPath =
      signature.authPath :=
  globalSignatureRevealResult_field table key encoding chains signature state Signature.authPath (by cases key <;> intros <;> rfl)

theorem globalSignatureRevealResult_inl_top (leafIndex : LeafIndex) :
    (globalSignatureRevealResult table (.inl leafIndex) encoding chains signature state).1.top =
      signature.top :=
  globalSignatureRevealResult_field table _ encoding chains signature state Signature.top (fun _ _ _ => rfl)

theorem globalSignatureRevealResult_inr_chainValue (topKey : TopIndex) :
    (globalSignatureRevealResult table (.inr topKey) encoding chains signature state).1.chainValue =
      signature.chainValue :=
  globalSignatureRevealResult_field table _ encoding chains signature state Signature.chainValue (fun _ _ _ => rfl)

theorem globalSignatureRevealResult_inr_topRandomness (topKey : TopIndex) :
    (globalSignatureRevealResult table (.inr topKey) encoding chains signature state).1.top.randomness =
      signature.top.randomness :=
  globalSignatureRevealResult_field table _ encoding chains signature state (·.top.randomness) (fun _ _ _ => rfl)

theorem globalSignatureRevealResult_inr_topAuthPath (topKey : TopIndex) :
    (globalSignatureRevealResult table (.inr topKey) encoding chains signature state).1.top.authPath =
      signature.top.authPath :=
  globalSignatureRevealResult_field table _ encoding chains signature state (·.top.authPath) (fun _ _ _ => rfl)

theorem globalSignatureRevealResult_cache :
    (globalSignatureRevealResult table key encoding chains signature state).2.cache = state.cache := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih => rw [globalSignatureRevealResult, ih]; rfl

theorem globalSignatureRevealResult_keygenCache :
    (globalSignatureRevealResult table key encoding chains signature state).2.keygenCache =
      state.keygenCache := by
  induction chains generalizing signature state with
  | nil => rfl
  | cons chain chains ih => rw [globalSignatureRevealResult, ih]; rfl

end Reveal

/-- Reveal the chain values a returned signature sends: its bottom ones and those of its top
signature. An unsigned bottom tree's signature is never returned, so nothing is revealed. -/
noncomputable def revealGlobalSignature
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature) :
    StateT GlobalCausalHashState
      (OracleComp (RevealProbeOracleSimulation.World GlobalChainValueIndex)) Signature :=
  fun state =>
    match topSigned (topKeyOf request.leafIndex) with
    | none => pure (signature, state)
    | some (_, topEncoding) => do
        let bottom ← (revealGlobalSignatureChains (.inl request.leafIndex) encoding allChains signature).run state
        (revealGlobalSignatureChains (.inr (topKeyOf request.leafIndex)) topEncoding allChains bottom.1).run bottom.2

noncomputable def globalSignatureFullRevealResult
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) : Signature × GlobalCausalHashState :=
  match topSigned (topKeyOf request.leafIndex) with
  | none => (signature, state)
  | some (_, topEncoding) =>
      let bottom := globalSignatureRevealResult table (.inl request.leafIndex) encoding allChains signature state
      globalSignatureRevealResult table (.inr (topKeyOf request.leafIndex)) topEncoding allChains bottom.1 bottom.2

noncomputable def globalSignatureFullRevealTrace
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) :
    RevealProbeOracleSimulation.ActionTrace GlobalChainValueIndex :=
  match topSigned (topKeyOf request.leafIndex) with
  | none => []
  | some (_, topEncoding) =>
      globalSignatureRevealTrace table (.inl request.leafIndex) encoding allChains ++
        globalSignatureRevealTrace table (.inr (topKeyOf request.leafIndex)) topEncoding allChains

theorem simulate_eagerTrace_revealGlobalSignature
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) :
    (simulateQ (RevealProbeOracleSimulation.eagerTraceImpl table)
        ((revealGlobalSignature topSigned request encoding signature).run state)).run =
      pure (globalSignatureFullRevealResult table topSigned request encoding signature state,
        globalSignatureFullRevealTrace table topSigned request encoding) := by
  unfold globalSignatureFullRevealResult globalSignatureFullRevealTrace
  cases htop : topSigned (topKeyOf request.leafIndex) with
  | none =>
      have hrun : (revealGlobalSignature topSigned request encoding signature).run state =
          pure (signature, state) := by
        unfold revealGlobalSignature
        rw [htop]
        rfl
      rw [hrun]
      simp
  | some signed =>
      obtain ⟨randomness, topEncoding⟩ := signed
      have hrun : (revealGlobalSignature topSigned request encoding signature).run state =
          ((revealGlobalSignatureChains (.inl request.leafIndex) encoding allChains signature).run state >>=
            fun bottom => (revealGlobalSignatureChains (.inr (topKeyOf request.leafIndex)) topEncoding allChains
              bottom.1).run bottom.2) := by
        unfold revealGlobalSignature
        rw [htop]
        rfl
      rw [hrun, simulateQ_bind, WriterT.run_bind',
        simulate_eagerTrace_revealGlobalSignatureChains]
      simp only [pure_bind]
      rw [simulate_eagerTrace_revealGlobalSignatureChains]
      simp

theorem revealGlobalSignature_run_isProbeQueryBoundP
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) :
    (revealGlobalSignature topSigned request encoding signature).run state
        |>.IsQueryBoundP RevealProbeOracleSimulation.IsProbeQuery 0 := by
  cases htop : topSigned (topKeyOf request.leafIndex) with
  | none =>
      have hrun : (revealGlobalSignature topSigned request encoding signature).run state =
          pure (signature, state) := by
        unfold revealGlobalSignature
        rw [htop]
        rfl
      rw [hrun]
      exact OracleComp.isQueryBoundP_pure _ _ 0
  | some signed =>
      obtain ⟨randomness, topEncoding⟩ := signed
      have hrun : (revealGlobalSignature topSigned request encoding signature).run state =
          ((revealGlobalSignatureChains (.inl request.leafIndex) encoding allChains signature).run state >>=
            fun bottom => (revealGlobalSignatureChains (.inr (topKeyOf request.leafIndex)) topEncoding allChains
              bottom.1).run bottom.2) := by
        unfold revealGlobalSignature
        rw [htop]
        rfl
      rw [hrun]
      apply OracleComp.isQueryBoundP_bind (n := 0) (m := 0)
        (revealGlobalSignatureChains_run_isProbeQueryBoundP (.inl request.leafIndex) encoding allChains
          signature state)
      intro bottom _
      exact revealGlobalSignatureChains_run_isProbeQueryBoundP (.inr (topKeyOf request.leafIndex))
        topEncoding allChains
        bottom.1 bottom.2

theorem globalSignatureFullRevealResult_cache
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureFullRevealResult table topSigned request encoding signature
      state).2.cache = state.cache := by
  unfold globalSignatureFullRevealResult
  cases topSigned (topKeyOf request.leafIndex) with
  | none => rfl
  | some signed =>
      simp only
      rw [globalSignatureRevealResult_cache, globalSignatureRevealResult_cache]

theorem globalSignatureFullRevealResult_randomness
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureFullRevealResult table topSigned request encoding signature
      state).1.randomness = signature.randomness := by
  unfold globalSignatureFullRevealResult
  cases topSigned (topKeyOf request.leafIndex) with
  | none => rfl
  | some signed =>
      simp only
      rw [globalSignatureRevealResult_randomness, globalSignatureRevealResult_randomness]

theorem globalSignatureFullRevealResult_keygenCache
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature)
    (state : GlobalCausalHashState) :
    (globalSignatureFullRevealResult table topSigned request encoding signature
      state).2.keygenCache = state.keygenCache := by
  unfold globalSignatureFullRevealResult
  cases topSigned (topKeyOf request.leafIndex) with
  | none => rfl
  | some signed =>
      simp only
      rw [globalSignatureRevealResult_keygenCache, globalSignatureRevealResult_keygenCache]

def ProgrammedGlobalChainKeygenView.keyResult
    (view : ProgrammedGlobalChainKeygenView) :
    (PublicKey × SecretKey) × QueryCache HashSpec :=
  ((view.publicKey, view.secretKey), view.cache)

theorem actualGlobalChainKeygen_support_keyResult
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support actualGlobalChainKeygen) :
    view.keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅) := by
  unfold actualGlobalChainKeygen at hview
  rw [mem_support_bind_iff] at hview
  obtain ⟨keyResult, hkeyResult, hpure⟩ := hview
  simp only [support_pure, Set.mem_singleton_iff] at hpure
  subst view
  exact hkeyResult

theorem trajectoryProgrammedGlobalChainKeygen_support_keyResult
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support trajectoryProgrammedGlobalChainKeygen) :
    view.keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅) := by
  apply actualGlobalChainKeygen_support_keyResult view
  exact (OracleComp.support_eq_of_evalDistEq
    evalDist_actualGlobalChainKeygen_eq_trajectoryProgrammed).symm.subset hview

theorem trajectoryProgrammedGlobalChainKeygen_support_treeCacheStable
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support trajectoryProgrammedGlobalChainKeygen) :
    TreeCacheStable view.secretKey.parameter view.secretKey.chainStart
      view.cache :=
  keygen_support_treeCacheStable view.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult view hview)

theorem trajectoryProgrammedGlobalChainKeygen_support_topCacheStable
    (view : ProgrammedGlobalChainKeygenView)
    (hview : view ∈ support trajectoryProgrammedGlobalChainKeygen) :
    TopCacheStable view.secretKey view.cache :=
  keygen_support_topCacheStable view.keyResult
    (trajectoryProgrammedGlobalChainKeygen_support_keyResult view hview)

def ProgrammedGlobalChainKeygenStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : KeygenViewWithBase) : Prop :=
  ProgrammedGlobalChainKeygenRelation left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache ∧
    TopCacheStable left.secretKey left.cache ∧
    TopCacheStable right.1.secretKey right.1.cache

theorem keygen_parameter_eq
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    keyResult.1.1.parameter = keyResult.1.2.parameter := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, _hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hkeyResult
  rw [hkey]
  rfl

theorem LayerSignature.eq_of_fields
    (left right : LayerSignature)
    (hrandomness : left.randomness = right.randomness)
    (hchainValue : left.chainValue = right.chainValue)
    (hauthPath : left.authPath = right.authPath) :
    left = right := by
  cases left
  cases right
  simp_all

/-- When its bottom tree is signed, a signature replayed from one key generation is the one the
other key generation's signer writes the revealed table values into. -/
theorem keygenViews_signWithEncoding_eq_globalReveal
    (left : ProgrammedGlobalChainKeygenView)
    (right : KeygenViewWithBase)
    (hrel : ProgrammedGlobalChainKeygenStableRelation left right)
    (hleftSupport : left ∈ support trajectoryProgrammedGlobalChainKeygen)
    (_hrightSupport : right.1 ∈ support trajectoryProgrammedGlobalChainKeygen)
    (leftCache rightCache : QueryCache HashSpec)
    (hleftLe : left.cache ≤ leftCache)
    (hrightLe : right.1.cache ≤ rightCache)
    (request : SignRequest) (randomness : Randomness) (encoding : Encoding)
    (rightState : GlobalCausalHashState)
    (topRandomness : Randomness) (topEncoding : Encoding)
    (htop : left.secretKey.topSigned (topKeyOf request.leafIndex) =
      some (topRandomness, topEncoding)) :
    Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        request.leafIndex randomness encoding =
      (globalSignatureFullRevealResult right.2 right.1.secretKey.topSigned request encoding
        (Concrete.CacheReplay.signWithEncoding rightCache right.1.secretKey
          request.leafIndex randomness encoding) rightState).1 := by
  have hleftKey := trajectoryProgrammedGlobalChainKeygen_support_keyResult
    left hleftSupport
  have hrightTop : right.1.secretKey.topSigned (topKeyOf request.leafIndex) =
      some (topRandomness, topEncoding) := by
    rw [← hrel.1.2.2.1]
    exact htop
  have htable : globalKeygenChainValueTable left.cache left.secretKey = right.2 := by
    rw [trajectoryProgrammedGlobalChainKeygen_support_table left hleftSupport, hrel.1.1]
  unfold globalSignatureFullRevealResult
  rw [hrightTop]
  simp only
  apply Signature.eq_of_fields
  · rw [globalSignatureRevealResult_randomness, globalSignatureRevealResult_randomness]
    rfl
  · funext chain
    rw [globalSignatureRevealResult_inr_chainValue]
    refine Eq.trans ?_ (globalSignatureRevealResult_allChains_chainValue right.2
      (.inl request.leafIndex) encoding _ rightState chain).symm
    have hchain :=
      Concrete.CacheReplay.signWithEncoding_chainValue_eq_keygenChainValueTable
        left.keyResult hleftKey leftCache hleftLe request.leafIndex randomness
          encoding chain
    rw [show (Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
        request.leafIndex randomness encoding).chainValue chain =
      keygenChainValueTable left.cache left.secretKey chain
        (.inl request.leafIndex, encoding chain) by
          simpa [ProgrammedGlobalChainKeygenView.keyResult] using hchain]
    rw [← htable]
    rfl
  · funext level
    calc
      (Concrete.CacheReplay.signWithEncoding leftCache left.secretKey
          request.leafIndex randomness encoding).authPath level =
        Concrete.CacheReplay.authenticationPath left.cache left.secretKey
          request.leafIndex level := by
            rw [Concrete.CacheReplay.signWithEncoding]
            exact congrFun (hrel.2.1.authenticationPath_eq left.secretKey
              left.cache leftCache hleftLe request.leafIndex).symm level
      _ = Concrete.CacheReplay.authenticationPath right.1.cache
          right.1.secretKey request.leafIndex level :=
            congrFun (hrel.1.2.2.2.1 request.leafIndex) level
      _ = _ := by
        rw [globalSignatureRevealResult_authPath, globalSignatureRevealResult_authPath]
        change Concrete.CacheReplay.authenticationPath right.1.cache
            right.1.secretKey request.leafIndex level =
          Concrete.CacheReplay.authenticationPath rightCache
            right.1.secretKey request.leafIndex level
        exact congrFun (hrel.2.2.1.authenticationPath_eq right.1.secretKey
          right.1.cache rightCache hrightLe request.leafIndex) level
  · have hleftTop := hrel.2.2.2.1 leftCache hleftLe (topKeyOf request.leafIndex)
    have hrightTopStable := hrel.2.2.2.2 rightCache hrightLe (topKeyOf request.leafIndex)
    apply LayerSignature.eq_of_fields
    · rw [globalSignatureRevealResult_inr_topRandomness, globalSignatureRevealResult_inl_top]
      change (Concrete.CacheReplay.topPartFromCache leftCache left.secretKey
          (topKeyOf request.leafIndex)).randomness =
        (Concrete.CacheReplay.topPartFromCache rightCache right.1.secretKey
          (topKeyOf request.leafIndex)).randomness
      simp [Concrete.CacheReplay.topPartFromCache, htop, hrightTop]
    · funext chain
      refine Eq.trans ?_ (globalSignatureRevealResult_allChains_chainValue right.2
        (.inr (topKeyOf request.leafIndex)) topEncoding _ _ chain).symm
      change (Concrete.CacheReplay.topPartFromCache leftCache left.secretKey
          (topKeyOf request.leafIndex)).chainValue chain = _
      have hchain := Concrete.CacheReplay.topPartFromCache_chainValue_eq_keygenChainValueTable
        left.keyResult hleftKey leftCache hleftLe (topKeyOf request.leafIndex) topRandomness
        topEncoding htop chain
      rw [show (Concrete.CacheReplay.topPartFromCache leftCache left.secretKey
          (topKeyOf request.leafIndex)).chainValue chain =
        keygenChainValueTable left.cache left.secretKey chain
          (.inr (topKeyOf request.leafIndex), topEncoding chain) by
            simpa [ProgrammedGlobalChainKeygenView.keyResult] using hchain, ← htable]
      rfl
    · funext level
      rw [globalSignatureRevealResult_inr_topAuthPath, globalSignatureRevealResult_inl_top]
      change (Concrete.CacheReplay.topPartFromCache leftCache left.secretKey
          (topKeyOf request.leafIndex)).authPath level =
        (Concrete.CacheReplay.topPartFromCache rightCache right.1.secretKey
          (topKeyOf request.leafIndex)).authPath level
      rw [← hleftTop, ← hrightTopStable]
      simp only [Concrete.CacheReplay.topPartFromCache, htop, hrightTop]
      exact hrel.1.2.2.2.2 (topKeyOf request.leafIndex) level.val

def GlobalSigningComparableHashInput
    (parameter : PublicParameter) (input : HashInput) : Prop :=
  ∃ leafIndex message randomness,
    input = Concrete.CacheView.encodingInput parameter leafIndex
      (message, randomness)

def GlobalSigningRevealsAgree
    (state : GlobalCausalHashState) : Prop :=
  ∀ index value, state.revealed index = some value → table index = value

theorem GlobalSigningRevealsAgree.setCache
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (cache : QueryCache HashSpec) :
    GlobalSigningRevealsAgree table { state with cache := cache } :=
  hagrees

theorem GlobalSigningRevealsAgree.recordReveal
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (index : GlobalChainValueIndex) :
    GlobalSigningRevealsAgree table
      (state.recordReveal index (table index)) := by
  intro candidate value hvalue
  by_cases heq : candidate = index
  · subst candidate
    simp [GlobalCausalHashState.recordReveal] at hvalue
    exact hvalue
  · simp [GlobalCausalHashState.recordReveal,
      Function.update_of_ne heq] at hvalue
    exact hagrees candidate value hvalue

theorem GlobalSigningRevealsAgree.globalSignatureRevealResult
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (key : ChainKey) (encoding : ChainIndex → Digit)
    (chains : List ChainIndex) (signature : Signature) :
    GlobalSigningRevealsAgree table
      (globalSignatureRevealResult table key encoding chains signature state).2 := by
  induction chains generalizing signature state with
  | nil => exact hagrees
  | cons chain chains ih =>
      apply ih
      exact hagrees.recordReveal (chain, key, encoding chain)

theorem GlobalSigningRevealsAgree.globalSignatureFullRevealResult
    {table : GlobalChainValueIndex → Digest}
    {state : GlobalCausalHashState}
    (hagrees : GlobalSigningRevealsAgree table state)
    (topSigned : TopIndex → Option (Randomness × Encoding))
    (request : SignRequest) (encoding : ChainIndex → Digit) (signature : Signature) :
    GlobalSigningRevealsAgree table
      (globalSignatureFullRevealResult table topSigned request encoding signature state).2 := by
  unfold XmssSecurity.CappedChain.globalSignatureFullRevealResult
  cases topSigned (topKeyOf request.leafIndex) with
  | none => exact hagrees
  | some signed =>
      exact (hagrees.globalSignatureRevealResult (.inl request.leafIndex) encoding allChains
        signature).globalSignatureRevealResult (.inr (topKeyOf request.leafIndex)) signed.2
          allChains _

def ProgrammedGlobalChainKeygenFullCacheRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : KeygenViewWithBase) : Prop :=
  ProgrammedGlobalChainKeygenRelation left right ∧
    ∃ leftEndpoints rightEndpoints,
      GlobalTreeCacheCorrespondence left.secretKey.parameter leftEndpoints
        rightEndpoints left.cache right.1.cache ∧
      ReplayEndpointsMatch left.secretKey.parameter left.secretKey.keyChainStart
        leftEndpoints left.cache ∧
      ReplayEndpointsMatch right.1.secretKey.parameter
        right.1.secretKey.keyChainStart rightEndpoints right.1.cache

def GlobalTreeSigningCacheRelation
    (parameter : PublicParameter)
    (leftStart rightStart : ChainKey → ChainIndex → Digest)
    (leftCache rightCache : QueryCache HashSpec) : Prop :=
  ∃ leftEndpoints rightEndpoints,
    GlobalTreeCacheCorrespondence parameter leftEndpoints rightEndpoints
      leftCache rightCache ∧
    ReplayEndpointsMatch parameter leftStart leftEndpoints leftCache ∧
    ReplayEndpointsMatch parameter rightStart rightEndpoints rightCache

def ProgrammedGlobalChainKeygenFullCacheStableRelation
    (left : ProgrammedGlobalChainKeygenView)
    (right : KeygenViewWithBase) : Prop :=
  ProgrammedGlobalChainKeygenFullCacheRelation left right ∧
    TreeCacheStable left.secretKey.parameter left.secretKey.chainStart
      left.cache ∧
    TreeCacheStable right.1.secretKey.parameter right.1.secretKey.chainStart
      right.1.cache ∧
    TopCacheStable left.secretKey left.cache ∧
    TopCacheStable right.1.secretKey right.1.cache ∧
    GlobalTreeSigningCacheRelation left.secretKey.parameter
      left.secretKey.keyChainStart right.1.secretKey.keyChainStart left.cache
        right.1.cache

theorem ProgrammedGlobalChainKeygenFullCacheStableRelation.toStable
    {left : ProgrammedGlobalChainKeygenView}
    {right : KeygenViewWithBase}
    (hrel : ProgrammedGlobalChainKeygenFullCacheStableRelation left right) :
    ProgrammedGlobalChainKeygenStableRelation left right :=
  ⟨hrel.1.1, hrel.2.1, hrel.2.2.1, hrel.2.2.2.1, hrel.2.2.2.2.1⟩

end XmssSecurity.CappedChain

import XmssSecurity.Proof.CacheVerify
import XmssSecurity.Proof.LazyScheme
import VCVio.OracleComp.QueryTracking.CachingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv
import XmssSecurity.Proof.StatementLemmas

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

def answer (cache : QueryCache HashSpec) (input : HashInput) : HashOutput :=
  (cache input).getD 0

def answerFn (cache : QueryCache HashSpec) : QueryImpl HashSpec Id :=
  fun input => answer cache input

@[simp]
theorem truncateHash_answer (cache : QueryCache HashSpec) (input : HashInput) :
    truncateHash (answer cache input) = CacheView.digestAt cache input := by
  cases hcache : cache input with
  | none =>
      simp only [answer, CacheView.digestAt, hcache, Option.getD_none]
      exact truncateHash_zero
  | some output => simp [answer, CacheView.digestAt, hcache]

@[simp]
theorem eval_oracleHash (cache : QueryCache HashSpec) (input : HashInput) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.oracleHash input : OracleComp HashSpec HashOutput) = answer cache input := by
  simpa [Concrete.oracleHash, answerFn] using
    evalWithAnswerFn_query (answerFn cache) input

@[simp]
theorem eval_tweakableHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) =
      CacheView.tweakableHash cache parameter domain payload := by
  simp [Concrete.tweakableHash, CacheView.tweakableHash]

@[simp]
theorem eval_encodingHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (message : Message)
    (randomness : Randomness) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.encodingHash parameter epoch message randomness : OracleComp HashSpec Digest) =
      CacheView.encodingHash cache parameter epoch (message, randomness) := by
  simp [Concrete.encodingHash, CacheView.encodingHash, CacheView.encodingInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_chainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.chainStep cache parameter epoch chain) position steps value := by
  induction steps with
  | zero => simp [Concrete.chainWalk, Wots.walk]
  | succ steps ih =>
      simp only [Concrete.chainWalk, evalWithAnswerFn_bind, ih, Wots.walk]
      by_cases hposition : position + steps < chainLength - 1
      · simp [hposition, Concrete.chainHash, CacheView.chainStep,
          CacheView.chainInput, CacheView.tweakableHash]
      · simp [hposition, CacheView.chainStep]

@[simp]
theorem eval_recoverChain (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (digit : Digit) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.recoverChain parameter epoch chain digit value : OracleComp HashSpec Digest) =
      Wots.recoverChain (CacheView.chainStep cache parameter epoch chain) digit value := by
  simp [Concrete.recoverChain, Wots.recoverChain]

@[simp]
theorem eval_sequenceFin (cache : QueryCache HashSpec) {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn (answerFn cache) (Concrete.sequenceFin computation) =
      fun index => evalWithAnswerFn (answerFn cache) (computation index) := by
  induction n with
  | zero =>
      funext index
      exact Fin.elim0 index
  | succ n ih =>
      simp only [Concrete.sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      funext index
      exact Fin.cases rfl (fun _ => rfl) index

@[simp]
theorem eval_recoverEndpoints (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (encoding : Encoding)
    (signature : Signature) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.recoverEndpoints parameter epoch encoding signature :
        OracleComp HashSpec (ChainIndex → Digest)) =
      XmssSecurity.recoveredEndpoints
        (fun chain => CacheView.chainStep cache parameter epoch chain)
        encoding signature.chainValue := by
  funext chain
  simp [Concrete.recoverEndpoints, XmssSecurity.recoveredEndpoints]

@[simp]
theorem eval_leafHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch)
    (endpoints : ChainIndex → Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.leafHash parameter epoch endpoints : OracleComp HashSpec Digest) =
      CacheView.leafHash cache parameter epoch endpoints := by
  simp [Concrete.leafHash, CacheView.leafHash, CacheView.leafInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_nodeHash (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (level : MerkleLevel) (node : MerkleNode)
    (left right : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.nodeHash parameter level node left right : OracleComp HashSpec Digest) =
      CacheView.merkleHash cache parameter level node left right := by
  simp [Concrete.nodeHash, CacheView.merkleHash, CacheView.merkleInput,
    CacheView.tweakableHash]

@[simp]
theorem eval_oneTimePublicKey (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.oneTimePublicKey parameter secret epoch :
        OracleComp HashSpec (ChainIndex → Digest)) =
      oneTimePublicKey cache parameter secret epoch := by
  funext chain
  simp [Concrete.oneTimePublicKey, oneTimePublicKey]

@[simp]
theorem eval_leafAt (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (epoch : Epoch) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.leafAt parameter secret epoch : OracleComp HashSpec Digest) =
      leafAt cache parameter secret epoch := by
  simp [Concrete.leafAt, leafAt]

@[simp]
theorem eval_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.treeNode parameter secret levels node : OracleComp HashSpec Digest) =
      treeNode cache parameter secret levels node := by
  induction levels generalizing node with
  | zero => simp [Concrete.treeNode_zero_eq, treeNode_zero_eq]
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      simp only [evalWithAnswerFn_bind, ih, treeNode_succ_eq]
      split <;> simp_all

/-! The statement stores the precomputed secret key as `evalWithAnswerFn (replayHash cache)` runs of its own oracle algorithms; `answerFn` is the same answer function, so the `eval_*` lemmas above give the first-order `CacheView`/`CacheReplay` forms of the stored tables. -/

theorem answerFn_eq_replayHash (cache : QueryCache HashSpec) :
    answerFn cache = Concrete.replayHash cache := rfl

@[simp]
theorem eval_replayHash_chainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (Concrete.replayHash cache)
      (Concrete.chainWalk parameter epoch chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.chainStep cache parameter epoch chain) position steps value := by
  rw [← answerFn_eq_replayHash]
  exact eval_chainWalk cache parameter epoch chain position steps value

@[simp]
theorem eval_replayHash_treeNode (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : Epoch → ChainIndex → Digest)
    (levels : Nat) (node : MerkleNode) :
    evalWithAnswerFn (Concrete.replayHash cache)
      (Concrete.treeNode parameter secret levels node : OracleComp HashSpec Digest) =
      treeNode cache parameter secret levels node := by
  rw [← answerFn_eq_replayHash]
  exact eval_treeNode cache parameter secret levels node

@[simp]
theorem precomputedSecretKey_chainValue (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec)
    (epoch : Epoch) (chain : ChainIndex) (digit : Digit) :
    (Concrete.precomputedSecretKey parameter secret cache).chainValue epoch chain digit =
      Wots.walk (CacheView.chainStep cache parameter epoch chain) 0 digit.val
        (secret epoch chain) :=
  eval_replayHash_chainWalk cache parameter epoch chain 0 digit.val (secret epoch chain)

@[simp]
theorem precomputedSecretKey_treeValue (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec)
    (height : MerkleHeight) (node : MerkleNode) :
    (Concrete.precomputedSecretKey parameter secret cache).treeValue height node =
      treeNode cache parameter secret height.val node :=
  eval_replayHash_treeNode cache parameter secret height.val node

def signedChainValues (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (epoch : Epoch) (encoding : Encoding) : ChainIndex → Digest :=
  fun chain => Wots.walk
    (CacheView.chainStep cache secretKey.parameter epoch chain) 0
    (encoding chain).val (secretKey.chainStart epoch chain)

def authenticationPath (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (epoch : Epoch) : Fin treeHeight → Digest :=
  fun level => treeNode cache secretKey.parameter secretKey.chainStart level.val
    (Concrete.authenticationPathNode epoch level)

def signWithEncoding (cache : QueryCache HashSpec) (secretKey : SecretKey)
    (epoch : Epoch) (randomness : Randomness) (encoding : Encoding) : Signature :=
  ⟨randomness, signedChainValues cache secretKey epoch encoding,
    authenticationPath cache secretKey epoch⟩

theorem precomputedSignedChainValues_eq (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec)
    (epoch : Epoch) (encoding : Encoding) :
    (fun chain => (Concrete.precomputedSecretKey parameter secret cache).chainValue epoch chain (encoding chain)) =
      signedChainValues cache (Concrete.precomputedSecretKey parameter secret cache)
        epoch encoding := by
  funext chain
  exact precomputedSecretKey_chainValue parameter secret cache epoch chain (encoding chain)

theorem precomputedAuthenticationPath_eq (parameter : PublicParameter)
    (secret : Epoch → ChainIndex → Digest) (cache : QueryCache HashSpec) (epoch : Epoch) :
    (fun level : Fin treeHeight => (Concrete.precomputedSecretKey parameter secret cache).treeValue
        level.castSucc (Concrete.authenticationPathNode epoch level)) =
      authenticationPath cache (Concrete.precomputedSecretKey parameter secret cache)
        epoch := by
  funext level
  exact precomputedSecretKey_treeValue parameter secret cache level.castSucc
    (Concrete.authenticationPathNode epoch level)

@[simp]
theorem eval_authenticationRoot (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (epoch : Epoch) (signature : Signature)
    (levels : Nat) (leaf : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.authenticationRoot parameter epoch signature levels leaf :
        OracleComp HashSpec Digest) =
      Merkle.ascend (CacheView.nodeHash cache parameter epoch)
        (Concrete.signaturePath signature) 0 levels leaf := by
  induction levels with
  | zero => simp [Concrete.authenticationRoot, Merkle.ascend]
  | succ levels ih =>
      simp only [Concrete.authenticationRoot, evalWithAnswerFn_bind, ih, Merkle.ascend,
        Nat.zero_add]
      by_cases hlevel : levels < treeHeight
      · by_cases hbit : epoch.val.testBit levels = true
        · simp [Concrete.authenticationNodeHash, CacheView.nodeHash, hlevel, hbit,
            Concrete.nodeHash, CacheView.nodeInput, CacheView.authenticationNodePayload,
            CacheView.tweakableHash]
        · simp [Concrete.authenticationNodeHash, CacheView.nodeHash, hlevel, hbit,
            Concrete.nodeHash, CacheView.nodeInput, CacheView.authenticationNodePayload,
            CacheView.tweakableHash]
      · simp [Concrete.authenticationNodeHash, CacheView.nodeHash, hlevel]

@[simp]
theorem eval_verifyAfterLeaf (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (epoch : Epoch) (signature : Signature) (leaf : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.verifyAfterLeaf publicKey epoch signature leaf : OracleComp HashSpec Bool) =
      decide (Merkle.ascend (CacheView.nodeHash cache publicKey.parameter epoch)
        (Concrete.signaturePath signature) 0 treeHeight leaf = publicKey.root) := by
  simp [Concrete.verifyAfterLeaf]

@[simp]
theorem eval_verify (cache : QueryCache HashSpec) (publicKey : PublicKey)
    (epoch : Epoch) (message : Message) (signature : Signature) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool) =
      Concrete.verifyFromCache cache publicKey epoch message signature := by
  classical
  unfold Concrete.verify Concrete.verifyFromCache
  simp only [evalWithAnswerFn_bind, eval_encodingHash]
  cases TargetSum.decodeDigest
    (CacheView.encodingHash cache publicKey.parameter epoch (message, signature.randomness)) <;> simp

theorem randomOracle_query_caches (input : HashInput)
    (initialCache : QueryCache HashSpec) (output : HashOutput)
    (finalCache : QueryCache HashSpec)
    (hmem : (output, finalCache) ∈
      support ((randomOracle (spec := HashSpec) input).run initialCache)) :
    finalCache input = some output := by
  cases hcache : initialCache input with
  | none =>
      rw [QueryImpl.withCaching_run_none _ hcache, support_map] at hmem
      obtain ⟨sampled, _, hresult⟩ := hmem
      cases hresult
      exact QueryCache.cacheQuery_self initialCache input output
  | some cached =>
      rw [QueryImpl.withCaching_run_some _ hcache, support_pure,
        Set.mem_singleton_iff] at hmem
      cases hmem
      exact hcache

theorem randomOracle_cache_le {α : Type} (computation : OracleComp HashSpec α)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hmem : result ∈ support ((simulateQ randomOracle computation).run initialCache)) :
    initialCache ≤ result.2 := by
  exact OracleComp.simulateQ_run_preservesInv randomOracle
    (fun cache => initialCache ≤ cache)
    (by
      intro input cache hcache queryResult hquery
      exact hcache.trans
        (QueryImpl.withCaching_cache_le uniformSampleImpl input cache
          queryResult hquery))
    computation initialCache le_rfl result hmem

/-- Rerunning a lazy random-oracle computation against any extension of a cache produced by a
successful first run is deterministic and leaves the larger cache unchanged. -/
theorem randomOracle_rerun_largerCache_eq_pure_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α)
    (initialCache resultCache largerCache : QueryCache HashSpec) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hle : resultCache ≤ largerCache) :
    (simulateQ randomOracle computation).run largerCache =
      pure (result, largerCache) := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache largerCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, _hcache⟩ := hmem
      rfl
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le (next output) middleCache
          (result, resultCache) hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        QueryImpl.withCaching_run_some _ hlarger]
      simp only [pure_bind]
      exact ih output middleCache resultCache largerCache result hrest hle

/-- Replaying a lazy-oracle execution against its final cache reproduces its result. -/
theorem eval_answerFn_finalCache_eq_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α) (initialCache finalCache : QueryCache HashSpec)
    (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache)) :
    evalWithAnswerFn (answerFn finalCache) computation = result := by
  induction computation using OracleComp.inductionOn generalizing initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.1.symm
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ finalCache :=
        randomOracle_cache_le (next output) middleCache (result, finalCache) hrest
      have hfinal : finalCache input = some output := hmiddleLe hmiddle
      simp only [evalWithAnswerFn_bind]
      have hqueryEval :
          evalWithAnswerFn (answerFn finalCache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) = output := by
        simpa [Concrete.oracleHash, answer, hfinal] using
          eval_oracleHash finalCache input
      rw [hqueryEval]
      exact ih output middleCache finalCache result hrest

/-- Replaying an execution against any extension of its final cache reproduces its result. -/
theorem eval_answerFn_largerCache_eq_of_mem_support {α : Type}
    (computation : OracleComp HashSpec α)
    (initialCache resultCache largerCache : QueryCache HashSpec) (result : α)
    (hmem : (result, resultCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (hle : resultCache ≤ largerCache) :
    evalWithAnswerFn (answerFn largerCache) computation = result := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache resultCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hmem.1.symm
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = some output :=
        randomOracle_query_caches input initialCache output middleCache hquery
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le (next output) middleCache (result, resultCache) hrest
      have hlarger : largerCache input = some output := hle (hmiddleLe hmiddle)
      simp only [evalWithAnswerFn_bind]
      have hqueryEval :
          evalWithAnswerFn (answerFn largerCache)
            (liftM (OracleSpec.query input) : OracleComp HashSpec HashOutput) = output := by
        simpa [Concrete.oracleHash, answer, hlarger] using
          eval_oracleHash largerCache input
      rw [hqueryEval]
      exact ih output middleCache resultCache result hrest hle

theorem verifyFromCache_eq_of_mem_support
    (publicKey : PublicKey) (epoch : Epoch) (message : Message)
    (signature : Signature) (initialCache finalCache : QueryCache HashSpec)
    (result : Bool)
    (hmem : (result, finalCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)).run
          initialCache)) :
    Concrete.verifyFromCache finalCache publicKey epoch message signature = result := by
  rw [← eval_verify]
  exact eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.verify publicKey epoch message signature : OracleComp HashSpec Bool)
    initialCache finalCache result hmem

end XmssSecurity.Concrete.CacheReplay

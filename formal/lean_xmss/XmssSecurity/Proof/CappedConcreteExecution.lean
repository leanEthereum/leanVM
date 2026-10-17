import XmssSecurity.Proof.OutcomeClassification
import XmssSecurity.Proof.PrecomputedKeygenCache

open OracleComp OracleSpec

namespace XmssSecurity

theorem capped_detailed_execution_verification_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.verified = Concrete.verifyFromCache execution.2 execution.1.publicKey
      execution.1.forgery.leafIndex execution.1.forgery.message execution.1.forgery.signature := by
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, _hkeygen, hrest⟩ := hmem
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, hverify, hout⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  subst execution
  simp only
  have hroute :
      simulateQ romImpl
          (Concrete.scheme.verify publicKey forgery.leafIndex forgery.message
            forgery.signature) =
        simulateQ randomOracle
          (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
            OracleComp HashSpec Bool) := by
    simp only [Concrete.scheme, romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.verify publicKey forgery.leafIndex forgery.message forgery.signature :
        OracleComp HashSpec Bool)
  rw [hroute] at hverify
  exact (Concrete.CacheReplay.verifyFromCache_eq_of_mem_support publicKey forgery.leafIndex
    forgery.message forgery.signature adversaryCache finalCache verified hverify).symm

theorem Concrete.CacheReplay.topSignFrom_decode_of_eval (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (key : TopIndex) (root : Digest) (base : Randomness)
    (attempts trial : Nat) (randomness : Randomness) (encoding : Encoding)
    (heval : evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.topSignFrom parameter key root base attempts trial :
        OracleComp HashSpec (Option (Randomness × Encoding))) = some (randomness, encoding)) :
    TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash cache parameter key (root, randomness)) = some encoding := by
  have hdigest : ∀ randomness, evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.topEncodingHash parameter key root randomness : OracleComp HashSpec Digest) =
      Concrete.CacheView.topEncodingHash cache parameter key (root, randomness) := by
    intro randomness
    simp [Concrete.topEncodingHash, Concrete.CacheView.topEncodingHash,
      Concrete.CacheView.topEncodingInput, Concrete.CacheView.tweakableHash]
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom] at heval
  | succ attempts ih =>
      simp only [Concrete.topSignFrom, evalWithAnswerFn_bind, hdigest] at heval
      split at heval
      · rename_i found hdecode
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at heval
        obtain ⟨rfl, rfl⟩ := heval
        exact hdecode
      · exact ih (trial + 1) heval

theorem Concrete.CacheReplay.eval_honestKeygen (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness) :
    evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
        OracleComp HashSpec _) =
      (Concrete.CacheReplay.topTreeNode cache parameter topSecret treeHeight Concrete.rootNode,
        fun key => evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
          (Concrete.topSignFrom parameter key
            (Concrete.CacheReplay.treeNode cache parameter secret treeHeight
              (Concrete.bottomRootNode key)) (topBase key) signingAttemptLimit 0 :
            OracleComp HashSpec (Option (Randomness × Encoding)))) := by
  simp [Concrete.honestKeygen, evalWithAnswerFn_bind]

set_option linter.constructorNameAsVariable false in
/-- Key generation's honest computation, replayed in the final cache, gives the root and the top
signatures. -/
theorem capped_detailed_execution_keygen_eval
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    ∃ topBase : TopIndex → Randomness,
      execution.1.publicKey.parameter = execution.1.secretKey.parameter ∧
      evalWithAnswerFn (Concrete.CacheReplay.answerFn execution.2)
        (Concrete.honestKeygen execution.1.secretKey.parameter execution.1.secretKey.chainStart
          execution.1.secretKey.topChainStart (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _) =
        (execution.1.publicKey.root, execution.1.secretKey.topSigned) := by
  unfold detailedGameWithCache detailedGameCore at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨⟨publicKey, secretKey⟩, keyCache⟩, hkeygen, hrest⟩ := hmem
  have hkeyCacheLe : keyCache ≤ execution.2 :=
    xmssRom_cache_le _ keyCache execution hrest
  simp only [Concrete.scheme] at hkeygen
  unfold Concrete.precomputedKeygen at hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨parameter, parameterCache⟩, _hparameter, hkeygen⟩ := hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨secret, secretCache⟩, _hsecret, hkeygen⟩ := hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨topSecret, topSecretCache⟩, _htopSecret, hkeygen⟩ := hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨topBase, topBaseCache⟩, _htopBase, hkeygen⟩ := hkeygen
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hkeygen
  obtain ⟨⟨treeResult, rootCache⟩, hroot, hout⟩ := hkeygen
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hout
  cases hout
  unfold detailedGameAfterKeygen at hrest
  simp only at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨⟨forgery, signingLog⟩, adversaryCache⟩, _hadversary, hverifyRest⟩ := hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hverifyRest
  obtain ⟨⟨verified, finalCache⟩, _hverify, hfinal⟩ := hverifyRest
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hfinal
  cases hfinal
  let honest : OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
    Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key))
  have hroute :
      simulateQ romImpl (liftM honest.withQueryLog) = simulateQ randomOracle honest.withQueryLog := by
    simp only [romImpl]
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp)) honest.withQueryLog
  rw [hroute] at hroot
  have hroot' : (treeResult.1, keyCache) ∈ support
      ((simulateQ randomOracle honest).run topBaseCache) := by
    rw [← withQueryLog_cache_projection, support_map]
    exact ⟨(treeResult, keyCache), hroot, rfl⟩
  refine ⟨topBase, rfl, ?_⟩
  exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support honest topBaseCache
    keyCache finalCache treeResult.1 hroot' hkeyCacheLe

theorem capped_detailed_execution_key_components_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey.parameter = execution.1.secretKey.parameter ∧
      execution.1.publicKey.root = Concrete.CacheReplay.topTreeNode execution.2
        execution.1.secretKey.parameter execution.1.secretKey.topChainStart treeHeight
        Concrete.rootNode := by
  obtain ⟨topBase, hparameter, heval⟩ :=
    capped_detailed_execution_keygen_eval adversary execution hmem
  rw [Concrete.CacheReplay.eval_honestKeygen] at heval
  exact ⟨hparameter, (congrArg Prod.fst heval).symm⟩

/-- The top signatures key generation computed decode, in the final cache, on their bottom roots. -/
theorem capped_detailed_execution_topSigned_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    ∀ key randomness encoding,
      execution.1.secretKey.topSigned key = some (randomness, encoding) →
        TargetSum.decodeDigest
          (Concrete.CacheView.topEncodingHash execution.2 execution.1.secretKey.parameter key
            (Concrete.bottomRoot execution.2 execution.1.secretKey key, randomness)) = some encoding := by
  intro key randomness encoding hsigned
  obtain ⟨topBase, -, heval⟩ :=
    capped_detailed_execution_keygen_eval adversary execution hmem
  rw [Concrete.CacheReplay.eval_honestKeygen] at heval
  have hkey := congrFun (congrArg Prod.snd heval) key
  simp only at hkey
  rw [hsigned] at hkey
  exact Concrete.CacheReplay.topSignFrom_decode_of_eval execution.2 _ key _ (topBase key)
    signingAttemptLimit 0 randomness encoding hkey

theorem capped_detailed_execution_key_consistent
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary)) :
    execution.1.publicKey =
      Concrete.CacheReplay.publicKeyFromCache execution.2 execution.1.secretKey := by
  obtain ⟨hparameter, hroot⟩ :=
    capped_detailed_execution_key_components_consistent adversary execution hmem
  cases hpublicKey : execution.1.publicKey with
  | mk root parameter =>
      simp only [hpublicKey] at hparameter hroot ⊢
      subst parameter
      exact Concrete.CacheReplay.publicKey_eq_publicKeyFromCache execution.2
        execution.1.secretKey root hroot

theorem capped_detailed_execution_consistent_of_signing
    (adversary : Adversary)
    (execution : GameOutcome × QueryCache HashSpec)
    (hmem : execution ∈ support
      (detailedGameWithCache Concrete.scheme adversary))
    (hsigning : ∀ request signature,
      SigningTranscript.Returned execution.1.signingLog request signature →
      ∃ encoding,
        TargetSum.decodeDigest
          (Concrete.CacheView.encodingHash execution.2 execution.1.secretKey.parameter
            request.leafIndex (request.message, signature.randomness)) = some encoding ∧
        signature = Concrete.CacheReplay.signWithEncoding execution.2 execution.1.secretKey
          request.leafIndex signature.randomness encoding) :
    ConcreteOutcomeConsistent execution.2 execution.1 :=
  ⟨capped_detailed_execution_key_consistent adversary execution hmem,
    capped_detailed_execution_verification_consistent adversary execution hmem, hsigning,
    capped_detailed_execution_topSigned_consistent adversary execution hmem⟩

end XmssSecurity

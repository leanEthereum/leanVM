import XmssSecurity.Proof.ChainOraclePresampling

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

theorem verify_true_chain_query_cached_as_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding) (chain : ChainIndex) (offset : Nat)
    (hoffset : offset < chainLength - 1 - (encoding chain).val)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
        (message, signature.randomness)) = some encoding)
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.chainInput publicKey.parameter leafIndex chain
        ⟨(encoding chain).val + offset, by omega⟩
        (Wots.walk (Concrete.CacheView.chainStep largerCache publicKey.parameter leafIndex chain)
          (encoding chain).val offset (signature.chainValue chain))) = some output := by
  unfold Concrete.verify at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hafterDigest⟩ := hmem
  cases hactualDecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hactualDecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Bool.true_eq_false] at hafterDigest
      exact hafterDigest.1.elim
  | some actualEncoding =>
      have hdigestResultLe : digestCache ≤ resultCache :=
        randomOracle_cache_le
          (do
            let endpoints ← Concrete.recoverEndpoints publicKey.parameter leafIndex
              actualEncoding signature
            let leaf ← Concrete.leafHash publicKey.parameter leafIndex endpoints
            Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          digestCache (true, resultCache) (by
            simpa only [hactualDecode] using hafterDigest)
      have hdigestEval := eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
          OracleComp HashSpec Digest)
        initialCache digestCache largerCache digest hdigest (hdigestResultLe.trans hle)
      rw [eval_encodingHash] at hdigestEval
      have hencoding : actualEncoding = encoding := by
        rw [hdigestEval, hactualDecode] at hdecode
        exact Option.some.inj hdecode
      subst actualEncoding
      simp only [hactualDecode] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterDigest
      obtain ⟨⟨endpoints, endpointsCache⟩, hendpoints, hafterEndpoints⟩ := hafterDigest
      have hendpointsResultLe : endpointsCache ≤ resultCache :=
        randomOracle_cache_le
          (do
            let leaf ← Concrete.leafHash publicKey.parameter leafIndex endpoints
            Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)
          endpointsCache (true, resultCache) hafterEndpoints
      unfold Concrete.recoverEndpoints at hendpoints
      obtain ⟨beforeCache, afterCache, value, hchain, hchainLe⟩ :=
        sequenceFin_component_support_in_largerCache
          (fun index => Concrete.recoverChain publicKey.parameter leafIndex index
            (encoding index) (signature.chainValue index) :
            ChainIndex → OracleComp HashSpec Digest)
          chain digestCache endpointsCache largerCache endpoints hendpoints
          (hendpointsResultLe.trans hle)
      unfold Concrete.recoverChain at hchain
      exact chainWalk_query_cached_in_largerCache publicKey.parameter leafIndex chain
        (encoding chain).val (chainLength - 1 - (encoding chain).val)
        (signature.chainValue chain) offset hoffset (by omega) beforeCache afterCache
        largerCache value hchain hchainLe

end XmssSecurity.Concrete.CacheReplay

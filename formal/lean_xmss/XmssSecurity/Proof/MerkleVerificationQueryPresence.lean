import XmssSecurity.Proof.MerkleQueryPresence

open OracleComp OracleSpec ENNReal

namespace XmssSecurity.Concrete.CacheReplay

set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

def verificationAfterEncoding (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (encoding : Encoding) : OracleComp HashSpec Bool := do
  let endpoints ← Concrete.recoverEndpoints publicKey.parameter leafIndex encoding signature
  let leaf ← Concrete.leafHash publicKey.parameter leafIndex endpoints
  Concrete.verifyAfterLeaf publicKey leafIndex signature leaf

attribute [irreducible] verificationAfterEncoding

def verificationAfterEndpoints (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (endpoints : ChainIndex → Digest) : OracleComp HashSpec Bool := do
  let leaf ← Concrete.leafHash publicKey.parameter leafIndex endpoints
  Concrete.verifyAfterLeaf publicKey leafIndex signature leaf

attribute [irreducible] verificationAfterEndpoints

def authenticationRootComputation (parameter : PublicParameter) (leafIndex : LeafIndex)
    (signature : Signature) (levels : Nat) (leaf : Digest) : OracleComp HashSpec Digest :=
  Concrete.authenticationRoot parameter leafIndex signature levels leaf

def verificationAfterLeafRoot (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) : OracleComp HashSpec Bool := do
  let root ← authenticationRootComputation publicKey.parameter leafIndex signature treeHeight leaf
  Concrete.verifyTop publicKey (topKeyOf leafIndex) root signature.top

theorem verificationAfterLeafRoot_eq (publicKey : PublicKey) (leafIndex : LeafIndex)
    (signature : Signature) (leaf : Digest) :
    verificationAfterLeafRoot publicKey leafIndex signature leaf =
      (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool) := by
  unfold verificationAfterLeafRoot authenticationRootComputation Concrete.verifyAfterLeaf
  rfl

attribute [irreducible] authenticationRootComputation verificationAfterLeafRoot

inductive VerifiedDigestRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec) : Prop where
  | intro (actualEncoding : Encoding) (digestCache : QueryCache HashSpec) (digest : Digest)
      (digest_mem : (digest, digestCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
            OracleComp HashSpec Digest)).run initialCache))
      (decode_eq : TargetSum.decodeDigest digest = some actualEncoding)
      (rest_mem : (true, resultCache) ∈ support
        ((simulateQ randomOracle
          (verificationAfterEncoding publicKey leafIndex signature actualEncoding)).run digestCache))
      (digest_le : digestCache ≤ resultCache) :
      VerifiedDigestRun publicKey leafIndex message signature initialCache resultCache

theorem verify_true_digestRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache)) :
    VerifiedDigestRun publicKey leafIndex message signature initialCache resultCache := by
  unfold Concrete.verify at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hafterDigest⟩ := hmem
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Bool.true_eq_false] at hafterDigest
      exact hafterDigest.1.elim
  | some encoding =>
      have hrest : (true, resultCache) ∈ support
          ((simulateQ randomOracle
            (verificationAfterEncoding publicKey leafIndex signature encoding)).run digestCache) := by
        simpa only [hdecode, verificationAfterEncoding] using hafterDigest
      exact .intro encoding digestCache digest hdigest hdecode hrest
        (randomOracle_cache_le
          (verificationAfterEncoding publicKey leafIndex signature encoding)
          digestCache (true, resultCache) hrest)

inductive VerifiedEndpointsRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec) : Prop where
  | intro (actualEncoding : Encoding) (digestCache endpointsCache : QueryCache HashSpec)
      (digest : Digest) (endpoints : ChainIndex → Digest)
      (digest_mem : (digest, digestCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
            OracleComp HashSpec Digest)).run initialCache))
      (decode_eq : TargetSum.decodeDigest digest = some actualEncoding)
      (endpoints_mem : (endpoints, endpointsCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.recoverEndpoints publicKey.parameter leafIndex actualEncoding signature :
            OracleComp HashSpec (ChainIndex → Digest))).run digestCache))
      (rest_mem : (true, resultCache) ∈ support
        ((simulateQ randomOracle
          (verificationAfterEndpoints publicKey leafIndex signature endpoints)).run endpointsCache))
      (digest_le : digestCache ≤ resultCache) (endpoints_le : endpointsCache ≤ resultCache) :
      VerifiedEndpointsRun publicKey leafIndex message signature initialCache resultCache

theorem VerifiedDigestRun.toEndpointsRun
    {publicKey : PublicKey} {leafIndex : LeafIndex} {message : Message} {signature : Signature}
    {initialCache resultCache : QueryCache HashSpec}
    (run : VerifiedDigestRun publicKey leafIndex message signature initialCache resultCache) :
    VerifiedEndpointsRun publicKey leafIndex message signature initialCache resultCache := by
  obtain ⟨actualEncoding, digestCache, digest, hdigest, hdecode, hrest, hdigestLe⟩ := run
  unfold verificationAfterEncoding at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨endpoints, endpointsCache⟩, hendpoints, hafterEndpoints⟩ := hrest
  have hafter : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (verificationAfterEndpoints publicKey leafIndex signature endpoints)).run endpointsCache) := by
    simpa only [verificationAfterEndpoints] using hafterEndpoints
  exact .intro actualEncoding digestCache endpointsCache digest endpoints hdigest hdecode
    hendpoints hafter hdigestLe
    (randomOracle_cache_le (verificationAfterEndpoints publicKey leafIndex signature endpoints)
      endpointsCache (true, resultCache) hafter)

inductive VerifiedLeafRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (initialCache resultCache : QueryCache HashSpec) : Prop where
  | intro (actualEncoding : Encoding)
      (digestCache endpointsCache leafCache : QueryCache HashSpec)
      (digest : Digest) (endpoints : ChainIndex → Digest) (leaf : Digest)
      (digest_mem : (digest, digestCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
            OracleComp HashSpec Digest)).run initialCache))
      (decode_eq : TargetSum.decodeDigest digest = some actualEncoding)
      (endpoints_mem : (endpoints, endpointsCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.recoverEndpoints publicKey.parameter leafIndex actualEncoding signature :
            OracleComp HashSpec (ChainIndex → Digest))).run digestCache))
      (leaf_mem : (leaf, leafCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.leafHash publicKey.parameter leafIndex endpoints :
            OracleComp HashSpec Digest)).run endpointsCache))
      (rest_mem : (true, resultCache) ∈ support
        ((simulateQ randomOracle
          (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
            OracleComp HashSpec Bool)).run leafCache))
      (digest_le : digestCache ≤ resultCache) (endpoints_le : endpointsCache ≤ resultCache)
      (leaf_le : leafCache ≤ resultCache) :
      VerifiedLeafRun publicKey leafIndex message signature initialCache resultCache

theorem VerifiedEndpointsRun.toLeafRun
    {publicKey : PublicKey} {leafIndex : LeafIndex} {message : Message} {signature : Signature}
    {initialCache resultCache : QueryCache HashSpec}
    (run : VerifiedEndpointsRun publicKey leafIndex message signature initialCache resultCache) :
    VerifiedLeafRun publicKey leafIndex message signature initialCache resultCache := by
  obtain ⟨actualEncoding, digestCache, endpointsCache, digest, endpoints, hdigest, hdecode,
      hendpoints, hrest, hdigestLe, hendpointsLe⟩ := run
  unfold verificationAfterEndpoints at hrest
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨⟨leaf, leafCache⟩, hleaf, hafterLeaf⟩ := hrest
  exact .intro actualEncoding digestCache endpointsCache leafCache digest endpoints leaf hdigest
    hdecode hendpoints hleaf hafterLeaf hdigestLe hendpointsLe
    (randomOracle_cache_le
      (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf : OracleComp HashSpec Bool)
      leafCache (true, resultCache) hafterLeaf)

theorem authenticationRootRun_of_verifyAfterLeaf
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature)
    (leafCache : QueryCache HashSpec) (leaf : Digest) (resultCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verifyAfterLeaf publicKey leafIndex signature leaf :
          OracleComp HashSpec Bool)).run leafCache)) :
    ∃ rootCache root,
      (root, rootCache) ∈ support
        ((simulateQ randomOracle
          (authenticationRootComputation publicKey.parameter leafIndex signature treeHeight leaf)).run
            leafCache) ∧
      rootCache ≤ resultCache := by
  have hmem' : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (verificationAfterLeafRoot publicKey leafIndex signature leaf)).run leafCache) := by
    rw [verificationAfterLeafRoot_eq]
    exact hmem
  unfold verificationAfterLeafRoot at hmem'
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem'
  obtain ⟨⟨root, rootCache⟩, hroot, hresult⟩ := hmem'
  exact ⟨rootCache, root, hroot,
    randomOracle_cache_le (Concrete.verifyTop publicKey (topKeyOf leafIndex) root signature.top :
      OracleComp HashSpec Bool) rootCache (true, resultCache) hresult⟩

inductive VerifiedAuthenticationRootRun
    (publicKey : PublicKey) (leafIndex : LeafIndex) (signature : Signature)
    (encoding : Encoding) (resultCache largerCache : QueryCache HashSpec) : Prop where
  | intro (leafCache : QueryCache HashSpec) (leaf : Digest)
      (rootCache : QueryCache HashSpec) (root : Digest)
      (root_mem : (root, rootCache) ∈ support
        ((simulateQ randomOracle
          (authenticationRootComputation publicKey.parameter leafIndex signature treeHeight leaf)).run
            leafCache))
      (root_le : rootCache ≤ resultCache)
      (leaf_eq : Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex
        (recoveredEndpoints
          (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter leafIndex chain)
          encoding signature.chainValue) = leaf) :
      VerifiedAuthenticationRootRun publicKey leafIndex signature encoding resultCache largerCache

theorem verify_true_authenticationRoot_support_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
        (message, signature.randomness)) = some encoding)
    (hle : resultCache ≤ largerCache) :
    VerifiedAuthenticationRootRun publicKey leafIndex signature encoding resultCache largerCache := by
  have leafRun :=
    ((verify_true_digestRun publicKey leafIndex message signature initialCache resultCache hmem).toEndpointsRun).toLeafRun
  obtain ⟨actualEncoding, digestCache, endpointsCache, leafCache, digest, endpoints, leaf,
      hdigest, hactualDecode, hendpoints, hleaf, hafterLeaf, hdigestLe,
      hendpointsLe, hleafLe⟩ := leafRun
  obtain ⟨rootCache, root, hroot, hrootLe⟩ :=
    authenticationRootRun_of_verifyAfterLeaf publicKey leafIndex signature leafCache leaf
      resultCache hafterLeaf
  have hdigestEval := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.encodingHash publicKey.parameter leafIndex message signature.randomness :
      OracleComp HashSpec Digest)
    initialCache digestCache largerCache digest hdigest (hdigestLe.trans hle)
  rw [eval_encodingHash] at hdigestEval
  have hencoding : actualEncoding = encoding := by
    rw [hdigestEval, hactualDecode] at hdecode
    exact Option.some.inj hdecode
  subst actualEncoding
  have hendpointsEval := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.recoverEndpoints publicKey.parameter leafIndex encoding signature :
      OracleComp HashSpec (ChainIndex → Digest))
    digestCache endpointsCache largerCache endpoints hendpoints (hendpointsLe.trans hle)
  rw [eval_recoverEndpoints] at hendpointsEval
  have hleafEval := eval_answerFn_largerCache_eq_of_mem_support
    (Concrete.leafHash publicKey.parameter leafIndex endpoints : OracleComp HashSpec Digest)
    endpointsCache leafCache largerCache leaf hleaf (hleafLe.trans hle)
  rw [eval_leafHash] at hleafEval
  refine .intro leafCache leaf rootCache root hroot hrootLe ?_
  exact (congrArg
    (Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex)
    hendpointsEval).trans hleafEval

theorem authenticationRoot_query_cached_as_in_largerCache
    (parameter : PublicParameter) (leafIndex : LeafIndex) (signature : Signature)
    (levels : Nat) (leaf : Digest) (target : MerkleLevel)
    (htarget : target.val < levels) (hlevels : levels ≤ treeHeight)
    (initialCache resultCache largerCache : QueryCache HashSpec) (root : Digest)
    (hmem : (root, resultCache) ∈ support
      ((simulateQ randomOracle
        (authenticationRootComputation parameter leafIndex signature levels leaf)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (Concrete.CacheView.nodeInput parameter leafIndex target
        (Merkle.ascend (Concrete.CacheView.nodeHash largerCache parameter leafIndex)
          (Concrete.signaturePath signature) 0 target.val leaf)
        (Concrete.signaturePath signature target.val)) = some output := by
  unfold authenticationRootComputation at hmem
  induction levels generalizing initialCache resultCache root with
  | zero => omega
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Concrete.authenticationRoot, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨current, currentCache⟩, hcurrent, hnode⟩ := hmem
      have hcurrentLe : currentCache ≤ resultCache :=
        randomOracle_cache_le
          (Concrete.authenticationNodeHash parameter leafIndex levels current
            (Concrete.signaturePath signature levels) : OracleComp HashSpec Digest)
          currentCache (root, resultCache) hnode
      by_cases heq : target.val = levels
      · have htargetEq : target = ⟨levels, hlevel⟩ := Fin.ext heq
        subst target
        have hcurrentEval := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.authenticationRoot parameter leafIndex signature levels leaf :
            OracleComp HashSpec Digest)
          initialCache currentCache largerCache current hcurrent (hcurrentLe.trans hle)
        rw [eval_authenticationRoot] at hcurrentEval
        unfold Concrete.authenticationNodeHash at hnode
        simp only [hlevel, ↓reduceDIte] at hnode
        by_cases hbit : leafIndex.val.testBit levels = true
        · simp only [hbit, ↓reduceIte] at hnode
          obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
            (.merkle ⟨levels, hlevel⟩ (Concrete.CacheView.nodeIndex leafIndex levels))
            (Concrete.nodePayload (Concrete.signaturePath signature levels) current)
            currentCache resultCache root (by
              simpa [Concrete.nodeHash] using hnode)
          refine ⟨output, ?_⟩
          rw [hcurrentEval]
          change resultCache
            (XmssSecurity.tweakableHashInput parameter
              (.merkle ⟨levels, hlevel⟩ (Concrete.CacheView.nodeIndex leafIndex levels))
              (if leafIndex.val.testBit levels = true then
                Concrete.nodePayload (Concrete.signaturePath signature levels) current
              else Concrete.nodePayload current
                (Concrete.signaturePath signature levels))) = some output
          rw [ite_eq_left hbit]
          exact hcached
        · have hbitFalse : leafIndex.val.testBit levels = false :=
            Bool.eq_false_of_not_eq_true hbit
          simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hnode
          obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
            (.merkle ⟨levels, hlevel⟩ (Concrete.CacheView.nodeIndex leafIndex levels))
            (Concrete.nodePayload current (Concrete.signaturePath signature levels))
            currentCache resultCache root (by
              simpa [Concrete.nodeHash] using hnode)
          refine ⟨output, ?_⟩
          rw [hcurrentEval]
          change resultCache
            (XmssSecurity.tweakableHashInput parameter
              (.merkle ⟨levels, hlevel⟩ (Concrete.CacheView.nodeIndex leafIndex levels))
              (if leafIndex.val.testBit levels = true then
                Concrete.nodePayload (Concrete.signaturePath signature levels) current
              else Concrete.nodePayload current
                (Concrete.signaturePath signature levels))) = some output
          rw [ite_eq_right hbit]
          exact hcached
      · have htargetLt : target.val < levels := by omega
        obtain ⟨output, hcached⟩ := ih htargetLt (Nat.le_of_succ_le hlevels)
          initialCache currentCache current hcurrent (hcurrentLe.trans hle)
        exact ⟨output, hcurrentLe hcached⟩


set_option maxHeartbeats 1200000 in
set_option linter.constructorNameAsVariable false in
theorem verify_true_merkle_query_cached_as_in_largerCache
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding) (target : MerkleLevel)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
        (message, signature.randomness)) = some encoding)
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (Concrete.CacheView.nodeInput publicKey.parameter leafIndex target
        (Merkle.ascend (Concrete.CacheView.nodeHash largerCache publicKey.parameter leafIndex)
          (Concrete.signaturePath signature) 0 target.val
          (Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter
                leafIndex chain)
              encoding signature.chainValue)))
        (Concrete.signaturePath signature target.val)) = some output := by
  obtain ⟨leafCache, leaf, rootCache, root, hroot, hrootLe, hleaf⟩ :=
    verify_true_authenticationRoot_support_in_largerCache publicKey leafIndex message signature
      encoding initialCache resultCache largerCache hmem hdecode hle
  obtain ⟨output, hcached⟩ := authenticationRoot_query_cached_as_in_largerCache
    publicKey.parameter leafIndex signature treeHeight leaf target target.isLt le_rfl leafCache
    rootCache largerCache root hroot (hrootLe.trans hle)
  rw [hleaf]
  exact ⟨output, hrootLe hcached⟩

end XmssSecurity.Concrete.CacheReplay

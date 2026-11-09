module

public import XmssSecurity.Proof.MerkleVerificationQueryPresence
public import XmssSecurity.Proof.ChainOraclePresampling

@[expose] public section

/-!
# The top layer's queries in a successful verification

A successful verification runs the top check on the bottom root its bottom layer reaches, and that
check caches its top message digest input, its top chain steps from the forged digits on, its top leaf
and every top node on its path.
-/

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

set_option linter.constructorNameAsVariable false
attribute [local irreducible] Concrete.topAuthenticationRoot

/-- A successful verification runs the top check on the bottom root, as the cache computes it. -/
theorem verify_true_verifyTop_run
    (publicKey : PublicKey) (leafIndex : LeafIndex) (message : Message) (signature : Signature)
    (encoding : Encoding) (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verify publicKey leafIndex message signature :
          OracleComp HashSpec Bool)).run initialCache))
    (hdecode : TargetSum.decodeDigest
      (Concrete.CacheView.encodingHash largerCache publicKey.parameter leafIndex
        (message, signature.randomness)) = some encoding)
    (hle : resultCache ≤ largerCache) :
    ∃ topCache, (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verifyTop publicKey (topKeyOf leafIndex)
          (Merkle.ascend (Concrete.CacheView.nodeHash largerCache publicKey.parameter leafIndex)
            (Concrete.signaturePath signature) 0 treeHeight
            (Concrete.CacheView.leafHash largerCache publicKey.parameter leafIndex
              (recoveredEndpoints
                (fun chain => Concrete.CacheView.chainStep largerCache publicKey.parameter
                  leafIndex chain)
                encoding signature.chainValue)))
          signature.top : OracleComp HashSpec Bool)).run topCache) := by
  have leafRun :=
    ((verify_true_digestRun publicKey leafIndex message signature initialCache resultCache
      hmem).toEndpointsRun).toLeafRun
  obtain ⟨actualEncoding, digestCache, endpointsCache, leafCache, digest, endpoints, leaf,
      hdigest, hactualDecode, hendpoints, hleaf, hafterLeaf, hdigestLe,
      hendpointsLe, hleafLe⟩ := leafRun
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
  rw [← verificationAfterLeafRoot_eq] at hafterLeaf
  unfold verificationAfterLeafRoot at hafterLeaf
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterLeaf
  obtain ⟨⟨root, rootCache⟩, hroot, htop⟩ := hafterLeaf
  dsimp only at htop
  have hrootLe : rootCache ≤ resultCache :=
    randomOracle_cache_le
      (Concrete.verifyTop publicKey (topKeyOf leafIndex) root signature.top :
        OracleComp HashSpec Bool) rootCache (true, resultCache) htop
  have hrootEval := eval_answerFn_largerCache_eq_of_mem_support
    (authenticationRootComputation publicKey.parameter leafIndex signature treeHeight leaf)
    leafCache rootCache largerCache root hroot (hrootLe.trans hle)
  unfold authenticationRootComputation at hrootEval
  rw [eval_authenticationRoot] at hrootEval
  refine ⟨rootCache, ?_⟩
  rw [hendpointsEval, hleafEval, hrootEval]
  exact htop

theorem topChainWalk_query_cached_in_largerCache
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps)
    (hposition : position + offset < chainLength - 1)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.topChainWalk parameter key chain position steps value :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.topChainInput parameter key chain
        ⟨position + offset, hposition⟩
        (Wots.walk (Concrete.CacheView.topChainStep largerCache parameter key chain)
          position offset value)) = some output := by
  induction steps generalizing offset initialCache resultCache digest with
  | zero => omega
  | succ steps ih =>
      rw [Concrete.topChainWalk, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨previous, middleCache⟩, hprefix, hrest⟩ := hmem
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le
          (if hlast : position + steps < chainLength - 1 then
            Concrete.topChainHash parameter key chain ⟨position + steps, hlast⟩ previous
          else pure 0 : OracleComp HashSpec Digest)
          middleCache (digest, resultCache) hrest
      by_cases hbefore : offset < steps
      · exact ih offset hbefore hposition initialCache middleCache previous hprefix
          (hmiddleLe.trans hle)
      · have hoffsetEq : offset = steps := by omega
        subst offset
        simp only [hposition, ↓reduceDIte] at hrest
        obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
          (.topChain key chain ⟨position + steps, hposition⟩)
          (Concrete.digestBytes previous) middleCache resultCache digest hrest
        have hprevious := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.topChainWalk parameter key chain position steps value :
            OracleComp HashSpec Digest)
          initialCache middleCache largerCache previous hprefix (hmiddleLe.trans hle)
        rw [eval_topChainWalk] at hprevious
        refine ⟨output, ?_⟩
        rw [hprevious]
        exact hle hcached

theorem topAuthenticationRoot_query_cached_as_in_largerCache
    (parameter : PublicParameter) (key : TopIndex) (path : Fin treeHeight → Digest)
    (levels : Nat) (leaf : Digest) (target : MerkleLevel)
    (htarget : target.val < levels) (hlevels : levels ≤ treeHeight)
    (initialCache resultCache largerCache : QueryCache HashSpec) (root : Digest)
    (hmem : (root, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.topAuthenticationRoot parameter key path levels leaf :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (Concrete.CacheView.topNodeInput parameter key target
        (Merkle.ascend (Concrete.CacheView.topNodeHash largerCache parameter key)
          (Concrete.layerPath ⟨0, fun _ => 0, path⟩) 0 target.val leaf)
        (Concrete.layerPath ⟨0, fun _ => 0, path⟩ target.val)) = some output := by
  induction levels generalizing initialCache resultCache root with
  | zero => omega
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      rw [Concrete.topAuthenticationRoot, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨current, currentCache⟩, hcurrent, hnode⟩ := hmem
      simp only [hlevel, ↓reduceDIte] at hnode
      have hcurrentLe : currentCache ≤ resultCache :=
        randomOracle_cache_le _ currentCache (root, resultCache) hnode
      by_cases heq : target.val = levels
      · have htargetEq : target = ⟨levels, hlevel⟩ := Fin.ext heq
        subst target
        have hcurrentEval := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.topAuthenticationRoot parameter key path levels leaf :
            OracleComp HashSpec Digest)
          initialCache currentCache largerCache current hcurrent (hcurrentLe.trans hle)
        rw [eval_topAuthenticationRoot] at hcurrentEval
        have hsibling : Concrete.layerPath ⟨0, fun _ => 0, path⟩ levels = path ⟨levels, hlevel⟩ := by
          simp [Concrete.layerPath, hlevel]
        rw [hcurrentEval, hsibling]
        by_cases hbit : key.val.testBit levels = true
        · simp only [hbit, ↓reduceIte] at hnode
          obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
            (.topMerkle ⟨levels, hlevel⟩ (Concrete.topNodeIndex key levels))
            (Concrete.nodePayload (path ⟨levels, hlevel⟩) current)
            currentCache resultCache root (by simpa [Concrete.topNodeHash] using hnode)
          refine ⟨output, ?_⟩
          change resultCache (XmssSecurity.tweakableHashInput parameter
            (.topMerkle ⟨levels, hlevel⟩ (Concrete.topNodeIndex key levels))
            (if key.val.testBit levels then
              Concrete.nodePayload (path ⟨levels, hlevel⟩) current
            else Concrete.nodePayload current (path ⟨levels, hlevel⟩))) = some output
          rw [ite_eq_left hbit]
          exact hcached
        · have hbitFalse : key.val.testBit levels = false :=
            Bool.eq_false_of_not_eq_true hbit
          simp only [hbitFalse, Bool.false_eq_true, ↓reduceIte] at hnode
          obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
            (.topMerkle ⟨levels, hlevel⟩ (Concrete.topNodeIndex key levels))
            (Concrete.nodePayload current (path ⟨levels, hlevel⟩))
            currentCache resultCache root (by simpa [Concrete.topNodeHash] using hnode)
          refine ⟨output, ?_⟩
          change resultCache (XmssSecurity.tweakableHashInput parameter
            (.topMerkle ⟨levels, hlevel⟩ (Concrete.topNodeIndex key levels))
            (if key.val.testBit levels then
              Concrete.nodePayload (path ⟨levels, hlevel⟩) current
            else Concrete.nodePayload current (path ⟨levels, hlevel⟩))) = some output
          rw [ite_eq_right hbit]
          exact hcached
      · have htargetLt : target.val < levels := by omega
        obtain ⟨output, hcached⟩ := ih htargetLt (Nat.le_of_succ_le hlevels)
          initialCache currentCache current hcurrent (hcurrentLe.trans hle)
        exact ⟨output, hcurrentLe hcached⟩

/-- What a successful top check caches: its digest input, the forged top chains from their digits,
the top leaf and the top nodes on its path. -/
def TopQueriesCached (cache : QueryCache HashSpec) (parameter : PublicParameter) (key : TopIndex)
    (root : Digest) (part : LayerSignature) : Prop :=
  ∃ encoding,
    TargetSum.decodeDigest
      (Concrete.CacheView.topEncodingHash cache parameter key (root, part.randomness)) =
        some encoding ∧
    (∃ output, cache (Concrete.CacheView.topEncodingInput parameter key (root, part.randomness)) =
      some output) ∧
    (∀ chain offset (hoffset : offset < chainLength - 1 - (encoding chain).val),
      ∃ output, cache
        (Concrete.CacheView.topChainInput parameter key chain
          ⟨(encoding chain).val + offset, by omega⟩
          (Wots.walk (Concrete.CacheView.topChainStep cache parameter key chain)
            (encoding chain).val offset (part.chainValue chain))) = some output) ∧
    (∃ output, cache
      (Concrete.CacheView.topLeafInput parameter key
        (recoveredEndpoints (fun chain => Concrete.CacheView.topChainStep cache parameter key chain)
          encoding part.chainValue)) = some output) ∧
    (∀ level : MerkleLevel, ∃ output, cache
      (Concrete.CacheView.topNodeInput parameter key level
        (Merkle.ascend (Concrete.CacheView.topNodeHash cache parameter key)
          (Concrete.layerPath part) 0 level.val
          (Concrete.CacheView.topLeafHash cache parameter key
            (recoveredEndpoints
              (fun chain => Concrete.CacheView.topChainStep cache parameter key chain)
              encoding part.chainValue)))
        (Concrete.layerPath part level.val)) = some output)

theorem verifyTop_true_queries_cached
    (publicKey : PublicKey) (key : TopIndex) (root : Digest) (part : LayerSignature)
    (initialCache resultCache largerCache : QueryCache HashSpec)
    (hmem : (true, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.verifyTop publicKey key root part : OracleComp HashSpec Bool)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    TopQueriesCached largerCache publicKey.parameter key root part := by
  unfold Concrete.verifyTop at hmem
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
  obtain ⟨⟨digest, digestCache⟩, hdigest, hafterDigest⟩ := hmem
  cases hdecode : TargetSum.decodeDigest digest with
  | none =>
      simp only [hdecode, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq, Bool.true_eq_false] at hafterDigest
      exact hafterDigest.1.elim
  | some encoding =>
      simp only [hdecode] at hafterDigest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterDigest
      obtain ⟨⟨endpoints, endpointsCache⟩, hendpoints, hafterEndpoints⟩ := hafterDigest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterEndpoints
      obtain ⟨⟨leaf, leafCache⟩, hleaf, hafterLeaf⟩ := hafterEndpoints
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hafterLeaf
      obtain ⟨⟨topRoot, rootCache⟩, hroot, hfinal⟩ := hafterLeaf
      dsimp only at hendpoints hleaf hroot
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
      have hrootLarger : rootCache ≤ largerCache := by
        rw [← hfinal.2]
        exact hle
      have hleafLe : leafCache ≤ rootCache :=
        randomOracle_cache_le _ leafCache (topRoot, rootCache) hroot
      have hendpointsLe : endpointsCache ≤ rootCache :=
        (randomOracle_cache_le _ endpointsCache (leaf, leafCache) hleaf).trans hleafLe
      have hdigestLe : digestCache ≤ rootCache :=
        (randomOracle_cache_le _ digestCache (endpoints, endpointsCache) hendpoints).trans
          hendpointsLe
      have hdigestEval := eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.topEncodingHash publicKey.parameter key root part.randomness :
          OracleComp HashSpec Digest)
        initialCache digestCache largerCache digest hdigest (hdigestLe.trans hrootLarger)
      have hdigestView : evalWithAnswerFn (answerFn largerCache)
          (Concrete.topEncodingHash publicKey.parameter key root part.randomness :
            OracleComp HashSpec Digest) =
          Concrete.CacheView.topEncodingHash largerCache publicKey.parameter key
            (root, part.randomness) := by
        simp [Concrete.topEncodingHash, Concrete.CacheView.topEncodingHash,
          Concrete.CacheView.topEncodingInput, Concrete.CacheView.tweakableHash]
      have hendpointsEval := eval_answerFn_largerCache_eq_of_mem_support _
        digestCache endpointsCache largerCache endpoints hendpoints (hendpointsLe.trans hrootLarger)
      simp only [eval_sequenceFin, eval_topChainWalk] at hendpointsEval
      have hleafEval := eval_answerFn_largerCache_eq_of_mem_support
        (Concrete.topLeafHash publicKey.parameter key endpoints : OracleComp HashSpec Digest)
        endpointsCache leafCache largerCache leaf hleaf (hleafLe.trans hrootLarger)
      have hleafView : evalWithAnswerFn (answerFn largerCache)
          (Concrete.topLeafHash publicKey.parameter key endpoints : OracleComp HashSpec Digest) =
          Concrete.CacheView.topLeafHash largerCache publicKey.parameter key endpoints := by
        simp [Concrete.topLeafHash, Concrete.CacheView.topLeafHash,
          Concrete.CacheView.topLeafInput, Concrete.CacheView.tweakableHash]
      rw [hleafView] at hleafEval
      have hendpointsEq : endpoints = recoveredEndpoints
          (fun chain => Concrete.CacheView.topChainStep largerCache publicKey.parameter key chain)
          encoding part.chainValue := by
        rw [← hendpointsEval]
        rfl
      refine ⟨encoding, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hdigestView, hdigestEval, hdecode]
      · obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached publicKey.parameter
          (.topEncoding key) (Concrete.topEncodingPayload root part.randomness)
          initialCache digestCache digest (by simpa [Concrete.topEncodingHash] using hdigest)
        exact ⟨output, hrootLarger (hdigestLe hcached)⟩
      · intro chain offset hoffset
        obtain ⟨beforeCache, afterCache, value, hchain, hchainLe⟩ :=
          sequenceFin_component_support_in_largerCache
            (fun index => Concrete.topChainWalk publicKey.parameter key index
              (encoding index).val (chainLength - 1 - (encoding index).val)
              (part.chainValue index) : ChainIndex → OracleComp HashSpec Digest)
            chain digestCache endpointsCache largerCache endpoints hendpoints
            (hendpointsLe.trans hrootLarger)
        exact topChainWalk_query_cached_in_largerCache publicKey.parameter
          key chain (encoding chain).val (chainLength - 1 - (encoding chain).val)
          (part.chainValue chain) offset hoffset (by omega) beforeCache afterCache largerCache
          value hchain hchainLe
      · obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached publicKey.parameter
          (.topLeaf key) (Concrete.leafPayload endpoints)
          endpointsCache leafCache leaf (by simpa [Concrete.topLeafHash] using hleaf)
        refine ⟨output, ?_⟩
        rw [← hendpointsEq]
        exact hrootLarger (hleafLe hcached)
      · intro level
        obtain ⟨output, hcached⟩ := topAuthenticationRoot_query_cached_as_in_largerCache
          publicKey.parameter key part.authPath treeHeight leaf level level.isLt le_rfl
          leafCache rootCache largerCache topRoot hroot hrootLarger
        refine ⟨output, ?_⟩
        rw [← hendpointsEq, hleafEval]
        exact hrootLarger hcached

end XmssSecurity.Concrete.CacheReplay

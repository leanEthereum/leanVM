module

public import XmssSecurity.Proof.MerkleQueryBound
public import XmssSecurity.Proof.QueryPresence
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.Concrete.CacheReplay

theorem treeNode_merkle_query_cached_in_largerCache
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (hcontains : MerkleAddressInSubtree targetLevel targetNode levels node)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.treeNode parameter secret levels node :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, resultCache
      (Concrete.CacheView.merkleInput parameter targetLevel targetNode
        (treeNode largerCache parameter secret targetLevel.val
          (Concrete.childNode targetNode false))
        (treeNode largerCache parameter secret targetLevel.val
          (Concrete.childNode targetNode true))) = some output := by
  induction levels generalizing node initialCache resultCache digest with
  | zero => simp [MerkleAddressInSubtree] at hcontains
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      rw [Concrete.treeNode_succ_eq, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨left, leftCache⟩, hleft, hrest⟩ := hmem
      have hrestAll := hrest
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨right, rightCache⟩, hright, hnode⟩ := hrest
      by_cases hcurrent : targetLevel.val = levels
      · have htargetLevel : targetLevel = ⟨levels, hlevel⟩ := Fin.ext hcurrent
        subst targetLevel
        have htargetNode : targetNode = node := by
          unfold MerkleAddressInSubtree at hcontains
          have hcover : TreeCovers 0 node targetNode := by
            simpa [hcurrent] using hcontains.2
          exact (treeCovers_zero_iff node targetNode).mp hcover |>.symm
        subst targetNode
        have hrightLe : rightCache ≤ resultCache :=
          randomOracle_cache_le
            (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            rightCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hnode)
        obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
          (.merkle ⟨levels, hlevel⟩ node) (Concrete.nodePayload left right)
          rightCache resultCache digest (by
            simpa [Concrete.nodeHash, hlevel] using hnode)
        have hleftEval := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.treeNode parameter secret levels (Concrete.childNode node false) :
            OracleComp HashSpec Digest)
          initialCache leftCache largerCache left hleft
          ((randomOracle_cache_le
            (do
              let right ← Concrete.treeNode parameter secret levels
                (Concrete.childNode node true)
              Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            leftCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hrestAll)).trans hle)
        have hrightEval := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.treeNode parameter secret levels (Concrete.childNode node true) :
            OracleComp HashSpec Digest)
          leftCache rightCache largerCache right hright (hrightLe.trans hle)
        rw [eval_treeNode] at hleftEval hrightEval
        refine ⟨output, ?_⟩
        rw [hleftEval, hrightEval]
        exact hcached
      · have htargetLt : targetLevel.val < levels := by
          unfold MerkleAddressInSubtree at hcontains
          omega
        have hleftLe : leftCache ≤ resultCache :=
          randomOracle_cache_le
            (do
              let right ← Concrete.treeNode parameter secret levels
                (Concrete.childNode node true)
              Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
              OracleComp HashSpec Digest)
            leftCache (digest, resultCache) (by
              simpa only [hlevel, ↓reduceDIte] using hrestAll)
        have hpartition := merkleAddressInSubtree_step_sum targetLevel targetNode levels
          node hlevel hvalid
        rw [ite_eq_left hcontains] at hpartition
        have hdomain : HashDomain.merkle ⟨levels, hlevel⟩ node ≠
            .merkle targetLevel targetNode := by
          intro heq
          have hlevelEq := congrArg Fin.val (HashDomain.merkle.inj heq).1
          exact hcurrent hlevelEq.symm
        rw [ite_eq_right hdomain, add_zero] at hpartition
        by_cases hleftContains : MerkleAddressInSubtree targetLevel targetNode levels
            (Concrete.childNode node false)
        · obtain ⟨output, hcached⟩ :=
            ih (Concrete.childNode node false) (Nat.le_of_succ_le hlevels)
              hleftValid hleftContains initialCache leftCache left hleft (hleftLe.trans hle)
          exact ⟨output, hleftLe hcached⟩
        · have hrightContains : MerkleAddressInSubtree targetLevel targetNode levels
              (Concrete.childNode node true) := by
            simp only [hleftContains, ite_false, zero_add] at hpartition
            split at hpartition
            · assumption
            · omega
          have hrightLe : rightCache ≤ resultCache :=
            randomOracle_cache_le
              (Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
                OracleComp HashSpec Digest)
              rightCache (digest, resultCache) (by
                simpa only [hlevel, ↓reduceDIte] using hnode)
          obtain ⟨output, hcached⟩ :=
            ih (Concrete.childNode node true) (Nat.le_of_succ_le hlevels)
              hrightValid hrightContains leftCache rightCache right hright (hrightLe.trans hle)
          exact ⟨output, hrightLe hcached⟩

theorem rootTree_merkle_query_cached
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (hnode : targetNode.val < 2 ^ (2 * treeHeight - (targetLevel.val + 1)))
    (root : Digest × (TopIndex → Option (Randomness × Encoding))) (cache largerCache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (hle : cache ≤ largerCache) :
    ∃ output, cache
      (Concrete.CacheView.merkleInput parameter targetLevel targetNode
        (treeNode largerCache parameter secret targetLevel.val
          (Concrete.childNode targetNode false))
        (treeNode largerCache parameter secret targetLevel.val
          (Concrete.childNode targetNode true))) = some output := by
  have hlevel := targetLevel.isLt
  have hpow : 0 < 2 ^ (treeHeight - (targetLevel.val + 1)) := pow_pos (by omega) _
  have hkey : targetNode.val / 2 ^ (treeHeight - (targetLevel.val + 1)) < topLifetime := by
    rw [Nat.div_lt_iff_lt_mul hpow, topLifetime, ← pow_add]
    convert hnode using 2
    simp only [treeHeight] at hlevel ⊢
    omega
  let key : TopIndex := ⟨_, hkey⟩
  obtain ⟨beforeCache, afterCache, digest, htree, hafter⟩ :=
    honestKeygen_runsBelow_bottomTree parameter secret topSecret _ ∅ cache root hmem key
  apply treeNode_merkle_query_cached_in_largerCache parameter secret targetLevel targetNode
    treeHeight (Concrete.bottomRootNode key) le_rfl (treeSubtreeValid_bottomRootNode key) ?_
    beforeCache afterCache largerCache digest htree (hafter.trans hle) |>.imp fun _ h => hafter h
  refine ⟨hlevel, ?_, ?_⟩
  · exact Nat.div_mul_le_self _ _
  · simp only [Concrete.bottomRootNode, key]
    rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hpow

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity

theorem Concrete.keygen_cache_has_merkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  exact Concrete.CacheReplay.rootTree_merkle_query_cached parameter secret topSecret topBase level node hnode
    root keyResult.2 largerCache hroot hle

theorem Concrete.keygen_cache_has_merkleInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output :=
  Concrete.keygen_cache_has_merkleInput_in_largerCache keyResult hmem keyResult.2 le_rfl
    level node hnode

theorem Concrete.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false),
        Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) :
    keyResult.2 (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) =
      none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_merkleInput_in_largerCache keyResult hmem largerCache hle
      level node hnode
  cases hforged : keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      apply hne
      apply Concrete.nodePayload_injective
      exact payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter
        (.merkle level node)
        (Concrete.keygen_cache_unique_merkleAddress keyResult hmem level node
          (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right)
          (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
            (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
              keyResult.1.2.chainStart level.val (Concrete.childNode node false))
            (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
              keyResult.1.2.chainStart level.val (Concrete.childNode node true)))
          forgedOutput honestOutput (by simp [Concrete.CacheView.merkleInput])
          (by simp [Concrete.CacheView.merkleInput]) hforged hhonest)

theorem Concrete.keygen_merkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) =
    (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node false),
      Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) := by
  obtain ⟨initialOutput, hinitial⟩ :=
    Concrete.keygen_cache_has_merkleInput keyResult hmem level node hnode
  obtain ⟨largerOutput, hlarger⟩ :=
    Concrete.keygen_cache_has_merkleInput_in_largerCache keyResult hmem largerCache hle
      level node hnode
  apply Concrete.nodePayload_injective
  exact payload_eq_of_tweakableHashInput_eq keyResult.1.2.parameter (.merkle level node)
    (Concrete.keygen_cache_unique_merkleAddress keyResult hmem level node
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true)))
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true)))
      initialOutput largerOutput (by simp [Concrete.CacheView.merkleInput])
      (by simp [Concrete.CacheView.merkleInput]) hinitial hlarger)

end XmssSecurity

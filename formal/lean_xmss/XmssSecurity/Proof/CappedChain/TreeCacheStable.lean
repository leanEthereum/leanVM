module

public import XmssSecurity.Proof.CausalAuthenticationPathIndependence
public import XmssSecurity.Proof.HonestKeygenRun

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity.CappedChain

def TreeCacheStable
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ (levels : Nat) (node : MerkleNode),
    levels ≤ treeHeight → TreeSubtreeValid levels node →
    ∀ (largerCache : QueryCache HashSpec), cache ≤ largerCache →
    (simulateQ randomOracle
      (Concrete.treeNode parameter secret levels node :
        OracleComp HashSpec Digest)).run largerCache =
      pure (Concrete.CacheReplay.treeNode cache parameter secret levels node,
        largerCache)

theorem TreeCacheStable.treeNode_eq
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable parameter secret cache)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache) :
    Concrete.CacheReplay.treeNode cache parameter secret levels node =
      Concrete.CacheReplay.treeNode largerCache parameter secret levels node := by
  have hrun := hstable levels node hlevels hvalid largerCache hle
  have hmem :
      (Concrete.CacheReplay.treeNode cache parameter secret levels node,
        largerCache) ∈ support
          ((simulateQ randomOracle
            (Concrete.treeNode parameter secret levels node :
              OracleComp HashSpec Digest)).run largerCache) := by
    rw [hrun]
    simp
  have hreplay := Concrete.CacheReplay.eval_answerFn_finalCache_eq_of_mem_support
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest)
    largerCache largerCache
      (Concrete.CacheReplay.treeNode cache parameter secret levels node) hmem
  rw [Concrete.CacheReplay.eval_treeNode] at hreplay
  exact hreplay.symm

theorem TreeCacheStable.authenticationPath_eq
    (secretKey : SecretKey) (cache : QueryCache HashSpec)
    (hstable : TreeCacheStable secretKey.parameter secretKey.chainStart cache)
    (largerCache : QueryCache HashSpec) (hle : cache ≤ largerCache)
    (leafIndex : LeafIndex) :
    Concrete.CacheReplay.authenticationPath cache secretKey leafIndex =
      Concrete.CacheReplay.authenticationPath largerCache secretKey leafIndex := by
  funext level
  exact TreeCacheStable.treeNode_eq secretKey.parameter secretKey.chainStart
    cache hstable level.val (Concrete.authenticationPathNode leafIndex level)
      (by omega) (authenticationPathNode_subtreeValid leafIndex level)
        largerCache hle

/-- The honest top signatures replayed from the key-generation cache do not change in larger caches. -/
def TopCacheStable (secretKey : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  ∀ largerCache, cache ≤ largerCache → ∀ key,
    Concrete.CacheReplay.topPartFromCache cache secretKey key =
      Concrete.CacheReplay.topPartFromCache largerCache secretKey key

end XmssSecurity.CappedChain

namespace XmssSecurity

theorem keygen_support_treeCacheStable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    CappedChain.TreeCacheStable keyResult.1.2.parameter keyResult.1.2.chainStart
      keyResult.2 := by
  obtain ⟨parameter, secret, topSecret, topBase, result, hkey, hresult⟩ :=
    Concrete.keygen_support_rootTree keyResult hkeyResult
  rw [hkey]
  intro levels node hlevels hvalid largerCache hle
  refine ((Concrete.CacheReplay.honestKeygen_runsBelow_treeNode hresult levels node hlevels
    hvalid).run_eq largerCache hle).trans ?_
  rw [Concrete.CacheReplay.eval_treeNode]
  rfl

theorem keygen_support_topCacheStable
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeyResult : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅)) :
    CappedChain.TopCacheStable keyResult.1.2 keyResult.2 := by
  obtain ⟨parameter, secret, topSecret, topBase, result, hkey, hresult⟩ :=
    Concrete.keygen_support_rootTree keyResult hkeyResult
  rw [hkey]
  dsimp only [SecretKey.withoutPrecomputation]
  intro largerCache hle key
  unfold Concrete.CacheReplay.topPartFromCache
  split
  · rename_i randomness encoding _
    congr 1
    · funext chain
      have hrun := Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk hresult key chain
        (encoding chain).val (Nat.le_pred_of_lt (encoding chain).isLt)
      have heval := hrun.eval_eq largerCache hle
      rw [Concrete.CacheReplay.eval_topChainWalk, Concrete.CacheReplay.eval_topChainWalk] at heval
      exact heval
    · funext level
      have hlevel := level.isLt
      have hnode : (Concrete.topPathNode key level).val < 2 ^ (treeHeight - level.val) := by
        have hquotient : key.val / 2 ^ level.val < 2 ^ (treeHeight - level.val) := by
          rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _), ← pow_add,
            Nat.sub_add_cancel hlevel.le]
          exact key.isLt
        have hone : 1 < 2 ^ (treeHeight - level.val) :=
          Nat.one_lt_two_pow (by omega)
        exact (Nat.mod_le _ _).trans_lt (Nat.xor_lt_two_pow hquotient hone)
      have hrun := Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hresult level.val
        (Concrete.topPathNode key level) hlevel.le hnode
      have heval := hrun.eval_eq largerCache hle
      rw [Concrete.CacheReplay.eval_topTreeNode, Concrete.CacheReplay.eval_topTreeNode] at heval
      simp only [Concrete.honestTopPath, hlevel, ↓reduceDIte]
      exact heval
  · rfl

end XmssSecurity

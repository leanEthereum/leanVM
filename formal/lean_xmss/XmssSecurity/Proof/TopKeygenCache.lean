import XmssSecurity.Proof.PrecomputedKeyConsistency
import XmssSecurity.Proof.ConcreteForgery
import XmssSecurity.Proof.TopKeygenQueryBound
import XmssSecurity.Proof.TopVerificationQueryPresence

/-!
# Key generation's cache: the bottom forest's nodes and the top layer

What key generation caches at the bottom forest's Merkle addresses (global node indices, so level
`ℓ` uses nodes below `2^(2h - ℓ - 1)`), and at the top layer's addresses: one honest input per top
chain step, top leaf and top Merkle node, and at a top message digest address only the trials of
the honest bottom root, of which the selected one is the only one that decodes.
-/

open OracleComp OracleSpec

namespace XmssSecurity

/-! ### The bottom forest's Merkle nodes -/

theorem Concrete.precomputedKeygen_cache_has_forestMerkleInput_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false))
        (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) = some output :=
  Concrete.keygen_cache_has_merkleInput_in_largerCache _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) largerCache hle level node hnode

theorem Concrete.precomputedKeygen_cache_forestMerkleInput_eq_none_of_ne_in_largerCache
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (level : MerkleLevel) (node : MerkleNode)
    (hnode : node.val < 2 ^ (2 * treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node false),
        Concrete.CacheReplay.treeNode largerCache keyResult.1.2.parameter
          keyResult.1.2.chainStart level.val (Concrete.childNode node true))) :
    keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level node left right) = none :=
  Concrete.keygen_cache_merkleInput_eq_none_of_ne_in_largerCache _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) largerCache hle level node hnode
    left right hne

theorem Concrete.precomputedKeygen_forestMerkleChildren_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
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
        keyResult.1.2.chainStart level.val (Concrete.childNode node true)) :=
  Concrete.keygen_merkleChildren_eq_of_cache_le _
    (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem) largerCache hle level node hnode

/-- Key generation fixes every honest bottom root in all later cache extensions. -/
theorem Concrete.precomputedKeygen_bottomRoot_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache) (key : TopIndex) :
    Concrete.bottomRoot keyResult.2 keyResult.1.2 key =
      Concrete.bottomRoot largerCache keyResult.1.2 key := by
  have hlevel : treeHeight - 1 < treeHeight := by decide
  let level : MerkleLevel := ⟨treeHeight - 1, hlevel⟩
  have hnode : (Concrete.bottomRootNode key).val < 2 ^ (2 * treeHeight - (level.val + 1)) := by
    have hkey := key.isLt
    simp only [Concrete.bottomRootNode, level, topLifetime, treeHeight] at hkey ⊢
    omega
  have hchildren := Concrete.precomputedKeygen_forestMerkleChildren_eq_of_cache_le keyResult hmem
    largerCache hle level (Concrete.bottomRootNode key) hnode
  obtain ⟨output, hcached⟩ :=
    Concrete.precomputedKeygen_cache_has_forestMerkleInput_in_largerCache keyResult hmem
      largerCache hle level (Concrete.bottomRootNode key) hnode
  simp only [Prod.mk.injEq] at hchildren
  unfold Concrete.bottomRoot
  rw [show treeHeight = (treeHeight - 1) + 1 by decide, Concrete.CacheReplay.treeNode_succ_eq,
    Concrete.CacheReplay.treeNode_succ_eq, dite_eq_left hlevel, dite_eq_left hlevel]
  unfold Concrete.CacheView.merkleHash
  change Concrete.CacheView.digestAt keyResult.2
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level (Concrete.bottomRootNode key)
        _ _) =
    Concrete.CacheView.digestAt largerCache
      (Concrete.CacheView.merkleInput keyResult.1.2.parameter level (Concrete.bottomRootNode key)
        _ _)
  rw [hchildren.1, hchildren.2, Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
    Concrete.CacheView.digestAt_eq_of_cache_eq_some (hle hcached)]

/-! ### Top chains -/

-- The top tree is fully concrete at `treeHeight`; keep elaboration from unfolding it.
attribute [local irreducible] Concrete.topTreeNode

/-- A precomputed key generation contains a run of the honest computation on its own secret key. -/
theorem Concrete.precomputedKeygen_honestRun
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅)) :
    ∃ (topBase : TopIndex → Randomness)
      (result : Digest × (TopIndex → Option (Randomness × Encoding))),
      result.2 = keyResult.1.2.topSigned ∧
      (result, keyResult.2) ∈ support ((simulateQ randomOracle
        (Concrete.honestKeygen keyResult.1.2.parameter keyResult.1.2.chainStart
          keyResult.1.2.topChainStart (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅) := by
  obtain ⟨parameter, secret, topSecret, topBase, result, hkey, hrun⟩ :=
    Concrete.keygen_support_rootTree _ (Concrete.precomputedKeygen_support_oldKeygen keyResult hmem)
  have hparameter : keyResult.1.2.parameter = parameter := congrArg (fun r => r.2.parameter) hkey
  have hsecret : keyResult.1.2.chainStart = secret := congrArg (fun r => r.2.chainStart) hkey
  have htopSecret : keyResult.1.2.topChainStart = topSecret :=
    congrArg (fun r => r.2.topChainStart) hkey
  have htopSigned : keyResult.1.2.topSigned = result.2 := congrArg (fun r => r.2.topSigned) hkey
  refine ⟨topBase, result, htopSigned.symm, ?_⟩
  rw [hparameter, hsecret, htopSecret]
  exact hrun

theorem Concrete.CacheReplay.eval_topOneTimePublicKey (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest) (key : TopIndex) :
    evalWithAnswerFn (Concrete.CacheReplay.answerFn cache)
      (Concrete.topOneTimePublicKey parameter topSecret key :
        OracleComp HashSpec (ChainIndex → Digest)) =
      Concrete.CacheReplay.topOneTimePublicKey cache parameter topSecret key := by
  funext chain
  simp [Concrete.topOneTimePublicKey, Concrete.CacheReplay.topOneTimePublicKey]

/-- Key generation caches every honest top chain step. -/
theorem Concrete.precomputedKeygen_cache_has_topChainInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, keyResult.2
      (Concrete.CacheView.topChainInput keyResult.1.2.parameter key chain step
        (Wots.walk
          (Concrete.CacheView.topChainStep keyResult.2 keyResult.1.2.parameter key chain)
          0 step.val (keyResult.1.2.topChainStart key chain))) = some output := by
  obtain ⟨topBase, result, _, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
  obtain ⟨beforeCache, afterCache, value, hwalk, hafter⟩ :=
    Concrete.CacheReplay.honestKeygen_runsBelow_topChainWalk hrun key chain (step.val + 1)
      (by have := step.isLt; omega)
  obtain ⟨output, hcached⟩ := Concrete.CacheReplay.topChainWalk_query_cached_in_largerCache
    keyResult.1.2.parameter key chain 0 (step.val + 1) (keyResult.1.2.topChainStart key chain)
    step.val (by omega) (by have := step.isLt; omega) beforeCache afterCache keyResult.2 value
    hwalk hafter
  have hstep : (⟨0 + step.val, by have := step.isLt; omega⟩ : ChainStep) = step :=
    Fin.ext (Nat.zero_add _)
  rw [hstep] at hcached
  exact ⟨output, hcached⟩

/-- Key generation caches no other input at an honest top chain step's address. -/
theorem Concrete.precomputedKeygen_cache_topChainInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (hne : value ≠ Wots.walk
      (Concrete.CacheView.topChainStep keyResult.2 keyResult.1.2.parameter key chain)
      0 step.val (keyResult.1.2.topChainStart key chain)) :
    keyResult.2
      (Concrete.CacheView.topChainInput keyResult.1.2.parameter key chain step value) = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.precomputedKeygen_cache_has_topChainInput keyResult hmem key chain step
  cases hforged : keyResult.2
      (Concrete.CacheView.topChainInput keyResult.1.2.parameter key chain step value) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      obtain ⟨topBase, result, _, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
      have heq := Concrete.CacheReplay.cache_unique_of_query_bound_one _ _ ∅ keyResult.2 result
        (Concrete.honestKeygen_queryBound_topChainAddress keyResult.1.2.parameter
          keyResult.1.2.chainStart keyResult.1.2.topChainStart topBase key chain step)
        (by simp) hrun _ _ forgedOutput honestOutput
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl) hforged hhonest
      exact hne (Concrete.digestBytes_injective
        (payload_eq_of_tweakableHashInput_eq _ _ heq))

theorem Concrete.CacheView.topChainStep_eq (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex) (position : Nat)
    (value : Digest) (hposition : position < chainLength - 1) :
    topChainStep cache parameter key chain position value =
      digestAt cache (topChainInput parameter key chain ⟨position, hposition⟩ value) := by
  simp [topChainStep, hposition]

/-- Key generation fixes every honest top chain value in all later cache extensions. -/
theorem Concrete.precomputedKeygen_topChainWalk_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (key : TopIndex) (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1) :
    Wots.walk
        (Concrete.CacheView.topChainStep keyResult.2 keyResult.1.2.parameter key chain)
        0 steps (keyResult.1.2.topChainStart key chain) =
      Wots.walk
        (Concrete.CacheView.topChainStep largerCache keyResult.1.2.parameter key chain)
        0 steps (keyResult.1.2.topChainStart key chain) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hstep : steps < chainLength - 1 := by omega
      obtain ⟨output, hcached⟩ := Concrete.precomputedKeygen_cache_has_topChainInput keyResult
        hmem key chain ⟨steps, hstep⟩
      simp only [Wots.walk, Nat.zero_add]
      rw [← ih (by omega), Concrete.CacheView.topChainStep_eq _ _ _ _ _ _ hstep,
        Concrete.CacheView.topChainStep_eq _ _ _ _ _ _ hstep,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some (hle hcached)]

/-! ### Top leaves -/

theorem Concrete.precomputedKeygen_topOneTimePublicKey_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache) (key : TopIndex) :
    Concrete.CacheReplay.topOneTimePublicKey keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.topChainStart key =
      Concrete.CacheReplay.topOneTimePublicKey largerCache keyResult.1.2.parameter
        keyResult.1.2.topChainStart key := by
  funext chain
  exact Concrete.precomputedKeygen_topChainWalk_eq_of_cache_le keyResult hmem largerCache hle
    key chain (chainLength - 1) le_rfl

/-- Key generation caches every honest top leaf. -/
theorem Concrete.precomputedKeygen_cache_has_topLeafInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) :
    ∃ output, keyResult.2
      (Concrete.CacheView.topLeafInput keyResult.1.2.parameter key
        (Concrete.CacheReplay.topOneTimePublicKey keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart key)) = some output := by
  obtain ⟨topBase, result, _, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
  obtain ⟨beforeCache, afterCache, value, hleaf, hafter⟩ :=
    Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hrun 0 key (by omega)
      (by rw [Nat.sub_zero]; exact key.isLt)
  rw [Concrete.topTreeNode, Concrete.topLeafAt] at hleaf
  obtain ⟨endpoints, endpointsCache, hendpoints, hhash, hendpointsLe⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hleaf
  obtain ⟨output, hcached, _⟩ := Concrete.CacheReplay.tweakableHash_query_cached
    keyResult.1.2.parameter (.topLeaf key) (Concrete.leafPayload endpoints) endpointsCache
    afterCache value hhash
  have hendpointsEval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support _
    beforeCache endpointsCache keyResult.2 endpoints hendpoints
    ((Concrete.CacheReplay.randomOracle_cache_le _ _ _ hhash).trans hafter)
  rw [Concrete.CacheReplay.eval_topOneTimePublicKey] at hendpointsEval
  refine ⟨output, ?_⟩
  rw [hendpointsEval]
  exact hafter hcached

/-- Key generation caches no other input at an honest top leaf's address. -/
theorem Concrete.precomputedKeygen_cache_topLeafInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) (endpoints : ChainIndex → Digest)
    (hne : endpoints ≠ Concrete.CacheReplay.topOneTimePublicKey keyResult.2
      keyResult.1.2.parameter keyResult.1.2.topChainStart key) :
    keyResult.2 (Concrete.CacheView.topLeafInput keyResult.1.2.parameter key endpoints) = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.precomputedKeygen_cache_has_topLeafInput keyResult hmem key
  cases hforged : keyResult.2
      (Concrete.CacheView.topLeafInput keyResult.1.2.parameter key endpoints) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      obtain ⟨topBase, result, _, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
      have heq := Concrete.CacheReplay.cache_unique_of_query_bound_one _ _ ∅ keyResult.2 result
        (Concrete.honestKeygen_queryBound_topLeafAddress keyResult.1.2.parameter
          keyResult.1.2.chainStart keyResult.1.2.topChainStart topBase key)
        (by simp) hrun _ _ forgedOutput honestOutput
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl) hforged hhonest
      exact hne (Concrete.leafPayload_injective (payload_eq_of_tweakableHashInput_eq _ _ heq))

/-! ### Top Merkle nodes -/

/-- Key generation caches every honest top Merkle node. -/
theorem Concrete.precomputedKeygen_cache_has_topMerkleInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (level : MerkleLevel) (node : TopNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1))) :
    ∃ output, keyResult.2
      (Concrete.CacheView.topMerkleInput keyResult.1.2.parameter level node
        (Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val (Concrete.topChildNode node false))
        (Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val (Concrete.topChildNode node true))) =
        some output := by
  obtain ⟨topBase, result, _, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
  obtain ⟨beforeCache, afterCache, value, hnodeRun, hafter⟩ :=
    Concrete.CacheReplay.honestKeygen_runsBelow_topTreeNode hrun (level.val + 1) node
      level.isLt hnode
  rw [Concrete.topTreeNode] at hnodeRun
  obtain ⟨left, leftCache, hleft, hrest, hleftLe⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hnodeRun
  obtain ⟨right, rightCache, hright, hhash, hrightLe⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hrest
  simp only [level.isLt, ↓reduceDIte] at hhash
  obtain ⟨output, hcached, _⟩ := Concrete.CacheReplay.tweakableHash_query_cached
    keyResult.1.2.parameter (.topMerkle ⟨level.val, level.isLt⟩ node)
    (Concrete.nodePayload left right) rightCache afterCache value hhash
  have hleftEval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support _
    beforeCache leftCache keyResult.2 left hleft (hleftLe.trans hafter)
  have hrightEval := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support _
    leftCache rightCache keyResult.2 right hright (hrightLe.trans hafter)
  rw [Concrete.CacheReplay.eval_topTreeNode] at hleftEval hrightEval
  refine ⟨output, ?_⟩
  rw [hleftEval, hrightEval]
  exact hafter hcached

/-- Key generation caches no other input at an honest top Merkle node's address. -/
theorem Concrete.precomputedKeygen_cache_topMerkleInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (level : MerkleLevel) (node : TopNode)
    (hnode : node.val < 2 ^ (treeHeight - (level.val + 1)))
    (left right : Digest)
    (hne : (left, right) ≠
      (Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val (Concrete.topChildNode node false),
        Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
          keyResult.1.2.topChainStart level.val (Concrete.topChildNode node true))) :
    keyResult.2
      (Concrete.CacheView.topMerkleInput keyResult.1.2.parameter level node left right) = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.precomputedKeygen_cache_has_topMerkleInput keyResult hmem level node hnode
  cases hforged : keyResult.2
      (Concrete.CacheView.topMerkleInput keyResult.1.2.parameter level node left right) with
  | none => rfl
  | some forgedOutput =>
      exfalso
      obtain ⟨topBase, result, _, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
      have heq := Concrete.CacheReplay.cache_unique_of_query_bound_one _ _ ∅ keyResult.2 result
        (Concrete.honestKeygen_queryBound_topMerkleAddress keyResult.1.2.parameter
          keyResult.1.2.chainStart keyResult.1.2.topChainStart topBase level node)
        (by simp) hrun _ _ forgedOutput honestOutput
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl)
        ((atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl) hforged hhonest
      exact hne (Concrete.nodePayload_injective (payload_eq_of_tweakableHashInput_eq _ _ heq))

theorem Concrete.topChildNode_lt (levels : Nat) (node : TopNode)
    (hnode : node.val < 2 ^ (treeHeight - (levels + 1))) (hlevels : levels < treeHeight)
    (right : Bool) :
    (Concrete.topChildNode node right).val < 2 ^ (treeHeight - levels) := by
  have hsplit : 2 ^ (treeHeight - levels) = 2 * 2 ^ (treeHeight - (levels + 1)) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hbound : 2 * node.val + (if right then 1 else 0) < 2 ^ (treeHeight - levels) := by
    rw [hsplit]
    split <;> omega
  have hlife : 2 ^ (treeHeight - levels) ≤ topLifetime := by
    simp only [topLifetime]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  simp only [Concrete.topChildNode, Concrete.topNodeOfNat]
  rw [Nat.mod_eq_of_lt (hbound.trans_le hlife)]
  exact hbound

/-- Key generation fixes every honest top tree node in all later cache extensions. -/
theorem Concrete.precomputedKeygen_topTreeNode_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (levels : Nat) (hlevels : levels ≤ treeHeight) (node : TopNode)
    (hnode : node.val < 2 ^ (treeHeight - levels)) :
    Concrete.CacheReplay.topTreeNode keyResult.2 keyResult.1.2.parameter
        keyResult.1.2.topChainStart levels node =
      Concrete.CacheReplay.topTreeNode largerCache keyResult.1.2.parameter
        keyResult.1.2.topChainStart levels node := by
  induction levels generalizing node with
  | zero =>
      obtain ⟨output, hcached⟩ :=
        Concrete.precomputedKeygen_cache_has_topLeafInput keyResult hmem node
      rw [Concrete.CacheReplay.topTreeNode_zero_eq, Concrete.CacheReplay.topTreeNode_zero_eq]
      unfold Concrete.CacheReplay.topLeafAt Concrete.CacheView.topLeafHash
      rw [← Concrete.precomputedKeygen_topOneTimePublicKey_eq_of_cache_le keyResult hmem
          largerCache hle node,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some (hle hcached)]
  | succ levels ih =>
      have hlevel : levels < treeHeight := by omega
      have hchild := fun right => Concrete.topChildNode_lt levels node hnode hlevel right
      rw [Concrete.CacheReplay.topTreeNode_succ_eq, Concrete.CacheReplay.topTreeNode_succ_eq,
        dite_eq_left hlevel, dite_eq_left hlevel]
      obtain ⟨output, hcached⟩ := Concrete.precomputedKeygen_cache_has_topMerkleInput keyResult
        hmem ⟨levels, hlevel⟩ node hnode
      unfold Concrete.CacheView.topMerkleHash
      rw [← ih (by omega) _ (hchild false), ← ih (by omega) _ (hchild true),
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some (hle hcached)]

/-! ### Top message digests -/

/-- A computation making no query in a class leaves the cache unchanged on that class. -/
theorem Concrete.CacheReplay.cache_eq_of_zero_query_bound {α : Type}
    (computation : OracleComp HashSpec α) (p : HashInput → Prop) [DecidablePred p]
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hbound : computation.IsQueryBoundP p 0)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (input : HashInput) (hinput : p input) : finalCache input = initialCache input := by
  induction computation using OracleComp.inductionOn generalizing
      initialCache finalCache result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [hmem.2]
  | query_bind queried next ih =>
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hbound
      have hnot : ¬ p queried := by simpa using hbound.1
      have hne : queried ≠ input := fun heq => hnot (heq ▸ hinput)
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨output, middleCache⟩, hquery, hrest⟩ := hmem
      have hmiddle : middleCache input = initialCache input := by
        cases hqueried : initialCache queried with
        | none =>
            rw [QueryImpl.withCaching_run_none _ hqueried, support_map] at hquery
            obtain ⟨sampled, _hsampled, heq⟩ := hquery
            cases heq
            exact QueryCache.cacheQuery_of_ne initialCache output hne.symm
        | some cached =>
            rw [QueryImpl.withCaching_run_some _ hqueried, support_pure,
              Set.mem_singleton_iff] at hquery
            cases hquery
            rfl
      rw [← hmiddle]
      exact ih output middleCache finalCache result (by simpa [hnot] using hbound.2 output) hrest

theorem Concrete.CacheReplay.sequenceFin_component_value {α : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (target : Fin n)
    (initialCache cache : QueryCache HashSpec) (values : Fin n → α)
    (hmem : (values, cache) ∈ support
      ((simulateQ randomOracle (Concrete.sequenceFin computation)).run initialCache)) :
    ∃ beforeCache afterCache,
      (values target, afterCache) ∈ support
        ((simulateQ randomOracle (computation target)).run beforeCache) ∧
      afterCache ≤ cache := by
  induction n generalizing initialCache with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin] at hmem
      obtain ⟨head, headCache, hhead, hrest, hheadLe⟩ :=
        Concrete.CacheReplay.runsBelow_bind_left hmem
      obtain ⟨tail, tailCache, htail, hfinal, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hrest
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
      obtain ⟨hvalues, hcache⟩ := hfinal
      subst hvalues
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · exact ⟨initialCache, headCache, hhead, hheadLe⟩
      · rw [← hcache] at htail
        obtain ⟨beforeCache, afterCache, hcomponent, hle⟩ :=
          ih (fun index => computation index.succ) tailTarget headCache tail htail
        exact ⟨beforeCache, afterCache, hcomponent, hle⟩

section TopEncoding

variable (parameter : PublicParameter) (key : TopIndex)

/-- A cached input at key `b`'s top message digest address whose digest decodes to `encoding`. -/
def TopDecodesAt (cache : QueryCache HashSpec) (input : HashInput) (encoding : Encoding) : Prop :=
  AtHashAddress parameter (.topEncoding key) input ∧
    ∃ output, cache input = some output ∧
      TargetSum.decodeDigest (truncateHash output) = some encoding

/-- Every decoding input at key `b`'s address is the trial a top signature `signed` selected, of one
bottom root. -/
def TopDecodingsSelected (cache : QueryCache HashSpec)
    (signed : Option (Randomness × Encoding)) : Prop :=
  ∃ root, ∀ input encoding, TopDecodesAt parameter key cache input encoding →
    ∃ randomness, signed = some (randomness, encoding) ∧
      input = Concrete.CacheView.topEncodingInput parameter key (root, randomness)

theorem topDecodesAt_of_zero_query_bound {α : Type} (computation : OracleComp HashSpec α)
    (hbound : computation.IsQueryBoundP (AtHashAddress parameter (.topEncoding key)) 0)
    (initialCache finalCache : QueryCache HashSpec) (result : α)
    (hmem : (result, finalCache) ∈
      support ((simulateQ randomOracle computation).run initialCache))
    (input : HashInput) (encoding : Encoding) :
    TopDecodesAt parameter key finalCache input encoding ↔
      TopDecodesAt parameter key initialCache input encoding := by
  constructor
  · rintro ⟨hat, output, hcached, hdecode⟩
    rw [Concrete.CacheReplay.cache_eq_of_zero_query_bound computation _ initialCache finalCache
      result hbound hmem input hat] at hcached
    exact ⟨hat, output, hcached, hdecode⟩
  · rintro ⟨hat, output, hcached, hdecode⟩
    rw [← Concrete.CacheReplay.cache_eq_of_zero_query_bound computation _ initialCache finalCache
      result hbound hmem input hat] at hcached
    exact ⟨hat, output, hcached, hdecode⟩

/-- One trial caches its own input and changes no other cache entry. -/
theorem topEncodingHash_run (root : Digest) (randomness : Randomness)
    (initialCache finalCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, finalCache) ∈ support ((simulateQ randomOracle
      (Concrete.topEncodingHash parameter key root randomness : OracleComp HashSpec Digest)).run
        initialCache)) :
    ∃ output, finalCache (Concrete.CacheView.topEncodingInput parameter key (root, randomness)) =
        some output ∧ digest = truncateHash output ∧
      ∀ input, input ≠ Concrete.CacheView.topEncodingInput parameter key (root, randomness) →
        finalCache input = initialCache input := by
  obtain ⟨output, hcached, hdigest⟩ := Concrete.CacheReplay.tweakableHash_query_cached parameter
    (.topEncoding key) (Concrete.topEncodingPayload root randomness) initialCache finalCache digest
    hmem
  refine ⟨output, hcached, hdigest, fun input hne => ?_⟩
  refine Concrete.CacheReplay.cache_eq_of_zero_query_bound _
    (· ≠ Concrete.CacheView.topEncodingInput parameter key (root, randomness))
    initialCache finalCache digest ?_ hmem input hne
  simp [Concrete.topEncodingHash, Concrete.tweakableHash, Concrete.oracleHash,
    Concrete.CacheView.topEncodingInput]

/-- A grinding returning a trial caches it, with its codeword. -/
theorem topSignFrom_some_cached (root : Digest) (base : Randomness) :
    ∀ (attempts trial : Nat) (initialCache finalCache : QueryCache HashSpec)
      (randomness : Randomness) (encoding : Encoding),
      (some (randomness, encoding), finalCache) ∈ support ((simulateQ randomOracle
        (Concrete.topSignFrom parameter key root base attempts trial :
          OracleComp HashSpec _)).run initialCache) →
      ∃ output, finalCache
          (Concrete.CacheView.topEncodingInput parameter key (root, randomness)) = some output ∧
        TargetSum.decodeDigest (truncateHash output) = some encoding := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial initialCache finalCache randomness encoding hmem
      simp [Concrete.topSignFrom] at hmem
  | succ attempts ih =>
      intro trial initialCache finalCache randomness encoding hmem
      rw [Concrete.topSignFrom] at hmem
      obtain ⟨digest, digestCache, hdigest, hrest, _⟩ :=
        Concrete.CacheReplay.runsBelow_bind_left hmem
      obtain ⟨output, hcached, hdigestEq, _⟩ := topEncodingHash_run parameter key root _
        initialCache digestCache digest hdigest
      cases hdecode : TargetSum.decodeDigest digest with
      | none =>
          rw [hdecode] at hrest
          exact ih (trial + 1) digestCache finalCache randomness encoding hrest
      | some selected =>
          rw [hdecode] at hrest
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq, Option.some.injEq] at hrest
          obtain ⟨⟨hrandomness, hencoding⟩, hcache⟩ := hrest
          subst hrandomness hencoding hcache
          exact ⟨output, hcached, hdigestEq ▸ hdecode⟩

/-- From a cache with no decoding input at its address, a grinding leaves only its selected trial
decoding there. -/
theorem topSignFrom_decodings (root : Digest) (base : Randomness) :
    ∀ (attempts trial : Nat) (initialCache finalCache : QueryCache HashSpec)
      (result : Option (Randomness × Encoding)),
      (result, finalCache) ∈ support ((simulateQ randomOracle
        (Concrete.topSignFrom parameter key root base attempts trial :
          OracleComp HashSpec _)).run initialCache) →
      (∀ input encoding, ¬ TopDecodesAt parameter key initialCache input encoding) →
      ∀ input encoding, TopDecodesAt parameter key finalCache input encoding →
        ∃ randomness, result = some (randomness, encoding) ∧
          input = Concrete.CacheView.topEncodingInput parameter key (root, randomness) := by
  intro attempts
  induction attempts with
  | zero =>
      intro trial initialCache finalCache result hmem hnone input encoding hdecodes
      simp only [Concrete.topSignFrom, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rw [hmem.2] at hdecodes
      exact (hnone input encoding hdecodes).elim
  | succ attempts ih =>
      intro trial initialCache finalCache result hmem hnone input encoding hdecodes
      rw [Concrete.topSignFrom] at hmem
      obtain ⟨digest, digestCache, hdigest, hrest, _⟩ :=
        Concrete.CacheReplay.runsBelow_bind_left hmem
      obtain ⟨output, hcached, hdigestEq, hother⟩ := topEncodingHash_run parameter key root _
        initialCache digestCache digest hdigest
      have hdigestOther : ∀ input encoding, TopDecodesAt parameter key digestCache input encoding →
          input = Concrete.CacheView.topEncodingInput parameter key
            (root, base + BitVec.ofNat randomnessBits trial) ∧
          TargetSum.decodeDigest digest = some encoding := by
        rintro input encoding ⟨hat, inputOutput, hinput, hinputDecode⟩
        by_cases hsame : input = Concrete.CacheView.topEncodingInput parameter key
            (root, base + BitVec.ofNat randomnessBits trial)
        · subst hsame
          rw [hcached] at hinput
          cases hinput
          exact ⟨rfl, hdigestEq ▸ hinputDecode⟩
        · rw [hother input hsame] at hinput
          exact (hnone input encoding ⟨hat, inputOutput, hinput, hinputDecode⟩).elim
      cases hdecode : TargetSum.decodeDigest digest with
      | none =>
          rw [hdecode] at hrest
          refine ih (trial + 1) digestCache finalCache result hrest ?_ input encoding hdecodes
          intro input encoding hdecodes
          rw [hdecode] at hdigestOther
          exact absurd (hdigestOther input encoding hdecodes).2 (by simp)
      | some selected =>
          rw [hdecode] at hrest hdigestOther
          simp only [simulateQ_pure, StateT.run_pure, support_pure,
            Set.mem_singleton_iff, Prod.mk.injEq] at hrest
          obtain ⟨hresult, hcache⟩ := hrest
          rw [hcache] at hdecodes
          obtain ⟨hinput, hencoding⟩ := hdigestOther input encoding hdecodes
          cases hencoding
          exact ⟨_, hresult, hinput⟩

theorem topSignFrom_queryBound_zero_other_key (otherKey : TopIndex) (hne : otherKey ≠ key)
    (root : Digest) (base : Randomness) (attempts trial : Nat) :
    (Concrete.topSignFrom parameter otherKey root base attempts trial :
      OracleComp HashSpec (Option (Randomness × Encoding))).IsQueryBoundP
        (AtHashAddress parameter (.topEncoding key)) 0 := by
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom]
  | succ attempts ih =>
      rw [Concrete.topSignFrom]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _ _ (by simpa using hne)) ?_
      intro digest _
      split
      · simp
      · exact ih _

theorem topDecodingsSelected_sequenceFin {n : Nat}
    (computation : Fin n → OracleComp HashSpec (Option (Randomness × Encoding))) (target : Fin n)
    (hother : ∀ index, index ≠ target →
      (computation index).IsQueryBoundP (AtHashAddress parameter (.topEncoding key)) 0)
    (htarget : ∀ initialCache finalCache result,
      (result, finalCache) ∈ support
        ((simulateQ randomOracle (computation target)).run initialCache) →
      (∀ input encoding, ¬ TopDecodesAt parameter key initialCache input encoding) →
      TopDecodingsSelected parameter key finalCache result)
    (initialCache finalCache : QueryCache HashSpec) (values : Fin n → Option (Randomness × Encoding))
    (hmem : (values, finalCache) ∈ support
      ((simulateQ randomOracle (Concrete.sequenceFin computation)).run initialCache))
    (hnone : ∀ input encoding, ¬ TopDecodesAt parameter key initialCache input encoding) :
    TopDecodingsSelected parameter key finalCache (values target) := by
  induction n generalizing initialCache with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin] at hmem
      obtain ⟨head, headCache, hhead, hrest, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hmem
      obtain ⟨tail, tailCache, htail, hfinal, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hrest
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
      obtain ⟨hvalues, hcache⟩ := hfinal
      subst hvalues
      rw [← hcache] at htail
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · obtain ⟨root, hselected⟩ := htarget initialCache headCache head hhead hnone
        refine ⟨root, fun input encoding hdecodes => hselected input encoding ?_⟩
        refine (topDecodesAt_of_zero_query_bound parameter key _
          (Concrete.sequenceFin_queryBound_zero _ _ fun index =>
            hother index.succ (Fin.succ_ne_zero _))
          headCache finalCache tail htail input encoding).1 hdecodes
      · have hheadNone : ∀ input encoding, ¬ TopDecodesAt parameter key headCache input encoding :=
          fun input encoding hdecodes => hnone input encoding
            ((topDecodesAt_of_zero_query_bound parameter key _
              (hother 0 (Fin.succ_ne_zero _).symm)
              initialCache headCache head hhead input encoding).1 hdecodes)
        exact ih (fun index => computation index.succ) tailTarget
          (fun index hne => hother index.succ (by simpa using hne)) htarget headCache tail htail
          hheadNone

end TopEncoding

/-- Key generation's honest computation leaves, at each top message digest address, only the trial
its grinding selected decoding. -/
theorem Concrete.honestKeygen_topDecodingsSelected
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support ((simulateQ randomOracle
      (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
        OracleComp HashSpec _)).run ∅))
    (key : TopIndex) :
    TopDecodingsSelected parameter key cache (result.2 key) := by
  have hbottom : RejectsBottomTree parameter (AtHashAddress parameter (.topEncoding key)) := by
    intro domain payload hdomain _ hat
    rw [atHashAddress_tweakableHashInput_iff] at hat
    subst hat
    simp [HashDomain.isTop] at hdomain
  have htree (index : TopIndex) := Concrete.treeNode_queryBound_zero_of_rejectsBottomTree
    parameter _ hbottom secret treeHeight (Concrete.bottomRootNode index)
  unfold Concrete.honestKeygen at hmem
  obtain ⟨topSigned, signedCache, hsigned, hrest, _⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hmem
  obtain ⟨root, rootCache, hroot, hfinal, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hrest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
  obtain ⟨hresult, hcache⟩ := hfinal
  subst hresult
  rw [← hcache] at hroot
  have hselected := topDecodingsSelected_sequenceFin parameter key _ key
    (fun index hne => OracleComp.isQueryBoundP_bind (m := 0) (htree index)
      fun bottomRoot _ => OracleComp.isQueryBoundP_bind (m := 0) (by simp) fun base _ =>
        topSignFrom_queryBound_zero_other_key parameter key index hne bottomRoot base _ 0)
    (fun initialCache finalCache result hcomponent hnone => by
      obtain ⟨bottomRoot, bottomCache, hbottomRun, hbase, _⟩ :=
        Concrete.CacheReplay.runsBelow_bind_left hcomponent
      obtain ⟨base, baseCache, hbaseRun, hsign, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hbase
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hbaseRun
      rw [hbaseRun.2] at hsign
      refine ⟨bottomRoot, topSignFrom_decodings parameter key bottomRoot _ _ 0 bottomCache
        finalCache result hsign ?_⟩
      intro input encoding hdecodes
      exact hnone input encoding ((topDecodesAt_of_zero_query_bound parameter key _ (htree key)
        initialCache bottomCache bottomRoot hbottomRun input encoding).1 hdecodes))
    ∅ signedCache topSigned hsigned (by
      rintro input encoding ⟨_, output, hcached, _⟩
      simp at hcached)
  obtain ⟨bottomRoot, hbottom⟩ := hselected
  refine ⟨bottomRoot, fun input encoding hdecodes => hbottom input encoding ?_⟩
  exact (topDecodesAt_of_zero_query_bound parameter key _
    (Concrete.topTreeNode_queryBound_zero_topEncoding parameter topSecret key _ _)
    signedCache cache root hroot input encoding).1 hdecodes

/-! ### Top message digests -/

theorem Concrete.CacheView.topEncodingInput_injective (parameter : PublicParameter)
    (key : TopIndex) : Function.Injective (topEncodingInput parameter key) := by
  rintro ⟨leftRoot, leftRandomness⟩ ⟨rightRoot, rightRandomness⟩ heq
  have hpayload := payload_eq_of_tweakableHashInput_eq parameter (.topEncoding key) heq
  obtain ⟨hroot, hrandomness⟩ := List.append_inj hpayload (by simp)
  exact Prod.ext (bytesLE_injective 16 hroot) (bytesLE_injective 16 hrandomness)

/-- Key generation caches the selected trial of every successful top grinding, with its codeword. -/
theorem Concrete.precomputedKeygen_cache_topEncodingInput_selected
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : keyResult.1.2.topSigned key = some (randomness, encoding)) :
    ∃ output, keyResult.2
        (Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key
          (Concrete.bottomRoot keyResult.2 keyResult.1.2 key, randomness)) = some output ∧
      TargetSum.decodeDigest (truncateHash output) = some encoding := by
  obtain ⟨topBase, result, hresult, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
  unfold Concrete.honestKeygen at hrun
  obtain ⟨topSigned, signedCache, hsignedRun, hrest, hsignedLe⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hrun
  obtain ⟨root, rootCache, _, hfinal, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hrest
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hfinal
  have htopSigned : topSigned key = some (randomness, encoding) := by
    rw [← hsigned, ← hresult, hfinal.1]
  obtain ⟨componentCache, afterCache, hcomponent, hafterLe⟩ :=
    Concrete.CacheReplay.sequenceFin_component_value _ key ∅ signedCache topSigned hsignedRun
  rw [htopSigned] at hcomponent
  obtain ⟨bottomRoot, bottomCache, hbottomRun, hbase, hbottomLe⟩ :=
    Concrete.CacheReplay.runsBelow_bind_left hcomponent
  obtain ⟨base, baseCache, hbaseRun, hsign, _⟩ := Concrete.CacheReplay.runsBelow_bind_left hbase
  simp only [simulateQ_pure, StateT.run_pure, support_pure,
    Set.mem_singleton_iff, Prod.mk.injEq] at hbaseRun
  rw [hbaseRun.2] at hsign
  obtain ⟨output, hcached, hdecode⟩ := topSignFrom_some_cached keyResult.1.2.parameter key
    bottomRoot base _ 0 bottomCache afterCache randomness encoding hsign
  have hroot := Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support _
    componentCache bottomCache keyResult.2 bottomRoot hbottomRun
    (hbottomLe.trans (hafterLe.trans hsignedLe))
  rw [Concrete.CacheReplay.eval_treeNode] at hroot
  refine ⟨output, ?_, hdecode⟩
  unfold Concrete.bottomRoot
  rw [hroot]
  exact hsignedLe (hafterLe hcached)

/-- Key generation caches the selected trial of every successful top grinding. -/
theorem Concrete.precomputedKeygen_cache_has_topEncodingInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) (randomness : Randomness) (encoding : Encoding)
    (hsigned : keyResult.1.2.topSigned key = some (randomness, encoding)) :
    ∃ output, keyResult.2
      (Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key
        (Concrete.bottomRoot keyResult.2 keyResult.1.2 key, randomness)) = some output := by
  obtain ⟨output, hcached, _⟩ := Concrete.precomputedKeygen_cache_topEncodingInput_selected
    keyResult hmem key randomness encoding hsigned
  exact ⟨output, hcached⟩

/-- A top message digest input key generation caches whose digest decodes is the selected trial of a
successful grinding: it is the honest bottom root with the selected randomizer. The other trials,
also of the honest bottom root, all fail to decode. -/
theorem Concrete.precomputedKeygen_cache_topEncodingInput_decode
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.precomputedKeygen).run ∅))
    (key : TopIndex) (input : Digest × Randomness) (output : HashOutput)
    (hcached : keyResult.2
      (Concrete.CacheView.topEncodingInput keyResult.1.2.parameter key input) = some output)
    (encoding : Encoding) (hdecode : TargetSum.decodeDigest (truncateHash output) = some encoding) :
    keyResult.1.2.topSigned key = some (input.2, encoding) ∧
      input.1 = Concrete.bottomRoot keyResult.2 keyResult.1.2 key := by
  obtain ⟨topBase, result, hresult, hrun⟩ := Concrete.precomputedKeygen_honestRun keyResult hmem
  obtain ⟨root, hselected⟩ := Concrete.honestKeygen_topDecodingsSelected _ _ _ topBase result
    keyResult.2 hrun key
  rw [hresult] at hselected
  obtain ⟨randomness, hsigned, hinput⟩ := hselected _ encoding
    ⟨(atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl, output, hcached, hdecode⟩
  have hinputEq := Concrete.CacheView.topEncodingInput_injective _ key hinput
  subst hinputEq
  refine ⟨hsigned, ?_⟩
  obtain ⟨honestOutput, hhonest, hhonestDecode⟩ :=
    Concrete.precomputedKeygen_cache_topEncodingInput_selected keyResult hmem key randomness
      encoding hsigned
  obtain ⟨honestRandomness, _, hhonestInput⟩ := hselected _ encoding
    ⟨(atHashAddress_tweakableHashInput_iff _ _ _ _).2 rfl, honestOutput, hhonest, hhonestDecode⟩
  have hhonestEq := Concrete.CacheView.topEncodingInput_injective _ key hhonestInput
  exact (congrArg Prod.fst hhonestEq).symm

end XmssSecurity

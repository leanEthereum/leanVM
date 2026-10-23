import XmssSecurity.Proof.TreeQueryBound
import XmssSecurity.Proof.StatementLemmas

namespace XmssSecurity

def MerkleAddressInSubtree (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) : Prop :=
  targetLevel.val < levels ∧
    TreeCovers (levels - (targetLevel.val + 1)) node targetNode

instance (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) :
    Decidable (MerkleAddressInSubtree targetLevel targetNode levels node) := by
  unfold MerkleAddressInSubtree
  infer_instance

theorem treeSubtreeValid_mono {small large : Nat} {node : MerkleNode}
    (hle : small ≤ large) (hvalid : TreeSubtreeValid large node) :
    TreeSubtreeValid small node := by
  unfold TreeSubtreeValid at hvalid ⊢
  have hpow : 2 ^ small ≤ 2 ^ large := Nat.pow_le_pow_right (by omega) hle
  nlinarith

theorem treeCovers_zero_iff (left right : MerkleNode) :
    TreeCovers 0 left right ↔ left = right := by
  constructor
  · intro h
    apply Fin.ext
    unfold TreeCovers at h
    simp only [pow_zero, mul_one] at h
    omega
  · rintro rfl
    unfold TreeCovers
    simp

theorem treeCovers_unique {levels : Nat} {left right leafIndex : MerkleNode}
    (hleft : TreeCovers levels left leafIndex) (hright : TreeCovers levels right leafIndex) :
    left = right := by
  unfold TreeCovers at hleft hright
  apply Fin.ext
  rw [← Nat.div_eq_of_lt_le hleft.1 hleft.2, ← Nat.div_eq_of_lt_le hright.1 hright.2]

theorem merkleAddressInSubtree_step_sum
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode) (hlevel : levels < treeHeight)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (if MerkleAddressInSubtree targetLevel targetNode levels
          (Concrete.childNode node false) then 1 else 0) +
        ((if MerkleAddressInSubtree targetLevel targetNode levels
          (Concrete.childNode node true) then 1 else 0) +
          if HashDomain.merkle ⟨levels, hlevel⟩ node =
            .merkle targetLevel targetNode then 1 else 0) =
      if MerkleAddressInSubtree targetLevel targetNode (levels + 1) node then 1 else 0 := by
  by_cases hlt : targetLevel.val < levels
  · have hparentLt : targetLevel.val < levels + 1 := by omega
    have hexponent : levels + 1 - (targetLevel.val + 1) =
        (levels - (targetLevel.val + 1)) + 1 := by omega
    have hsmall : (levels - (targetLevel.val + 1)) + 1 ≤ levels + 1 := by omega
    have hpartition := treeCovers_children_sum
      (levels - (targetLevel.val + 1)) node targetNode
      (treeSubtreeValid_mono hsmall hvalid)
    have hdomain : HashDomain.merkle ⟨levels, hlevel⟩ node ≠
        .merkle targetLevel targetNode := by
      intro heq
      have hlevelEq := congrArg Fin.val (HashDomain.merkle.inj heq).1
      simp only at hlevelEq
      omega
    unfold MerkleAddressInSubtree
    simp only [hlt, hparentLt, true_and, hdomain, ite_false, add_zero]
    rw [hexponent]
    exact hpartition
  · by_cases heq : targetLevel.val = levels
    · have hlevelEq : targetLevel = ⟨levels, hlevel⟩ := by
        apply Fin.ext
        exact heq
      subst targetLevel
      simp only [MerkleAddressInSubtree, lt_self_iff_false, false_and, ite_false,
        Nat.lt_succ_self, true_and, Nat.sub_self, treeCovers_zero_iff,
        HashDomain.merkle.injEq]
      simp
    · have habove : levels < targetLevel.val := by omega
      have hnotParent : ¬targetLevel.val < levels + 1 := by omega
      have hdomain : HashDomain.merkle ⟨levels, hlevel⟩ node ≠
          .merkle targetLevel targetNode := by
        intro hsame
        have hlevelEq := congrArg Fin.val (HashDomain.merkle.inj hsame).1
        simp only at hlevelEq
        omega
      simp [MerkleAddressInSubtree, hlt, hnotParent, hdomain]

open OracleComp OracleSpec

theorem Concrete.treeNode_queryBound_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode))
        (if MerkleAddressInSubtree targetLevel targetNode levels node then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      simpa [MerkleAddressInSubtree] using
        Concrete.leafAt_queryBound_zero_merkleAddress parameter secret node
          targetLevel targetNode
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleftValid := childNode_subtreeValid levels node false hvalid
      have hrightValid := childNode_subtreeValid levels node true hvalid
      have hleft := ih (Concrete.childNode node false)
        (Nat.le_of_succ_le hlevels) hleftValid
      have hright := ih (Concrete.childNode node true)
        (Nat.le_of_succ_le hlevels) hrightValid
      rw [Concrete.treeNode_succ_eq]
      have hcontinuation (left : Digest) :
          (do
            let right ← Concrete.treeNode parameter secret levels
              (Concrete.childNode node true)
            Concrete.nodeHash parameter ⟨levels, hlevel⟩ node left right :
            OracleComp HashSpec Digest).IsQueryBoundP
              (AtHashAddress parameter (.merkle targetLevel targetNode))
              ((if MerkleAddressInSubtree targetLevel targetNode levels
                  (Concrete.childNode node true) then 1 else 0) +
                if HashDomain.merkle ⟨levels, hlevel⟩ node =
                  .merkle targetLevel targetNode then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind hright ?_
        intro right _
        by_cases heq : HashDomain.merkle ⟨levels, hlevel⟩ node =
            .merkle targetLevel targetNode
        · simp only [heq, ite_eq_left]
          obtain ⟨hlevelEq, hnodeEq⟩ := HashDomain.merkle.inj heq
          subst targetLevel
          subst targetNode
          exact Concrete.tweakableHash_queryBound_atAddress parameter
            (.merkle ⟨levels, hlevel⟩ node) (Concrete.nodePayload left right)
        · simp only [heq, ite_false]
          exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
            (.merkle targetLevel targetNode) (.merkle ⟨levels, hlevel⟩ node)
            (Concrete.nodePayload left right) heq
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte,
        merkleAddressInSubtree_step_sum targetLevel targetNode levels node hlevel hvalid]
        using hall

theorem Concrete.rootTree_queryBound_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLevel : MerkleLevel) (targetNode : MerkleNode) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.merkle targetLevel targetNode)) 1 := by
  have hbound (key : TopIndex) := Concrete.treeNode_queryBound_merkleAddress parameter secret
    targetLevel targetNode treeHeight (Concrete.bottomRootNode key) le_rfl
    (treeSubtreeValid_bottomRootNode key)
  have htop := rejectsTop_atHashAddress parameter (.merkle targetLevel targetNode) rfl
  by_cases hex : ∃ key, MerkleAddressInSubtree targetLevel targetNode treeHeight
      (Concrete.bottomRootNode key)
  · obtain ⟨target, htarget⟩ := hex
    refine Concrete.honestKeygen_queryBound_one parameter _ secret topSecret _ target htop
      (fun _ _ => by simp) (by simpa [htarget] using hbound target) fun key hne => ?_
    have hnot : ¬ MerkleAddressInSubtree targetLevel targetNode treeHeight
        (Concrete.bottomRootNode key) := fun hkey => hne (by
      have := treeCovers_unique hkey.2 htarget.2
      exact Fin.ext (by simpa [Concrete.bottomRootNode] using this))
    simpa [hnot] using hbound key
  · simp only [not_exists] at hex
    exact (Concrete.honestKeygen_queryBound_of_bottomTrees parameter _ secret topSecret _
      (fun _ => 0) 0 htop (fun _ _ => by simp) (fun key => by simpa [hex key] using hbound key)
      fun computation h => Concrete.sequenceFin_queryBound_zero computation _ h).mono (by omega)


theorem Concrete.CacheReplay.rootTree_cache_unique_merkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (root : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (root, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetLevel : MerkleLevel) (targetNode : MerkleNode)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.merkle targetLevel targetNode) left)
    (hrightP : AtHashAddress parameter (.merkle targetLevel targetNode) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right := by
  exact Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.merkle targetLevel targetNode)) ∅ cache root
    (Concrete.rootTree_queryBound_merkleAddress parameter secret topSecret topBase targetLevel targetNode)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

end XmssSecurity

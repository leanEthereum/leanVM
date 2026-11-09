module

public import XmssSecurity.Proof.HonestKeygenRun

@[expose] public section

/-!
# Key generation queries each top chain, leaf and Merkle address at most once

Only the top tree queries those addresses: the bottom trees query bottom domains, and the top grinding
only top message digests. The top tree queries each such address at most once.
-/

open OracleComp OracleSpec

namespace XmssSecurity

-- The top tree is fully concrete at `treeHeight`; keep elaboration from unfolding it.
attribute [local irreducible] Concrete.topTreeNode

def TopCovers (levels : Nat) (node : TopNode) (key : TopIndex) : Prop :=
  node.val * 2 ^ levels ≤ key.val ∧ key.val < (node.val + 1) * 2 ^ levels

instance (levels : Nat) (node : TopNode) (key : TopIndex) :
    Decidable (TopCovers levels node key) := by
  unfold TopCovers
  infer_instance

def TopSubtreeValid (levels : Nat) (node : TopNode) : Prop :=
  (node.val + 1) * 2 ^ levels ≤ topLifetime

theorem topChildNode_subtreeValid (levels : Nat) (node : TopNode)
    (right : Bool) (hvalid : TopSubtreeValid (levels + 1) node) :
    TopSubtreeValid levels (Concrete.topChildNode node right) := by
  unfold TopSubtreeValid
  rw [Concrete.CacheReplay.topChildNode_val levels node right hvalid]
  unfold TopSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem topCovers_children_sum (levels : Nat) (node : TopNode) (key : TopIndex)
    (hvalid : TopSubtreeValid (levels + 1) node) :
    (if TopCovers levels (Concrete.topChildNode node false) key then 1 else 0) +
        (if TopCovers levels (Concrete.topChildNode node true) key then 1 else 0) =
      if TopCovers (levels + 1) node key then 1 else 0 := by
  by_cases hleft : TopCovers levels (Concrete.topChildNode node false) key
  <;> by_cases hright : TopCovers levels (Concrete.topChildNode node true) key
  <;> by_cases hparent : TopCovers (levels + 1) node key
  <;> simp only [hleft, hright, hparent, ↓reduceIte]
  all_goals
    unfold TopCovers at hleft hright hparent
    simp only [Concrete.CacheReplay.topChildNode_val levels node false hvalid,
      Concrete.CacheReplay.topChildNode_val levels node true hvalid,
      Bool.false_eq_true, ↓reduceIte] at hleft hright
    rw [pow_succ] at hparent
    have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
    ring_nf at hleft hright hparent
    omega

theorem topCovers_zero_iff (node : TopNode) (key : TopIndex) :
    TopCovers 0 node key ↔ node = key := by
  constructor
  · intro h
    apply Fin.ext
    unfold TopCovers at h
    simp only [pow_zero, mul_one] at h
    omega
  · rintro rfl
    unfold TopCovers
    simp

theorem topSubtreeValid_mono {small large : Nat} {node : TopNode}
    (hle : small ≤ large) (hvalid : TopSubtreeValid large node) :
    TopSubtreeValid small node := by
  unfold TopSubtreeValid at hvalid ⊢
  have hpow : 2 ^ small ≤ 2 ^ large := Nat.pow_le_pow_right (by omega) hle
  nlinarith

/-! ### Top chains and leaves -/

theorem Concrete.topChainWalk_queryBound_zero_of_avoids
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain)
    (havoid : ∀ offset, offset < steps →
      ∀ hvalid : position + offset < chainLength - 1,
        HashDomain.topChain key chain ⟨position + offset, hvalid⟩ ≠ targetDomain) :
    (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 0 := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (ih fun offset hoffset => havoid offset (by omega)) ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
          (.topChain key chain ⟨position + steps, by assumption⟩)
          (Concrete.digestBytes previous) (havoid steps (by omega) _)
      · simp

set_option maxHeartbeats 800000 in
theorem Concrete.topChainWalk_queryBound_atAddress
    (parameter : PublicParameter) (key : TopIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (targetDomain : HashDomain) :
    (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter targetDomain) 1 := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      split
      · rename_i hposition
        let calledDomain : HashDomain :=
          .topChain key chain ⟨position + steps, hposition⟩
        by_cases heq : calledDomain = targetDomain
        · subst targetDomain
          have hprefix :
              (Concrete.topChainWalk parameter key chain position steps value :
                OracleComp HashSpec Digest).IsQueryBoundP
                  (AtHashAddress parameter calledDomain) 0 := by
            apply Concrete.topChainWalk_queryBound_zero_of_avoids
            intro offset hoffset hvalid hsame
            simp only [calledDomain, HashDomain.topChain.injEq, Fin.mk.injEq] at hsame
            omega
          refine OracleComp.isQueryBoundP_bind (m := 1) hprefix ?_
          intro previous _
          exact Concrete.tweakableHash_queryBound_atAddress parameter calledDomain
            (Concrete.digestBytes previous)
        · refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
          intro previous _
          exact Concrete.tweakableHash_queryBound_atOtherAddress parameter targetDomain
            calledDomain (Concrete.digestBytes previous) heq
      · refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
        intro previous _
        simp

/-- A top leaf queries the top chain addresses of its own key only, each at most once. -/
theorem Concrete.topLeafAt_queryBound_chainAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key targetKey : TopIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.topChain targetKey targetChain targetStep))
      (if key = targetKey then 1 else 0) := by
  have hleaf (endpoints : ChainIndex → Digest) :
      (Concrete.topLeafHash parameter key endpoints : OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.topChain targetKey targetChain targetStep)) 0 :=
    Concrete.tweakableHash_queryBound_atOtherAddress parameter
      (.topChain targetKey targetChain targetStep) (.topLeaf key)
      (Concrete.leafPayload endpoints) (by simp)
  rw [Concrete.topLeafAt]
  by_cases hkey : key = targetKey
  · subst targetKey
    rw [ite_eq_left rfl]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ fun endpoints _ => hleaf endpoints
    rw [Concrete.topOneTimePublicKey]
    apply Concrete.sequenceFin_queryBound_one _ _ targetChain
    · exact Concrete.topChainWalk_queryBound_atAddress parameter key targetChain 0
        (chainLength - 1) (topSecret key targetChain) _
    · intro chain hchain
      apply Concrete.topChainWalk_queryBound_zero_of_avoids
      intro offset _ hvalid heq
      simp only [HashDomain.topChain.injEq] at heq
      exact hchain heq.2.1
  · rw [ite_eq_right hkey]
    refine OracleComp.isQueryBoundP_bind (m := 0) ?_ fun endpoints _ => hleaf endpoints
    rw [Concrete.topOneTimePublicKey]
    refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
    apply Concrete.topChainWalk_queryBound_zero_of_avoids
    intro offset _ hvalid heq
    simp only [HashDomain.topChain.injEq] at heq
    exact hkey heq.1

/-- A top leaf queries its own leaf address once and no other top leaf address. -/
theorem Concrete.topLeafAt_queryBound_leafAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key targetKey : TopIndex) :
    (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.topLeaf targetKey)) (if key = targetKey then 1 else 0) := by
  have hchains : (Concrete.topOneTimePublicKey parameter topSecret key :
      OracleComp HashSpec (ChainIndex → Digest)).IsQueryBoundP
        (AtHashAddress parameter (.topLeaf targetKey)) 0 := by
    rw [Concrete.topOneTimePublicKey]
    refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
    apply Concrete.topChainWalk_queryBound_zero_of_avoids
    intro offset _ hvalid heq
    cases heq
  rw [Concrete.topLeafAt]
  by_cases hkey : key = targetKey
  · subst targetKey
    rw [ite_eq_left rfl]
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 1) hchains fun endpoints _ =>
      Concrete.tweakableHash_queryBound_atAddress parameter (.topLeaf key)
        (Concrete.leafPayload endpoints)
  · rw [ite_eq_right hkey]
    exact OracleComp.isQueryBoundP_bind (n := 0) (m := 0) hchains fun endpoints _ =>
      Concrete.tweakableHash_queryBound_atOtherAddress parameter (.topLeaf targetKey)
        (.topLeaf key) (Concrete.leafPayload endpoints) (by simpa using hkey)

theorem Concrete.topLeafAt_queryBound_zero_merkleAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) (targetLevel : MerkleLevel) (targetNode : TopNode) :
    (Concrete.topLeafAt parameter topSecret key : OracleComp HashSpec Digest).IsQueryBoundP
      (AtHashAddress parameter (.topMerkle targetLevel targetNode)) 0 := by
  rw [Concrete.topLeafAt]
  refine OracleComp.isQueryBoundP_bind (m := 0) ?_ ?_
  · rw [Concrete.topOneTimePublicKey]
    refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
    apply Concrete.topChainWalk_queryBound_zero_of_avoids
    intro offset _ hvalid heq
    cases heq
  · intro endpoints _
    exact Concrete.tweakableHash_queryBound_atOtherAddress parameter _ (.topLeaf key)
      (Concrete.leafPayload endpoints) (by simp)

/-! ### The top tree -/

/-- The top tree queries a top chain or leaf address of the keys it covers, at most once. -/
theorem Concrete.topTreeNode_queryBound_keyAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (targetKey : TopIndex) (target : HashDomain)
    (hleaf : ∀ key, (Concrete.topLeafAt parameter topSecret key :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter target)
        (if key = targetKey then 1 else 0))
    (hmerkle : ∀ level node, HashDomain.topMerkle level node ≠ target)
    (levels : Nat) (node : TopNode) (hlevels : levels ≤ treeHeight)
    (hvalid : TopSubtreeValid levels node) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter target)
        (if TopCovers levels node targetKey then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.topTreeNode]
      simpa only [topCovers_zero_iff] using hleaf node
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleft := ih (Concrete.topChildNode node false) (Nat.le_of_succ_le hlevels)
        (topChildNode_subtreeValid levels node false hvalid)
      have hright := ih (Concrete.topChildNode node true) (Nat.le_of_succ_le hlevels)
        (topChildNode_subtreeValid levels node true hvalid)
      rw [Concrete.topTreeNode, ← topCovers_children_sum levels node targetKey hvalid]
      refine OracleComp.isQueryBoundP_bind hleft fun left _ => ?_
      refine (OracleComp.isQueryBoundP_bind (m := 0) hright fun right _ => ?_).mono (by omega)
      simp only [hlevel, ↓reduceDIte]
      exact Concrete.tweakableHash_queryBound_atOtherAddress parameter target
        (.topMerkle ⟨levels, hlevel⟩ node) (Concrete.nodePayload left right) (hmerkle _ _)

def TopMerkleInSubtree (targetLevel : MerkleLevel) (targetNode : TopNode)
    (levels : Nat) (node : TopNode) : Prop :=
  targetLevel.val < levels ∧ TopCovers (levels - (targetLevel.val + 1)) node targetNode

instance (targetLevel : MerkleLevel) (targetNode : TopNode) (levels : Nat) (node : TopNode) :
    Decidable (TopMerkleInSubtree targetLevel targetNode levels node) := by
  unfold TopMerkleInSubtree
  infer_instance

theorem topMerkleInSubtree_step_sum
    (targetLevel : MerkleLevel) (targetNode : TopNode)
    (levels : Nat) (node : TopNode) (hlevel : levels < treeHeight)
    (hvalid : TopSubtreeValid (levels + 1) node) :
    (if TopMerkleInSubtree targetLevel targetNode levels
          (Concrete.topChildNode node false) then 1 else 0) +
        ((if TopMerkleInSubtree targetLevel targetNode levels
          (Concrete.topChildNode node true) then 1 else 0) +
          if HashDomain.topMerkle ⟨levels, hlevel⟩ node =
            .topMerkle targetLevel targetNode then 1 else 0) =
      if TopMerkleInSubtree targetLevel targetNode (levels + 1) node then 1 else 0 := by
  by_cases hlt : targetLevel.val < levels
  · have hparentLt : targetLevel.val < levels + 1 := by omega
    have hexponent : levels + 1 - (targetLevel.val + 1) =
        (levels - (targetLevel.val + 1)) + 1 := by omega
    have hsmall : (levels - (targetLevel.val + 1)) + 1 ≤ levels + 1 := by omega
    have hpartition := topCovers_children_sum
      (levels - (targetLevel.val + 1)) node targetNode
      (topSubtreeValid_mono hsmall hvalid)
    have hdomain : HashDomain.topMerkle ⟨levels, hlevel⟩ node ≠
        .topMerkle targetLevel targetNode := by
      intro heq
      have hlevelEq := congrArg Fin.val (HashDomain.topMerkle.inj heq).1
      simp only at hlevelEq
      omega
    unfold TopMerkleInSubtree
    simp only [hlt, hparentLt, true_and, hdomain, ite_false, add_zero]
    rw [hexponent]
    exact hpartition
  · by_cases heq : targetLevel.val = levels
    · have hlevelEq : targetLevel = ⟨levels, hlevel⟩ := by
        apply Fin.ext
        exact heq
      subst targetLevel
      simp only [TopMerkleInSubtree, lt_self_iff_false, false_and, ite_false,
        Nat.lt_succ_self, true_and, Nat.sub_self, topCovers_zero_iff,
        HashDomain.topMerkle.injEq]
      simp
    · have habove : levels < targetLevel.val := by omega
      have hnotParent : ¬targetLevel.val < levels + 1 := by omega
      have hdomain : HashDomain.topMerkle ⟨levels, hlevel⟩ node ≠
          .topMerkle targetLevel targetNode := by
        intro hsame
        have hlevelEq := congrArg Fin.val (HashDomain.topMerkle.inj hsame).1
        simp only at hlevelEq
        omega
      simp [TopMerkleInSubtree, hlt, hnotParent, hdomain]

theorem Concrete.topTreeNode_queryBound_merkleAddress
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (targetLevel : MerkleLevel) (targetNode : TopNode)
    (levels : Nat) (node : TopNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TopSubtreeValid levels node) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.topMerkle targetLevel targetNode))
        (if TopMerkleInSubtree targetLevel targetNode levels node then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.topTreeNode]
      simpa [TopMerkleInSubtree] using
        Concrete.topLeafAt_queryBound_zero_merkleAddress parameter topSecret node
          targetLevel targetNode
  | succ levels ih =>
      have hlevel : levels < treeHeight := Nat.lt_of_succ_le hlevels
      have hleft := ih (Concrete.topChildNode node false) (Nat.le_of_succ_le hlevels)
        (topChildNode_subtreeValid levels node false hvalid)
      have hright := ih (Concrete.topChildNode node true) (Nat.le_of_succ_le hlevels)
        (topChildNode_subtreeValid levels node true hvalid)
      rw [Concrete.topTreeNode,
        ← topMerkleInSubtree_step_sum targetLevel targetNode levels node hlevel hvalid]
      refine OracleComp.isQueryBoundP_bind hleft fun left _ => ?_
      refine OracleComp.isQueryBoundP_bind hright fun right _ => ?_
      simp only [hlevel, ↓reduceDIte]
      by_cases heq : HashDomain.topMerkle ⟨levels, hlevel⟩ node =
          .topMerkle targetLevel targetNode
      · simp only [heq, ite_eq_left]
        obtain ⟨hlevelEq, hnodeEq⟩ := HashDomain.topMerkle.inj heq
        subst targetLevel
        subst targetNode
        exact Concrete.tweakableHash_queryBound_atAddress parameter
          (.topMerkle ⟨levels, hlevel⟩ node) (Concrete.nodePayload left right)
      · simp only [heq, ite_false]
        exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
          (.topMerkle targetLevel targetNode) (.topMerkle ⟨levels, hlevel⟩ node)
          (Concrete.nodePayload left right) heq

/-- The top tree queries no top message digest address. -/
theorem Concrete.topTreeNode_queryBound_zero_topEncoding
    (parameter : PublicParameter) (topSecret : TopIndex → ChainIndex → Digest)
    (key : TopIndex) (levels : Nat) (node : TopNode) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter (.topEncoding key)) 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.topTreeNode, Concrete.topLeafAt]
      refine OracleComp.isQueryBoundP_bind (m := 0) ?_ fun endpoints _ =>
        Concrete.tweakableHash_queryBound_atOtherAddress parameter _ (.topLeaf node)
          (Concrete.leafPayload endpoints) (by simp)
      rw [Concrete.topOneTimePublicKey]
      refine Concrete.sequenceFin_queryBound_zero _ _ fun chain => ?_
      apply Concrete.topChainWalk_queryBound_zero_of_avoids
      intro offset _ hvalid heq
      cases heq
  | succ levels ih =>
      rw [Concrete.topTreeNode]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) fun left _ => ?_
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) fun right _ => ?_
      split
      · exact Concrete.tweakableHash_queryBound_atOtherAddress parameter _ _ _ (by simp)
      · simp

/-! ### Key generation -/

theorem Concrete.topSignFrom_queryBound_zero_of_not_encoding
    (parameter : PublicParameter) (target : HashDomain)
    (htarget : ∀ key, HashDomain.topEncoding key ≠ target)
    (key : TopIndex) (root : Digest) (base : Randomness) (attempts trial : Nat) :
    (Concrete.topSignFrom parameter key root base attempts trial :
      OracleComp HashSpec (Option (Randomness × Encoding))).IsQueryBoundP
        (AtHashAddress parameter target) 0 := by
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom]
  | succ attempts ih =>
      rw [Concrete.topSignFrom]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.tweakableHash_queryBound_atOtherAddress parameter target _ _ (htarget key)) ?_
      intro digest _
      split
      · simp
      · exact ih _

/-- Key generation's honest computation queries a top chain, leaf or Merkle address only in its
top tree. -/
theorem Concrete.honestKeygen_queryBound_of_topTree
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (target : HashDomain) (htop : target.isTop = true)
    (htarget : ∀ key, HashDomain.topEncoding key ≠ target) (n : Nat)
    (htree : (Concrete.topTreeNode parameter topSecret treeHeight Concrete.rootNode :
      OracleComp HashSpec Digest).IsQueryBoundP (AtHashAddress parameter target) n) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter target) n := by
  have hbottom : RejectsBottomTree parameter (AtHashAddress parameter target) := by
    intro domain payload hdomain _ hat
    rw [atHashAddress_tweakableHashInput_iff] at hat
    subst hat
    simp [hdomain] at htop
  unfold Concrete.honestKeygen
  refine OracleComp.IsQueryBoundP.mono (n := 0 + (n + 0))
    (OracleComp.isQueryBoundP_bind
      (Concrete.sequenceFin_queryBound_zero _ _ fun key => ?_) fun _ _ =>
      OracleComp.isQueryBoundP_bind htree fun _ _ => OracleComp.isQueryBoundP_pure _ _ _)
    (by omega)
  exact OracleComp.isQueryBoundP_bind (m := 0)
    (Concrete.treeNode_queryBound_zero_of_rejectsBottomTree parameter _ hbottom secret _ _)
    fun root _ => OracleComp.isQueryBoundP_bind (m := 0) (by simp) fun base _ =>
      Concrete.topSignFrom_queryBound_zero_of_not_encoding parameter target htarget key root base
        _ 0

theorem topSubtreeValid_rootNode : TopSubtreeValid treeHeight Concrete.rootNode := by
  simp [TopSubtreeValid, Concrete.rootNode, topLifetime]

theorem Concrete.honestKeygen_queryBound_topChainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (key : TopIndex) (chain : ChainIndex) (step : ChainStep) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter (.topChain key chain step)) 1 :=
  Concrete.honestKeygen_queryBound_of_topTree parameter secret topSecret topBase _ rfl
    (by simp) 1 ((Concrete.topTreeNode_queryBound_keyAddress parameter topSecret key _
      (fun leafKey => Concrete.topLeafAt_queryBound_chainAddress parameter topSecret leafKey key
        chain step) (by simp) treeHeight Concrete.rootNode le_rfl topSubtreeValid_rootNode).mono
      (by split <;> omega))

theorem Concrete.honestKeygen_queryBound_topLeafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (key : TopIndex) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter (.topLeaf key)) 1 :=
  Concrete.honestKeygen_queryBound_of_topTree parameter secret topSecret topBase _ rfl
    (by simp) 1 ((Concrete.topTreeNode_queryBound_keyAddress parameter topSecret key _
      (fun leafKey => Concrete.topLeafAt_queryBound_leafAddress parameter topSecret leafKey key)
      (by simp) treeHeight Concrete.rootNode le_rfl topSubtreeValid_rootNode).mono
      (by split <;> omega))

theorem Concrete.honestKeygen_queryBound_topMerkleAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (level : MerkleLevel) (node : TopNode) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP (AtHashAddress parameter (.topMerkle level node)) 1 :=
  Concrete.honestKeygen_queryBound_of_topTree parameter secret topSecret topBase _ rfl
    (by simp) 1 ((Concrete.topTreeNode_queryBound_merkleAddress parameter topSecret level node
      treeHeight Concrete.rootNode le_rfl topSubtreeValid_rootNode).mono (by split <;> omega))

end XmssSecurity

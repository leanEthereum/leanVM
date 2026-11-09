module

public import XmssSecurity.Proof.ConcreteQueryBound
public import XmssSecurity.Proof.StatementLemmas

@[expose] public section

open OracleComp OracleSpec

namespace XmssSecurity

def TreeCovers (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) : Prop :=
  node.val * 2 ^ levels ≤ leafIndex.val ∧ leafIndex.val < (node.val + 1) * 2 ^ levels

def TreeSubtreeValid (levels : Nat) (node : MerkleNode) : Prop :=
  (node.val + 1) * 2 ^ levels ≤ lifetime

instance (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex) :
    Decidable (TreeCovers levels node leafIndex) := by
  unfold TreeCovers
  infer_instance

theorem childNode_val_of_subtreeValid_succ (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    (Concrete.childNode node right).val = 2 * node.val + if right then 1 else 0 := by
  rw [Concrete.childNode, Concrete.merkleNodeOfNat]
  apply Nat.mod_eq_of_lt
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem childNode_subtreeValid (levels : Nat) (node : MerkleNode)
    (right : Bool) (hvalid : TreeSubtreeValid (levels + 1) node) :
    TreeSubtreeValid levels (Concrete.childNode node right) := by
  unfold TreeSubtreeValid
  rw [childNode_val_of_subtreeValid_succ levels node right hvalid]
  unfold TreeSubtreeValid at hvalid
  rw [pow_succ] at hvalid
  have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
  split <;> nlinarith

theorem treeCovers_children_sum (levels : Nat) (node : MerkleNode) (leafIndex : LeafIndex)
    (hvalid : TreeSubtreeValid (levels + 1) node) :
    (if TreeCovers levels (Concrete.childNode node false) leafIndex then 1 else 0) +
        (if TreeCovers levels (Concrete.childNode node true) leafIndex then 1 else 0) =
      if TreeCovers (levels + 1) node leafIndex then 1 else 0 := by
  by_cases hleft : TreeCovers levels (Concrete.childNode node false) leafIndex
  <;> by_cases hright : TreeCovers levels (Concrete.childNode node true) leafIndex
  <;> by_cases hparent : TreeCovers (levels + 1) node leafIndex
  <;> simp only [hleft, hright, hparent, ↓reduceIte]
  all_goals
    unfold TreeCovers at hleft hright hparent
    simp only [childNode_val_of_subtreeValid_succ levels node false hvalid,
      childNode_val_of_subtreeValid_succ levels node true hvalid,
      Bool.false_eq_true, ↓reduceIte] at hleft hright
    rw [pow_succ] at hparent
    have hpow : 0 < 2 ^ levels := pow_pos (by omega) _
    ring_nf at hleft hright hparent
    omega

theorem Concrete.treeNode_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex))
        (if TreeCovers levels node targetLeafIndex then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      by_cases hcover : TreeCovers 0 node targetLeafIndex
      · have heq : node = targetLeafIndex := by
          apply Fin.ext
          unfold TreeCovers at hcover
          simp only [pow_zero, mul_one] at hcover
          omega
        subst targetLeafIndex
        simpa [hcover] using
          Concrete.leafAt_queryBound_leafAddress parameter secret node node
      · have hne : node ≠ targetLeafIndex := by
          intro heq
          subst targetLeafIndex
          apply hcover
          unfold TreeCovers
          simp
        simpa [hcover] using
          Concrete.leafAt_queryBound_zero_at_other_leaf parameter secret node
            targetLeafIndex hne
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
              (AtHashAddress parameter (.leaf targetLeafIndex))
              (if TreeCovers levels (Concrete.childNode node true) targetLeafIndex then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind (m := 0) hright ?_
        intro right _
        exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
          (.leaf targetLeafIndex) (.merkle ⟨levels, hlevel⟩ node)
          (Concrete.nodePayload left right) (by simp)
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte, Nat.add_zero,
        treeCovers_children_sum levels node targetLeafIndex hvalid] using hall

/-! ### Key generation's honest computation by part

The bottom trees query only bottom chain, leaf and Merkle domains, the top grinding and the top tree
only top domains, so a predicate that rejects the top domains is bounded by the bottom trees alone. -/

/-- A predicate rejecting every input of the top layer's domains. -/
def RejectsTop (parameter : PublicParameter) (p : HashInput → Prop) : Prop :=
  ∀ domain payload, domain.isTop = true → ¬ p (tweakableHashInput parameter domain payload)

/-- A predicate rejecting every input of the bottom chain, leaf and Merkle domains. -/
def RejectsBottomTree (parameter : PublicParameter) (p : HashInput → Prop) : Prop :=
  ∀ domain payload, domain.isTop = false → (∀ leafIndex, domain ≠ .encoding leafIndex) →
    ¬ p (tweakableHashInput parameter domain payload)

-- The top tree is fully concrete at `treeHeight`; keep elaboration from unfolding it.
attribute [local irreducible] Concrete.topTreeNode

theorem Concrete.tweakableHash_queryBound_zero_of_not
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (p : HashInput → Prop) [DecidablePred p]
    (hnot : ¬ p (tweakableHashInput parameter domain payload)) :
    (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  simp [Concrete.tweakableHash, Concrete.oracleHash, hnot]

section HonestKeygenParts

variable (parameter : PublicParameter) (p : HashInput → Prop) [DecidablePred p]

theorem Concrete.topChainWalk_queryBound_zero_of_rejectsTop (htop : RejectsTop parameter p)
    (key : TopIndex) (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.topChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction steps with
  | zero => simp [Concrete.topChainWalk]
  | succ steps ih =>
      rw [Concrete.topChainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)
      · simp

theorem Concrete.topTreeNode_queryBound_zero_of_rejectsTop (htop : RejectsTop parameter p)
    (topSecret : TopIndex → ChainIndex → Digest) (levels : Nat) (node : TopNode) :
    (Concrete.topTreeNode parameter topSecret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.topTreeNode, Concrete.topLeafAt]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.sequenceFin_queryBound_zero _ p fun chain =>
          Concrete.topChainWalk_queryBound_zero_of_rejectsTop parameter p htop _ _ _ _ _) ?_
      intro endpoints _
      exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)
  | succ levels ih =>
      rw [Concrete.topTreeNode]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro right _
      split
      · exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)
      · simp

theorem Concrete.topSignFrom_queryBound_zero_of_rejectsTop (htop : RejectsTop parameter p)
    (key : TopIndex) (root : Digest) (base : Randomness) (attempts trial : Nat) :
    (Concrete.topSignFrom parameter key root base attempts trial :
      OracleComp HashSpec (Option (Randomness × Encoding))).IsQueryBoundP p 0 := by
  induction attempts generalizing trial with
  | zero => simp [Concrete.topSignFrom]
  | succ attempts ih =>
      rw [Concrete.topSignFrom]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p (htop _ _ rfl)) ?_
      intro digest _
      split
      · simp
      · exact ih _

theorem Concrete.chainWalk_queryBound_zero_of_rejectsBottomTree
    (hbottom : RejectsBottomTree parameter p)
    (leafIndex : LeafIndex) (chain : ChainIndex) (position steps : Nat) (value : Digest) :
    (Concrete.chainWalk parameter leafIndex chain position steps value :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction steps with
  | zero => simp [Concrete.chainWalk]
  | succ steps ih =>
      rw [Concrete.chainWalk]
      refine OracleComp.isQueryBoundP_bind (m := 0) ih ?_
      intro previous _
      split
      · exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p
          (hbottom _ _ rfl (by simp))
      · simp

theorem Concrete.treeNode_queryBound_zero_of_rejectsBottomTree
    (hbottom : RejectsBottomTree parameter p)
    (secret : LeafIndex → ChainIndex → Digest) (levels : Nat) (node : MerkleNode) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP p 0 := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq, Concrete.leafAt]
      refine OracleComp.isQueryBoundP_bind (m := 0)
        (Concrete.sequenceFin_queryBound_zero _ p fun chain =>
          Concrete.chainWalk_queryBound_zero_of_rejectsBottomTree parameter p hbottom _ _ _ _ _) ?_
      intro endpoints _
      exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p
        (hbottom _ _ rfl (by simp))
  | succ levels ih =>
      rw [Concrete.treeNode_succ_eq]
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro left _
      refine OracleComp.isQueryBoundP_bind (m := 0) (ih _) ?_
      intro right _
      split
      · exact Concrete.tweakableHash_queryBound_zero_of_not parameter _ _ p
          (hbottom _ _ rfl (by simp))
      · simp

variable (secret : LeafIndex → ChainIndex → Digest) (topSecret : TopIndex → ChainIndex → Digest)
  (topBase : TopIndex → Digest → OracleComp HashSpec Randomness)

/-- Key generation's honest computation is bounded by its bottom trees, for a predicate rejecting
the top domains and met by no top base query. -/
theorem Concrete.honestKeygen_queryBound_of_bottomTrees (bound : TopIndex → Nat) (n : Nat)
    (htop : RejectsTop parameter p) (hbase : ∀ key root, (topBase key root).IsQueryBoundP p 0)
    (htrees : ∀ key, (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode key) :
      OracleComp HashSpec Digest).IsQueryBoundP p (bound key))
    (hsequence : ∀ computation : TopIndex → OracleComp HashSpec (Option (Randomness × Encoding)),
      (∀ key, (computation key).IsQueryBoundP p (bound key)) →
        (Concrete.sequenceFin computation).IsQueryBoundP p n) :
    (Concrete.honestKeygen parameter secret topSecret topBase :
      OracleComp HashSpec _).IsQueryBoundP p n := by
  unfold Concrete.honestKeygen
  refine OracleComp.IsQueryBoundP.mono (n := n + (0 + 0))
    (OracleComp.isQueryBoundP_bind (hsequence _ fun key => ?_) fun _ _ =>
      OracleComp.isQueryBoundP_bind
        (Concrete.topTreeNode_queryBound_zero_of_rejectsTop parameter p htop topSecret _ _)
        fun _ _ => OracleComp.isQueryBoundP_pure p _ _) (by omega)
  exact OracleComp.IsQueryBoundP.mono (n := bound key + (0 + 0))
    (OracleComp.isQueryBoundP_bind (htrees key) fun root _ =>
      OracleComp.isQueryBoundP_bind (hbase key root) fun base _ =>
        Concrete.topSignFrom_queryBound_zero_of_rejectsTop parameter p htop key root base _ 0)
    (by omega)

/-- Key generation's honest computation makes no query rejected by both layers' trees and grinding. -/
theorem Concrete.honestKeygen_queryBound_zero
    (htop : RejectsTop parameter p) (hbottom : RejectsBottomTree parameter p)
    (hbase : ∀ key root, (topBase key root).IsQueryBoundP p 0) :
    (Concrete.honestKeygen parameter secret topSecret topBase :
      OracleComp HashSpec _).IsQueryBoundP p 0 :=
  Concrete.honestKeygen_queryBound_of_bottomTrees parameter p secret topSecret topBase (fun _ => 0) 0
    htop hbase
    (fun _ => Concrete.treeNode_queryBound_zero_of_rejectsBottomTree parameter p hbottom secret _ _)
    fun computation h => Concrete.sequenceFin_queryBound_zero computation p h

/-- Key generation's honest computation queries an address of one bottom tree at most once. -/
theorem Concrete.honestKeygen_queryBound_one (target : TopIndex)
    (htop : RejectsTop parameter p) (hbase : ∀ key root, (topBase key root).IsQueryBoundP p 0)
    (htarget : (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode target) :
      OracleComp HashSpec Digest).IsQueryBoundP p 1)
    (hother : ∀ key, key ≠ target →
      (Concrete.treeNode parameter secret treeHeight (Concrete.bottomRootNode key) :
        OracleComp HashSpec Digest).IsQueryBoundP p 0) :
    (Concrete.honestKeygen parameter secret topSecret topBase :
      OracleComp HashSpec _).IsQueryBoundP p 1 :=
  Concrete.honestKeygen_queryBound_of_bottomTrees parameter p secret topSecret topBase
    (fun key => if key = target then 1 else 0) 1 htop hbase
    (fun key => by split <;> rename_i h <;> [exact h ▸ htarget; exact hother key h])
    fun computation h => Concrete.sequenceFin_queryBound_one computation p target
      (by simpa using h target) fun key hne => by simpa [hne] using h key

end HonestKeygenParts

theorem rejectsTop_atHashAddress (parameter : PublicParameter) (target : HashDomain)
    (htarget : target.isTop = false) : RejectsTop parameter (AtHashAddress parameter target) := by
  intro domain payload hdomain hat
  rw [atHashAddress_tweakableHashInput_iff] at hat
  subst hat
  simp [htarget] at hdomain

theorem treeCovers_bottomRootNode_iff (key : TopIndex) (leafIndex : LeafIndex) :
    TreeCovers treeHeight (Concrete.bottomRootNode key) leafIndex ↔ key = topKeyOf leafIndex := by
  have hleaf := leafIndex.isLt
  simp only [TreeCovers, Concrete.bottomRootNode, topKeyOf, Fin.ext_iff, treeHeight, lifetime] at hleaf ⊢
  omega

theorem treeSubtreeValid_bottomRootNode (key : TopIndex) :
    TreeSubtreeValid treeHeight (Concrete.bottomRootNode key) := by
  have hkey := key.isLt
  simp only [TreeSubtreeValid, Concrete.bottomRootNode, topLifetime, treeHeight, lifetime] at hkey ⊢
  omega

/-- The honest computation of key generation queries each bottom leaf address at most once. -/
theorem Concrete.rootTree_queryBound_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLeafIndex : LeafIndex) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.leaf targetLeafIndex)) 1 := by
  refine Concrete.honestKeygen_queryBound_one parameter _ secret topSecret _ (topKeyOf targetLeafIndex)
    (rejectsTop_atHashAddress parameter _ rfl) (fun _ _ => by simp) ?_ ?_
  · simpa [(treeCovers_bottomRootNode_iff _ _).2 rfl] using
      Concrete.treeNode_queryBound_leafAddress parameter secret targetLeafIndex treeHeight
        (Concrete.bottomRootNode (topKeyOf targetLeafIndex)) le_rfl (treeSubtreeValid_bottomRootNode _)
  · intro key hne
    simpa [treeCovers_bottomRootNode_iff, hne] using
      Concrete.treeNode_queryBound_leafAddress parameter secret targetLeafIndex treeHeight
        (Concrete.bottomRootNode key) le_rfl (treeSubtreeValid_bottomRootNode _)

/-- A supported execution of key generation's honest computation from an empty cache contains at most one input at each bottom leaf address. -/
theorem Concrete.CacheReplay.rootTree_cache_unique_leafAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetLeafIndex : LeafIndex) (left right : HashInput)
    (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.leaf targetLeafIndex) left)
    (hrightP : AtHashAddress parameter (.leaf targetLeafIndex) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right :=
  Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.leaf targetLeafIndex)) ∅ cache result
    (Concrete.rootTree_queryBound_leafAddress parameter secret topSecret topBase targetLeafIndex)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright

theorem Concrete.treeNode_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (levels : Nat) (node : MerkleNode)
    (hlevels : levels ≤ treeHeight) (hvalid : TreeSubtreeValid levels node) :
    (Concrete.treeNode parameter secret levels node :
      OracleComp HashSpec Digest).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep))
        (if TreeCovers levels node targetLeafIndex then 1 else 0) := by
  induction levels generalizing node with
  | zero =>
      rw [Concrete.treeNode_zero_eq]
      by_cases hcover : TreeCovers 0 node targetLeafIndex
      · have heq : node = targetLeafIndex := by
          apply Fin.ext
          unfold TreeCovers at hcover
          simp only [pow_zero, mul_one] at hcover
          omega
        subst targetLeafIndex
        simpa [hcover] using
          Concrete.leafAt_queryBound_chainAddress parameter secret node node
            targetChain targetStep
      · have hne : node ≠ targetLeafIndex := by
          intro heq
          subst targetLeafIndex
          apply hcover
          unfold TreeCovers
          simp
        simpa [hcover] using
          Concrete.leafAt_queryBound_zero_chainAddress_at_other_leafIndex parameter secret node
            targetLeafIndex targetChain targetStep hne
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
              (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep))
              (if TreeCovers levels (Concrete.childNode node true) targetLeafIndex then 1 else 0) := by
        refine OracleComp.isQueryBoundP_bind (m := 0) hright ?_
        intro right _
        exact Concrete.tweakableHash_queryBound_atOtherAddress parameter
          (.chain targetLeafIndex targetChain targetStep) (.merkle ⟨levels, hlevel⟩ node)
          (Concrete.nodePayload left right) (by simp)
      have hall := OracleComp.isQueryBoundP_bind hleft
        (fun left _ => hcontinuation left)
      simpa only [hlevel, ↓reduceDIte, Nat.add_zero,
        treeCovers_children_sum levels node targetLeafIndex hvalid] using hall

/-- The honest computation of key generation queries each bottom chain-step address at most once. -/
theorem Concrete.rootTree_queryBound_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep) :
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _).IsQueryBoundP
        (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) 1 := by
  refine Concrete.honestKeygen_queryBound_one parameter _ secret topSecret _ (topKeyOf targetLeafIndex)
    (rejectsTop_atHashAddress parameter _ rfl) (fun _ _ => by simp) ?_ ?_
  · simpa [(treeCovers_bottomRootNode_iff _ _).2 rfl] using
      Concrete.treeNode_queryBound_chainAddress parameter secret targetLeafIndex targetChain
        targetStep treeHeight (Concrete.bottomRootNode (topKeyOf targetLeafIndex)) le_rfl
        (treeSubtreeValid_bottomRootNode _)
  · intro key hne
    simpa [treeCovers_bottomRootNode_iff, hne] using
      Concrete.treeNode_queryBound_chainAddress parameter secret targetLeafIndex targetChain
        targetStep treeHeight (Concrete.bottomRootNode key) le_rfl (treeSubtreeValid_bottomRootNode _)

/-- A supported execution of key generation's honest computation from an empty cache contains at most one input at each bottom chain-step address. -/
theorem Concrete.CacheReplay.rootTree_cache_unique_chainAddress
    (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest)
    (topSecret : TopIndex → ChainIndex → Digest) (topBase : TopIndex → Randomness)
    (result : Digest × (TopIndex → Option (Randomness × Encoding))) (cache : QueryCache HashSpec)
    (hmem : (result, cache) ∈ support
      ((simulateQ randomOracle
        (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
          OracleComp HashSpec _)).run ∅))
    (targetLeafIndex : LeafIndex) (targetChain : ChainIndex) (targetStep : ChainStep)
    (left right : HashInput) (leftOutput rightOutput : HashOutput)
    (hleftP : AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep) left)
    (hrightP : AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep) right)
    (hleft : cache left = some leftOutput)
    (hright : cache right = some rightOutput) :
    left = right :=
  Concrete.CacheReplay.cache_unique_of_query_bound_one
    (Concrete.honestKeygen parameter secret topSecret (fun key _ => pure (topBase key)) :
      OracleComp HashSpec _)
    (AtHashAddress parameter (.chain targetLeafIndex targetChain targetStep)) ∅ cache result
    (Concrete.rootTree_queryBound_chainAddress parameter secret topSecret topBase targetLeafIndex
      targetChain targetStep)
    (by simp) hmem left right leftOutput rightOutput hleftP hrightP hleft hright
end XmssSecurity

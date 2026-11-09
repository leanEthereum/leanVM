module

public import XmssSecurity.Proof.ConcreteCorrectness
public import XmssSecurity.Proof.TreeQueryBound

@[expose] public section

namespace XmssSecurity

theorem treeSubtreeValid_pathNode
    (leafIndex : LeafIndex) (levels : Nat) (hlevels : levels ≤ treeHeight) :
    TreeSubtreeValid levels
      (Concrete.CacheReplay.pathNode leafIndex levels) := by
  have hfactor :
      2 ^ (2 * treeHeight - levels) * 2 ^ levels = lifetime := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rfl
  have hquotient : leafIndex.val / 2 ^ levels < 2 ^ (2 * treeHeight - levels) := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos (by omega) _)]
    rw [hfactor]
    exact leafIndex.isLt
  have hpath :
      (Concrete.CacheReplay.pathNode leafIndex levels).val =
        leafIndex.val / 2 ^ levels := by
    unfold Concrete.CacheReplay.pathNode Concrete.merkleNodeOfNat
    exact Nat.mod_eq_of_lt
      ((Nat.div_le_self leafIndex.val _).trans_lt leafIndex.isLt)
  unfold TreeSubtreeValid
  rw [hpath]
  nlinarith

theorem authenticationPathNode_subtreeValid
    (leafIndex : LeafIndex) (level : MerkleLevel) :
    TreeSubtreeValid level.val
      (Concrete.authenticationPathNode leafIndex level) := by
  have hparent : TreeSubtreeValid (level.val + 1)
      (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) :=
    treeSubtreeValid_pathNode leafIndex (level.val + 1) (by omega)
  have hchildren := Concrete.CacheReplay.pathNode_children
    leafIndex level.val level.isLt
  by_cases hbit : leafIndex.val.testBit level.val = true
  · rw [ite_eq_left hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) false hparent
    rw [hchildren.1] at hvalid
    exact hvalid
  · rw [ite_eq_right hbit] at hchildren
    have hvalid := childNode_subtreeValid level.val
      (Concrete.CacheReplay.pathNode leafIndex (level.val + 1)) true hparent
    rw [hchildren.2] at hvalid
    exact hvalid

end XmssSecurity

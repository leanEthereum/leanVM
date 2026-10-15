import Sphincs.Recovery

/-!
Correctness of the pruned Merkle path, including the surrogate spine.
The argument holds for every hash function and every subtree height from 0 to 26.
The chain and FORS recovery lemmas are adapted from leanVM b7a107256.
-/

open OracleComp

namespace Sphincs.Completeness

open Concrete Seeded

variable (f : QueryImpl HashSpec Id) [Params]

theorem eval_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (level : Fin (layerHeight lay)) :
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf
        : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) level
      = if level.val < subtreeHeight then
          node f parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
        else evalWithAnswerFn f (surrogate parameter seed level.val : OracleComp HashSpec Digest) := by
  simp only [Seeded.treePath, eval_sequenceFin]
  split <;> rfl

/-- The verifier's index above the kept subtree is the signer's spine index. -/
theorem landed_div (parameter : PublicParameter) (leaf : LeafIndex)
    (hland : Landed parameter leaf) (steps : Nat) :
    leaf.val / 2 ^ (subtreeHeight + steps) = subtreePosition parameter / 2 ^ steps := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, hland]

/-- The subtree path followed by the surrogate siblings recovers every node of the spine. -/
theorem eval_treeFold_spine (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (hland : Landed parameter leaf)
    (path : Nat → Digest)
    (hlow : ∀ level, level < subtreeHeight →
      path level = node f parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level) 1))
    (steps : Nat)
    (hhigh : ∀ t, t < steps → path (subtreeHeight + t) =
      evalWithAnswerFn f (surrogate parameter seed (subtreeHeight + t)
        : OracleComp HashSpec Digest)) :
    evalWithAnswerFn f (treeFold parameter lay tree leaf path (subtreeHeight + steps)
      (node f parameter lay tree seed 0 leaf.val) : OracleComp HashSpec Digest) =
    evalWithAnswerFn f (spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Nat.add_zero, eval_treeFold_path f parameter lay tree seed leaf path _ hlow]
      rw [hland]
      rfl
  | succ steps ih =>
      rw [Nat.add_succ, treeFold, evalWithAnswerFn_bind,
        ih (fun t ht => hhigh t (Nat.lt_succ_of_lt ht)), hhigh steps (Nat.lt_succ_self _)]
      have hbit : leaf.val.testBit (subtreeHeight + steps) =
          (subtreePosition parameter / 2 ^ steps).testBit 0 := by
        rw [← landed_div parameter leaf hland steps]
        simpa only [Nat.zero_add] using Nat.testBit_add leaf.val 0 (subtreeHeight + steps)
      have hidx : leaf.val / 2 ^ (subtreeHeight + steps + 1) =
          subtreePosition parameter / 2 ^ steps / 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul, landed_div parameter leaf hland steps]
      simp only [spineNode, evalWithAnswerFn_bind, hbit, hidx]

/-- A complete pruned authentication path reaches the generated root. -/
theorem eval_treeFold_pruned_path (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (hland : Landed parameter leaf)
    (path : Nat → Digest)
    (hpath : ∀ level (hlevel : level < layerHeight lay), path level =
      evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf
        : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) ⟨level, hlevel⟩) :
    evalWithAnswerFn f (treeFold parameter lay tree leaf path totalHeight
      (node f parameter lay tree seed 0 leaf.val) : OracleComp HashSpec Digest) =
    evalWithAnswerFn f (treeRoot parameter lay tree seed : OracleComp HashSpec Digest) := by
  have hb := Params.subtreeHeight_le (self := inferInstance)
  have hsum : subtreeHeight + (totalHeight - subtreeHeight) = totalHeight :=
    Nat.add_sub_of_le hb
  rw [treeRoot, ← hsum, Nat.add_sub_cancel_left]
  apply eval_treeFold_spine f parameter lay tree seed leaf hland path
  · intro level hlevel
    have hlt : level < layerHeight lay := lt_of_lt_of_le hlevel hb
    rw [hpath level hlt, eval_treePath, if_pos hlevel]
  · intro t ht
    have hlt : subtreeHeight + t < layerHeight lay := by
      change subtreeHeight + t < totalHeight
      omega
    rw [hpath _ hlt, eval_treePath,
      if_neg (show ¬subtreeHeight + t < subtreeHeight by omega)]

end Sphincs.Completeness

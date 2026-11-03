import FORS.Scheme.Recovery

/-!
Correctness of the pruned Merkle path, including the surrogate spine, at every layer: the top
layer's kept subtree and its surrogates, and the whole trees below the top layer (whose kept part
is the whole tree, with no surrogate). The argument holds for every hash function, height and
shape. The chain recovery lemmas are adapted from leanVM b7a107256.
-/

open OracleComp

namespace FORS.Completeness

variable [Params]

open Concrete Seeded

variable (f : QueryImpl HashSpec Id)

/-! ### The shape of the layers -/

theorem layerHeight_top : layerHeight topLayer = maxLayerHeight := if_pos rfl

theorem layerHeight_of_ne_top (lay : Layer) (h : lay.val ≠ 0) : layerHeight lay = lowerHeight :=
  if_neg h

theorem heightBelow_top : heightBelow topLayer = lowerHeight * (numLayers - 1) := by
  simp [heightBelow, topLayer]

theorem maxLayerHeight_add : heightBelow topLayer + maxLayerHeight = totalHeight := by
  rw [heightBelow_top]
  have h1 := Params.lower_le
  have h2 := numLayers_pos
  unfold maxLayerHeight
  have : lowerHeight * numLayers = lowerHeight * (numLayers - 1) + lowerHeight := by
    rw [← Nat.mul_succ]; congr 1; omega
  omega

theorem heightBelow_le_subtree : heightBelow topLayer ≤ subtreeHeight := by
  rw [heightBelow_top]; exact Params.below_le

theorem keptHeight_top : keptHeight topLayer = subtreeHeight - heightBelow topLayer := if_pos rfl

theorem keptHeight_of_ne_top (lay : Layer) (h : lay.val ≠ 0) : keptHeight lay = layerHeight lay :=
  if_neg h

theorem keptHeight_le (lay : Layer) : keptHeight lay ≤ layerHeight lay := by
  by_cases h : lay.val = 0
  · have hl : lay = topLayer := Fin.ext h
    subst hl
    rw [keptHeight_top, layerHeight_top]
    have := maxLayerHeight_add
    have := subtreeHeight_le_total
    omega
  · rw [keptHeight_of_ne_top lay h]

theorem keptPosition_of_ne_top (parameter : PublicParameter) (lay : Layer) (h : lay.val ≠ 0) :
    keptPosition parameter lay = 0 := if_neg h

/-- Below the top layer, a leaf of a tree is kept. -/
theorem kept_of_ne_top (parameter : PublicParameter) (lay : Layer) (h : lay.val ≠ 0)
    (leaf : LeafIndex) (hleaf : leaf.val < 2 ^ layerHeight lay) : Kept parameter lay leaf := by
  unfold Kept
  rw [keptHeight_of_ne_top lay h, keptPosition_of_ne_top parameter lay h, Nat.div_eq_of_lt hleaf]

/-- The leaf of a layer on the path of an index lies in its tree. -/
theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The top layer's leaf of an index is the index without its bits below the top layer. -/
theorem leafIndexAt_top (index : Index) :
    (leafIndexAt index topLayer).val = index.val / 2 ^ heightBelow topLayer := by
  unfold leafIndexAt
  simp only
  rw [layerHeight_top]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.add_comm, maxLayerHeight_add]
  exact index.isLt

/-- The key of a layer on the path of an index signs the index's bits above that layer: its tree
`index / 2^heightBelow lay` of the layer below, or the instance itself at the bottom. -/
theorem childTree_path (index : Index) (lay : Layer) :
    (childTree lay (treeIndexAt index lay) (leafIndexAt index lay)).val =
      index.val / 2 ^ heightBelow lay := by
  simp only [childTree, treeIndexAt, leafIndexAt]
  rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt)

theorem heightBelow_succ (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    heightBelow ⟨lay.val + 1, hbelow⟩ + layerHeight ⟨lay.val + 1, hbelow⟩ = heightBelow lay := by
  rw [layerHeight_of_ne_top _ (Nat.succ_ne_zero _)]
  simp only [heightBelow]
  have : numLayers - 1 - lay.val = (numLayers - 1 - (lay.val + 1)) + 1 := by omega
  rw [this, Nat.mul_succ]

/-- Above the bottom layer, the key on the path signs the next tree down the path. -/
theorem childTree_path_above (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    childTree lay (treeIndexAt index lay) (leafIndexAt index lay) =
      treeIndexAt index ⟨lay.val + 1, hbelow⟩ := by
  apply Fin.ext
  rw [childTree_path]
  simp only [treeIndexAt]
  rw [heightBelow_succ lay hbelow]

/-- At the bottom layer, the key on the path signs the index's own FORS instance. -/
theorem childTree_path_bottom (index : Index) :
    childTree bottomLayer (treeIndexAt index bottomLayer) (leafIndexAt index bottomLayer) = index := by
  apply Fin.ext
  rw [childTree_path]
  simp [heightBelow, bottomLayer]

/-- A landed index keeps its leaf at every layer. -/
theorem kept_leafIndexAt (parameter : PublicParameter) (index : Index) (hland : Landed parameter index)
    (lay : Layer) : Kept parameter lay (leafIndexAt index lay) := by
  by_cases h : lay.val = 0
  · have hl : lay = topLayer := Fin.ext h
    subst hl
    unfold Kept
    rw [leafIndexAt_top, keptHeight_top, Nat.div_div_eq_div_mul, ← pow_add,
      Nat.add_sub_cancel' heightBelow_le_subtree]
    exact hland
  · exact kept_of_ne_top parameter lay h _ (leafIndexAt_lt index lay)

/-- At the top layer, an index's leaf is kept exactly when the index lands. -/
theorem landed_of_kept_top (parameter : PublicParameter) (index : Index)
    (hkept : Kept parameter topLayer (leafIndexAt index topLayer)) : Landed parameter index := by
  unfold Kept at hkept
  rw [leafIndexAt_top, keptHeight_top, Nat.div_div_eq_div_mul, ← pow_add,
    Nat.add_sub_cancel' heightBelow_le_subtree] at hkept
  exact hkept

/-! ### The path -/

theorem eval_treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (level : Fin (layerHeight lay)) :
    evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf
        : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) level
      = if level.val < keptHeight lay then
          node f parameter lay tree seed level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
        else evalWithAnswerFn f (surrogate parameter seed level.val : OracleComp HashSpec Digest) := by
  simp only [Seeded.treePath, eval_sequenceFin]
  split <;> rfl

/-- The verifier's index above the kept part is the signer's spine index. -/
theorem kept_div (parameter : PublicParameter) (lay : Layer) (leaf : LeafIndex)
    (hkept : Kept parameter lay leaf) (steps : Nat) :
    leaf.val / 2 ^ (keptHeight lay + steps) = keptPosition parameter lay / 2 ^ steps := by
  rw [pow_add, ← Nat.div_div_eq_div_mul, hkept]

/-- The kept part's path followed by the surrogate siblings recovers every node of the spine. -/
theorem eval_treeFold_spine (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (hkept : Kept parameter lay leaf)
    (path : Nat → Digest)
    (hlow : ∀ level, level < keptHeight lay →
      path level = node f parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level) 1))
    (steps : Nat)
    (hhigh : ∀ t, t < steps → path (keptHeight lay + t) =
      evalWithAnswerFn f (surrogate parameter seed (keptHeight lay + t)
        : OracleComp HashSpec Digest)) :
    evalWithAnswerFn f (treeFold parameter lay tree leaf path (keptHeight lay + steps)
      (node f parameter lay tree seed 0 leaf.val) : OracleComp HashSpec Digest) =
    evalWithAnswerFn f (spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Nat.add_zero, eval_treeFold_path f parameter lay tree seed leaf path _ hlow]
      rw [hkept]
      rfl
  | succ steps ih =>
      rw [Nat.add_succ, treeFold, evalWithAnswerFn_bind,
        ih (fun t ht => hhigh t (Nat.lt_succ_of_lt ht)), hhigh steps (Nat.lt_succ_self _)]
      have hbit : leaf.val.testBit (keptHeight lay + steps) =
          (keptPosition parameter lay / 2 ^ steps).testBit 0 := by
        rw [← kept_div parameter lay leaf hkept steps]
        simpa only [Nat.zero_add] using Nat.testBit_add leaf.val 0 (keptHeight lay + steps)
      have hidx : leaf.val / 2 ^ (keptHeight lay + steps + 1) =
          keptPosition parameter lay / 2 ^ steps / 2 := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul, kept_div parameter lay leaf hkept steps]
      simp only [spineNode, evalWithAnswerFn_bind, hbit, hidx]

/-- A complete pruned authentication path reaches the generated root of the layer's tree. -/
theorem eval_treeFold_pruned_path (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (seed : MasterSeed) (leaf : LeafIndex) (hkept : Kept parameter lay leaf)
    (path : Nat → Digest)
    (hpath : ∀ level (hlevel : level < layerHeight lay), path level =
      evalWithAnswerFn f (Seeded.treePath parameter lay tree seed leaf
        : OracleComp HashSpec (Fin (layerHeight lay) → Digest)) ⟨level, hlevel⟩) :
    evalWithAnswerFn f (treeFold parameter lay tree leaf path (layerHeight lay)
      (node f parameter lay tree seed 0 leaf.val) : OracleComp HashSpec Digest) =
    evalWithAnswerFn f (treeRoot parameter lay tree seed : OracleComp HashSpec Digest) := by
  have hb := keptHeight_le lay
  have hsum : keptHeight lay + (layerHeight lay - keptHeight lay) = layerHeight lay :=
    Nat.add_sub_of_le hb
  rw [treeRoot, ← hsum, Nat.add_sub_cancel_left]
  apply eval_treeFold_spine f parameter lay tree seed leaf hkept path
  · intro level hlevel
    have hlt : level < layerHeight lay := lt_of_lt_of_le hlevel hb
    rw [hpath level hlt, eval_treePath, if_pos hlevel]
  · intro t ht
    have hlt : keptHeight lay + t < layerHeight lay := by omega
    rw [hpath _ hlt, eval_treePath,
      if_neg (show ¬keptHeight lay + t < keptHeight lay by omega)]

end FORS.Completeness

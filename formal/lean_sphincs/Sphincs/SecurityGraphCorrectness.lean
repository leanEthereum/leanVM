import Sphincs.SecurityPrunedGraph
import Sphincs.SecurityForestWitness

/-! Canonical graph labels agree with actual seeded computations. The only graph hypotheses are
its query-response consistency and untouched surrogate boundary, which `BridgeAssembly` supplies
for every sample. No correctness of the labels is assumed. -/

open OracleComp OracleSpec
namespace Sphincs.Security.GraphCorrectness
open Concrete Completeness Graph PrunedGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
set_option allowUnsafeReducibility true
attribute [local reducible] digestBits HashSpec Id
set_option allowUnsafeReducibility false
attribute [local irreducible] Seeded.treeNode Seeded.subNode Seeded.topNode Seeded.spineNode chainWalk
  forestWalk sequenceFin

variable [inst : Params]

omit [Params] in
theorem one_lt_leaf_capacity : 1 < 2 ^ maxLayerHeight := by decide

def otsSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leaf chain => Completeness.otsSecret f parameter lay tree leaf seed chain

def ftsSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    ForestSecrets :=
  fun index c s j a i => Completeness.forestSecret f parameter index c s j a i seed

def surrogates (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    Fin totalHeight → Digest := fun level =>
  evalWithAnswerFn f (Seeded.surrogate parameter seed level.val : OracleComp HashSpec Digest)

def Consistent (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (labels : CanonicalGraphLabels) : Prop :=
  ∀ position, active parameter position → labels position =
    f (canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      position labels)

def BoundaryCorrect (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
    (labels : CanonicalGraphLabels) : Prop :=
  ∀ position value, boundary parameter (surrogates f parameter seed) position = some value →
    truncateHash (labels position) = value

-- The instance is passed explicitly so that `unusedSectionVars` sees `hconsistent` use it.
variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed)
  (labels : CanonicalGraphLabels) (hconsistent : @Consistent inst f parameter seed labels)

include hconsistent in
theorem chain_value (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hland : Landed parameter leaf) (chain : ChainIndex) (step : ChainStep) :
    truncateHash (labels (.chain lay tree leaf chain step)) =
      Chain.honestChain f parameter lay tree leaf chain
        (otsSecrets f parameter seed lay tree leaf chain) (step.val + 1) := by
  obtain ⟨step, hstep⟩ := step
  induction step with
  | zero =>
      rw [hconsistent (.chain lay tree leaf chain ⟨0, hstep⟩) hland,
        Chain.honestChain_succ _ _ _ _ _ _ _ _ hstep]
      have hz : Chain.honestChain f parameter lay tree leaf chain
          (otsSecrets f parameter seed lay tree leaf chain) 0 =
          otsSecrets f parameter seed lay tree leaf chain := by
        unfold Chain.honestChain
        rw [chainWalk]
        rfl
      rw [hz]
      apply congrArg (fun input : HashInput => truncateHash (f input))
      simp only [canonicalGraphInput, canonicalGraphSlots, Position.domain,
        ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | succ step ih =>
      have hprev : step < chainLength - 1 := by omega
      rw [hconsistent (.chain lay tree leaf chain ⟨step + 1, hstep⟩) hland,
        Chain.honestChain_succ _ _ _ _ _ _ _ _ hstep]
      apply congrArg (fun input : HashInput => truncateHash (f input))
      simp only [canonicalGraphInput, canonicalGraphSlots, Position.children, Position.domain]
      simp only [show step + 1 ≠ 0 by omega, show 0 < step + 1 by omega,
        ↓reduceIte, ↓reduceDIte, Nat.add_sub_cancel, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [ih hprev]

include hconsistent in
theorem leaf_input (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hland : Landed parameter leaf) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.leaf lay tree leaf) labels = tweakableHashInput parameter (.leaf lay tree leaf)
        (leafPayload (otsEndpoint f parameter lay tree leaf seed)) := by
  unfold canonicalGraphInput canonicalGraphSlots
  simp only [Position.children, Position.domain, List.map_ofFn]
  congr 1
  apply congrArg (fun values : List Digest => values.flatMap (bytesLE 16))
  apply congrArg List.ofFn
  funext chain
  simp only [Function.comp_apply]
  rw [chain_value f parameter seed labels hconsistent lay tree leaf hland chain]
  rfl

include hconsistent in
theorem leaf_value (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hland : Landed parameter leaf) :
    truncateHash (labels (.leaf lay tree leaf)) = node f parameter lay tree seed 0 leaf.val := by
  rw [hconsistent (.leaf lay tree leaf) hland,
    leaf_input f parameter seed labels hconsistent lay tree leaf hland, node_zero]
  simp only [leafHash, eval_tweakableHash]

/-- Graph location for a tree node, including the level-zero leaf. -/
def treePosition (lay : Layer) (tree : TreeIndex) :
    (level : Nat) → level ≤ maxLayerHeight → LeafIndex → Position
  | 0, _, index => .leaf lay tree index
  | level + 1, hlevel, index => .node lay tree ⟨level, by omega⟩ index

omit hconsistent [Params] in
theorem tree_input (lay : Layer) (tree : TreeIndex) (level : Nat)
    (hlevel : level + 1 ≤ maxLayerHeight) (index : LeafIndex)
    (hindex : 2 * index.val + 1 < 2 ^ maxLayerHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (treePosition lay tree (level + 1) hlevel index) labels =
    tweakableHashInput parameter (.node lay tree (level + 1) index.val)
      (nodePayload
        (truncateHash (labels (treePosition lay tree level (by omega) ⟨2 * index.val, by omega⟩)))
        (truncateHash (labels (treePosition lay tree level (by omega) ⟨2 * index.val + 1, hindex⟩)))) := by
  cases level <;>
    simp [treePosition, canonicalGraphInput, canonicalGraphSlots, Position.children,
      Position.domain, hindex, nodePayload]

omit f parameter seed labels hconsistent [Params] in
theorem child_index_bound {height level index : Nat} (hlevel : level + 1 ≤ height)
    (hindex : index < 2 ^ (height - (level + 1))) :
    2 * index + 1 < 2 ^ (height - level) := by
  have hsub : height - level = height - (level + 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  omega

omit f parameter seed labels hconsistent [Params] in
theorem double_div_pow (index level bit : Nat) (hbit : bit < 2) :
    (2 * index + bit) / 2 ^ (level + 1) = index / 2 ^ level := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ level), ← Nat.div_div_eq_div_mul]
  have hdiv : (2 * index + bit) / 2 = index := by omega
  rw [hdiv]

omit f seed labels hconsistent in
theorem treePosition_active_below (lay : Layer) (tree : TreeIndex) (level : Nat)
    (hlevel : level ≤ maxLayerHeight) (hlower : level ≤ subtreeHeight) (index : LeafIndex)
    (hkept : index.val / 2 ^ (subtreeHeight - level) = subtreePosition parameter) :
    active parameter (treePosition lay tree level hlevel index) := by
  cases level with
  | zero => simpa only [treePosition, active, Landed, Nat.sub_zero] using hkept
  | succ level => simpa only [treePosition, active, KeptNode, ite_eq_left hlower] using hkept

include hconsistent in
theorem tree_value_below (lay : Layer) (tree : TreeIndex) (level : Nat)
    (hlevel : level ≤ maxLayerHeight) (hlower : level ≤ subtreeHeight) (index : LeafIndex)
    (hindex : index.val < 2 ^ (maxLayerHeight - level))
    (hkept : index.val / 2 ^ (subtreeHeight - level) = subtreePosition parameter) :
    truncateHash (labels (treePosition lay tree level hlevel index)) =
      node f parameter lay tree seed level index.val := by
  induction level generalizing index with
  | zero =>
      exact leaf_value f parameter seed labels hconsistent lay tree index
        (by simpa only [Landed, Nat.sub_zero] using hkept)
  | succ level ih =>
      have hchildren := child_index_bound hlevel hindex
      have hglobal : 2 * index.val + 1 < 2 ^ maxLayerHeight :=
        hchildren.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
      have hsub : subtreeHeight - level = subtreeHeight - (level + 1) + 1 := by omega
      have hleft : (2 * index.val) / 2 ^ (subtreeHeight - level) = subtreePosition parameter := by
        rw [hsub, show 2 * index.val = 2 * index.val + 0 by omega, double_div_pow _ _ 0 (by decide)]
        exact hkept
      have hright : (2 * index.val + 1) / 2 ^ (subtreeHeight - level) = subtreePosition parameter := by
        rw [hsub, double_div_pow _ _ 1 (by decide)]
        exact hkept
      rw [hconsistent _ (treePosition_active_below parameter lay tree (level + 1) hlevel hlower index hkept),
        tree_input f parameter seed labels lay tree level hlevel index hglobal, node_succ,
        ih (by omega) (by omega) _ (by change 2 * index.val < _; omega) hleft,
        ih (by omega) (by omega) _ hchildren hright]

omit f seed labels hconsistent in
theorem spineIndex_range (level : Nat) (hlower : subtreeHeight ≤ level)
    (hupper : level ≤ maxLayerHeight) : spineIndex parameter level < 2 ^ (maxLayerHeight - level) := by
  unfold spineIndex
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  rw [← Nat.pow_add]
  have hexp : maxLayerHeight - level + (level - subtreeHeight) = totalHeight - subtreeHeight := by
    change totalHeight - level + (level - subtreeHeight) = totalHeight - subtreeHeight
    change level ≤ totalHeight at hupper
    omega
  rw [hexp]
  exact subtreePosition_lt parameter

omit f seed labels hconsistent in
theorem spineIndex_step (level : Nat) (hlower : subtreeHeight ≤ level) :
    spineIndex parameter (level + 1) = spineIndex parameter level / 2 := by
  unfold spineIndex
  rw [show level + 1 - subtreeHeight = (level - subtreeHeight) + 1 by omega,
    Nat.pow_succ, Nat.div_div_eq_div_mul]

omit f seed labels hconsistent in
theorem spinePosition_active (lay : Layer) (tree : TreeIndex) (level : Nat)
    (hlower : subtreeHeight ≤ level) (hupper : level ≤ maxLayerHeight) :
    active parameter (treePosition lay tree level hupper
      ⟨spineIndex parameter level, (spineIndex_range parameter level hlower hupper).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))⟩) := by
  cases level with
  | zero =>
      have hb : subtreeHeight = 0 := by omega
      simp [treePosition, active, Landed, spineIndex, hb]
  | succ level =>
      simp only [treePosition, active, KeptNode]
      split
      next h =>
        have heq : level + 1 = subtreeHeight := by omega
        simp [spineIndex, heq]
      next => trivial

omit hconsistent in
theorem boundary_tree_value (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (level : Fin totalHeight)
    (hlower : subtreeHeight ≤ level.val) :
    truncateHash (labels (treePosition lay tree level.val (by have := level.isLt; exact Nat.le_of_lt this)
      ⟨boundaryIndex parameter level.val, boundaryIndex_lt parameter level.val⟩)) =
        evalWithAnswerFn f (Seeded.surrogate parameter seed level.val : OracleComp HashSpec Digest) := by
  apply hboundary
  obtain ⟨level, hlevel⟩ := level
  cases level with
  | zero =>
      have hb : subtreeHeight = 0 := by change subtreeHeight ≤ 0 at hlower; omega
      simp [treePosition, boundary, hb, surrogates]
  | succ level =>
      simp [treePosition, boundary, hlevel, hlower, surrogates]

omit hconsistent [Params] in
theorem tree_input_ordered (lay : Layer) (tree : TreeIndex) (level : Nat)
    (hlevel : level + 1 ≤ maxLayerHeight) (current : LeafIndex) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (treePosition lay tree (level + 1) hlevel
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩) labels =
    tweakableHashInput parameter (.node lay tree (level + 1) (current.val / 2))
      (orderedPayload (current.val.testBit 0)
        (truncateHash (labels (treePosition lay tree level (by omega) current)))
        (truncateHash (labels (treePosition lay tree level (by omega)
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt one_lt_leaf_capacity⟩)))) := by
  have hglobal : 2 * (current.val / 2) + 1 < 2 ^ maxLayerHeight := by
    have hc := current.isLt
    norm_num [maxLayerHeight] at hc ⊢
    omega
  rw [tree_input f parameter seed labels lay tree level hlevel _ hglobal]
  have hparts := Nat.div_add_mod current.val 2
  cases hb : current.val.testBit 0 with
  | false =>
      have hm := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2), by omega⟩ : LeafIndex) = current := Fin.ext (by dsimp only; omega)
      have hsibling : (⟨2 * (current.val / 2) + 1, hglobal⟩ : LeafIndex) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt one_lt_leaf_capacity⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) + 1 = current.val ^^^ 1
        rw [Nat.xor_one_of_even (Nat.even_iff.mpr hm)]
        omega
      simp only [orderedPayload, Bool.false_eq_true, ↓reduceIte, hcurrent, hsibling]
  | true =>
      have hm := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2) + 1, hglobal⟩ : LeafIndex) = current := Fin.ext (by dsimp only; omega)
      have hsibling : (⟨2 * (current.val / 2), by omega⟩ : LeafIndex) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt one_lt_leaf_capacity⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) = current.val ^^^ 1
        rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hm)]
        omega
      simp only [orderedPayload, ↓reduceIte, hcurrent, hsibling]

include hconsistent in
theorem spine_value (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (steps : Nat)
    (hupper : subtreeHeight + steps ≤ maxLayerHeight) :
    truncateHash (labels (treePosition lay tree (subtreeHeight + steps) hupper
      ⟨spineIndex parameter (subtreeHeight + steps), spineIndex_lt parameter _⟩)) =
      evalWithAnswerFn f (Seeded.spineNode parameter lay tree seed steps : OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      have hb : subtreeHeight ≤ maxLayerHeight := by omega
      have hi : subtreePosition parameter < 2 ^ maxLayerHeight := by
        exact (subtreePosition_lt parameter).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
      simp only [Nat.add_zero, spineIndex, Nat.sub_self, pow_zero, Nat.div_one]
      rw [Seeded.spineNode]
      exact tree_value_below f parameter seed labels hconsistent lay tree subtreeHeight hb le_rfl
        ⟨subtreePosition parameter, hi⟩ (subtreePosition_lt parameter) (by simp)
  | succ steps ih =>
      have hprev : subtreeHeight + steps ≤ maxLayerHeight := by omega
      have hact := spinePosition_active parameter lay tree (subtreeHeight + (steps + 1))
        (by omega) hupper
      have hlevel : subtreeHeight + steps < totalHeight := by change _ < maxLayerHeight; omega
      have hbnd := boundary_tree_value f parameter seed labels hboundary lay tree
        ⟨subtreeHeight + steps, hlevel⟩ (by change subtreeHeight ≤ subtreeHeight + steps; omega)
      rw [hconsistent _ hact]
      have hparent := spineIndex_step parameter (subtreeHeight + steps) (by omega)
      have hpos : (⟨spineIndex parameter (subtreeHeight + (steps + 1)), spineIndex_lt parameter _⟩ : LeafIndex) =
          ⟨spineIndex parameter (subtreeHeight + steps) / 2,
            (Nat.div_le_self _ _).trans_lt (spineIndex_lt parameter _)⟩ := by
        apply Fin.ext
        simpa only [Nat.add_assoc] using hparent
      rw [hpos]
      have hinput := tree_input_ordered f parameter seed labels lay tree (subtreeHeight + steps) hupper
        ⟨spineIndex parameter (subtreeHeight + steps), spineIndex_lt parameter _⟩
      refine (congrArg (fun input : HashInput => truncateHash (f input)) hinput).trans ?_
      rw [Seeded.spineNode]
      simp only [evalWithAnswerFn_bind]
      have hi := ih hprev
      have hs : truncateHash (labels (treePosition lay tree (subtreeHeight + steps) hprev
          ⟨Nat.xor (spineIndex parameter (subtreeHeight + steps)) 1,
            Nat.xor_lt_two_pow (spineIndex_lt parameter _) one_lt_leaf_capacity⟩)) =
          evalWithAnswerFn f (Seeded.surrogate parameter seed (subtreeHeight + steps) :
            OracleComp HashSpec Digest) := hbnd
      have hidx : spineIndex parameter (subtreeHeight + steps) = subtreePosition parameter / 2 ^ steps := by
        simp only [spineIndex, Nat.add_sub_cancel_left]
      cases hb : (subtreePosition parameter / 2 ^ steps).testBit 0 <;>
        try simp only [Bool.false_eq_true, ↓reduceIte, eval_tweakableHash]
      all_goals
        apply congrArg (fun input : HashInput => truncateHash (f input))
        have hb' := hb
        rw [← hidx] at hb'
        simp only [orderedPayload, hb', Bool.false_eq_true, ↓reduceIte]
        rw [hi, hs, hidx]

include hconsistent in
theorem chain_input (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hland : Landed parameter leaf) (chain : ChainIndex) (step : ChainStep) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.chain lay tree leaf chain step) labels =
    tweakableHashInput parameter (.chain lay tree leaf chain step)
      (bytesLE 16 (Chain.honestChain f parameter lay tree leaf chain
        (otsSecrets f parameter seed lay tree leaf chain) step.val)) := by
  obtain ⟨step, hstep⟩ := step
  cases step with
  | zero =>
      have hz : Chain.honestChain f parameter lay tree leaf chain
          (otsSecrets f parameter seed lay tree leaf chain) 0 =
          otsSecrets f parameter seed lay tree leaf chain := by
        unfold Chain.honestChain
        rw [chainWalk]
        rfl
      rw [hz]
      simp [canonicalGraphInput, canonicalGraphSlots, Position.domain]
  | succ step =>
      simp only [canonicalGraphInput, canonicalGraphSlots, Position.children, Position.domain]
      simp only [show step + 1 ≠ 0 by omega, show 0 < step + 1 by omega,
        ↓reduceIte, ↓reduceDIte, Nat.add_sub_cancel, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [chain_value f parameter seed labels hconsistent lay tree leaf hland chain ⟨step, by omega⟩]

omit f parameter seed labels hconsistent [Params] in
theorem quotient_range (height level index : Nat) (hlevel : level ≤ height)
    (hindex : index < 2 ^ height) : index / 2 ^ level < 2 ^ (height - level) := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  rw [← Nat.pow_add, Nat.sub_add_cancel hlevel]
  exact hindex

omit f seed labels hconsistent in
theorem pathNode_kept (leaf : LeafIndex) (hland : Landed parameter leaf) (level : Nat)
    (hlevel : level ≤ subtreeHeight) :
    (leaf.val / 2 ^ level) / 2 ^ (subtreeHeight - level) = subtreePosition parameter := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_of_le hlevel]
  exact hland

omit f seed labels hconsistent in
theorem pathSibling_kept (leaf : LeafIndex) (hland : Landed parameter leaf) (level : Nat)
    (hlevel : level < subtreeHeight) :
    (Nat.xor (leaf.val / 2 ^ level) 1) / 2 ^ (subtreeHeight - level) = subtreePosition parameter := by
  change ((leaf.val / 2 ^ level) ^^^ 1) / 2 ^ (subtreeHeight - level) = _
  rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega)), Nat.xor_zero,
    pathNode_kept parameter leaf hland level (by omega)]

omit hconsistent in
theorem canonicalPath_below (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (level : Nat) (hlower : level < subtreeHeight) :
    canonicalTreePath f parameter lay tree seed leaf level =
      node f parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level) 1) := by
  have hlevel : level < layerHeight lay := hlower.trans_le Params.subtreeHeight_le
  rw [canonicalTreePath, dite_eq_left hlevel, eval_treePath, ite_eq_left hlower]

include hconsistent in
theorem tree_path_value (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hland : Landed parameter leaf)
    (level : Nat) (hlevel : level ≤ totalHeight) :
    truncateHash (labels (treePosition lay tree level hlevel
      ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩)) =
    merkleValue f parameter (fun height index => .node lay tree height index) leaf.val
      (canonicalTreePath f parameter lay tree seed leaf)
      (node f parameter lay tree seed 0 leaf.val) level := by
  by_cases hlower : level ≤ subtreeHeight
  · rw [tree_value_below f parameter seed labels hconsistent lay tree level hlevel hlower _
      (quotient_range maxLayerHeight level leaf.val hlevel leaf.isLt)
      (pathNode_kept parameter leaf hland level hlower)]
    symm
    rw [merkleValue, merkleFold_treeFold]
    exact eval_treeFold_path f parameter lay tree seed leaf _ level
      (fun k hk => canonicalPath_below f parameter seed lay tree leaf k (by omega))
  · have hb : subtreeHeight ≤ level := by omega
    have hsum : subtreeHeight + (level - subtreeHeight) = level := Nat.add_sub_of_le hb
    have hindex : leaf.val / 2 ^ level = spineIndex parameter level := by
      rw [← hsum, landed_div parameter leaf hland]
      simp only [spineIndex, Nat.add_sub_cancel_left]
    have hposition : (⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩ : LeafIndex) =
        ⟨spineIndex parameter level, spineIndex_lt parameter level⟩ := Fin.ext hindex
    rw [hposition]
    have hspine := spine_value f parameter seed labels hconsistent hboundary lay tree
      (level - subtreeHeight) (by change subtreeHeight + (level - subtreeHeight) ≤ totalHeight; omega)
    simp only [hsum] at hspine
    rw [hspine]
    symm
    rw [merkleValue, merkleFold_treeFold]
    simpa only [hsum] using eval_treeFold_spine f parameter lay tree seed leaf hland _
      (fun k hk => canonicalPath_below f parameter seed lay tree leaf k hk)
      (level - subtreeHeight) (fun k hk => canonicalTreePath_surrogate f parameter lay tree seed leaf
        (subtreeHeight + k) (by omega) (by omega))

include hconsistent in
theorem tree_path_sibling (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hland : Landed parameter leaf)
    (level : Nat) (hlevel : level < totalHeight) :
    truncateHash (labels (treePosition lay tree level (Nat.le_of_lt hlevel)
      ⟨Nat.xor (leaf.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩)) =
      canonicalTreePath f parameter lay tree seed leaf level := by
  by_cases hlower : level < subtreeHeight
  · rw [canonicalPath_below f parameter seed lay tree leaf level hlower]
    exact tree_value_below f parameter seed labels hconsistent lay tree level (Nat.le_of_lt hlevel)
      (by omega) _
      (Nat.xor_lt_two_pow (quotient_range maxLayerHeight level leaf.val (Nat.le_of_lt hlevel) leaf.isLt)
        (Nat.one_lt_two_pow (by change level < maxLayerHeight at hlevel; omega)))
      (pathSibling_kept parameter leaf hland level hlower)
  · have hb : subtreeHeight ≤ level := by omega
    have hindex : leaf.val / 2 ^ level = spineIndex parameter level := by
      have hsum : subtreeHeight + (level - subtreeHeight) = level := Nat.add_sub_of_le hb
      rw [← hsum, landed_div parameter leaf hland]
      simp only [spineIndex, Nat.add_sub_cancel_left]
    have hposition : (⟨Nat.xor (leaf.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩ : LeafIndex) =
        ⟨boundaryIndex parameter level, boundaryIndex_lt parameter level⟩ := by
      apply Fin.ext
      exact congrArg (fun index => Nat.xor index 1) hindex
    rw [hposition, canonicalTreePath_surrogate f parameter lay tree seed leaf level hb hlevel]
    exact boundary_tree_value f parameter seed labels hboundary lay tree ⟨level, hlevel⟩ hb

include hconsistent in
/-- The exempt input at each retained path node is exactly the canonical verifier-fold input. -/
theorem tree_path_input (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hland : Landed parameter leaf)
    (level : Nat) (hlevel : level < totalHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (treePosition lay tree (level + 1) hlevel
        ⟨leaf.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt leaf.isLt⟩) labels =
    merkleInput f parameter (fun height index => .node lay tree height index) leaf.val
      (canonicalTreePath f parameter lay tree seed leaf)
      (node f parameter lay tree seed 0 leaf.val) level := by
  have hparent : (⟨leaf.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt leaf.isLt⟩ : LeafIndex) =
      ⟨(leaf.val / 2 ^ level) / 2,
        (Nat.div_le_self _ _).trans_lt ((Nat.div_le_self _ _).trans_lt leaf.isLt)⟩ := by
    apply Fin.ext
    change leaf.val / 2 ^ (level + 1) = (leaf.val / 2 ^ level) / 2
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hparent, tree_input_ordered f parameter seed labels lay tree level hlevel
    ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩,
    tree_path_value f parameter seed labels hconsistent hboundary lay tree leaf hland level (Nat.le_of_lt hlevel),
    tree_path_sibling f parameter seed labels hconsistent hboundary lay tree leaf hland level hlevel]
  simp only [merkleInput]
  have hbit : (leaf.val / 2 ^ level).testBit 0 = leaf.val.testBit level := by
    simpa only [Nat.zero_add] using (Nat.testBit_add leaf.val 0 level).symm
  rw [hbit, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

omit f seed labels hconsistent in
theorem tree_path_active (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hland : Landed parameter leaf) (level : Nat) (hlevel : level ≤ totalHeight) :
    active parameter (treePosition lay tree level hlevel
      ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩) := by
  by_cases hlower : level ≤ subtreeHeight
  · exact treePosition_active_below parameter lay tree level hlevel hlower _
      (pathNode_kept parameter leaf hland level hlower)
  · have hb : subtreeHeight ≤ level := by omega
    have hsum : subtreeHeight + (level - subtreeHeight) = level := Nat.add_sub_of_le hb
    have hindex : leaf.val / 2 ^ level = spineIndex parameter level := by
      rw [← hsum, landed_div parameter leaf hland]
      simp only [spineIndex, Nat.add_sub_cancel_left]
    have hposition : (⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩ : LeafIndex) =
        ⟨spineIndex parameter level, spineIndex_lt parameter level⟩ := Fin.ext hindex
    rw [hposition]
    exact spinePosition_active parameter lay tree level hb hlevel

include hconsistent in
theorem tree_root_value (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) :
    truncateHash (labels (treePosition lay tree totalHeight le_rfl ⟨0, by decide⟩)) =
      evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) := by
  have hb := Params.subtreeHeight_le (self := inferInstance)
  have hsum : subtreeHeight + (totalHeight - subtreeHeight) = totalHeight := Nat.add_sub_of_le hb
  have hindex : spineIndex parameter totalHeight = 0 :=
    Nat.div_eq_of_lt (subtreePosition_lt parameter)
  have hs := spine_value f parameter seed labels hconsistent hboundary lay tree
    (totalHeight - subtreeHeight) (by change _ ≤ totalHeight; omega)
  simpa only [hsum, hindex, Seeded.treeRoot] using hs

/-! ### The forest

Every forest position is prepared. Its label is the honest value: chain steps the chain values,
WOTS-key leaves the child leaves, subtree and tree nodes the honest nodes, the tree leaves the
hashes of the four level-2 nodes of their subtrees and the roots position the forest key, the hash of
the sixteen level-3 nodes of the trees. -/

section Forest

variable (index : Index) (c : Coord)

omit hconsistent [Params] in
theorem fchain_input (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep)
    (hprev : ∀ (hpos : 0 < t.val), truncateHash (labels (.fchain index c s j a i ⟨t.val - 1, by omega⟩)) =
      Forest.honestChain f parameter index c s j a i (Completeness.forestSecret f parameter index c s j a i seed)
        t.val) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.fchain index c s j a i t) labels =
    tweakableHashInput parameter (.fchain index c s j a i t)
      (bytesLE 16 (Forest.honestChain f parameter index c s j a i
        (Completeness.forestSecret f parameter index c s j a i seed) t.val)) := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | zero =>
      have hz : Forest.honestChain f parameter index c s j a i
          (Completeness.forestSecret f parameter index c s j a i seed) 0 =
          Completeness.forestSecret f parameter index c s j a i seed := by
        unfold Forest.honestChain
        rw [forestWalk]
        rfl
      rw [hz]
      simp only [canonicalGraphInput, canonicalGraphSlots, Position.domain, ftsSecrets,
        ↓reduceIte, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  | succ t =>
      have h := hprev (by simp)
      simp only [canonicalGraphInput, canonicalGraphSlots, Position.children, Position.domain]
      simp only [show t + 1 ≠ 0 by omega, show 0 < t + 1 by omega,
        ↓reduceIte, ↓reduceDIte, Nat.add_sub_cancel, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      simp only [Nat.add_sub_cancel] at h
      rw [h]

include hconsistent in
theorem fchain_value (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (t : FStep) :
    truncateHash (labels (.fchain index c s j a i t)) =
      Forest.honestChain f parameter index c s j a i
        (Completeness.forestSecret f parameter index c s j a i seed) (t.val + 1) := by
  obtain ⟨t, ht⟩ := t
  induction t with
  | zero =>
      rw [hconsistent (.fchain index c s j a i ⟨0, ht⟩) trivial,
        fchain_input f parameter seed labels index c s j a i ⟨0, ht⟩ (fun h => absurd h (by simp)),
        Forest.honestChain_succ _ _ _ _ _ _ _ _ _ _ ht]
  | succ t ih =>
      rw [hconsistent (.fchain index c s j a i ⟨t + 1, ht⟩) trivial,
        fchain_input f parameter seed labels index c s j a i ⟨t + 1, ht⟩ (fun _ => ih (by omega)),
        Forest.honestChain_succ _ _ _ _ _ _ _ _ _ _ ht]

omit [Params] in
theorem honestChain_eq_chainValueOf (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (pos : Nat) :
    Forest.honestChain f parameter index c s j a i (Completeness.forestSecret f parameter index c s j a i seed) pos =
      Completeness.chainValueOf f parameter index c s j a i seed pos := rfl

include hconsistent in
theorem childLeaf_input (s : SuperIdx) (j : SubIdx) (a : ChildIdx) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.childLeaf index c s j a) labels = tweakableHashInput parameter (.childLeaf index c s j a)
        (childPayload (Completeness.childEnds f parameter index c s j seed a)) := by
  unfold canonicalGraphInput canonicalGraphSlots
  simp only [Position.children, Position.domain, List.map_ofFn]
  congr 1
  apply congrArg (fun values : List Digest => values.flatMap (bytesLE 16))
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply]
  rw [fchain_value f parameter seed labels hconsistent index c s j a i]
  rfl

include hconsistent in
theorem childLeaf_value (s : SuperIdx) (j : SubIdx) (a : ChildIdx) :
    truncateHash (labels (.childLeaf index c s j a)) = Completeness.childLeafValue f parameter index c s j seed a := by
  rw [hconsistent (.childLeaf index c s j a) trivial, childLeaf_input f parameter seed labels hconsistent]
  rfl

/-- Graph location for a subtree node, including the level-zero WOTS-key leaf. -/
def subPosition (s : SuperIdx) (j : SubIdx) :
    (level : Nat) → level ≤ subHeight → ChildIdx → Position
  | 0, _, a => .childLeaf index c s j a
  | level + 1, hlevel, nd => .subNode index c s j ⟨level, by omega⟩ nd

/-- Graph location for a tree node, including the level-zero tree leaf. -/
def topPosition :
    (level : Nat) → level ≤ topHeight → SuperIdx → Position
  | 0, _, s => .superChild index c s
  | level + 1, hlevel, nd => .topNode index c ⟨level, by omega⟩ nd

omit hconsistent [Params] in
theorem sub_input (s : SuperIdx) (j : SubIdx) (level : Nat) (hlevel : level + 1 ≤ subHeight) (nd : ChildIdx)
    (hindex : 2 * nd.val + 1 < 2 ^ subHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (subPosition index c s j (level + 1) hlevel nd) labels =
    tweakableHashInput parameter (.subNode index c s j ⟨level, by omega⟩ nd)
      (nodePayload
        (truncateHash (labels (subPosition index c s j level (by omega) ⟨2 * nd.val, by omega⟩)))
        (truncateHash (labels (subPosition index c s j level (by omega) ⟨2 * nd.val + 1, hindex⟩)))) := by
  cases level <;>
    simp [subPosition, canonicalGraphInput, canonicalGraphSlots, Position.children,
      Position.domain, hindex, nodePayload]

omit hconsistent [Params] in
theorem top_input (level : Nat) (hlevel : level + 1 ≤ topHeight) (nd : SuperIdx)
    (hindex : 2 * nd.val + 1 < 2 ^ topHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (topPosition index c (level + 1) hlevel nd) labels =
    tweakableHashInput parameter (.topNode index c ⟨level, by omega⟩ nd)
      (nodePayload
        (truncateHash (labels (topPosition index c level (by omega) ⟨2 * nd.val, by omega⟩)))
        (truncateHash (labels (topPosition index c level (by omega) ⟨2 * nd.val + 1, hindex⟩)))) := by
  cases level <;>
    simp [topPosition, canonicalGraphInput, canonicalGraphSlots, Position.children,
      Position.domain, hindex, nodePayload]

include hconsistent in
theorem sub_value (s : SuperIdx) (j : SubIdx) (level : Nat) (hlevel : level ≤ subHeight) (nd : ChildIdx)
    (hindex : nd.val < 2 ^ (subHeight - level)) :
    truncateHash (labels (subPosition index c s j level hlevel nd)) =
      Completeness.subNodeValue f parameter index c s j seed level nd.val := by
  induction level generalizing nd with
  | zero =>
      rw [show subPosition index c s j 0 hlevel nd = .childLeaf index c s j nd from rfl,
        childLeaf_value f parameter seed labels hconsistent, Completeness.subNodeValue_zero]
  | succ level ih =>
      have hchildren := child_index_bound hlevel hindex
      have hglobal : 2 * nd.val + 1 < 2 ^ subHeight :=
        hchildren.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
      rw [hconsistent (subPosition index c s j (level + 1) hlevel nd) (by trivial),
        sub_input f parameter seed labels index c s j level hlevel nd hglobal,
        Completeness.subNodeValue_succ f parameter index c s j seed level nd.val (by omega)]
      rw [ih (by omega) _ (by change 2 * nd.val < _; omega), ih (by omega) _ hchildren]
      congr 4
      exact Fin.ext (Nat.mod_eq_of_lt nd.isLt).symm

include hconsistent in
theorem super_input (s : SuperIdx) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.superChild index c s) labels =
    tweakableHashInput parameter (.superChild index c s)
      (superPayload (Completeness.subTopsValue f parameter index c seed s)) := by
  have h : ∀ (j : SubIdx) (nd : ChildIdx) (_ : nd.val < 2 ^ (subHeight - (subHeight - 1))),
      truncateHash (labels (.subNode index c s j ⟨subHeight - 2, by decide⟩ nd)) =
        Completeness.subNodeValue f parameter index c s j seed (subHeight - 1) nd.val :=
    fun j nd hnd => sub_value f parameter seed labels hconsistent index c s j (subHeight - 1) (by decide) nd hnd
  simp only [canonicalGraphInput, canonicalGraphSlots, Position.children, Position.domain,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, superPayload,
    nodePayload, Completeness.subTopsValue, List.append_assoc]
  rw [h 0 ⟨0, by decide⟩ (by decide), h 0 ⟨1, by decide⟩ (by decide), h 1 ⟨0, by decide⟩ (by decide),
    h 1 ⟨1, by decide⟩ (by decide)]

include hconsistent in
theorem super_value (s : SuperIdx) :
    truncateHash (labels (.superChild index c s)) = Completeness.superValue f parameter index c seed s := by
  rw [hconsistent (.superChild index c s) trivial, super_input f parameter seed labels hconsistent,
    Forest.superValue_eq]

include hconsistent in
theorem top_value (level : Nat) (hlevel : level ≤ topHeight) (nd : SuperIdx)
    (hindex : nd.val < 2 ^ (topHeight - level)) :
    truncateHash (labels (topPosition index c level hlevel nd)) =
      Completeness.topNodeValue f parameter index c seed level nd.val := by
  induction level generalizing nd with
  | zero =>
      rw [show topPosition index c 0 hlevel nd = .superChild index c nd from rfl,
        super_value f parameter seed labels hconsistent, Completeness.topNodeValue_zero]
  | succ level ih =>
      have hchildren := child_index_bound hlevel hindex
      have hglobal : 2 * nd.val + 1 < 2 ^ topHeight :=
        hchildren.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
      rw [hconsistent (topPosition index c (level + 1) hlevel nd) (by trivial),
        top_input f parameter seed labels index c level hlevel nd hglobal,
        Completeness.topNodeValue_succ f parameter index c seed level nd.val (by omega)]
      rw [ih (by omega) _ (by change 2 * nd.val < _; omega), ih (by omega) _ hchildren]
      congr 4
      exact Fin.ext (Nat.mod_eq_of_lt nd.isLt).symm

include hconsistent in
theorem roots_input :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.roots index) labels =
    tweakableHashInput parameter (.roots index) (rootsPayload (Forest.canonicalRoots f parameter index seed)) := by
  have h : ∀ (c' : Coord) (nd : SuperIdx) (_ : nd.val < 2 ^ (topHeight - (topHeight - 1))),
      truncateHash (labels (.topNode index c' ⟨topHeight - 2, by decide⟩ nd)) =
        Completeness.topNodeValue f parameter index c' seed (topHeight - 1) nd.val :=
    fun c' nd hnd => top_value f parameter seed labels hconsistent index c' (topHeight - 1) (by decide) nd hnd
  unfold canonicalGraphInput canonicalGraphSlots
  simp only [Position.children, Position.domain]
  congr 1
  rw [List.map_flatMap, List.flatMap_assoc, rootsPayload, List.ofFn_eq_map, List.flatMap_map]
  apply List.flatMap_congr
  intro c' _
  simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil, nodePayload,
    Forest.canonicalRoots, Completeness.topTopsValue]
  rw [h c' ⟨0, by decide⟩ (by decide), h c' ⟨1, by decide⟩ (by decide)]

include hconsistent in
theorem forest_key_value :
    truncateHash (labels (.roots index)) =
      evalWithAnswerFn f (Seeded.forestKey parameter index seed : OracleComp HashSpec Digest) := by
  rw [hconsistent (.roots index) trivial, roots_input f parameter seed labels hconsistent index,
    Forest.forestKey_eq]

/-! #### Paths -/

omit hconsistent [Params] in
theorem sub_input_ordered (s : SuperIdx) (j : SubIdx) (level : Nat) (hlevel : level + 1 ≤ subHeight)
    (current : ChildIdx) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (subPosition index c s j (level + 1) hlevel
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩) labels =
    tweakableHashInput parameter (.subNode index c s j ⟨level, by omega⟩
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩)
      (orderedPayload (current.val.testBit 0)
        (truncateHash (labels (subPosition index c s j level (by omega) current)))
        (truncateHash (labels (subPosition index c s j level (by omega)
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt (by decide)⟩)))) := by
  have hglobal : 2 * (current.val / 2) + 1 < 2 ^ subHeight := by
    have hc := current.isLt
    norm_num [subHeight] at hc ⊢
    omega
  rw [sub_input f parameter seed labels index c s j level hlevel _ hglobal]
  cases hb : current.val.testBit 0 with
  | false =>
      have hm := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2), by omega⟩ : ChildIdx) = current :=
        Fin.ext (by change 2 * (current.val / 2) = current.val; omega)
      have hsibling : (⟨2 * (current.val / 2) + 1, hglobal⟩ : ChildIdx) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt (by decide)⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) + 1 = current.val ^^^ 1
        rw [Nat.xor_one_of_even (Nat.even_iff.mpr hm)]
        omega
      simp only [orderedPayload, Bool.false_eq_true, ↓reduceIte, hcurrent, hsibling]
  | true =>
      have hm := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2) + 1, hglobal⟩ : ChildIdx) = current :=
        Fin.ext (by change 2 * (current.val / 2) + 1 = current.val; omega)
      have hsibling : (⟨2 * (current.val / 2), by omega⟩ : ChildIdx) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt (by decide)⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) = current.val ^^^ 1
        rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hm)]
        omega
      simp only [orderedPayload, ↓reduceIte, hcurrent, hsibling]

omit hconsistent [Params] in
theorem top_input_ordered (level : Nat) (hlevel : level + 1 ≤ topHeight) (current : SuperIdx) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (topPosition index c (level + 1) hlevel
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩) labels =
    tweakableHashInput parameter (.topNode index c ⟨level, by omega⟩
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩)
      (orderedPayload (current.val.testBit 0)
        (truncateHash (labels (topPosition index c level (by omega) current)))
        (truncateHash (labels (topPosition index c level (by omega)
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt (by decide)⟩)))) := by
  have hglobal : 2 * (current.val / 2) + 1 < 2 ^ topHeight := by
    have hc := current.isLt
    norm_num [topHeight] at hc ⊢
    omega
  rw [top_input f parameter seed labels index c level hlevel _ hglobal]
  cases hb : current.val.testBit 0 with
  | false =>
      have hm := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2), by omega⟩ : SuperIdx) = current :=
        Fin.ext (by change 2 * (current.val / 2) = current.val; omega)
      have hsibling : (⟨2 * (current.val / 2) + 1, hglobal⟩ : SuperIdx) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt (by decide)⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) + 1 = current.val ^^^ 1
        rw [Nat.xor_one_of_even (Nat.even_iff.mpr hm)]
        omega
      simp only [orderedPayload, Bool.false_eq_true, ↓reduceIte, hcurrent, hsibling]
  | true =>
      have hm := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2) + 1, hglobal⟩ : SuperIdx) = current :=
        Fin.ext (by change 2 * (current.val / 2) + 1 = current.val; omega)
      have hsibling : (⟨2 * (current.val / 2), by omega⟩ : SuperIdx) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt (by decide)⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) = current.val ^^^ 1
        rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hm)]
        omega
      simp only [orderedPayload, ↓reduceIte, hcurrent, hsibling]

include hconsistent in
theorem sub_path_value (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (level : Nat) (hlevel : level ≤ subHeight) :
    truncateHash (labels (subPosition index c s j level hlevel
      ⟨a.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt a.isLt⟩)) =
    merkleValue f parameter (Forest.subDomain index c s j) a.val
      (Forest.subPathExt (Forest.canonicalSubPath f parameter index seed c s j a))
      (Completeness.childLeafValue f parameter index c s j seed a) level := by
  rw [sub_value f parameter seed labels hconsistent index c s j level hlevel _
    (quotient_range subHeight level a.val hlevel a.isLt)]
  symm
  rw [merkleValue, Forest.merkleFold_subFold _ _ _ _ _ _ _ _ hlevel, ← Completeness.subNodeValue_zero]
  exact Completeness.eval_subFold_path f parameter index c s j seed a _ level hlevel (fun _ _ _ => rfl)

include hconsistent in
theorem top_path_value (s : SuperIdx) (level : Nat) (hlevel : level ≤ topHeight) :
    truncateHash (labels (topPosition index c level hlevel
      ⟨s.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt s.isLt⟩)) =
    merkleValue f parameter (Forest.topDomain index c) s.val
      (Forest.topPathExt (Forest.canonicalTopPath f parameter index seed c s))
      (Completeness.superValue f parameter index c seed s) level := by
  rw [top_value f parameter seed labels hconsistent index c level hlevel _
    (quotient_range topHeight level s.val hlevel s.isLt)]
  symm
  rw [merkleValue, Forest.merkleFold_topFold _ _ _ _ _ _ hlevel, ← Completeness.topNodeValue_zero]
  exact Completeness.eval_topFold_path f parameter index c seed s _ level hlevel (fun _ _ _ => rfl)

include hconsistent in
theorem sub_path_sibling (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (level : Nat) (hlevel : level < subHeight) :
    truncateHash (labels (subPosition index c s j level (Nat.le_of_lt hlevel)
      ⟨Nat.xor (a.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt a.isLt) (by decide)⟩)) =
      Forest.subPathExt (Forest.canonicalSubPath f parameter index seed c s j a) level := by
  rw [Forest.subPathExt, dite_eq_left hlevel, Forest.canonicalSubPath]
  exact sub_value f parameter seed labels hconsistent index c s j level (Nat.le_of_lt hlevel) _
    (Nat.xor_lt_two_pow (quotient_range subHeight level a.val (Nat.le_of_lt hlevel) a.isLt)
      (Nat.one_lt_two_pow (by omega)))

include hconsistent in
theorem top_path_sibling (s : SuperIdx) (level : Nat) (hlevel : level < topHeight) :
    truncateHash (labels (topPosition index c level (Nat.le_of_lt hlevel)
      ⟨Nat.xor (s.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt s.isLt) (by decide)⟩)) =
      Forest.topPathExt (Forest.canonicalTopPath f parameter index seed c s) level := by
  rw [Forest.topPathExt, dite_eq_left hlevel, Forest.canonicalTopPath]
  exact top_value f parameter seed labels hconsistent index c level (Nat.le_of_lt hlevel) _
    (Nat.xor_lt_two_pow (quotient_range topHeight level s.val (Nat.le_of_lt hlevel) s.isLt)
      (Nat.one_lt_two_pow (by omega)))

include hconsistent in
theorem sub_path_input (s : SuperIdx) (j : SubIdx) (a : ChildIdx) (level : Nat) (hlevel : level < subHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (subPosition index c s j (level + 1) hlevel
        ⟨a.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt a.isLt⟩) labels =
    merkleInput f parameter (Forest.subDomain index c s j) a.val
      (Forest.subPathExt (Forest.canonicalSubPath f parameter index seed c s j a))
      (Completeness.childLeafValue f parameter index c s j seed a) level := by
  have hparent : (⟨a.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt a.isLt⟩ : ChildIdx) =
      ⟨(a.val / 2 ^ level) / 2,
        (Nat.div_le_self _ _).trans_lt ((Nat.div_le_self _ _).trans_lt a.isLt)⟩ := by
    apply Fin.ext
    change a.val / 2 ^ (level + 1) = (a.val / 2 ^ level) / 2
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hparent, sub_input_ordered f parameter seed labels index c s j level hlevel
    ⟨a.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt a.isLt⟩,
    sub_path_value f parameter seed labels hconsistent index c s j a level (Nat.le_of_lt hlevel),
    sub_path_sibling f parameter seed labels hconsistent index c s j a level hlevel]
  simp only [merkleInput]
  have hbit : (a.val / 2 ^ level).testBit 0 = a.val.testBit level := by
    simpa only [Nat.zero_add] using (Nat.testBit_add a.val 0 level).symm
  rw [hbit]
  congr 1
  rw [Forest.subDomain, dite_eq_left ⟨by omega, by omega⟩]
  congr 1
  apply Fin.ext
  change a.val / 2 ^ level / 2 = a.val / 2 ^ (level + 1) % 2 ^ subHeight
  rw [Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt a.isLt), Nat.pow_succ, Nat.div_div_eq_div_mul]

include hconsistent in
theorem top_path_input (s : SuperIdx) (level : Nat) (hlevel : level < topHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (topPosition index c (level + 1) hlevel
        ⟨s.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt s.isLt⟩) labels =
    merkleInput f parameter (Forest.topDomain index c) s.val
      (Forest.topPathExt (Forest.canonicalTopPath f parameter index seed c s))
      (Completeness.superValue f parameter index c seed s) level := by
  have hparent : (⟨s.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt s.isLt⟩ : SuperIdx) =
      ⟨(s.val / 2 ^ level) / 2,
        (Nat.div_le_self _ _).trans_lt ((Nat.div_le_self _ _).trans_lt s.isLt)⟩ := by
    apply Fin.ext
    change s.val / 2 ^ (level + 1) = (s.val / 2 ^ level) / 2
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hparent, top_input_ordered f parameter seed labels index c level hlevel
    ⟨s.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt s.isLt⟩,
    top_path_value f parameter seed labels hconsistent index c s level (Nat.le_of_lt hlevel),
    top_path_sibling f parameter seed labels hconsistent index c s level hlevel]
  simp only [merkleInput]
  have hbit : (s.val / 2 ^ level).testBit 0 = s.val.testBit level := by
    simpa only [Nat.zero_add] using (Nat.testBit_add s.val 0 level).symm
  rw [hbit]
  congr 1
  rw [Forest.topDomain, dite_eq_left ⟨by omega, by omega⟩]
  congr 1
  apply Fin.ext
  change s.val / 2 ^ level / 2 = s.val / 2 ^ (level + 1) % 2 ^ topHeight
  rw [Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt s.isLt), Nat.pow_succ, Nat.div_div_eq_div_mul]

end Forest

omit [Params] in
/-- Material tables with their full hash outputs truncated exactly as key derivation does. -/
def materialOts (material : SeedModel.Material) : Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leaf chain => truncateHash (material.2 (.inl (lay, tree, leaf, chain)))

omit [Params] in
def materialFts (material : SeedModel.Material) : ForestSecrets :=
  fun index c s j a i => truncateHash (material.2 (.inr (.inl (index, c, s, j, a, i))))

omit [Params] in
def materialSurrogates (material : SeedModel.Material) : Fin totalHeight → Digest :=
  fun level => truncateHash (material.2 (.inr (.inr level)))

omit parameter labels hconsistent [Params] in
theorem materialOts_eq (material : SeedModel.Material) (hagrees : SeedModel.PreparedAgreement f seed material) :
    materialOts material = otsSecrets f (SeedModel.parameter material) seed := by
  funext lay tree leaf chain
  exact (SeedModel.eval_ots_prepared f seed material hagrees lay tree leaf chain).symm

omit parameter labels hconsistent [Params] in
theorem materialFts_eq (material : SeedModel.Material) (hagrees : SeedModel.PreparedAgreement f seed material) :
    materialFts material = ftsSecrets f (SeedModel.parameter material) seed := by
  funext index c s j a i
  exact (SeedModel.eval_forest_prepared f seed material hagrees index c s j a i).symm

omit parameter labels hconsistent [Params] in
theorem materialSurrogates_eq (material : SeedModel.Material)
    (hagrees : SeedModel.PreparedAgreement f seed material) :
    materialSurrogates material = surrogates f (SeedModel.parameter material) seed := by
  funext level
  unfold surrogates
  rw [Seeded.surrogate, dite_eq_left level.isLt]
  exact (SeedModel.eval_surrogate_prepared f seed material hagrees level).symm

end Sphincs.Security.GraphCorrectness

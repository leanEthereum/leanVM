import FORS.GraphView.Pruned
import FORS.Classification.Fors

/-! Canonical graph labels agree with actual seeded computations. The only graph hypotheses are
its query-response consistency and untouched surrogate boundary, which `Reduction/PreparedSample` supplies
for every sample. No correctness of the labels is assumed. -/

open OracleComp OracleSpec
namespace FORS.Security.GraphCorrectness

variable [Params]
open Concrete Completeness Graph PrunedGraph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable
set_option allowUnsafeReducibility true
attribute [local reducible] digestBits HashSpec Id
set_option allowUnsafeReducibility false
attribute [local irreducible] Seeded.treeNode Seeded.forsNode Seeded.spineNode chainWalk
  sequenceFin

theorem one_lt_leaf_capacity : 1 < 2 ^ maxLayerHeight := Nat.one_lt_two_pow maxLayerHeight_pos.ne'

def otsSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leaf chain => Completeness.otsSecret f parameter lay tree leaf seed chain

def ftsSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    ForsSecrets :=
  fun index κ leaf => Completeness.forsSecretValue f parameter index κ seed leaf

def surrogates (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    Fin maxLayerHeight → Digest := fun level =>
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
  (labels : CanonicalGraphLabels) (hconsistent : @Consistent _ f parameter seed labels)

/-! ### The layers' trees

At every layer the labels of a retained tree are its honest values: the kept part (the whole tree
below the top layer) and, in the top layer's root tree, the spine above the kept subtree, whose
siblings are the surrogates. -/

omit f seed labels hconsistent in
theorem keptPosition_lt (lay : Layer) :
    keptPosition parameter lay < 2 ^ (layerHeight lay - keptHeight lay) := by
  by_cases h : lay.val = 0
  · have hl : lay = topLayer := Fin.ext h
    subst hl
    have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
    rw [hpos, Completeness.keptHeight_top, Completeness.layerHeight_top]
    have h1 := Completeness.maxLayerHeight_add
    have h2 := Completeness.heightBelow_le_subtree
    have h3 := subtreeHeight_le_total
    rw [show maxLayerHeight - (subtreeHeight - heightBelow topLayer) = totalHeight - subtreeHeight by omega]
    exact subtreePosition_lt parameter
  · rw [keptPosition_of_ne_top parameter lay h, keptHeight_of_ne_top lay h, Nat.sub_self, pow_zero]
    exact Nat.one_pos

include hconsistent in
theorem chain_value (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) (chain : ChainIndex) (step : ChainStep) :
    truncateHash (labels (.chain lay tree leaf chain step)) =
      Chain.honestChain f parameter lay tree leaf chain
        (otsSecrets f parameter seed lay tree leaf chain) (step.val + 1) := by
  obtain ⟨step, hstep⟩ := step
  induction step with
  | zero =>
      rw [hconsistent (.chain lay tree leaf chain ⟨0, hstep⟩) hactive,
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
      rw [hconsistent (.chain lay tree leaf chain ⟨step + 1, hstep⟩) hactive,
        Chain.honestChain_succ _ _ _ _ _ _ _ _ hstep]
      apply congrArg (fun input : HashInput => truncateHash (f input))
      simp only [canonicalGraphInput, canonicalGraphSlots, Position.children, Position.domain]
      simp only [show step + 1 ≠ 0 by omega, show 0 < step + 1 by omega,
        ↓reduceIte, ↓reduceDIte, Nat.add_sub_cancel, List.map_cons, List.map_nil,
        List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [ih hprev]

include hconsistent in
theorem leaf_input (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) :
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
  rw [chain_value f parameter seed labels hconsistent lay tree leaf hactive chain]
  rfl

include hconsistent in
theorem leaf_value (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) :
    truncateHash (labels (.leaf lay tree leaf)) = node f parameter lay tree seed 0 leaf.val := by
  rw [hconsistent (.leaf lay tree leaf) hactive,
    leaf_input f parameter seed labels hconsistent lay tree leaf hactive, node_zero]
  simp only [leafHash, eval_tweakableHash]

/-- Graph location for a tree node, including the level-zero leaf. -/
def treePosition (lay : Layer) (tree : TreeIndex) :
    (level : Nat) → level ≤ maxLayerHeight → LeafIndex → Position
  | 0, _, index => .leaf lay tree index
  | level + 1, hlevel, index => .node lay tree ⟨level, by omega⟩ index

omit hconsistent in
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

omit f parameter seed labels hconsistent in
theorem child_index_bound {height level index : Nat} (hlevel : level + 1 ≤ height)
    (hindex : index < 2 ^ (height - (level + 1))) :
    2 * index + 1 < 2 ^ (height - level) := by
  have hsub : height - level = height - (level + 1) + 1 := by omega
  rw [hsub, Nat.pow_succ]
  omega

omit f parameter seed labels hconsistent in
theorem double_div_pow (index level bit : Nat) (hbit : bit < 2) :
    (2 * index + bit) / 2 ^ (level + 1) = index / 2 ^ level := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ level), ← Nat.div_div_eq_div_mul]
  have hdiv : (2 * index + bit) / 2 = index := by omega
  rw [hdiv]

omit f seed labels hconsistent in
/-- A node of the kept part of a retained tree is retained. -/
theorem treePosition_active_below (lay : Layer) (tree : TreeIndex) (htree : TreeActive parameter lay tree)
    (level : Nat) (hlevel : level ≤ maxLayerHeight) (hlower : level ≤ keptHeight lay) (index : LeafIndex)
    (hindex : index.val < 2 ^ (layerHeight lay - level))
    (hkept : index.val / 2 ^ (keptHeight lay - level) = keptPosition parameter lay) :
    active parameter (treePosition lay tree level hlevel index) := by
  have hKL := Completeness.keptHeight_le lay
  cases level with
  | zero =>
      refine (keyActive_iff parameter lay tree index).2 ⟨htree, ?_, ?_⟩
      · simpa only [Kept, Nat.sub_zero] using hkept
      · simpa only [Nat.sub_zero] using hindex
  | succ level =>
      change NodeActive parameter lay tree (level + 1) index.val
      unfold NodeActive
      by_cases htop : lay = topLayer
      · subst htop
        rw [if_pos rfl]
        refine ⟨treeActive_top parameter tree htree, ?_⟩
        have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
        unfold KeptNode
        rw [if_pos hlower, ← hpos]
        exact hkept
      · rw [if_neg htop]
        have hpow : 2 ^ (level + 1) * 2 ^ (layerHeight lay - (level + 1)) = 2 ^ layerHeight lay := by
          rw [← pow_add]; congr 1; omega
        have hleaf : index.val * 2 ^ (level + 1) < 2 ^ maxLayerHeight := by
          have : index.val * 2 ^ (level + 1) < 2 ^ layerHeight lay := by
            rw [← hpow, Nat.mul_comm (2 ^ (level + 1))]
            exact Nat.mul_lt_mul_of_pos_right hindex (Nat.two_pow_pos _)
          exact this.trans_le (Nat.pow_le_pow_right (by decide) (layerHeight_le lay))
        refine ⟨by omega, ⟨index.val * 2 ^ (level + 1), hleaf⟩, ?_, ?_⟩
        · refine (keyActive_iff parameter lay tree _).2 ⟨htree, ?_, ?_⟩
          · have hlay : lay.val ≠ 0 := fun e => htop (Fin.ext e)
            apply kept_of_ne_top parameter lay hlay
            change index.val * 2 ^ (level + 1) < 2 ^ layerHeight lay
            rw [← hpow, Nat.mul_comm (2 ^ (level + 1))]
            exact Nat.mul_lt_mul_of_pos_right hindex (Nat.two_pow_pos _)
          · change index.val * 2 ^ (level + 1) < 2 ^ layerHeight lay
            rw [← hpow, Nat.mul_comm (2 ^ (level + 1))]
            exact Nat.mul_lt_mul_of_pos_right hindex (Nat.two_pow_pos _)
        · change index.val * 2 ^ (level + 1) / 2 ^ (level + 1) = index.val
          exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

include hconsistent in
/-- The labels of the kept part of a retained tree are the honest nodes. -/
theorem tree_value_below (lay : Layer) (tree : TreeIndex) (htree : TreeActive parameter lay tree)
    (level : Nat) (hlevel : level ≤ maxLayerHeight) (hlower : level ≤ keptHeight lay) (index : LeafIndex)
    (hindex : index.val < 2 ^ (layerHeight lay - level))
    (hkept : index.val / 2 ^ (keptHeight lay - level) = keptPosition parameter lay) :
    truncateHash (labels (treePosition lay tree level hlevel index)) =
      node f parameter lay tree seed level index.val := by
  have hKL := Completeness.keptHeight_le lay
  induction level generalizing index with
  | zero =>
      exact leaf_value f parameter seed labels hconsistent lay tree index
        ((keyActive_iff parameter lay tree index).2 ⟨htree,
          by simpa only [Kept, Nat.sub_zero] using hkept, by simpa only [Nat.sub_zero] using hindex⟩)
  | succ level ih =>
      have hchildren := child_index_bound (Nat.le_trans hlower hKL) hindex
      have hglobal : 2 * index.val + 1 < 2 ^ maxLayerHeight :=
        hchildren.trans_le ((Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)).trans
          (Nat.pow_le_pow_right (by decide) (layerHeight_le lay)))
      have hsub : keptHeight lay - level = keptHeight lay - (level + 1) + 1 := by omega
      have hleft : (2 * index.val) / 2 ^ (keptHeight lay - level) = keptPosition parameter lay := by
        rw [hsub, show 2 * index.val = 2 * index.val + 0 by omega, double_div_pow _ _ 0 (by decide)]
        exact hkept
      have hright : (2 * index.val + 1) / 2 ^ (keptHeight lay - level) = keptPosition parameter lay := by
        rw [hsub, double_div_pow _ _ 1 (by decide)]
        exact hkept
      rw [hconsistent _ (treePosition_active_below parameter lay tree htree (level + 1) hlevel hlower
          index hindex hkept),
        tree_input f parameter seed labels lay tree level hlevel index hglobal, node_succ,
        ih (by omega) (by omega) _ (by change 2 * index.val < _; omega) hleft,
        ih (by omega) (by omega) _ hchildren hright]

/-! The spine of the top layer's root tree. -/

omit f seed labels hconsistent in
theorem spineIndex_range (level : Nat) (hlower : keptHeight topLayer ≤ level)
    (hupper : level ≤ maxLayerHeight) : spineIndex parameter level < 2 ^ (maxLayerHeight - level) := by
  unfold spineIndex
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  rw [← Nat.pow_add]
  have hk := keptPosition_lt parameter topLayer
  have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
  rw [hpos, Completeness.layerHeight_top] at hk
  rw [show maxLayerHeight - level + (level - keptHeight topLayer) =
    maxLayerHeight - keptHeight topLayer by omega]
  exact hk

omit f seed labels hconsistent in
theorem spineIndex_step (level : Nat) (hlower : keptHeight topLayer ≤ level) :
    spineIndex parameter (level + 1) = spineIndex parameter level / 2 := by
  unfold spineIndex
  rw [show level + 1 - keptHeight topLayer = (level - keptHeight topLayer) + 1 by omega,
    Nat.pow_succ, Nat.div_div_eq_div_mul]

omit f seed labels hconsistent in
theorem spinePosition_active (level : Nat) (hlower : keptHeight topLayer ≤ level)
    (hupper : level ≤ maxLayerHeight) :
    active parameter (treePosition topLayer rootTree level hupper
      ⟨spineIndex parameter level, (spineIndex_range parameter level hlower hupper).trans_le
        (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))⟩) := by
  have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
  cases level with
  | zero =>
      have hb : keptHeight topLayer = 0 := by omega
      refine (keyActive_iff parameter topLayer rootTree _).2 ⟨?_, ?_, ?_⟩
      · obtain ⟨index, hland⟩ : ∃ index : Index, Landed parameter index := by
          refine ⟨⟨subtreePosition parameter * 2 ^ subtreeHeight, ?_⟩, ?_⟩
          · rw [← subtree_size_mul]
            exact Nat.mul_lt_mul_of_pos_right (subtreePosition_lt parameter) (Nat.two_pow_pos _)
          · unfold Landed
            exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
        exact ⟨index, hland, Completeness.treeIndexAt_top index⟩
      · simp [Kept, spineIndex, hb, hpos]
      · rw [Completeness.layerHeight_top]
        exact (spineIndex_range parameter 0 hlower hupper).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  | succ level =>
      change NodeActive parameter topLayer rootTree (level + 1) (spineIndex parameter (level + 1))
      unfold NodeActive
      rw [if_pos rfl]
      refine ⟨rfl, ?_⟩
      unfold KeptNode
      split
      next h =>
        have heq : level + 1 = keptHeight topLayer := by omega
        simp [spineIndex, heq]
      next => trivial

omit hconsistent in
theorem boundary_tree_value (hboundary : BoundaryCorrect f parameter seed labels)
    (level : Fin maxLayerHeight) (hlower : keptHeight topLayer ≤ level.val) :
    truncateHash (labels (treePosition topLayer rootTree level.val (by have := level.isLt; exact Nat.le_of_lt this)
      ⟨boundaryIndex parameter level.val, boundaryIndex_lt parameter level.val⟩)) =
        evalWithAnswerFn f (Seeded.surrogate parameter seed level.val : OracleComp HashSpec Digest) := by
  apply hboundary
  obtain ⟨level, hlevel⟩ := level
  cases level with
  | zero =>
      have hb : keptHeight topLayer = 0 := by change keptHeight topLayer ≤ 0 at hlower; omega
      simp [treePosition, boundary, hb, surrogates]
  | succ level =>
      simp [treePosition, boundary, hlevel, hlower, surrogates]

omit hconsistent in
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
    have hpos : 0 < maxLayerHeight := maxLayerHeight_pos
    have h2 : 2 ^ maxLayerHeight = 2 * 2 ^ (maxLayerHeight - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
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
theorem spine_value (hboundary : BoundaryCorrect f parameter seed labels) (steps : Nat)
    (hupper : keptHeight topLayer + steps ≤ maxLayerHeight) :
    truncateHash (labels (treePosition topLayer rootTree (keptHeight topLayer + steps) hupper
      ⟨spineIndex parameter (keptHeight topLayer + steps), spineIndex_lt parameter _⟩)) =
      evalWithAnswerFn f (Seeded.spineNode parameter topLayer rootTree seed steps : OracleComp HashSpec Digest) := by
  have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
  have htree : TreeActive parameter topLayer rootTree := by
    refine ⟨⟨subtreePosition parameter * 2 ^ subtreeHeight, ?_⟩, ?_, Completeness.treeIndexAt_top _⟩
    · rw [← subtree_size_mul]
      exact Nat.mul_lt_mul_of_pos_right (subtreePosition_lt parameter) (Nat.two_pow_pos _)
    · unfold Landed
      exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
  induction steps with
  | zero =>
      have hb : keptHeight topLayer ≤ maxLayerHeight := by omega
      have hk := keptPosition_lt parameter topLayer
      rw [hpos] at hk
      have hi : subtreePosition parameter < 2 ^ maxLayerHeight :=
        hk.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _) |>.trans
          (Nat.pow_le_pow_right (by decide) (layerHeight_le topLayer)))
      simp only [Nat.add_zero, spineIndex, Nat.sub_self, pow_zero, Nat.div_one]
      rw [Seeded.spineNode]
      have hv := tree_value_below f parameter seed labels hconsistent topLayer rootTree htree
        (keptHeight topLayer) hb le_rfl ⟨subtreePosition parameter, hi⟩ hk (by simp [hpos])
      exact hv
  | succ steps ih =>
      have hprev : keptHeight topLayer + steps ≤ maxLayerHeight := by omega
      have hact := spinePosition_active parameter (keptHeight topLayer + (steps + 1)) (by omega) hupper
      have hlevel : keptHeight topLayer + steps < maxLayerHeight := by omega
      have hbnd := boundary_tree_value f parameter seed labels hboundary
        ⟨keptHeight topLayer + steps, hlevel⟩ (by change keptHeight topLayer ≤ keptHeight topLayer + steps; omega)
      rw [hconsistent _ hact]
      have hparent := spineIndex_step parameter (keptHeight topLayer + steps) (by omega)
      have hposn : (⟨spineIndex parameter (keptHeight topLayer + (steps + 1)), spineIndex_lt parameter _⟩ : LeafIndex) =
          ⟨spineIndex parameter (keptHeight topLayer + steps) / 2,
            (Nat.div_le_self _ _).trans_lt (spineIndex_lt parameter _)⟩ := by
        apply Fin.ext
        simpa only [Nat.add_assoc] using hparent
      rw [hposn]
      have hinput := tree_input_ordered f parameter seed labels topLayer rootTree
        (keptHeight topLayer + steps) hupper
        ⟨spineIndex parameter (keptHeight topLayer + steps), spineIndex_lt parameter _⟩
      refine (congrArg (fun input : HashInput => truncateHash (f input)) hinput).trans ?_
      rw [Seeded.spineNode]
      simp only [evalWithAnswerFn_bind]
      have hi := ih hprev
      have hs : truncateHash (labels (treePosition topLayer rootTree (keptHeight topLayer + steps) hprev
          ⟨Nat.xor (spineIndex parameter (keptHeight topLayer + steps)) 1,
            Nat.xor_lt_two_pow (spineIndex_lt parameter _) one_lt_leaf_capacity⟩)) =
          evalWithAnswerFn f (Seeded.surrogate parameter seed (keptHeight topLayer + steps) :
            OracleComp HashSpec Digest) := hbnd
      have hidx : spineIndex parameter (keptHeight topLayer + steps) =
          keptPosition parameter topLayer / 2 ^ steps := by
        simp only [spineIndex, Nat.add_sub_cancel_left, hpos]
      cases hb : (keptPosition parameter topLayer / 2 ^ steps).testBit 0 <;>
        try simp only [Bool.false_eq_true, ↓reduceIte, eval_tweakableHash]
      all_goals
        apply congrArg (fun input : HashInput => truncateHash (f input))
        have hb' := hb
        rw [← hidx] at hb'
        simp only [orderedPayload, hb', Bool.false_eq_true, ↓reduceIte]
        rw [hi, hs, hidx]

include hconsistent in
theorem chain_input (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) (chain : ChainIndex) (step : ChainStep) :
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
      rw [chain_value f parameter seed labels hconsistent lay tree leaf hactive chain ⟨step, by omega⟩]

omit f parameter seed labels hconsistent in
theorem quotient_range (height level index : Nat) (hlevel : level ≤ height)
    (hindex : index < 2 ^ height) : index / 2 ^ level < 2 ^ (height - level) := by
  apply (Nat.div_lt_iff_lt_mul (by positivity)).2
  rw [← Nat.pow_add, Nat.sub_add_cancel hlevel]
  exact hindex

omit f seed labels hconsistent in
theorem pathNode_kept (lay : Layer) (leaf : LeafIndex) (hkept : Kept parameter lay leaf) (level : Nat)
    (hlevel : level ≤ keptHeight lay) :
    (leaf.val / 2 ^ level) / 2 ^ (keptHeight lay - level) = keptPosition parameter lay := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_sub_of_le hlevel]
  exact hkept

omit f seed labels hconsistent in
theorem pathSibling_kept (lay : Layer) (leaf : LeafIndex) (hkept : Kept parameter lay leaf) (level : Nat)
    (hlevel : level < keptHeight lay) :
    (Nat.xor (leaf.val / 2 ^ level) 1) / 2 ^ (keptHeight lay - level) = keptPosition parameter lay := by
  change ((leaf.val / 2 ^ level) ^^^ 1) / 2 ^ (keptHeight lay - level) = _
  rw [Nat.xor_div_two_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega)), Nat.xor_zero,
    pathNode_kept parameter lay leaf hkept level (by omega)]

omit hconsistent in
theorem canonicalPath_below (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (level : Nat) (hlower : level < keptHeight lay) :
    canonicalTreePath f parameter lay tree seed leaf level =
      node f parameter lay tree seed level (Nat.xor (leaf.val / 2 ^ level) 1) := by
  have hlevel : level < layerHeight lay := hlower.trans_le (Completeness.keptHeight_le lay)
  rw [canonicalTreePath, dif_pos hlevel, eval_treePath, if_pos hlower]

omit f seed labels hconsistent in
/-- Above the kept part there is only the top layer's spine. -/
theorem top_of_above_kept (lay : Layer) (level : Nat) (hlevel : level ≤ layerHeight lay)
    (habove : ¬level ≤ keptHeight lay) : lay = topLayer := by
  by_contra htop
  have hlay : lay.val ≠ 0 := fun e => htop (Fin.ext e)
  rw [keptHeight_of_ne_top lay hlay] at habove
  exact habove hlevel

omit f seed labels hconsistent in
theorem treeActive_of_key (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) : TreeActive parameter lay tree :=
  ((keyActive_iff parameter lay tree leaf).1 hactive).1

omit f seed labels hconsistent in
theorem leaf_lt_of_key (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) : leaf.val < 2 ^ layerHeight lay :=
  ((keyActive_iff parameter lay tree leaf).1 hactive).2.2

omit f seed labels hconsistent in
theorem kept_of_key (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) : Kept parameter lay leaf :=
  ((keyActive_iff parameter lay tree leaf).1 hactive).2.1

include hconsistent in
theorem tree_path_value (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hactive : KeyActive parameter lay tree leaf)
    (level : Nat) (hlevel : level ≤ layerHeight lay) :
    truncateHash (labels (treePosition lay tree level (hlevel.trans (layerHeight_le lay))
      ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩)) =
    merkleValue f parameter (fun height index => .node lay tree height index) leaf.val
      (canonicalTreePath f parameter lay tree seed leaf)
      (node f parameter lay tree seed 0 leaf.val) level := by
  have hkept := kept_of_key parameter lay tree leaf hactive
  have hrange := leaf_lt_of_key parameter lay tree leaf hactive
  by_cases hlower : level ≤ keptHeight lay
  · rw [tree_value_below f parameter seed labels hconsistent lay tree
      (treeActive_of_key parameter lay tree leaf hactive) level _ hlower _
      (quotient_range (layerHeight lay) level leaf.val hlevel hrange)
      (pathNode_kept parameter lay leaf hkept level hlower)]
    symm
    rw [merkleValue, merkleFold_treeFold]
    exact eval_treeFold_path f parameter lay tree seed leaf _ level
      (fun k hk => canonicalPath_below f parameter seed lay tree leaf k (by omega))
  · have htop := top_of_above_kept lay level hlevel hlower
    subst htop
    have htree := treeActive_top parameter tree (treeActive_of_key parameter _ tree leaf hactive)
    subst htree
    have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
    have hb : keptHeight topLayer ≤ level := by omega
    have hsum : keptHeight topLayer + (level - keptHeight topLayer) = level := Nat.add_sub_of_le hb
    have hindex : leaf.val / 2 ^ level = spineIndex parameter level := by
      rw [← hsum, kept_div parameter topLayer leaf hkept, hpos]
      simp only [spineIndex, Nat.add_sub_cancel_left]
    have hposition : (⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩ : LeafIndex) =
        ⟨spineIndex parameter level, spineIndex_lt parameter level⟩ := Fin.ext hindex
    rw [hposition]
    have hspine := spine_value f parameter seed labels hconsistent hboundary
      (level - keptHeight topLayer) (by rw [hsum]; exact hlevel.trans (layerHeight_le _))
    simp only [hsum] at hspine
    rw [hspine]
    symm
    rw [merkleValue, merkleFold_treeFold]
    simpa only [hsum] using eval_treeFold_spine f parameter topLayer rootTree seed leaf hkept _
      (fun k hk => canonicalPath_below f parameter seed topLayer rootTree leaf k hk)
      (level - keptHeight topLayer) (fun k hk => canonicalTreePath_surrogate f parameter topLayer rootTree
        seed leaf (keptHeight topLayer + k) (by omega) (by omega))

include hconsistent in
theorem tree_path_sibling (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hactive : KeyActive parameter lay tree leaf)
    (level : Nat) (hlevel : level < layerHeight lay) :
    truncateHash (labels (treePosition lay tree level (Nat.le_of_lt (hlevel.trans_le (layerHeight_le lay)))
      ⟨Nat.xor (leaf.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩)) =
      canonicalTreePath f parameter lay tree seed leaf level := by
  have hkept := kept_of_key parameter lay tree leaf hactive
  have hrange := leaf_lt_of_key parameter lay tree leaf hactive
  by_cases hlower : level < keptHeight lay
  · rw [canonicalPath_below f parameter seed lay tree leaf level hlower]
    exact tree_value_below f parameter seed labels hconsistent lay tree
      (treeActive_of_key parameter lay tree leaf hactive) level _ (by omega) _
      (Nat.xor_lt_two_pow (quotient_range (layerHeight lay) level leaf.val (Nat.le_of_lt hlevel) hrange)
        (Nat.one_lt_two_pow (by omega)))
      (pathSibling_kept parameter lay leaf hkept level hlower)
  · have htop := top_of_above_kept lay (level + 1) hlevel (by omega)
    subst htop
    have htree := treeActive_top parameter tree (treeActive_of_key parameter _ tree leaf hactive)
    subst htree
    have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
    have hb : keptHeight topLayer ≤ level := by omega
    have hindex : leaf.val / 2 ^ level = spineIndex parameter level := by
      have hsum : keptHeight topLayer + (level - keptHeight topLayer) = level := Nat.add_sub_of_le hb
      rw [← hsum, kept_div parameter topLayer leaf hkept, hpos]
      simp only [spineIndex, Nat.add_sub_cancel_left]
    have hposition : (⟨Nat.xor (leaf.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt) one_lt_leaf_capacity⟩ : LeafIndex) =
        ⟨boundaryIndex parameter level, boundaryIndex_lt parameter level⟩ := by
      apply Fin.ext
      exact congrArg (fun index => Nat.xor index 1) hindex
    rw [hposition, canonicalTreePath_surrogate f parameter topLayer rootTree seed leaf level hb hlevel]
    exact boundary_tree_value f parameter seed labels hboundary
      ⟨level, hlevel.trans_le (layerHeight_le _)⟩ hb

include hconsistent in
/-- The exempt input at each retained path node is exactly the canonical verifier-fold input. -/
theorem tree_path_input (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (hactive : KeyActive parameter lay tree leaf)
    (level : Nat) (hlevel : level < layerHeight lay) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (treePosition lay tree (level + 1) (hlevel.trans_le (layerHeight_le lay))
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
  rw [hparent, tree_input_ordered f parameter seed labels lay tree level _
    ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩,
    tree_path_value f parameter seed labels hconsistent hboundary lay tree leaf hactive level
      (Nat.le_of_lt hlevel),
    tree_path_sibling f parameter seed labels hconsistent hboundary lay tree leaf hactive level hlevel]
  simp only [merkleInput]
  have hbit : (leaf.val / 2 ^ level).testBit 0 = leaf.val.testBit level := by
    simpa only [Nat.zero_add] using (Nat.testBit_add leaf.val 0 level).symm
  rw [hbit, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

omit f seed labels hconsistent in
theorem tree_path_active (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) (level : Nat) (hlevel : level ≤ layerHeight lay) :
    active parameter (treePosition lay tree level (hlevel.trans (layerHeight_le lay))
      ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩) := by
  have hkept := kept_of_key parameter lay tree leaf hactive
  have hrange := leaf_lt_of_key parameter lay tree leaf hactive
  by_cases hlower : level ≤ keptHeight lay
  · exact treePosition_active_below parameter lay tree (treeActive_of_key parameter lay tree leaf hactive)
      level _ hlower _ (quotient_range (layerHeight lay) level leaf.val hlevel hrange)
      (pathNode_kept parameter lay leaf hkept level hlower)
  · have htop := top_of_above_kept lay level hlevel hlower
    subst htop
    have htree := treeActive_top parameter tree (treeActive_of_key parameter _ tree leaf hactive)
    subst htree
    have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
    have hb : keptHeight topLayer ≤ level := by omega
    have hsum : keptHeight topLayer + (level - keptHeight topLayer) = level := Nat.add_sub_of_le hb
    have hindex : leaf.val / 2 ^ level = spineIndex parameter level := by
      rw [← hsum, kept_div parameter topLayer leaf hkept, hpos]
      simp only [spineIndex, Nat.add_sub_cancel_left]
    have hposition : (⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩ : LeafIndex) =
        ⟨spineIndex parameter level, spineIndex_lt parameter level⟩ := Fin.ext hindex
    rw [hposition]
    exact spinePosition_active parameter level hb _

include hconsistent in
/-- The label at the root of a retained tree is the tree's root. -/
theorem tree_root_value (hboundary : BoundaryCorrect f parameter seed labels)
    (lay : Layer) (tree : TreeIndex) (htree : TreeActive parameter lay tree) :
    truncateHash (labels (treePosition lay tree (layerHeight lay) (layerHeight_le lay)
      ⟨0, Nat.two_pow_pos _⟩)) =
      evalWithAnswerFn f (Seeded.treeRoot parameter lay tree seed : OracleComp HashSpec Digest) := by
  by_cases htop : lay = topLayer
  · subst htop
    have htr := treeActive_top parameter tree htree
    subst htr
    have hb := Completeness.keptHeight_le topLayer
    have hsum : keptHeight topLayer + (layerHeight topLayer - keptHeight topLayer) = layerHeight topLayer :=
      Nat.add_sub_of_le hb
    have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
    have hindex : spineIndex parameter (layerHeight topLayer) = 0 := by
      have hk := keptPosition_lt parameter topLayer
      rw [hpos] at hk
      exact Nat.div_eq_of_lt hk
    have hs := spine_value f parameter seed labels hconsistent hboundary
      (layerHeight topLayer - keptHeight topLayer) (by rw [hsum]; exact layerHeight_le _)
    simp only [hsum, hindex] at hs
    simpa only [Seeded.treeRoot] using hs
  · have hlay : lay.val ≠ 0 := fun e => htop (Fin.ext e)
    have hkh := keptHeight_of_ne_top lay hlay
    have hkp := keptPosition_of_ne_top parameter lay hlay
    have hv := tree_value_below f parameter seed labels hconsistent lay tree htree (layerHeight lay)
      (layerHeight_le lay) (le_of_eq hkh.symm) ⟨0, Nat.two_pow_pos _⟩ (by simp)
      (by simp [hkp])
    rw [hv, Seeded.treeRoot, hkh, Nat.sub_self, Seeded.spineNode, hkh, hkp]
    rfl

/-! ### FORS

Every FORS position is prepared. Its label is the honest value: a leaf the hash of its secret, a
node the honest node. The scheme does not hash a tree's root: the FORS key is the two level-`(a - 1)`
nodes of every tree (`keyLabels`). -/

section ForsTrees

variable (index : Index) (κ : FTree)

omit hconsistent in
theorem fleaf_input (leaf : FLeaf) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (.fleaf index κ leaf) labels =
    tweakableHashInput parameter (.forsLeaf index κ leaf)
      (bytesLE 16 (Completeness.forsSecretValue f parameter index κ seed leaf)) := by
  simp only [canonicalGraphInput, canonicalGraphSlots, Position.domain, ftsSecrets,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

include hconsistent in
theorem fleaf_value (leaf : FLeaf) :
    truncateHash (labels (.fleaf index κ leaf)) = Completeness.forsLeafValue f parameter index κ seed leaf := by
  rw [hconsistent (.fleaf index κ leaf) trivial, fleaf_input]
  rfl

/-- Graph location for a FORS node, including the level-zero leaf. -/
def forsPosition : (level : Nat) → level ≤ forsHeight → FLeaf → Position
  | 0, _, leaf => .fleaf index κ leaf
  | level + 1, hlevel, nd => .fnode index κ ⟨level, by omega⟩ nd

omit hconsistent in
theorem fnode_input (level : Nat) (hlevel : level + 1 ≤ forsHeight) (nd : FLeaf)
    (hindex : 2 * nd.val + 1 < 2 ^ forsHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (forsPosition index κ (level + 1) hlevel nd) labels =
    tweakableHashInput parameter (.forsNode index κ ⟨level, by omega⟩ nd)
      (nodePayload
        (truncateHash (labels (forsPosition index κ level (by omega) ⟨2 * nd.val, by omega⟩)))
        (truncateHash (labels (forsPosition index κ level (by omega) ⟨2 * nd.val + 1, hindex⟩)))) := by
  cases level <;>
    simp [forsPosition, canonicalGraphInput, canonicalGraphSlots, Position.children,
      Position.domain, hindex, nodePayload]

include hconsistent in
theorem fnode_value (level : Nat) (hlevel : level ≤ forsHeight) (nd : FLeaf)
    (hindex : nd.val < 2 ^ (forsHeight - level)) :
    truncateHash (labels (forsPosition index κ level hlevel nd)) =
      Completeness.forsNodeValue f parameter index κ seed level nd.val := by
  induction level generalizing nd with
  | zero =>
      rw [show forsPosition index κ 0 hlevel nd = .fleaf index κ nd from rfl,
        fleaf_value f parameter seed labels hconsistent, Completeness.forsNodeValue_zero]
  | succ level ih =>
      have hchildren := child_index_bound hlevel hindex
      have hglobal : 2 * nd.val + 1 < 2 ^ forsHeight :=
        hchildren.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
      rw [hconsistent (forsPosition index κ (level + 1) hlevel nd) (by trivial),
        fnode_input f parameter seed labels index κ level hlevel nd hglobal,
        Completeness.forsNodeValue_succ f parameter index κ seed level nd.val (by omega)]
      rw [ih (by omega) _ (by change 2 * nd.val < _; omega), ih (by omega) _ hchildren]
      congr 4
      exact Fin.ext (Nat.mod_eq_of_lt nd.isLt).symm

/-- The level of a tree's two top nodes as an `fnode` level (`a - 2`: level `a - 1`). -/
def topNodeLevel : FLevel := ⟨forsHeight - 2, by have := Params.forsHeight_ge; omega⟩

/-- The FORS key as graph labels: the two level-`(a - 1)` nodes of every tree. -/
def keyLabels : ForsKey :=
  fun κ' => (truncateHash (labels (.fnode index κ' topNodeLevel ⟨0, Nat.two_pow_pos _⟩)),
    truncateHash (labels (.fnode index κ' topNodeLevel ⟨1, Nat.one_lt_two_pow (by
      have := Params.forsHeight_ge; omega)⟩)))

include hconsistent in
theorem fors_key_value :
    keyLabels labels index =
      evalWithAnswerFn f (Seeded.forsKey parameter index seed : OracleComp HashSpec ForsKey) := by
  have ha := Params.forsHeight_ge
  have hlevel : forsHeight - 2 + 1 = forsHeight - 1 := by omega
  have h : ∀ (κ' : FTree) (nd : FLeaf) (_ : nd.val < 2),
      truncateHash (labels (.fnode index κ' topNodeLevel nd)) =
        Completeness.forsNodeValue f parameter index κ' seed (forsHeight - 1) nd.val := by
    intro κ' nd hnd
    have h1 : truncateHash (labels (.fnode index κ' topNodeLevel nd)) =
        Completeness.forsNodeValue f parameter index κ' seed (forsHeight - 2 + 1) nd.val :=
      fnode_value f parameter seed labels hconsistent index κ' (forsHeight - 2 + 1) (by omega) nd
        (by rw [show forsHeight - (forsHeight - 2 + 1) = 1 by omega]; simpa using hnd)
    rw [hlevel] at h1
    exact h1
  rw [Completeness.forsKey_eq]
  funext κ'
  simp only [keyLabels, Completeness.topsValue]
  rw [h κ' _ (by norm_num), h κ' _ (by norm_num)]

/-! #### Paths -/

omit hconsistent in
theorem fors_input_ordered (level : Nat) (hlevel : level + 1 ≤ forsHeight) (current : FLeaf) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (forsPosition index κ (level + 1) hlevel
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩) labels =
    tweakableHashInput parameter (.forsNode index κ ⟨level, by omega⟩
        ⟨current.val / 2, (Nat.div_le_self _ _).trans_lt current.isLt⟩)
      (orderedPayload (current.val.testBit 0)
        (truncateHash (labels (forsPosition index κ level (by omega) current)))
        (truncateHash (labels (forsPosition index κ level (by omega)
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt
            (Nat.one_lt_two_pow (by have := Params.forsHeight_ge; omega))⟩)))) := by
  have hglobal : 2 * (current.val / 2) + 1 < 2 ^ forsHeight := by
    have hc := current.isLt
    have : 2 ^ forsHeight = 2 * 2 ^ (forsHeight - 1) := by
      rw [← Nat.pow_succ']; congr 1; have := Params.forsHeight_ge; omega
    omega
  rw [fnode_input f parameter seed labels index κ level hlevel _ hglobal]
  cases hb : current.val.testBit 0 with
  | false =>
      have hm := Nat.mod_two_eq_zero_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2), by omega⟩ : FLeaf) = current :=
        Fin.ext (by change 2 * (current.val / 2) = current.val; omega)
      have hsibling : (⟨2 * (current.val / 2) + 1, hglobal⟩ : FLeaf) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt
            (Nat.one_lt_two_pow (by have := Params.forsHeight_ge; omega))⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) + 1 = current.val ^^^ 1
        rw [Nat.xor_one_of_even (Nat.even_iff.mpr hm)]
        omega
      simp only [orderedPayload, Bool.false_eq_true, ↓reduceIte, hcurrent, hsibling]
  | true =>
      have hm := Nat.mod_two_eq_one_iff_testBit_zero.mpr hb
      have hcurrent : (⟨2 * (current.val / 2) + 1, hglobal⟩ : FLeaf) = current :=
        Fin.ext (by change 2 * (current.val / 2) + 1 = current.val; omega)
      have hsibling : (⟨2 * (current.val / 2), by omega⟩ : FLeaf) =
          ⟨Nat.xor current.val 1, Nat.xor_lt_two_pow current.isLt
            (Nat.one_lt_two_pow (by have := Params.forsHeight_ge; omega))⟩ := by
        apply Fin.ext
        change 2 * (current.val / 2) = current.val ^^^ 1
        rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hm)]
        omega
      simp only [orderedPayload, ↓reduceIte, hcurrent, hsibling]

include hconsistent in
theorem fors_path_value (leaf : FLeaf) (level : Nat) (hlevel : level ≤ forsHeight) :
    truncateHash (labels (forsPosition index κ level hlevel
      ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩)) =
    merkleValue f parameter (Fors.forsDomain index κ) leaf.val
      (Fors.extendPath (Fors.canonicalPath f parameter index κ seed leaf))
      (Completeness.forsLeafValue f parameter index κ seed leaf) level := by
  rw [fnode_value f parameter seed labels hconsistent index κ level hlevel _
    (quotient_range forsHeight level leaf.val hlevel leaf.isLt)]
  symm
  rw [merkleValue, Fors.merkleFold_forsFold _ _ _ _ _ _ hlevel, ← Completeness.forsNodeValue_zero]
  exact Completeness.eval_forsFold_path f parameter index κ seed leaf _ level hlevel (fun _ _ _ => rfl)

include hconsistent in
theorem fors_path_sibling (leaf : FLeaf) (level : Nat) (hlevel : level < forsHeight) :
    truncateHash (labels (forsPosition index κ level (Nat.le_of_lt hlevel)
      ⟨Nat.xor (leaf.val / 2 ^ level) 1,
        Nat.xor_lt_two_pow ((Nat.div_le_self _ _).trans_lt leaf.isLt)
          (Nat.one_lt_two_pow (by have := Params.forsHeight_ge; omega))⟩)) =
      Fors.extendPath (Fors.canonicalPath f parameter index κ seed leaf) level := by
  rw [Fors.extendPath, dif_pos hlevel, Fors.canonicalPath]
  exact fnode_value f parameter seed labels hconsistent index κ level (Nat.le_of_lt hlevel) _
    (Nat.xor_lt_two_pow (quotient_range forsHeight level leaf.val (Nat.le_of_lt hlevel) leaf.isLt)
      (Nat.one_lt_two_pow (by omega)))

include hconsistent in
theorem fors_path_input (leaf : FLeaf) (level : Nat) (hlevel : level < forsHeight) :
    canonicalGraphInput parameter (otsSecrets f parameter seed) (ftsSecrets f parameter seed)
      (forsPosition index κ (level + 1) hlevel
        ⟨leaf.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt leaf.isLt⟩) labels =
    merkleInput f parameter (Fors.forsDomain index κ) leaf.val
      (Fors.extendPath (Fors.canonicalPath f parameter index κ seed leaf))
      (Completeness.forsLeafValue f parameter index κ seed leaf) level := by
  have hparent : (⟨leaf.val / 2 ^ (level + 1), (Nat.div_le_self _ _).trans_lt leaf.isLt⟩ : FLeaf) =
      ⟨(leaf.val / 2 ^ level) / 2,
        (Nat.div_le_self _ _).trans_lt ((Nat.div_le_self _ _).trans_lt leaf.isLt)⟩ := by
    apply Fin.ext
    change leaf.val / 2 ^ (level + 1) = (leaf.val / 2 ^ level) / 2
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [hparent, fors_input_ordered f parameter seed labels index κ level hlevel
    ⟨leaf.val / 2 ^ level, (Nat.div_le_self _ _).trans_lt leaf.isLt⟩,
    fors_path_value f parameter seed labels hconsistent index κ leaf level (Nat.le_of_lt hlevel),
    fors_path_sibling f parameter seed labels hconsistent index κ leaf level hlevel]
  simp only [merkleInput]
  have hbit : (leaf.val / 2 ^ level).testBit 0 = leaf.val.testBit level := by
    simpa only [Nat.zero_add] using (Nat.testBit_add leaf.val 0 level).symm
  rw [hbit]
  congr 1
  rw [Fors.forsDomain, dif_pos ⟨by omega, by omega⟩]
  congr 1
  apply Fin.ext
  change leaf.val / 2 ^ level / 2 = leaf.val / 2 ^ (level + 1) % 2 ^ forsHeight
  rw [Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt leaf.isLt), Nat.pow_succ, Nat.div_div_eq_div_mul]

end ForsTrees

/-- Material tables with their full hash outputs truncated exactly as key derivation does. -/
def materialOts (material : SeedModel.Material) : Layer → TreeIndex → LeafIndex → ChainIndex → Digest :=
  fun lay tree leaf chain => truncateHash (material.2 (.inl (lay, tree, leaf, chain)))

def materialFts (material : SeedModel.Material) : ForsSecrets :=
  fun index κ leaf => truncateHash (material.2 (.inr (.inl (index, κ, leaf))))

def materialSurrogates (material : SeedModel.Material) : Fin maxLayerHeight → Digest :=
  fun level => truncateHash (material.2 (.inr (.inr level)))

omit parameter labels hconsistent in
theorem materialOts_eq (material : SeedModel.Material) (hagrees : SeedModel.PreparedAgreement f seed material) :
    materialOts material = otsSecrets f (SeedModel.parameter material) seed := by
  funext lay tree leaf chain
  exact (SeedModel.eval_ots_prepared f seed material hagrees lay tree leaf chain).symm

omit parameter labels hconsistent in
theorem materialFts_eq (material : SeedModel.Material) (hagrees : SeedModel.PreparedAgreement f seed material) :
    materialFts material = ftsSecrets f (SeedModel.parameter material) seed := by
  funext index κ leaf
  exact (SeedModel.eval_fors_prepared f seed material hagrees index κ leaf).symm

omit parameter labels hconsistent in
theorem materialSurrogates_eq (material : SeedModel.Material)
    (hagrees : SeedModel.PreparedAgreement f seed material) :
    materialSurrogates material = surrogates f (SeedModel.parameter material) seed := by
  funext level
  unfold surrogates
  rw [Seeded.surrogate, dif_pos level.isLt]
  exact (SeedModel.eval_surrogate_prepared f seed material hagrees level).symm

end FORS.Security.GraphCorrectness

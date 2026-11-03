import FORS.Classification.Tree
import FORS.GraphView.Cache

section

/-! The exact off-spine address of each surrogate of the top layer's tree: the spine index and the
boundary index at each level. A boundary node is never a kept node, so a surrogate target at this
address cannot overlap a prepared canonical node. The levels count from the top layer's leaves, and
the kept subtree has height `keptHeight topLayer = b - heightBelow topLayer`. -/

open OracleComp OracleSpec

namespace FORS.Security

variable [Params]
open Concrete
attribute [local irreducible] Seeded.treeNode Seeded.treeRoot Seeded.spineNode
set_option maxHeartbeats 600000

theorem xor_one_ne (index : Nat) : Nat.xor index 1 ≠ index := by
  intro heq
  change index ^^^ 1 = index at heq
  by_cases heven : index % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr heven)] at heq
    omega
  · have hodd : index % 2 = 1 := by omega
    rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr hodd)] at heq
    omega


def spineIndex (parameter : PublicParameter) (level : Nat) : Nat :=
  subtreePosition parameter / 2 ^ (level - keptHeight topLayer)

def boundaryIndex (parameter : PublicParameter) (level : Nat) : Nat :=
  Nat.xor (spineIndex parameter level) 1

/-- Retained-subtree nodes of the top layer's tree below its root and the unique spine nodes above
it. -/
def KeptNode (parameter : PublicParameter) (level index : Nat) : Prop :=
  if level ≤ keptHeight topLayer then
    index / 2 ^ (keptHeight topLayer - level) = subtreePosition parameter
  else index = spineIndex parameter level

theorem boundary_not_kept (parameter : PublicParameter) (level : Nat)
    (hlevel : keptHeight topLayer ≤ level) : ¬KeptNode parameter level (boundaryIndex parameter level) := by
  unfold KeptNode
  by_cases heq : level = keptHeight topLayer
  · rw [heq]
    simp only [le_refl, ↓reduceIte, Nat.sub_self, pow_zero, Nat.div_one,
      boundaryIndex, spineIndex]
    exact xor_one_ne _
  · rw [if_neg (by omega : ¬level ≤ keptHeight topLayer)]
    exact xor_one_ne _

end FORS.Security

end

section

/-! The candidate's retained structural positions and off-spine surrogate boundary. A one-time key
(its chains and its leaf) is retained when it lies on the path of a landed index; a node of the top
layer's root tree when it is a kept or spine node; a node of a lower layer when it lies above a
retained key. FORS instances are conservatively prepared as well; exact serialized addresses keep
those extra nodes from adding targets to an individual query. The surrogates are nodes of the top
layer's root tree. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.PrunedGraph

variable [Params]

open Concrete Completeness Graph TargetAssignment
attribute [local instance] Classical.propDecidable


/-- The one-time key at leaf `leaf` of tree `tree` of layer `lay` lies on the path of a landed index. -/
def KeyActive (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Prop :=
  ∃ index : Index, Landed parameter index ∧ treeIndexAt index lay = tree ∧ leafIndexAt index lay = leaf

/-- The tree `tree` of layer `lay` lies on the path of a landed index. -/
def TreeActive (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) : Prop :=
  ∃ index : Index, Landed parameter index ∧ treeIndexAt index lay = tree

/-- The index bits below the layers above `lay` and its tree: `heightBelow lay + layerHeight lay`
is at most `heightBelow topLayer` below the top layer, and the height at the top. -/
theorem heightBelow_add_layerHeight_le (lay : Layer) (h : lay ≠ topLayer) :
    heightBelow lay + layerHeight lay ≤ heightBelow topLayer := by
  have hlay : lay.val ≠ 0 := fun e => h (Fin.ext e)
  rw [Completeness.layerHeight_of_ne_top lay hlay, Completeness.heightBelow_top]
  simp only [heightBelow]
  have := lay.isLt
  have : numLayers - 1 - lay.val + 1 ≤ numLayers - 1 := by omega
  calc lowerHeight * (numLayers - 1 - lay.val) + lowerHeight
      = lowerHeight * (numLayers - 1 - lay.val + 1) := by ring
    _ ≤ lowerHeight * (numLayers - 1) := Nat.mul_le_mul_left _ this

theorem heightBelow_add_layerHeight_top :
    heightBelow topLayer + layerHeight topLayer = totalHeight := by
  rw [Completeness.layerHeight_top, Completeness.maxLayerHeight_add]

/-- Replacing the bits of a layer's leaf in an index. -/
theorem exists_index_with_leaf (index0 : Index) (lay : Layer) (leaf : LeafIndex)
    (hleaf : leaf.val < 2 ^ layerHeight lay) :
    ∃ index : Index, treeIndexAt index lay = treeIndexAt index0 lay ∧ leafIndexAt index lay = leaf ∧
      index.val / 2 ^ (heightBelow lay + layerHeight lay) = index0.val / 2 ^ (heightBelow lay + layerHeight lay) ∧
      index.val / 2 ^ heightBelow lay = (index0.val / 2 ^ (heightBelow lay + layerHeight lay)) *
        2 ^ layerHeight lay + leaf.val := by
  set B := heightBelow lay
  set L := layerHeight lay
  have hBL : B + L ≤ totalHeight := by
    by_cases h : lay = topLayer
    · subst h; exact le_of_eq heightBelow_add_layerHeight_top
    · have h1 := heightBelow_add_layerHeight_le lay h
      have h2 := heightBelow_add_layerHeight_top
      omega
  set high := index0.val / 2 ^ (B + L)
  set low := index0.val % 2 ^ B
  have hlow : low < 2 ^ B := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hhigh : high < 2 ^ (totalHeight - (B + L)) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    rw [← pow_add, Nat.sub_add_cancel hBL]
    exact index0.isLt
  have hinner : leaf.val + high * 2 ^ L < 2 ^ (totalHeight - B) := by
    have h1 : (high + 1) * 2 ^ L ≤ 2 ^ (totalHeight - (B + L)) * 2 ^ L := Nat.mul_le_mul_right _ hhigh
    rw [← pow_add, show totalHeight - (B + L) + L = totalHeight - B by omega] at h1
    nlinarith
  have hval : low + (leaf.val + high * 2 ^ L) * 2 ^ B < 2 ^ totalHeight := by
    have h1 : (leaf.val + high * 2 ^ L + 1) * 2 ^ B ≤ 2 ^ (totalHeight - B) * 2 ^ B :=
      Nat.mul_le_mul_right _ hinner
    rw [← pow_add, Nat.sub_add_cancel (by omega)] at h1
    nlinarith
  have hdivB : (low + (leaf.val + high * 2 ^ L) * 2 ^ B) / 2 ^ B = leaf.val + high * 2 ^ L := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlow, Nat.zero_add]
  have hdivBL : (low + (leaf.val + high * 2 ^ L) * 2 ^ B) / 2 ^ (B + L) = high := by
    rw [pow_add, ← Nat.div_div_eq_div_mul, hdivB,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hleaf, Nat.zero_add]
  refine ⟨⟨low + (leaf.val + high * 2 ^ L) * 2 ^ B, hval⟩, ?_, ?_, ?_, ?_⟩
  · apply Fin.ext
    exact hdivBL
  · apply Fin.ext
    change (low + (leaf.val + high * 2 ^ L) * 2 ^ B) / 2 ^ B % 2 ^ L = leaf.val
    rw [hdivB, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hleaf]
  · exact hdivBL
  · change (low + (leaf.val + high * 2 ^ L) * 2 ^ B) / 2 ^ B = _
    rw [hdivB]
    ring

/-- A key is retained exactly when its tree is, its leaf is kept and lies in its tree. -/
theorem keyActive_iff (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    KeyActive parameter lay tree leaf ↔
      TreeActive parameter lay tree ∧ Kept parameter lay leaf ∧ leaf.val < 2 ^ layerHeight lay := by
  constructor
  · rintro ⟨index, hland, htree, hleaf⟩
    refine ⟨⟨index, hland, htree⟩, ?_, ?_⟩
    · rw [← hleaf]; exact Completeness.kept_leafIndexAt parameter index hland lay
    · rw [← hleaf]; exact Completeness.leafIndexAt_lt index lay
  · rintro ⟨⟨index0, hland0, htree0⟩, hkept, hrange⟩
    obtain ⟨index, htree, hleaf, hhigh, hmid⟩ := exists_index_with_leaf index0 lay leaf hrange
    refine ⟨index, ?_, htree.trans htree0, hleaf⟩
    unfold Landed
    by_cases htop : lay = topLayer
    · subst htop
      have hb := Completeness.heightBelow_le_subtree
      have hzero : index0.val / 2 ^ (heightBelow topLayer + layerHeight topLayer) = 0 := by
        rw [heightBelow_add_layerHeight_top]; exact Nat.div_eq_of_lt index0.isLt
      rw [hzero, Nat.zero_mul, Nat.zero_add] at hmid
      rw [show subtreeHeight = heightBelow topLayer + (subtreeHeight - heightBelow topLayer) by omega,
        pow_add, ← Nat.div_div_eq_div_mul, hmid]
      unfold Kept at hkept
      rw [Completeness.keptHeight_top] at hkept
      rw [hkept]
      rfl
    · have hle := heightBelow_add_layerHeight_le lay htop
      have hb : heightBelow topLayer ≤ subtreeHeight := Completeness.heightBelow_le_subtree
      have hsplit : subtreeHeight = (heightBelow lay + layerHeight lay) +
          (subtreeHeight - (heightBelow lay + layerHeight lay)) := by omega
      unfold Landed at hland0
      rw [hsplit, pow_add, ← Nat.div_div_eq_div_mul, hhigh, Nat.div_div_eq_div_mul, ← pow_add,
        ← hsplit]
      exact hland0

/-- Some index lands: `s · 2^b`. -/
theorem exists_landed (parameter : PublicParameter) : ∃ index : Index, Landed parameter index := by
  refine ⟨⟨subtreePosition parameter * 2 ^ subtreeHeight, ?_⟩, ?_⟩
  · rw [← subtree_size_mul]
    exact Nat.mul_lt_mul_of_pos_right (subtreePosition_lt parameter) (Nat.two_pow_pos _)
  · unfold Landed
    exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

theorem treeActive_rootTree (parameter : PublicParameter) : TreeActive parameter topLayer rootTree := by
  obtain ⟨index, hland⟩ := exists_landed parameter
  exact ⟨index, hland, Completeness.treeIndexAt_top index⟩

/-- The key of a layer above the bottom one on the path of a landed index signs a retained tree. -/
theorem treeActive_child (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hactive : KeyActive parameter lay tree leaf) (hbelow : lay.val + 1 < numLayers) :
    TreeActive parameter ⟨lay.val + 1, hbelow⟩ (childTree lay tree leaf) := by
  obtain ⟨index, hland, htree, hleaf⟩ := hactive
  refine ⟨index, hland, ?_⟩
  rw [← htree, ← hleaf, Completeness.childTree_path_above index lay hbelow]

/-- The top layer's only retained tree is its root tree. -/
theorem treeActive_top (parameter : PublicParameter) (tree : TreeIndex)
    (h : TreeActive parameter topLayer tree) : tree = rootTree := by
  obtain ⟨index, -, htree⟩ := h
  rw [← htree]
  exact Completeness.treeIndexAt_top index

/-- A node at `level` (counted from the leaves) of tree `tree` of layer `lay` is computed by the
honest key: a kept or spine node of the top layer's root tree, or a node above a retained key of a
lower layer. -/
def NodeActive (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (level index : Nat) : Prop :=
  if lay = topLayer then tree = rootTree ∧ KeptNode parameter level index
  else level ≤ layerHeight lay ∧
    ∃ leaf : LeafIndex, KeyActive parameter lay tree leaf ∧ leaf.val / 2 ^ level = index

def active (parameter : PublicParameter) : Position → Prop
  | .chain lay tree leaf _ _ => KeyActive parameter lay tree leaf
  | .leaf lay tree leaf => KeyActive parameter lay tree leaf
  | .node lay tree level index => NodeActive parameter lay tree (level.val + 1) index.val
  | _ => True

/-- The surrogate targets: the off-spine siblings of the top layer's root tree. -/
def boundary (parameter : PublicParameter) (surrogates : Fin maxLayerHeight → Digest) :
    Position → Option Digest
  | .leaf lay tree leaf =>
      if lay = topLayer ∧ tree = rootTree ∧ keptHeight topLayer = 0 ∧ leaf.val = boundaryIndex parameter 0 then
        some (surrogates ⟨0, maxLayerHeight_pos⟩) else none
  | .node lay tree level index =>
      if h : level.val + 1 < maxLayerHeight then
        if lay = topLayer ∧ tree = rootTree ∧ keptHeight topLayer ≤ level.val + 1 ∧
            index.val = boundaryIndex parameter (level.val + 1) then
          some (surrogates ⟨level.val + 1, h⟩) else none
      else none
  | _ => none

theorem boundary_inactive (parameter : PublicParameter) (surrogates : Fin maxLayerHeight → Digest)
    (position : Position) (value : Digest) (hboundary : boundary parameter surrogates position = some value) :
    ¬active parameter position := by
  cases position with
  | chain | fleaf | fnode => simp [boundary] at hboundary
  | leaf lay tree leaf =>
      simp only [boundary] at hboundary
      split at hboundary
      next h =>
        obtain ⟨hlay, htree, hzero, hleaf⟩ := h
        change ¬KeyActive parameter lay tree leaf
        rintro ⟨index, hland, -, hleafAt⟩
        have hkept := Completeness.kept_leafIndexAt parameter index hland lay
        rw [hleafAt, hlay] at hkept
        unfold Kept at hkept
        rw [hzero, pow_zero, Nat.div_one, hleaf] at hkept
        have hpos : keptPosition parameter topLayer = subtreePosition parameter := if_pos rfl
        rw [hpos] at hkept
        simp only [boundaryIndex, spineIndex, hzero, Nat.sub_self, pow_zero, Nat.div_one] at hkept
        exact xor_one_ne _ hkept
      next => simp at hboundary
  | node lay tree level index =>
      simp only [boundary] at hboundary
      split at hboundary
      next hlevel =>
        split at hboundary
        next h =>
          obtain ⟨hlay, htree, hlevel', hindex⟩ := h
          change ¬NodeActive parameter lay tree (level.val + 1) index.val
          unfold NodeActive
          rw [if_pos hlay, hindex]
          exact fun hkept => boundary_not_kept parameter (level.val + 1) hlevel' hkept.2
        next => simp at hboundary
      next => simp at hboundary

theorem spineIndex_lt (parameter : PublicParameter) (level : Nat) :
    spineIndex parameter level < 2 ^ maxLayerHeight := by
  have hsub := subtreePosition_lt parameter
  have hpow : 2 ^ (totalHeight - subtreeHeight) ≤ (2 : Nat) ^ maxLayerHeight := by
    apply Nat.pow_le_pow_right (by decide)
    have := Completeness.maxLayerHeight_add
    have := Completeness.heightBelow_le_subtree
    omega
  exact (Nat.div_le_self _ _).trans_lt (hsub.trans_le hpow)

theorem boundaryIndex_lt (parameter : PublicParameter) (level : Nat) :
    boundaryIndex parameter level < 2 ^ maxLayerHeight :=
  Nat.xor_lt_two_pow (spineIndex_lt parameter level) (Nat.one_lt_two_pow maxLayerHeight_pos.ne')

/-- A positive-height surrogate is targeted at a node-domain address. -/
def boundaryPosition (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (hpositive : 0 < level.val) : Position :=
  .node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
    ⟨boundaryIndex parameter level.val, boundaryIndex_lt parameter level.val⟩

theorem boundaryPosition_domain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (hpositive : 0 < level.val) :
    (boundaryPosition parameter lay tree level hpositive).domain =
      .node lay tree level.val (boundaryIndex parameter level.val) := by
  simp only [boundaryPosition, Position.domain, Nat.sub_add_cancel hpositive]

theorem boundaryPosition_value (parameter : PublicParameter) (surrogates : Fin maxLayerHeight → Digest)
    (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (hpositive : 0 < level.val)
    (hlay : lay = topLayer) (htree : tree = rootTree) (hlower : keptHeight topLayer ≤ level.val) :
    boundary parameter surrogates (boundaryPosition parameter lay tree level hpositive) =
      some (surrogates level) := by
  simp only [boundaryPosition, boundary, Nat.sub_add_cancel hpositive, level.isLt,
    ↓reduceDIte, hlay, htree, hlower, and_self, ↓reduceIte]

/-- Full outputs at the boundary retain exactly the seed-derived low 128 bits. -/
def initialLabels (parameter : PublicParameter) (surrogates : Fin maxLayerHeight → Digest) :
    CanonicalGraphLabels := fun position =>
  match boundary parameter surrogates position with
  | none => 0
  | some value => (0 : BitVec 128) ++ value

theorem initialLabels_boundary (parameter : PublicParameter) (surrogates : Fin maxLayerHeight → Digest)
    (position : Position) (value : Digest) (hboundary : boundary parameter surrogates position = some value) :
    truncateHash (initialLabels parameter surrogates position) = value := by
  simp only [initialLabels, hboundary]
  change ((0 : BitVec 128) ++ value).extractLsb' 0 128 = value
  exact BitVec.extractLsb'_append_eq_right

/-- The precise address extracted from an outside-subtree forgery has one surrogate target
and no exempt canonical input in the retained graph. -/
theorem referenceTable_surrogate (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : ForsSecrets) (surrogates : Fin maxLayerHeight → Digest)
    (labels : CanonicalGraphLabels) (lay : Layer) (tree : TreeIndex)
    (level : Fin maxLayerHeight) (hpositive : 0 < level.val) (hlay : lay = topLayer)
    (htree : tree = rootTree) (hlower : keptHeight topLayer ≤ level.val) :
    referenceTable parameter otsSecret ftsSecret (active parameter) (boundary parameter surrogates)
      labels (hashDomainFields (.node lay tree level.val (boundaryIndex parameter level.val))) =
        some ⟨none, surrogates level⟩ := by
  rw [← boundaryPosition_domain parameter lay tree level hpositive]
  have hb := boundaryPosition_value parameter surrogates lay tree level hpositive hlay htree hlower
  exact referenceTable_boundary parameter otsSecret ftsSecret (active parameter)
    (boundary parameter surrogates) labels (boundaryPosition parameter lay tree level hpositive)
    (boundary_inactive parameter surrogates _ _ hb) _ hb

end FORS.Security.PrunedGraph

end

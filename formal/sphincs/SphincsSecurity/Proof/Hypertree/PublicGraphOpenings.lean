import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraphHonest
import SphincsSecurity.Proof.Hypertree.CanonicalProbeRouting
import SphincsSecurity.Proof.Fts.FtsProbeGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] instFintypePosition

theorem openingSibling_lt (height leaf level : Nat) (hlevel : level < height) (hleaf : leaf < 2 ^ height) :
    Nat.xor (leaf / 2 ^ level) 1 < 2 ^ height := by
  have hspan := FtsProbeSimulation.sibling_node_bound height leaf level hlevel hleaf
  have hpow : 1 ≤ (2 : Nat) ^ level := Nat.one_le_pow level 2 (by decide)
  nlinarith

def treeOpeningPosition (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (level : Fin maxLayerHeight) : Position :=
  let sibling : LeafIndex := ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
    openingSibling_lt maxLayerHeight leaf.val level.val level.isLt leaf.isLt⟩
  if level.val = 0 then .leaf lay tree sibling
  else .node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩ sibling

def ftsOpeningPosition (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (level : Fin ftsTreeHeight) : Position :=
  let sibling : FtsLeaf := ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
    openingSibling_lt ftsTreeHeight leaf.val level.val level.isLt leaf.isLt⟩
  if level.val = 0 then .ftsLeaf index tree sibling
  else .ftsNode index tree ⟨level.val - 1, by have := level.isLt; omega⟩ sibling

theorem treeOpeningPosition_bound (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    (treeOpeningPosition lay tree leaf level).TreeBound := by
  unfold treeOpeningPosition
  split_ifs with hzero
  · trivial
  · simp only [Position.TreeBound, show level.val - 1 + 1 = level.val by omega]
    exact FtsProbeSimulation.sibling_node_bound maxLayerHeight leaf.val level.val level.isLt leaf.isLt

theorem ftsOpeningPosition_bound (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (level : Fin ftsTreeHeight) :
    (ftsOpeningPosition index tree leaf level).TreeBound := by
  unfold ftsOpeningPosition
  split_ifs with hzero
  · trivial
  · simp only [Position.TreeBound, show level.val - 1 + 1 = level.val by omega]
    exact FtsProbeSimulation.sibling_node_bound ftsTreeHeight leaf.val level.val level.isLt leaf.isLt

theorem treeOpeningPosition_public (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    ¬CanonicalCoordinate.Hidden words disclosed (.graph (treeOpeningPosition lay tree leaf level)) := by
  unfold treeOpeningPosition
  split_ifs <;> simp only [CanonicalCoordinate.Hidden, not_false_eq_true]

theorem ftsOpeningPosition_public (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (level : Fin ftsTreeHeight) :
    ¬CanonicalCoordinate.Hidden words disclosed (.graph (ftsOpeningPosition index tree leaf level)) := by
  unfold ftsOpeningPosition
  split_ifs <;> simp only [CanonicalCoordinate.Hidden, not_false_eq_true]

def knownTreePath (known : Labels) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Fin maxLayerHeight → Digest :=
  fun level => if level.val < layerHeight lay then known (.graph (treeOpeningPosition lay tree leaf level)) else 0

def knownFtsPath (known : Labels) (index : Index) (leaves : IndexGroup → FtsLeaf) : FtsTree → Fin ftsTreeHeight → Digest :=
  fun tree level => known (.graph (ftsOpeningPosition index tree (leaves (ftsIndexOf tree)) level))

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)

theorem canonicalGraph_treeOpening (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (treeOpeningPosition lay tree leaf level)) =
      evalWithAnswerFn f (treeNode parameter lay tree (otsSecret lay tree) level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)) := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ (treeOpeningPosition_bound lay tree leaf level)]
  change honestValue f parameter otsSecret ftsSecret (treeOpeningPosition lay tree leaf level) = _
  unfold treeOpeningPosition
  split_ifs with hzero
  · rw [honestValue_leaf]
    simp only [hzero, honestNode]
  · rw [honestValue_node, show level.val - 1 + 1 = level.val by omega]
    rfl

theorem canonicalGraph_ftsOpening (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (level : Fin ftsTreeHeight) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (ftsOpeningPosition index tree leaf level)) =
      evalWithAnswerFn f (ftsNode parameter index tree (ftsSecret index tree) level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)) := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ (ftsOpeningPosition_bound index tree leaf level)]
  change honestValue f parameter otsSecret ftsSecret (ftsOpeningPosition index tree leaf level) = _
  unfold ftsOpeningPosition
  split_ifs with hzero
  · rw [honestValue_ftsLeaf]
    simp only [hzero, honestFtsNode]
  · rw [honestValue_ftsNode, show level.val - 1 + 1 = level.val by omega]
    rfl

theorem knownTreePath_eq (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known
      (CanonicalCoordinate.value otsSecret ftsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f)))
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    knownTreePath known lay tree leaf = evalWithAnswerFn f (treePath parameter lay tree (otsSecret lay tree) leaf) := by
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  funext level
  rw [knownTreePath]
  split_ifs
  · rw [hagrees _ (treeOpeningPosition_public words disclosed lay tree leaf level)]
    exact canonicalGraph_treeOpening parameter otsSecret ftsSecret f lay tree leaf level
  · rfl

theorem knownFtsPath_eq (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known
      (CanonicalCoordinate.value otsSecret ftsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f)))
    (index : Index) (leaves : IndexGroup → FtsLeaf) :
    knownFtsPath known index leaves = evalWithAnswerFn f (ftsOpen parameter index leaves (ftsSecret index)) := by
  simp only [ftsOpen, evalWithAnswerFn_sequenceFin]
  funext tree level
  rw [knownFtsPath, hagrees _ (ftsOpeningPosition_public words disclosed index tree (leaves (ftsIndexOf tree)) level)]
  exact canonicalGraph_ftsOpening parameter otsSecret ftsSecret f index tree (leaves (ftsIndexOf tree)) level

def knownFrontier (known : Labels) (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chain =>
    if hzero : (words lay tree leaf chain).val = 0 then known (.otsStart lay tree leaf chain)
    else known (.graph (.chain lay tree leaf chain
      ⟨(words lay tree leaf chain).val - 1, by
        have hdigit := (words lay tree leaf chain).isLt
        simp only [chainLength, winternitzBits] at hdigit ⊢
        omega⟩))

theorem knownFrontier_eq (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels)) :
    knownFrontier known words = canonicalGraphFrontier otsSecret labels words := by
  funext lay tree leaf chain
  rw [knownFrontier, canonicalGraphFrontier]
  split_ifs with hzero
  · exact hagrees _ (by simp only [CanonicalCoordinate.Hidden, hzero, lt_self_iff_false, not_false_eq_true])
  · apply hagrees
    simp only [CanonicalCoordinate.Hidden]
    omega

def knownRoot (known : Labels) : Digest :=
  known (.graph (.node topLayer rootTree ⟨maxLayerHeight - 1, by decide⟩ ⟨0, by positivity⟩))

theorem knownRoot_eq (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels)) :
    knownRoot known = canonicalGraphRoot labels :=
  hagrees _ (by simp only [CanonicalCoordinate.Hidden, not_false_eq_true])

end SphincsSecurity.Concrete

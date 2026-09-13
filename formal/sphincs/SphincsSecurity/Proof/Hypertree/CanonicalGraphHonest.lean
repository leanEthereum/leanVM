import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.CanonicalGraph
import SphincsSecurity.Proof.Hypertree.CanonicalSigningFrontier
namespace SphincsSecurity

namespace Position

def TreeBound : Position → Prop
  | .node _ _ level index => 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ maxLayerHeight
  | .ftsNode _ _ level index => 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ ftsTreeHeight
  | _ => True

theorem TreeBound.valid (position : Position) (h : position.TreeBound) : position.Valid := by
  cases position with
  | node lay tree level index =>
      have hpow : 0 < (2 : Nat) ^ level.val := pow_pos (by decide) _
      have hmul := Nat.mul_le_mul_right (index.val + 1) (show 2 ≤ 2 ^ (level.val + 1) by
        rw [pow_succ]; omega)
      change 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ maxLayerHeight at h
      change 2 * index.val + 1 < 2 ^ maxLayerHeight
      omega
  | ftsNode index tree level node =>
      have hpow : 0 < (2 : Nat) ^ level.val := pow_pos (by decide) _
      have hmul := Nat.mul_le_mul_right (node.val + 1) (show 2 ≤ 2 ^ (level.val + 1) by
        rw [pow_succ]; omega)
      change 2 ^ (level.val + 1) * (node.val + 1) ≤ 2 ^ ftsTreeHeight at h
      change 2 * node.val + 1 < 2 ^ ftsTreeHeight
      omega
  | chain | leaf | ftsLeaf | ftsRoots => trivial

private theorem treeBound_children_arithmetic (height level index : Nat)
    (h : 2 ^ (level + 1) * (index + 1) ≤ 2 ^ height) :
    2 ^ level * (2 * index + 1) ≤ 2 ^ height ∧
      2 ^ level * (2 * index + 1 + 1) ≤ 2 ^ height := by
  rw [pow_succ] at h
  constructor <;> nlinarith [Nat.zero_le (2 ^ level)]

theorem TreeBound.child {position child : Position} (h : position.TreeBound)
    (hchild : child ∈ position.children) : child.TreeBound := by
  cases position with
  | chain lay tree leaf chain step =>
      simp only [children] at hchild
      split_ifs at hchild with hstep
      · rw [List.mem_singleton] at hchild
        subst child
        trivial
      · simp at hchild
  | leaf lay tree leaf =>
      simp only [children, List.mem_ofFn] at hchild
      obtain ⟨chain, rfl⟩ := hchild
      trivial
  | node lay tree level index =>
      have hvalid : 2 * index.val + 1 < 2 ^ maxLayerHeight := TreeBound.valid _ h
      rw [children, dif_pos hvalid] at hchild
      split_ifs at hchild with hlevel
      · have bounds := treeBound_children_arithmetic maxLayerHeight level.val index.val h
        rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;>
          simp only [TreeBound, show level.val - 1 + 1 = level.val by omega] <;>
          first | exact bounds.1 | exact bounds.2
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;> trivial
  | ftsLeaf => simp [children] at hchild
  | ftsNode index tree level node =>
      have hvalid : 2 * node.val + 1 < 2 ^ ftsTreeHeight := TreeBound.valid _ h
      rw [children, dif_pos hvalid] at hchild
      split_ifs at hchild with hlevel
      · have bounds := treeBound_children_arithmetic ftsTreeHeight level.val node.val h
        rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;>
          simp only [TreeBound, show level.val - 1 + 1 = level.val by omega] <;>
          first | exact bounds.1 | exact bounds.2
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;> trivial
  | ftsRoots index =>
      simp only [children, List.mem_ofFn] at hchild
      obtain ⟨tree, rfl⟩ := hchild
      norm_num [TreeBound, ftsTreeHeight]

end Position

namespace Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem canonicalGraphLabels_eq_honest (f : QueryImpl HashSpec Id)
    (position : Position) (hbound : position.TreeBound) :
    canonicalGraphLabels parameter otsSecret ftsSecret f position =
      f (honestInput f parameter otsSecret ftsSecret position) := by
  induction hdepth : position.depth using Nat.strong_induction_on generalizing position with
  | h depth ih =>
      rw [canonicalGraphLabels_consistent]
      apply congrArg f
      apply canonicalGraphInput_eq_honest parameter otsSecret ftsSecret f position (hbound.valid position)
      intro child hchild
      have hlt : child.depth < depth := by
        rw [← hdepth]
        exact Position.depth_lt_of_mem_children hchild
      rw [ih child.depth hlt child (hbound.child hchild) rfl]
      rfl

theorem canonicalGraphLabels_chain (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (.chain lay tree leaf chain step)) =
      honestChain f parameter lay tree leaf chain (otsSecret lay tree leaf chain) (step.val + 1) := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ (by trivial)]
  exact honestValue_chain f parameter otsSecret ftsSecret lay tree leaf chain step

def canonicalGraphRoot (labels : CanonicalGraphLabels) : Digest :=
  truncateHash (labels (.node topLayer rootTree ⟨maxLayerHeight - 1, by decide⟩ ⟨0, by positivity⟩))

theorem canonicalGraphLabels_root (f : QueryImpl HashSpec Id) :
    canonicalGraphRoot (canonicalGraphLabels parameter otsSecret ftsSecret f) =
      evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) := by
  rw [canonicalGraphRoot, canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _
    (by norm_num [Position.TreeBound, maxLayerHeight])]
  change honestValue f parameter otsSecret ftsSecret _ = _
  rw [honestValue_node]
  rfl

def canonicalGraphFrontier (labels : CanonicalGraphLabels) (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chain =>
    if h : (words lay tree leaf chain).val = 0 then otsSecret lay tree leaf chain
    else truncateHash (labels (.chain lay tree leaf chain
      ⟨(words lay tree leaf chain).val - 1, by have := (words lay tree leaf chain).isLt; omega⟩))

theorem canonicalGraphLabels_frontier (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (root : Digest) :
    canonicalGraphFrontier otsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f) words =
      canonicalFrontierValues ⟨parameter, root, otsSecret, ftsSecret⟩ f words := by
  funext lay tree leaf chain
  simp only [canonicalGraphFrontier, canonicalFrontierValues]
  split_ifs with hzero
  · rw [hzero]
    simp [chainWalk]
  · rw [canonicalGraphLabels_chain]
    have hstep : (words lay tree leaf chain).val - 1 + 1 = (words lay tree leaf chain).val := by omega
    simp only [hstep, honestChain]

end Concrete

end SphincsSecurity

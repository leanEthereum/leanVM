import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.Bytes
/-!
# The positions of the honest key

Six of the eight hash domains name a structural position: a chain step, a one-time leaf, a node of a
layer's tree, a few-time leaf, a node of a few-time tree, and the hash of a forest's roots. Each has
one honest payload, built from the honest values at the positions below it, and the tweak determines
which position it is. The message digest and the encoding are the two that name none: their payload
is not a function of the key, and no honest value is defined at them.

`Position` is that index set, made finite by keeping the level and index fields inside the widths the
instance uses rather than in `Nat`. It over-approximates: a node above a short layer's root is a
position here and has no honest meaning, which costs nothing since every statement about positions is
either an inclusion or a count. What matters is that `parentOf` and `children` agree, since the
accounting charges a position's settling to its parent, and that no position has two parents.
-/

namespace SphincsSecurity

open OracleComp

/-- A structural position of the honest key. A `node` at `level` is the node of actual level
`level + 1`, the leaves being the `leaf` positions; likewise for `ftsNode`. -/
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight) (nodeIdx : FtsLeaf)
  | ftsRoots (index : Index)
  deriving DecidableEq, Fintype

namespace Position

/-- The hash domain a position is hashed at. -/
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .ftsLeaf index tree leafIdx => HashDomain.ftsLeaf index tree leafIdx
  | .ftsNode index tree level nodeIdx => HashDomain.ftsNode index tree (level.val + 1) nodeIdx.val
  | .ftsRoots index => HashDomain.ftsRoots index

theorem domain_inRange (p : Position) : p.domain.InRange := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [maxLayerHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | ftsNode index tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [ftsTreeHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | chain => exact (trivial : True)
  | leaf => exact (trivial : True)
  | ftsLeaf => exact (trivial : True)
  | ftsRoots => exact (trivial : True)

theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]

/-- The last chain step, the one whose answer is the chain's endpoint. -/
def lastChainStep : ChainStep := ⟨chainLength - 2, by decide⟩

/-- The positions whose values the payload at this one is built from. -/
def children : Position → List Position
  | .chain lay tree leafIdx chainIdx step =>
      if h : 0 < step.val then [.chain lay tree leafIdx chainIdx ⟨step.val - 1, by omega⟩] else []
  | .leaf lay tree leafIdx =>
      List.ofFn fun chainIdx : ChainIndex => .chain lay tree leafIdx chainIdx lastChainStep
  | .node lay tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight then
        if hlevel : 0 < level.val then
          [.node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
            .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsLeaf _ _ _ => []
  | .ftsNode index tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ ftsTreeHeight then
        if hlevel : 0 < level.val then
          [.ftsNode index tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .ftsNode index tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.ftsLeaf index tree ⟨2 * nodeIdx.val, by omega⟩,
            .ftsLeaf index tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsRoots index =>
      List.ofFn fun tree : FtsTree =>
        .ftsNode index tree ⟨ftsTreeHeight - 1, by decide⟩ ⟨0, by positivity⟩

/-- The widest payload of the instance is a one-time leaf's `v = 42` chain endpoints. -/
theorem children_length_le (p : Position) : p.children.length ≤ numChains := by
  cases p <;> simp only [children] <;> (try split_ifs) <;> simp [numChains, ftsTrees]

/-! ### Children and parent agree

No position has two parents, which is what keeps the accounting's charge on a position's settling
from being paid twice, and every child of a position is charged there. -/

/-- A measure the payload recursion descends: a position's children are strictly below it. -/
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .ftsLeaf _ _ _ => 0
  | .ftsNode _ _ level _ => 1 + level.val
  | .ftsRoots _ => 1 + ftsTreeHeight

theorem depth_lt_of_mem_children {c d : Position} (hmem : c ∈ d.children) :
    c.depth < d.depth := by
  cases d with
  | chain lay tree leafIdx chainIdx step =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | leaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨chainIdx, hmem⟩ := hmem
      subst hmem
      simp [depth, lastChainStep, chainLength, winternitzBits]
  | node lay tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsLeaf => simp [children] at hmem
  | ftsNode index tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsRoots =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨tree, hmem⟩ := hmem
      subst hmem
      simp [depth, ftsTreeHeight]

end Position

end SphincsSecurity

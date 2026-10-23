/-
  LeanVM.Protocol.ToArkLib.Merkle

  Binary Merkle trees over an abstract hash: the root of `2^k` leaves, the authentication path of
  a leaf, and the verifier's recomputation of the root from a leaf and a path, with the two facts
  a compiler to Merkle-committed oracles needs: an honest path is accepted, and two accepted paths
  to one root at one index with different leaves exhibit a collision. Candidate for ArkLib.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# Merkle trees

A tree over `2^k` leaves is built level by level: the leaves are hashed by `hashLeaf`, and each
parent is `hashPair` of its two children, the left child first. The authentication path of a
leaf is the list of its siblings, leaf level first; a verifier recomputes the root by climbing
the path, placing the running node on the left at an even index and on the right at an odd one,
and compares it with the root it holds, after checking that the path has one sibling per level
of the announced depth and that the index is below the leaf count. Without the first check a
row whose bytes are two child digests opens as a leaf one level short, since nothing separates
the leaf hash from the node hash; without the second an index is read modulo the leaf count.

Nothing here depends on the hash: `verify_path` is an identity of definitions, and
`collision_of_rootOfPath_eq` turns two accepted openings that disagree on the leaf into a
collision of `hashLeaf` or of `hashPair`, which is what a collision-resistance assumption on the
hash turns into binding of the commitment.
-/

namespace LeanVM.Protocol.MerkleTree

@[expose] public section

variable {L D : Type} (hashLeaf : L → D) (hashPair : D → D → D)

/-! ## The tree -/

/-- The parents of a level of `2^(k+1)` nodes: adjacent pairs hashed, the left child first. -/
def parents {k : ℕ} (level : Vector D (2 ^ (k + 1))) : Vector D (2 ^ k) :=
  Vector.ofFn fun j ↦
    hashPair (level[2 * j.val]'(by have := j.isLt; rw [Nat.pow_succ]; omega))
      (level[2 * j.val + 1]'(by have := j.isLt; rw [Nat.pow_succ]; omega))

/-- The root of a level of `2^k` digests. -/
def rootOfLevel : (k : ℕ) → Vector D (2 ^ k) → D
  | 0, level => level[0]
  | k + 1, level => rootOfLevel k (parents hashPair level)

/-- The root of `2^k` leaves. -/
def root {k : ℕ} (leaves : Vector L (2 ^ k)) : D :=
  rootOfLevel hashPair k (leaves.map hashLeaf)

/-- The index of the node sharing a parent with node `i`: `i + 1` at an even index, `i - 1` at
an odd one (`i ^^^ 1`). -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

theorem sibling_lt {k i : ℕ} (hi : i < 2 ^ (k + 1)) : sibling i < 2 ^ (k + 1) := by
  unfold sibling; rw [Nat.pow_succ] at *; split <;> omega

theorem div_two_lt {k i : ℕ} (hi : i < 2 ^ (k + 1)) : i / 2 < 2 ^ k := by
  rw [Nat.pow_succ] at hi; omega

/-- The authentication path of node `i` of a level of `2^k` nodes: its sibling at this level,
then the path of its parent. -/
def pathOfLevel : (k : ℕ) → Vector D (2 ^ k) → Fin (2 ^ k) → List D
  | 0, _, _ => []
  | k + 1, level, i =>
    level[sibling i.val]'(sibling_lt i.isLt) ::
      pathOfLevel k (parents hashPair level) ⟨i.val / 2, div_two_lt i.isLt⟩

/-- The authentication path of leaf `i`: its siblings from the leaf level up to the root. -/
def path {k : ℕ} (leaves : Vector L (2 ^ k)) (i : Fin (2 ^ k)) : List D :=
  pathOfLevel hashPair k (leaves.map hashLeaf) i

/-! ## The verifier -/

/-- Climb a path from a node at index `i`: at an even index the node is the left child of the
next node, at an odd one the right child. -/
def climb (node : D) (i : ℕ) : List D → D
  | [] => node
  | s :: rest => climb (if i % 2 = 0 then hashPair node s else hashPair s node) (i / 2) rest

/-- The root that a leaf at index `i` and a path claim. -/
def rootOfPath (leaf : L) (i : ℕ) (path : List D) : D :=
  climb hashPair (hashLeaf leaf) i path

/-- Accept a leaf at index `i` under the root of a tree of depth `k`: the path has one sibling
per level, the index is below the leaf count, and the path climbs to the root. -/
def verify [DecidableEq D] (k : ℕ) (root : D) (i : ℕ) (leaf : L) (path : List D) : Bool :=
  decide (path.length = k ∧ i < 2 ^ k ∧ rootOfPath hashLeaf hashPair leaf i path = root)

/-! ## An honest path is accepted -/

theorem getElem_parents {k : ℕ} (level : Vector D (2 ^ (k + 1))) (j : ℕ) (hj : j < 2 ^ k) :
    (parents hashPair level)[j] =
      hashPair (level[2 * j]'(by rw [Nat.pow_succ]; omega))
        (level[2 * j + 1]'(by rw [Nat.pow_succ]; omega)) := by
  simp [parents]

/-- Climbing the path of a node reaches the root of its level. -/
theorem climb_pathOfLevel :
    ∀ (k : ℕ) (level : Vector D (2 ^ k)) (i : Fin (2 ^ k)),
      climb hashPair level[i] i (pathOfLevel hashPair k level i) = rootOfLevel hashPair k level
  | 0, level, i => by
    obtain ⟨i, hi⟩ := i
    have : i = 0 := by simp at hi; omega
    subst this
    simp [pathOfLevel, climb, rootOfLevel]
  | k + 1, level, i => by
    rw [pathOfLevel, climb, rootOfLevel, ← climb_pathOfLevel k (parents hashPair level)]
    congr 1
    · simp only [Fin.getElem_fin, getElem_parents]
      unfold sibling
      split
      · simp only [show 2 * (i.val / 2) = i.val by omega]
      · simp only [show 2 * (i.val / 2) = i.val - 1 by omega, show i.val - 1 + 1 = i.val by omega]
    · rfl

/-- A path has one sibling per level. -/
theorem length_pathOfLevel :
    ∀ (k : ℕ) (level : Vector D (2 ^ k)) (i : Fin (2 ^ k)),
      (pathOfLevel hashPair k level i).length = k
  | 0, _, _ => rfl
  | k + 1, level, i => by simp [pathOfLevel, length_pathOfLevel k]

theorem length_path {k : ℕ} (leaves : Vector L (2 ^ k)) (i : Fin (2 ^ k)) :
    (path hashLeaf hashPair leaves i).length = k :=
  length_pathOfLevel hashPair k (leaves.map hashLeaf) i

/-- The path of a leaf climbs to the root of the tree. -/
theorem rootOfPath_path {k : ℕ} (leaves : Vector L (2 ^ k)) (i : Fin (2 ^ k)) :
    rootOfPath hashLeaf hashPair leaves[i] i (path hashLeaf hashPair leaves i) =
      root hashLeaf hashPair leaves := by
  have := climb_pathOfLevel hashPair k (leaves.map hashLeaf) i
  simpa [rootOfPath, path, root] using this

/-- Completeness: the verifier accepts every leaf of a tree under its root with its path. -/
theorem verify_path [DecidableEq D] {k : ℕ} (leaves : Vector L (2 ^ k)) (i : Fin (2 ^ k)) :
    verify hashLeaf hashPair k (root hashLeaf hashPair leaves) i leaves[i]
      (path hashLeaf hashPair leaves i) = true :=
  decide_eq_true
    ⟨length_path hashLeaf hashPair leaves i, i.isLt, rootOfPath_path hashLeaf hashPair leaves i⟩

/-! ## Two accepted openings that disagree exhibit a collision -/

/-- Two distinct pairs with the same digest. -/
def PairCollision : Prop := ∃ a b a' b', (a, b) ≠ (a', b') ∧ hashPair a b = hashPair a' b'

/-- Two distinct leaves with the same digest. -/
def LeafCollision : Prop := ∃ a b, a ≠ b ∧ hashLeaf a = hashLeaf b

theorem pairCollision_of_climb_eq :
    ∀ (p p' : List D) (d d' : D) (i : ℕ), p.length = p'.length → d ≠ d' →
      climb hashPair d i p = climb hashPair d' i p' → PairCollision hashPair
  | [], [], _, _, _, _, hne, h => absurd h hne
  | [], _ :: _, _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _, _ => by simp at hl
  | s :: p, s' :: p', d, d', i, hl, hne, h => by
    simp only [climb] at h
    by_cases hnode : (if i % 2 = 0 then hashPair d s else hashPair s d) =
        if i % 2 = 0 then hashPair d' s' else hashPair s' d'
    · split at hnode
      · exact ⟨d, s, d', s', fun e ↦ hne (Prod.mk.inj e).1, hnode⟩
      · exact ⟨s, d, s', d', fun e ↦ hne (Prod.mk.inj e).2, hnode⟩
    · exact pairCollision_of_climb_eq p p' _ _ (i / 2) (by simpa using hl) hnode h

/-- Two paths of equal length from different leaves at the same index that reach the same root
exhibit a collision of the leaf hash or of the pair hash. -/
theorem collision_of_rootOfPath_eq {leaf leaf' : L} {i : ℕ} {p p' : List D}
    (hl : p.length = p'.length) (hne : leaf ≠ leaf')
    (h : rootOfPath hashLeaf hashPair leaf i p = rootOfPath hashLeaf hashPair leaf' i p') :
    LeafCollision hashLeaf ∨ PairCollision hashPair := by
  by_cases hd : hashLeaf leaf = hashLeaf leaf'
  · exact Or.inl ⟨leaf, leaf', hne, hd⟩
  · exact Or.inr (pairCollision_of_climb_eq hashPair p p' _ _ i hl hd h)

/-- Two accepted openings of one root at one index and depth with different leaves exhibit a
collision. -/
theorem collision_of_verify [DecidableEq D] {k : ℕ} {root : D} {leaf leaf' : L} {i : ℕ}
    {p p' : List D} (hne : leaf ≠ leaf')
    (h : verify hashLeaf hashPair k root i leaf p = true)
    (h' : verify hashLeaf hashPair k root i leaf' p' = true) :
    LeafCollision hashLeaf ∨ PairCollision hashPair := by
  simp only [verify, decide_eq_true_eq] at h h'
  obtain ⟨hl, _, h⟩ := h
  obtain ⟨hl', _, h'⟩ := h'
  exact collision_of_rootOfPath_eq hashLeaf hashPair (hl.trans hl'.symm) hne (h.trans h'.symm)

end
end LeanVM.Protocol.MerkleTree

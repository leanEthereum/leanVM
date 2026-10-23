/-
  LeanVM.Protocol.Merkle

  leanVM's Merkle trees: the generic tree over BLAKE2s-256 with leaves of `K` words, the leaf
  image with its zero prefix, and the verifier's path check.
-/

module

public import LeanVM.Protocol.Blake2sHash
public import LeanVM.Protocol.ToArkLib.Merkle

/-!
# leanVM's Merkle trees

The committer's tree is `crates/pcs/src/merkle.rs:50-61` (`merkle_tree`) of the
pinned leanVM (`127510d14c98ade4e8a97646c44fa7f1ff5e752d`): `2^k` leaves hashed by `hash_leaf`
on their little-endian words, parents by `hash_pair`, left child first, up to one root. A leaf is
a row of `K` words; a row narrower than the leaf width is hashed as its image `zeros ‖ row`, the
zero prefix being what a commitment with absent lanes leaves out of the proof
(`crates/verifier/src/merkle.rs:97-101`; `MerkleBuilder`, `pcs/src/merkle.rs:63-72`). The
verifier's check is `MerklePath::root` (`crates/verifier/src/merkle.rs:58-70`), climb the sibling
path from the leaf's digest, the running node on the left at an even index, and compare with the
root (`crates/verifier/src/transcript.rs:162-164`, `:174-177`), under the per-row checks of
`PrunedMerklePaths::expand` (`merkle.rs:87-93`): the row has the announced width, the path has
one sibling per level of the tree, and the index is below the leaf count. The pruned form in which
a proof carries the paths of one level's queries (the octopus) is the proof object's, not this
module's.

`merkleVerify_merklePath` is the completeness of the check; `collision_of_merkleVerify` is the
binding half, two accepted openings that disagree exhibit a collision of `hashWords` or
`hashPair`, both instances of the generic facts of `LeanVM.Protocol.ToArkLib.Merkle`.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters Blake2sHash

@[expose] public section

/-- The leaf image of a row of at most `leafWords` words: the row right-aligned, after a zero
prefix (`leaf_image`). A longer row comes back unchanged and fails the width check of
`merkleVerify`, where the pinned opener rejects it before the image is taken. -/
def leafImage (leafWords : ℕ) (row : List K) : List K :=
  List.replicate (leafWords - row.length) 0 ++ row

/-- The Merkle root of `2^k` leaves of `K` words (`merkle_tree`). -/
def merkleRoot {k : ℕ} (leaves : Vector (List K) (2 ^ k)) : Digest :=
  MerkleTree.root hashWords hashPair leaves

/-- The authentication path of leaf `i`: its siblings, leaf level first. -/
def merklePath {k : ℕ} (leaves : Vector (List K) (2 ^ k)) (i : Fin (2 ^ k)) : List Digest :=
  MerkleTree.path hashWords hashPair leaves i

/-- The verifier's check for a tree of `2 ^ depth` leaves of `leafWords` words: the row has the
announced width, the path one sibling per level, the index is below the leaf count, and the
path climbs to `root` (`PrunedMerklePaths::open`'s row checks, then `RawMerklePath::root`). -/
def merkleVerify (depth leafWords : ℕ) (root : Digest) (index : ℕ) (leaf : List K)
    (path : List Digest) : Bool :=
  decide (leaf.length = leafWords) &&
    @MerkleTree.verify _ _ hashWords hashPair Digest.decEq depth root index leaf path

/-- Completeness: every leaf of a tree is accepted under its root with its path, at the tree's
depth and the leaf's width. -/
theorem merkleVerify_merklePath {k leafWords : ℕ} (leaves : Vector (List K) (2 ^ k))
    (i : Fin (2 ^ k)) (hw : leaves[i].length = leafWords) :
    merkleVerify k leafWords (merkleRoot leaves) i leaves[i] (merklePath leaves i) = true := by
  unfold merkleVerify
  rw [hw, decide_eq_true rfl, Bool.true_and]
  exact @MerkleTree.verify_path _ _ hashWords hashPair Digest.decEq k leaves i

/-- Two accepted openings of one root at one index, depth and width with different leaves
exhibit a collision of the leaf hash or of the node hash. -/
theorem collision_of_merkleVerify {depth leafWords : ℕ} {root : Digest} {leaf leaf' : List K}
    {i : ℕ} {p p' : List Digest} (hne : leaf ≠ leaf')
    (h : merkleVerify depth leafWords root i leaf p = true)
    (h' : merkleVerify depth leafWords root i leaf' p' = true) :
    MerkleTree.LeafCollision hashWords ∨ MerkleTree.PairCollision hashPair := by
  simp only [merkleVerify, Bool.and_eq_true] at h h'
  exact @MerkleTree.collision_of_verify _ _ hashWords hashPair Digest.decEq depth root leaf leaf'
    i p p' hne h.2 h'.2

end
end LeanVM.Protocol

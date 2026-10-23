import LeanVM.Protocol.Merkle

/-!
# Merkle tree tests

A four-leaf tree of two-word leaves against a tree computed with CPython's `hashlib.blake2s`
(leaf `q` holds the words `2q + 1, 2q + 2`): the leaf digests, the root, and the path of leaf 2;
the verifier accepting that path, and rejecting a tampered sibling, a wrong index, an index at
or above the leaf count, a tampered row, an over-wide row, a short path, a long path, a wrong
depth and a wrong root (after the test `malformed_phases_are_rejected` of
`crates/fiat_shamir/src/merkle.rs` at leanVM `a386121f`, removed at `127510d1` with the Rust
verifier's Merkle code there); a node opened as a leaf, which the depth and width checks alone
reject; the zero-prefix leaf image; and the sibling index as `i ^^^ 1`, the form the pinned
prover uses (`crates/fiat_shamir/src/merkle.rs:84, 87` at `127510d1`; the verifier's
`(leaf >> lvl) ^ 1`, `merkle.rs:218` at `a386121f`, is removed, and the verifier of `127510d1`
pairs an even `index` with `index | 1`, `crates/verifier/src/merkle.rs:116`).
-/

namespace LeanVMTests.Protocol.Merkle

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash

/-- The word `n`. -/
def w (n : ℕ) : K := K.ofBits n

/-- Four leaves of two words each. -/
def leaves : Vector (List K) (2 ^ 2) := #v[[w 1, w 2], [w 3, w 4], [w 5, w 6], [w 7, w 8]]

def leaf0 : Digest :=
  #v[0x6b8928f2, 0x12389f83, 0xe4753c2b, 0x44f83b7f, 0x926dae68, 0xa0cb51b5, 0x1828562e, 0x44a89c61]

def leaf3 : Digest :=
  #v[0x9bab6c86, 0x345166bc, 0x5730c074, 0xc2393427, 0x9ef39974, 0x6dfecedf, 0xbd896888, 0x73752516]

/-- The parent of leaves 0 and 1. -/
def node01 : Digest :=
  #v[0x01a94e81, 0x0420c37d, 0xb019f25c, 0xdde39305, 0xfd847b9b, 0x4ca593a1, 0x94752d9b, 0x5860fd80]

def root : Digest :=
  #v[0x7e356111, 0x24253a30, 0x0b7ce2b6, 0xafccea2e, 0xc18c3ac5, 0x780bb6f6, 0xa9d96af7, 0x34ae5f2d]

/-- The path of leaf 2: its sibling leaf 3, then the parent of leaves 0 and 1. -/
def path2 : List Digest := [leaf3, node01]

/-! ## The honest tree -/

def leaf2 : Digest :=
  #v[0xeacefdb4, 0x9e397c69, 0xbcf9f243, 0xc7f40b56, 0x826da590, 0x3bb84405, 0xe99b0a9f, 0x03750514]

#guard hashWords [w 1, w 2] = leaf0
#guard hashWords [w 5, w 6] = leaf2
#guard hashWords [w 7, w 8] = leaf3
#guard hashPair leaf0 (hashWords [w 3, w 4]) = node01
#guard merkleRoot leaves = root
#guard merklePath leaves ⟨2, by decide⟩ = path2
#guard merkleVerify 2 2 root 2 [w 5, w 6] path2 = true

/-- The same acceptance, decided in the kernel. -/
example : merkleVerify 2 2 root 2 [w 5, w 6] path2 = true := by decide +kernel

/-! ## Mutations rejected -/

/- A tampered sibling. -/
#guard merkleVerify 2 2 root 2 [w 5, w 6] [leaf3.set 0 (leaf3[0] ^^^ 1), node01] = false

/- The right leaf at the wrong index: the sibling order flips. -/
#guard merkleVerify 2 2 root 3 [w 5, w 6] path2 = false

/- An index at or above the leaf count: `6` and `10` climb leaf 2's path bit for bit and would
reach the root without the range check. -/
#guard merkleVerify 2 2 root 6 [w 5, w 6] path2 = false
#guard merkleVerify 2 2 root 10 [w 5, w 6] path2 = false

/- A tampered row. -/
#guard merkleVerify 2 2 root 2 [w 5, w 7] path2 = false

/- A row wider than the leaf, bare and as its image. -/
#guard merkleVerify 2 2 root 2 [w 5, w 6, w 7] path2 = false
#guard merkleVerify 2 2 root 2 (leafImage 2 [w 5, w 6, w 7]) path2 = false

/- A path one sibling short, and one sibling long. -/
#guard merkleVerify 2 2 root 2 [w 5, w 6] [node01] = false
#guard merkleVerify 2 2 root 2 [w 5, w 6] [leaf3, node01, node01] = false

/- A wrong depth announced for the right path. -/
#guard merkleVerify 1 2 root 2 [w 5, w 6] path2 = false
#guard merkleVerify 3 2 root 2 [w 5, w 6] path2 = false

/- A wrong root. -/
#guard merkleVerify 2 2 (root.set 0 0) 2 [w 5, w 6] path2 = false

/-! ## A node opened as a leaf -/

/-- The eight words whose bytes are the digests of leaves 2 and 3: as a row they hash to the
parent of those leaves, since a leaf of eight words and a pair of digests are the same 64 bytes
to BLAKE2s. -/
def nodeAsLeaf : List K :=
  [ofWords leaf2[0] leaf2[1], ofWords leaf2[2] leaf2[3], ofWords leaf2[4] leaf2[5],
   ofWords leaf2[6] leaf2[7], ofWords leaf3[0] leaf3[1], ofWords leaf3[2] leaf3[3],
   ofWords leaf3[4] leaf3[5], ofWords leaf3[6] leaf3[7]]

#guard hashWords nodeAsLeaf = hashPair leaf2 leaf3

/- So a one-element path from it reaches the root, and only the depth and the width reject the
opening against the four-leaf tree of two-word leaves; against a two-leaf tree of eight-word
leaves it is the honest opening of leaf 1. -/
#guard merkleVerify 2 2 root 1 nodeAsLeaf [node01] = false
#guard merkleVerify 1 8 root 1 nodeAsLeaf [node01] = true

/-! ## The leaf image and the sibling index -/

/- A two-word row in a four-word leaf: two zero words first. -/
#guard leafImage 4 [w 7, w 8] = [0, 0, w 7, w 8]

/- Its digest, from `hashlib` on the 32 bytes `0 … 0, 07, 0 …, 08, 0 …`. -/
#guard hashWords (leafImage 4 [w 7, w 8]) =
  #v[0x3b711e04, 0xe64bb3a0, 0x1dee79f2, 0x378ad753, 0xbb717a8c, 0xd0e4ccc2, 0x66e2f70e, 0xb9a04311]

/- A row already of the leaf width is unchanged. -/
#guard leafImage 2 [w 7, w 8] = [w 7, w 8]

example : ∀ i < 16, MerkleTree.sibling i = i ^^^ 1 := by decide

end LeanVMTests.Protocol.Merkle

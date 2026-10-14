import EthCryptographySpecs.Xmss.Ots

/-!
# `Xmss.Merkle`

The Merkle tree over the one-time keys, one leaf per epoch.

A signature carries its leaf's co-path: the sibling of every node on the way up.

```text
level 2                 root
                      /      \
level 1          n_0            n_1
                /   \          /   \
level 0     l_0     l_1     l_2     l_3

signed leaf l_2 (epoch 2)
co-path     l_3 on level 0, then n_0 on level 1
```
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Nodes

A node sits at a level and a node index:

- The level is the height above the leaves, so leaves are on level 0.
- The node index counts the nodes of one level from the left, starting at 0.

Node `j` on level `l + 1` has children `2j` and `2j + 1` on level `l`. -/

/-- The parent of two nodes, hashed under its own place in the tree.

# Arguments

- `level`: the parent's level, at least 1.
- `index`: the parent's node index on that level. -/
def merkleNode (pp : PublicParam) (level index : Nat) (left right : Digest) :
    Digest :=
  -- The payload is the left child, then the right child.
  tweakHash pp .merkle (UInt32.ofNat level) (UInt32.ofNat index)
    (packBytes left ++ packBytes right)

/-- A node the key's epochs never reach, derived from the secret seed.

# Arguments

- `level`: the node's level.
- `index`: the node's index on that level. -/
def fillerNode (pp : PublicParam) (seed : Seed) (level index : Nat) : Digest :=
  -- Deriving it keeps the unsigned epochs hidden and costs no storage.
  tweakHash pp .filler (UInt32.ofNat level) (UInt32.ofNat index)
    (packBytes seed)

/-! ## The tree -/

/-- What fixes every node of a key's tree, once the leaves are given.

A key signs at the epochs of its range, and nowhere else. -/
structure TreeParams where
  /-- The public parameter every node of this tree is hashed under. -/
  publicParam : PublicParam
  /-- The secret the filler nodes are derived from. -/
  seed : Seed
  /-- The first epoch the key signs at. -/
  epochStart : Epoch
  /-- The last epoch the key signs at. -/
  epochEnd : Epoch
  /-- The range holds at least one epoch. -/
  epochStart_le_epochEnd : epochStart ≤ epochEnd

/-- Whether the subtree at `index` on `level` holds an epoch of the key. -/
def TreeParams.covers (tp : TreeParams) (level index : Nat) : Bool :=
  -- A node on `level` spans the epochs whose leading bits are `index`.
  --
  -- So shifting the two end epochs the same way brackets the nodes reached.
  tp.epochStart.toNat >>> level ≤ index
    && index ≤ tp.epochEnd.toNat >>> level

/-- The node at `index` on `level`, over the given leaves. -/
def TreeParams.node (tp : TreeParams) (leaves : Nat → Digest)
    (level index : Nat) : Digest :=
  -- Testing the range first cuts an unused subtree off at its top.
  --
  -- A key covering `R` epochs reaches `O(R + 32)` nodes, never `2 ^ 32`.
  if tp.covers level index then
    match level with
    -- One leaf per epoch, and the epoch is the leaf's index.
    | 0 => leaves index
    -- The two children of `index` on `level + 1` are `2 * index` and one more.
    | l + 1 => merkleNode tp.publicParam (l + 1) index
        (tp.node leaves l (2 * index)) (tp.node leaves l (2 * index + 1))
  else
    fillerNode tp.publicParam tp.seed level index

/-- The root of the tree: half of the public key. -/
def TreeParams.root (tp : TreeParams) (leaves : Nat → Digest) : Digest :=
  tp.node leaves LOG_LIFETIME 0

/-! ## The authentication path -/

/-- The sibling of the path node at `level`: its parent's other child. -/
def siblingIndex (epoch level : Nat) : Nat :=
  -- Shifting names the path node, flipping its bottom bit names the sibling.
  (epoch >>> level) ^^^ 1

/-- The co-path of the leaf at `epoch`, from the leaf upward. -/
def TreeParams.authPath (tp : TreeParams) (leaves : Nat → Digest)
    (epoch : Epoch) : Vector Digest LOG_LIFETIME :=
  Vector.ofFn fun level => tp.node leaves level (siblingIndex epoch.toNat level)

/-! ## Computing the root from a path -/

namespace Internal

/-- Fold the sibling at `level` into the node the verifier holds. -/
def climbStep (pp : PublicParam) (epoch level : Nat)
    (current sibling : Digest) : Digest :=
  -- Bit `level` of the epoch says which child of its parent the path node is.
  if (epoch >>> level) % 2 == 0 then
    merkleNode pp (level + 1) (epoch >>> (level + 1)) current sibling
  else
    merkleNode pp (level + 1) (epoch >>> (level + 1)) sibling current

/-- Climb the bottom `levels` levels of the path, starting from the leaf. -/
def climbUpto (pp : PublicParam) (epoch : Nat)
    (path : Vector Digest LOG_LIFETIME) (levels : Nat)
    (hl : levels ≤ LOG_LIFETIME) (leaf : Digest) : Digest :=
  match levels with
  | 0 => leaf
  -- The last step folds in the sibling at `l`, after climbing the `l` below it.
  | l + 1 => climbStep pp epoch l
      (climbUpto pp epoch path l (by omega) leaf) (path[l]'(by omega))

end Internal

/-- The root an authentication path reaches from a leaf. -/
def computeRoot (pp : PublicParam) (epoch : Epoch)
    (path : Vector Digest LOG_LIFETIME) (leaf : Digest) : Digest :=
  Internal.climbUpto pp epoch.toNat path LOG_LIFETIME (Nat.le_refl _) leaf

end EthCryptographySpecs.Xmss

import EthCryptographySpecs.Xmss.Errors
import EthCryptographySpecs.Xmss.Verify

/-!
# `Xmss.KeyGen`

Key generation.

The secret key is a seed and an epoch range, nothing more.

Everything else is recomputed from them: parameter, chain values, nodes.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## The secret key -/

/-- A seed, and the epochs it signs at. -/
structure SecretKey where
  /-- The master secret every other secret is derived from. -/
  seed : Seed
  /-- The first epoch the key signs at. -/
  epochStart : Epoch
  /-- The last epoch the key signs at. -/
  epochEnd : Epoch
  /-- The range holds at least one epoch. -/
  epochStart_le_epochEnd : epochStart ≤ epochEnd

/-! ## Derivations from the seed

The construction paper samples these values at random.

Here they are derived from the seed, so the seed alone regenerates the key. -/

/-- The public parameter: `Th(0^16, tweak(parameter, 0, 0), seed)`.

The all-zero parameter stands in for the one being derived. -/
def SecretKey.publicParam (sk : SecretKey) : PublicParam :=
  tweakHash (Vector.replicate PUBLIC_PARAM_LEN 0) .parameter 0 0
    (packBytes sk.seed)

/-- The starting value of each chain at an epoch.

Chain `i` starts at `Th(P, tweak(prf, i, epoch), seed)`. -/
def otsSecretKey (pp : PublicParam) (seed : Seed) (epoch : Epoch) :
    Vector Digest V :=
  Vector.ofFn fun i =>
    tweakHash pp .prf (UInt32.ofNat i.val) epoch (packBytes seed)

/-- The Merkle leaf of each epoch: its one-time public key, hashed. -/
def SecretKey.leaves (sk : SecretKey) (epoch : Nat) : Digest :=
  let pp := sk.publicParam
  -- Leaf indices are epochs, so the conversion never wraps.
  let ep := UInt32.ofNat epoch
  otsLeaf pp ep (otsPublicKey pp ep (otsSecretKey pp sk.seed ep))

/-- The Merkle tree the key signs under. -/
def SecretKey.tree (sk : SecretKey) : TreeParams where
  publicParam := sk.publicParam
  seed := sk.seed
  epochStart := sk.epochStart
  epochEnd := sk.epochEnd
  epochStart_le_epochEnd := sk.epochStart_le_epochEnd

/-- The public key: the root over the key's leaves, with its parameter. -/
def SecretKey.publicKey (sk : SecretKey) : PublicKey where
  merkleRoot := sk.tree.root sk.leaves
  publicParam := sk.publicParam

/-! ## Key generation -/

/-- The key pair grown from a seed, signing at the epochs of a range.

Rejects an empty range. -/
def keyGen (seed : Seed) (epochStart epochEnd : Epoch) :
    Except XmssError (SecretKey × PublicKey) :=
  if h : epochStart ≤ epochEnd then
    let sk : SecretKey := ⟨seed, epochStart, epochEnd, h⟩
    .ok (sk, sk.publicKey)
  else
    .error (.invalidEpochRange epochStart epochEnd)

end EthCryptographySpecs.Xmss

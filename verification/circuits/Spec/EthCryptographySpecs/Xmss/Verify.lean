import EthCryptographySpecs.Xmss.Encoding
import EthCryptographySpecs.Xmss.Merkle

/-!
# `Xmss.Verify`

Signature verification.

# Cost

A constant 133 hashes, whatever the message:

- Encoding: 1 hash of the message and the randomizer.
- Chains: 99 hashes.
  - Chain `i` walks `7 - x_i` steps, and the 42 digits always sum to 195.
  - So the steps total 42 * 7 - 195 = 99.
- Leaf: 1 hash of the 42 recovered public values.
- Root: 32 hashes, one parent per level from the leaf up.

A fixed count is what keeps the aggregation circuit a fixed size.

Nothing here needs to be constant time: every value it reads is public.
-/

namespace EthCryptographySpecs.Xmss

open EthCryptographySpecs.Xmss.Constants

/-! ## Keys and signatures -/

/-- What a verifier knows about a signer. -/
structure PublicKey where
  /-- The root of the Merkle tree over the signer's one-time keys. -/
  merkleRoot : Digest
  /-- The call site every hash of this key is made under. -/
  publicParam : PublicParam
  deriving DecidableEq

/-- A one-time signature, plus the path from its leaf to the root. -/
structure Signature where
  /-- One element per chain, revealed at the height its digit names. -/
  chainElements : Vector Digest V
  /-- The randomizer under which the message encodes. -/
  randomness : Randomness
  /-- The leaf's co-path, from the leaf upward. -/
  merklePath : Vector Digest LOG_LIFETIME
  deriving DecidableEq

/-! ## Verification -/

/-- Whether a signature signs a message at an epoch under a public key.

A yes or a no, never a reason.

Which step rejected a well-formed signature carries no consensus meaning. -/
def verify (pk : PublicKey) (msg : Message) (sig : Signature) (epoch : Epoch) :
    Bool :=
  let pp := pk.publicParam
  -- Step 1: recompute the digits.
  -- An inadmissible digest has no digits, so nothing below can accept.
  match wotsEncode pp msg sig.randomness epoch with
  | none => false
  | some x =>
    -- Step 2: walk chain `i` for `7 - x_i` steps, to its claimed public value.
    let publicValues := otsRecover pp epoch sig.chainElements x
    -- Step 3: hash the 42 claimed public values into the claimed leaf.
    let leaf := otsLeaf pp epoch publicValues
    -- Step 4: hash up the 32 levels, the epoch's bits choosing left or right.
    -- Step 5: the claimed leaf must reach the committed root.
    decide (computeRoot pp epoch sig.merklePath leaf = pk.merkleRoot)

end EthCryptographySpecs.Xmss

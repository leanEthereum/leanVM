import Leanxmss.Funs
import EthCryptographySpecs.Xmss

/-!
# The guest's values as the specification's

The guest holds every value as little-endian 64-bit words, and the specification as bytes: a value is the same in
both when its words' bytes are its bytes. These maps are part of the theorems' statements.
-/

open Aeneas Aeneas.Std
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Statement

/-- Words as the first `m` of their bytes: all of them where `m = 8 n`, as every use below has it. -/
def bytes {n : Std.Usize} (ws : Std.Array U64 n) (m : Nat) : Vector UInt8 m :=
  Vector.ofFn fun i => (Bytes.ofWords ws.val).getD i 0

/-- A digest, or a public parameter. -/
def digest (d : Std.Array U64 2#usize) : Digest := bytes d DIGEST_LEN

/-- A message. -/
def message (m : Std.Array U64 4#usize) : Message := bytes m MESSAGE_LEN

/-- A signature's randomness. -/
def randomness (r : Std.Array U64 3#usize) : Randomness := bytes r RANDOMNESS_LEN

/-- A leaf index is an epoch. -/
def epoch (i : Std.U32) : Epoch := UInt32.ofBitVec i.bv

/-- A public key: `merkle_root | public_param`. -/
def publicKey (pk : leanxmss.PublicKey) : EthCryptographySpecs.Xmss.PublicKey :=
  { merkleRoot := digest pk.merkle_root, publicParam := digest pk.public_param }

/-- A signature: `chain_tips | randomness | merkle_proof`. -/
def signature (s : leanxmss.Signature) : EthCryptographySpecs.Xmss.Signature :=
  { chainElements := Vector.ofFn fun i => digest (s.chain_tips.val.getD i.val default)
    randomness := randomness s.randomness
    merklePath := Vector.ofFn fun i => digest (s.merkle_proof.val.getD i.val default) }

end leanxmss.Statement

import LeanSphincsProofs.Hasher
import LeanSphincsProofs.Hash
import LeanSphincsProofs.Digest
import LeanSphincsProofs.Wots
import LeanSphincsProofs.Trees
import LeanSphincsProofs.Verify

/-!
# The theorem

The Rust `verify` of `crates/lean_sphincs`, as extracted, returns on every input, and returns what
the statement's verification does (`formal/Statement/LeanSphincs.lean`), given what the two
functions of `keccak256` the extraction leaves opaque compute (`SpongeSpec`, `Hasher.lean`):
`absorb` XORs a block into the state and permutes it, and `digest_of` reads the digest off the
state. Each function's theorem is proved in the file beside this one that its name suggests; here
they are composed.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open Sphincs
open LeanVM.Semantics (KeccakState)

namespace LeanSphincsProofs

/-- **The extracted `verify` computes the statement's verification**, over any permutation the
hasher computes Keccak-256 over. -/
theorem verify_spec {π : KeccakState → KeccakState} (H : HasherSpec π) : VerifySpec π :=
  have hth := th_spec H
  verify_of_specs (messageDigest_spec H hasher_clone)
    (forsRoot_spec hth keyAdrs_spec adrsWord_spec ofIndex_spec) ofIndex_spec
    (wotsLeaf_spec H hasher_clone hth keyAdrs_spec adrsWord_spec)
    (treeRoot_spec hth treeAdrs_spec adrsWord_spec)

/-- **The extracted `verify` is leanSPHINCS verification as deployed**, `Sphincs.verifyWithKeccak`,
the function the end statement's unforgeability is about (`Statement/Theorems.lean`), given that
`keccak256::absorb` and `digest_of` are the sponge step and the digest over Keccak-f[1600]. -/
theorem verify_eq_verifyWithKeccak (S : SpongeSpec LeanVM.Semantics.keccakF1600)
    (pk : lean_sphincs.scheme.LeanSphincsPublicKey) (m : Array Std.U8 32#usize)
    (sig : lean_sphincs.scheme.LeanSphincsSignature) :
    lean_sphincs.scheme.verify pk m sig =
      ok (verifyWithKeccak (toPublicKey pk) (toMessage m) (toSignature sig)) :=
  verify_spec (hasherSpec_of_sponge S) pk m sig

end LeanSphincsProofs

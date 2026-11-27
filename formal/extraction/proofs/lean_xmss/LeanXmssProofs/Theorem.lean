import Keccak256Proofs.Keccak
import LeanXmssProofs.Verify

/-!
# The theorem

The Rust `verify` of `crates/lean_xmss`, as extracted, returns on every input, and returns what
the statement's verification does (`formal/Statement/LeanXmss.lean`). Nothing is assumed: every
function on its path is extracted with its body, down to the Keccak-f[1600] permutation of
`keccak256` (`Keccak256Proofs.Keccak`). Each function's theorem is proved in the file beside this
one that its name suggests; here the hasher they are stated over is the one proved.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open LeanXmss
open LeanVM.Semantics (KeccakState)
open Keccak256Proofs

namespace LeanXmssProofs

/-- **The extracted `verify` is leanXMSS verification as deployed**, `LeanXmss.verifyWithKeccak`,
the function the end statement's unforgeability is about (`Statement/LeanXmss.lean`). -/
theorem verify_eq_verifyWithKeccak (pk : lean_xmss.scheme.LeanXmssPublicKey)
    (m : Array Std.U8 32#usize) (sig : lean_xmss.scheme.LeanXmssSignature) :
    lean_xmss.scheme.verify pk m sig =
      ok (verifyWithKeccak (toPublicKey pk) (toMessage m) (toSignature sig)) :=
  verify_spec (hasherSpec_of_sponge spongeSpec) pk m sig

end LeanXmssProofs

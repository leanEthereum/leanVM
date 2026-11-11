/-
  LeanVM.Protocol.EndToEnd.Completeness

  End-to-end completeness of the deployed leanVM verifier, unconditionally.
-/

module

public import LeanVM.Protocol.EndToEnd.Complete.Theorem
public import LeanVM.Protocol.WithHash

/-!
# End-to-end completeness

The deployed verifier is `Verifier.verify` (`Verifier.lean`), the compiled reading at Keccak-256 and
Keccak-f[1600] of `leanVmVerifierProgram` (`Statement/LeanVmVerifier.lean`), a transcription of
the Rust verifier `crates/verifier` at leanVM `40f877dc`. The statements here are those of
`EndToEnd.Complete`, which carry no hypothesis.

* `leanVm_interactiveComplete`: from a witness satisfying leanISA's constraint system at
  admissible sizes, for a valid rate, an honest strategy makes the verifier program accept
  against every challenge function, committing well-shaped words.
* `leanVm_complete`: for every hash function and permutation, the compiled honest prover produces
  a proof the compiled verifier accepts, as soon as its proof-of-work searches find nonces below
  the fuel; `leanVm_complete_keccak` is the deployed instance.
* `leanVm_complete_of_execution`: from a valid execution of at most `2^30` steps, a witness
  representing it, accepted as above when its sizes are admissible.

Completeness is perfect: the only way the honest prover fails is a proof-of-work search that finds
no nonce below the fuel, a search over Keccak-f outputs about which nothing is claimed here (the
random-oracle model bounds it, `Complete.Rom`).
-/

namespace LeanVM.Protocol.EndToEnd

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa LeanVM.Protocol.EndToEnd.Front
open LeanVM.Protocol.KeccakHash
open Air.Flat (EnsembleWitness)

@[expose] public section

end
end LeanVM.Protocol.EndToEnd

import LeanVM.Protocol.LeanVMSound
import LeanVM.Protocol.ErrorBounds
import LeanVM.Protocol.WithHash

/-!
# leanVM in the random-oracle model, locked

Statement locks of `LeanVM/Protocol/LeanVMSound.lean`: the verifier for any hash and permutation,
the deployed verifier, and the numbers of the two-oracle random-oracle model (a step of the proof
of `LeanVM.KnowledgeSoundness`, locked in `LeanVMTests.Protocol.LeanVMRpm`), with the axioms each
depends on.
-/

open LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol.LeanIsa LeanVM
open LeanVM.Protocol.KeccakHash

example (prog : LeanIsaProgram) (input : PublicInput) (proof : LeanVM.Protocol.Compile.Proof) :
    verify prog input proof = Id.run (verifierWithHash (m := Id) keccak256 keccakF1600 prog input proof) :=
  rfl

/-- The numbers: `13708` verifier queries, `2^-125` per message, a collision term of `5` per pair
of queries. -/
example (Q : ℕ) : soundnessError Q =
    ((Q + 13708 : ℕ) : ENNReal) *
        ((2 : ENNReal)⁻¹ ^ 125 + ((5 * (Q + 13708) : ℕ) : ENNReal) / 2 ^ 256) +
      ((13708 : ℕ) : ENNReal) / 2 ^ 256 := rfl

example {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ENNReal)⁻¹ ^ 60 :=
  soundnessError_le hQ

/-- The query positions' proofs of work have `17` bits. -/
example : LeanVM.Parameters.Whir.queryGrindingBits = 17 := rfl

/--
info: 'LeanVM.soundnessError_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms soundnessError_le

import LeanVM.Protocol.LeanVMSound
import LeanVM.Protocol.ErrorBounds
import LeanVM.Protocol.LeanVMSoundAS
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

/-- The query positions' proofs of work have `17` bits. -/
example : LeanVM.Parameters.Whir.queryGrindingBits = 17 := rfl

/--
info: 'LeanVM.soundnessRpmAS_le_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms soundnessRpmAS_le_statement

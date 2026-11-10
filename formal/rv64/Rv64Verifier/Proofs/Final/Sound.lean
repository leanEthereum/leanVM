import Rv64Verifier.Proofs.Final.WalkSpec
import Rv64Verifier.Proofs.Walk.AllF
import Rv64Verifier.Proofs.Walk.AllG

/-!
# Soundness, from the contracts still open

`soundness_of`: `Sound image` from `extend_desugared`'s contract as `walk` calls it
(`ExtendSpecE`) and `verify_stacked_opening`'s level loop and final level up to its terminal
check (`LoopSpec`, `ToCheck`). `main`, `walk`, `verify_bus_balance` and every other callee are
proved.
-/

namespace Rv64Verifier.Proofs.Final
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Model Rv64Verifier.Proofs.End

theorem soundness_of (hE : Walk.ExtendSpecE)
    (hL : Pcs.Vso.LoopSpec Transcript.OpeningsAt) (hT : Pcs.Vso.ToCheck Transcript.OpeningsAt) :
    Sound image :=
  Main.sound_of_walk (walkCall_of_walkO (walkSpec Bus.verifyBusBalanceBcClosed Walk.bcWalkClosed
    Walk.verifyKeccakE hE (Pcs.vsoSpec hL hT)))

end Rv64Verifier.Proofs.Final

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Final.soundness_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.soundness_of

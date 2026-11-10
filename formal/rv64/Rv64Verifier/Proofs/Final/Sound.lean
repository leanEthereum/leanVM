import Rv64Verifier.Proofs.Final.WalkSpec
import Rv64Verifier.Proofs.Walk.AllF
import Rv64Verifier.Proofs.Walk.AllG
import Rv64Verifier.Proofs.Pcs.AllRows0
import Rv64Verifier.Proofs.Pcs.AllRowsD

/-!
# Soundness

**`soundness : Sound image`** (`EndStatement.lean`): whenever the RV64IM image of the Rust
verifier, loaded with an input of at most `inputCapacity` words, halts with `a0 = 1`, the input
decodes and the trusted Lean verifier accepts it. No hypotheses.

`soundness_of` is the same from `verify_stacked_opening`'s level loop (`LoopSpec`); `loopSpec`
proves it from its two row paths (`RowsZero`, `RowsDeep`).
-/

namespace Rv64Verifier.Proofs.Final
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol.Compile Rv64Verifier.Model Rv64Verifier.Proofs.End

theorem soundness_of (hL : Pcs.Vso.LoopSpec Transcript.OpeningsAt) : Sound image :=
  Main.sound_of_walk (walkCall_of_walkO (walkSpec' Bus.verifyBusBalanceBcClosed Walk.bcWalkClosed
    Walk.verifyKeccakE (Pcs.vsoSpec hL Pcs.toCheckClosed)))

theorem soundness : Sound image :=
  soundness_of (Pcs.loopSpec Pcs.rowsZeroProved Pcs.Vso.rowsDeep)

end Rv64Verifier.Proofs.Final

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Final.soundness_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.soundness_of

/-- info: 'Rv64Verifier.Proofs.Final.soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Final.soundness

import Rv64Verifier.Proofs.Pcs.RingEvalSpec
import Rv64Verifier.Proofs.Pcs.BasisSpec
import Rv64Verifier.Proofs.Pcs.RingSwitchSpec
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Pcs.VsoBatch
import Rv64Verifier.Proofs.Pcs.VsoConfig
import Rv64Verifier.Proofs.Pcs.VsoMerkle
import Rv64Verifier.Proofs.Transcript.All
import Rv64Verifier.Proofs.Field.All
import Rv64Verifier.Proofs.Pcs.VsoRound
import Rv64Verifier.Proofs.Pcs.VsoFoldLoop
import Rv64Verifier.Proofs.Pcs.VsoOpenings

/-!
# The opening's contracts, their callees' discharged

`RingWeight::evaluate`, `StackBasis::evaluate` and `ring_switch` with their callees' contracts
proved.
-/

namespace Rv64Verifier.Proofs.Pcs
open Rv64Verifier.PcsContracts Rv64Verifier.Runtime

theorem ringEval : RingEvalSpec :=
  RingEval.ring_eval_spec tryAllocZeroed Runtime.memcpy Field.mul Field.eSquare

theorem basis : BasisSpec :=
  Basis.basis_spec tryAllocZeroed EqEval.eq_eval_proved ringEval Multilinear.eqAbove
    Field.mul Multilinear.dot

theorem ringSwitch : RingSwitchSpec :=
  RingSwitch.ring_switch_spec Transcript.samples Runtime.alloc_spec
    tryAllocZeroed Field.ePow Field.mul Multilinear.polyEval

theorem roundPolyErr : RoundPolyErrSpec := Transcript.roundPolyErr

end Rv64Verifier.Proofs.Pcs

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Pcs.ringEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.ringEval

/-- info: 'Rv64Verifier.Proofs.Pcs.basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.basis

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.exit

/-- info: 'Rv64Verifier.Model.Pcs.merkleRust_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Pcs.merkleRust_run

/-- info: 'Rv64Verifier.Model.Pcs.RodataOk.queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Pcs.RodataOk.queries

/-- info: 'Rv64Verifier.Model.Pcs.configLoop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Pcs.configLoop_eq

/-- info: 'Rv64Verifier.Proofs.Pcs.ringSwitch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.ringSwitch

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.toLevels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.toLevels

/-- info: 'Rv64Verifier.Proofs.Pcs.roundPolyErr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.roundPolyErr

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.init

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.enter

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.rnd_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.rnd_sample

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.growF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.growF

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.pushF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.pushF

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.growLF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.growLF

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.pushLF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.pushLF

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.roundStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.roundStep

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.foldRounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.foldRounds

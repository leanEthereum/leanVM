import Rv64Verifier.Proofs.Pcs.RingEvalSpec
import Rv64Verifier.Proofs.Pcs.BasisSpec
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Pcs.VsoBatch
import Rv64Verifier.Proofs.Pcs.VsoConfig
import Rv64Verifier.Proofs.Pcs.VsoMerkle

/-!
# The opening's contracts, their callees' discharged

`RingWeight::evaluate` and `StackBasis::evaluate` with their callees' contracts proved.
-/

namespace Rv64Verifier.Proofs.Pcs
open Rv64Verifier.PcsContracts Rv64Verifier.Runtime

theorem ringEval : RingEvalSpec :=
  RingEval.ring_eval_spec tryAllocZeroed Runtime.memcpy Field.mul Field.eSquare

theorem basis : BasisSpec :=
  Basis.basis_spec tryAllocZeroed EqEval.eq_eval_proved ringEval Multilinear.eqAbove
    Field.mul Multilinear.dot

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

import Rv64Verifier.Proofs.Bytecode.Evaluate
import Rv64Verifier.Proofs.Bytecode.Digest
import Rv64Verifier.Proofs.Multilinear.All

/-!
# `Bytecode::evaluate` and `Input::digest`, their callees' discharged

`evaluate` still takes `eq_kernel`'s contract.
-/

namespace Rv64Verifier.Proofs.Bytecode

theorem evaluate (hEK : EqKernelSpec) : EvaluateSpec :=
  Eval.evaluate_spec hEK Multilinear.fromElem Field.mul

end Rv64Verifier.Proofs.Bytecode

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Bytecode.evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bytecode.evaluate

/-- info: 'Rv64Verifier.Proofs.Bytecode.digest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bytecode.digest_spec

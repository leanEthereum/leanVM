import Rv64Verifier.Machine
import Rv64Verifier.SailWordOps
import Rv64Verifier.Frame
import Rv64Verifier.EndStatement
import Rv64Verifier.Model.Field
import Rv64Verifier.Model.Ext
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Sym
import Rv64Verifier.Field.ClmulLow
import Rv64Verifier.Field.BaseMul

/-! The axioms of the results so far: Lean's three, nothing native (`bv_decide` adds one). -/

/-- info: 'Rv64Verifier.Model.baseMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.baseMul_eq

/-- info: 'Rv64Verifier.Model.emul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.emul_eq

/-- info: 'Rv64Verifier.wordOp_sail_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.wordOp_sail_equiv

/-- info: 'Rv64Verifier.shiftOp_sail_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.shiftOp_sail_equiv

/-- info: 'Rv64Verifier.Field.ClmulLow.clmul_low_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Field.ClmulLow.clmul_low_correct

/-- info: 'Rv64Verifier.Field.BaseMul.base_mul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Field.BaseMul.base_mul_correct

/-- info: 'Rv64Verifier.Model.eqKernelRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.eqKernelRust_eq

/-- info: 'Rv64Verifier.Model.multilinearEvalRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.multilinearEvalRust_eq

/-- info: 'Rv64Verifier.Model.stackOffsetsRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.stackOffsetsRust_eq

/-- info: 'Rv64Verifier.Model.paddingWeightRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.paddingWeightRust_eq

import Rv64Verifier.Machine
import Rv64Verifier.SailWordOps
import Rv64Verifier.Frame
import Rv64Verifier.EndStatement
import Rv64Verifier.Model.Field
import Rv64Verifier.Model.Ext
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Model.FieldAlg
import Rv64Verifier.Model.Transcript
import Rv64Verifier.Proofs.End
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

/-- info: 'Rv64Verifier.Model.kSquare_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.kSquare_eq

/-- info: 'Rv64Verifier.Model.esquare_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.esquare_eq

/-- info: 'Rv64Verifier.Model.kInv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.kInv_eq

/-- info: 'Rv64Verifier.Model.epow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.epow_eq

/-- info: 'Rv64Verifier.Model.einv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.einv_eq

/-- info: 'Rv64Verifier.Model.powersM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.powersM_eq

/-- info: 'Rv64Verifier.Model.scaledMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.scaledMul_eq

/-- info: 'Rv64Verifier.Model.Sim.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.bind

/-- info: 'Rv64Verifier.Model.Sim.nextScalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.nextScalar

/-- info: 'Rv64Verifier.Model.Sim.grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.grind

/-- info: 'Rv64Verifier.Model.SimUnit.commit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.SimUnit.commit

/-- info: 'Rv64Verifier.Model.Sim.merkle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.merkle

/-- info: 'Rv64Verifier.Proofs.End.sound_of_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.End.sound_of_main

import Rv64Verifier.Machine
import Rv64Verifier.SailWordOps
import Rv64Verifier.Frame
import Rv64Verifier.EndStatement
import Rv64Verifier.Model.Field
import Rv64Verifier.Model.Ext
import Rv64Verifier.Model.Multilinear
import Rv64Verifier.Model.FieldAlg
import Rv64Verifier.Model.Transcript
import Rv64Verifier.Model.Bus
import Rv64Verifier.Model.Whir
import Rv64Verifier.Model.Layout
import Rv64Verifier.Model.KeccakGkr
import Rv64Verifier.Model.Hash
import Rv64Verifier.Model.Bytecode
import Rv64Verifier.Model.Walk
import Rv64Verifier.Proofs.End
import Rv64Verifier.Proofs.Common
import Rv64Verifier.Proofs.Rodata
import Rv64Verifier.Proofs.EqEval
import Rv64Verifier.Proofs.Field.All
import Rv64Verifier.Proofs.Runtime.All
import Rv64Verifier.Proofs.Hash.KeccakHash
import Rv64Verifier.Proofs.Hash.All
import Rv64Verifier.Proofs.Transcript.All
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Bus.All
import Rv64Verifier.Proofs.Pcs.All
import Rv64Verifier.Proofs.Gkr.All
import Rv64Verifier.Proofs.Layout.All
import Rv64Verifier.Proofs.Bytecode.All
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

/-- info: 'Rv64Verifier.Model.Sim.sumcheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.sumcheck

/-- info: 'Rv64Verifier.Model.Sim.verifyBusBalance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.verifyBusBalance

/-- info: 'Rv64Verifier.Model.Sim.tableSumcheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.tableSumcheck

/-- info: 'Rv64Verifier.Model.Sim.gkrLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Sim.gkrLoop

/-- info: 'Rv64Verifier.Model.LayoutMirror.buildLayoutRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.LayoutMirror.buildLayoutRust_eq

/-- info: 'Rv64Verifier.Model.LayoutMirror.buildLayoutRust_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.LayoutMirror.buildLayoutRust_rest

/-- info: 'Rv64Verifier.Model.LayoutMirror.buildLayoutRust_busLayout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.LayoutMirror.buildLayoutRust_busLayout

/-- info: 'Rv64Verifier.Model.LayoutMirror.busLayoutRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.LayoutMirror.busLayoutRust_eq

/-- info: 'Rv64Verifier.Model.LayoutMirror.ColumnClaimRust.onStack_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.LayoutMirror.ColumnClaimRust.onStack_eq

/-- info: 'Rv64Verifier.Model.Gkr.verifyKeccakRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Gkr.verifyKeccakRust_sim

/-- info: 'Rv64Verifier.Model.Gkr.verifyLayerRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Gkr.verifyLayerRust_sim

/-- info: 'Rv64Verifier.Model.Gkr.openRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Gkr.openRust_sim

/-- info: 'Rv64Verifier.Model.keccakFRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.keccakFRust_eq

/-- info: 'Rv64Verifier.Model.keccakHashRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.keccakHashRust_eq

/-- info: 'Rv64Verifier.Model.fiatShamirIvRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.fiatShamirIvRust_eq

/-- info: 'Rv64Verifier.Model.evaluateRust_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.evaluateRust_eq

/-- info: 'Rv64Verifier.Model.newRust_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.newRust_spec

/-- info: 'Rv64Verifier.Model.newRust_evaluate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.newRust_evaluate

/-- info: 'Rv64Verifier.Model.SimR.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.SimR.bind

/-- info: 'Rv64Verifier.Model.walkBodyRust_sim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.walkBodyRust_sim

/-- info: 'Rv64Verifier.Model.walkRust_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.walkRust_sound

/-- info: 'Rv64Verifier.Model.walkRust_sound_new' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.walkRust_sound_new

/-- info: 'Rv64Verifier.Proofs.EqEval.eq_eval_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.EqEval.eq_eval_spec

/-- info: 'Rv64Verifier.Proofs.Field.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Field.mul

/-- info: 'Rv64Verifier.Proofs.EqEval.eq_eval_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.EqEval.eq_eval_proved

/-- info: 'Rv64Verifier.Hash.KeccakF.keccak_f_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Hash.KeccakF.keccak_f_spec

/-- info: 'Rv64Verifier.Hash.XorBlock.xor_block_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Hash.XorBlock.xor_block_spec

/-- info: 'Rv64Verifier.Hash.KeccakHash.keccak_hash_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Hash.KeccakHash.keccak_hash_spec

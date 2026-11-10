import Rv64Verifier.Proofs.Bus.Fingerprints
import Rv64Verifier.Proofs.Bus.TsSpec
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Transcript.All
import Rv64Verifier.Proofs.Layout.All
import Rv64Verifier.Proofs.Bus.VbbSpine
import Rv64Verifier.Proofs.Bus.VbbTail9
import Rv64Verifier.Proofs.Bus.VbbGkrLoop
import Rv64Verifier.Proofs.Bus.VbbGkrSumcheck
import Rv64Verifier.Proofs.Bus.VbbGkrCheck
import Rv64Verifier.Proofs.Bus.VbbGkrIter
import Rv64Verifier.Proofs.Bus.VbbTail19
import Rv64Verifier.Proofs.Bus.VbbTail22
import Rv64Verifier.Proofs.Bus.VbbTail30
import Rv64Verifier.Proofs.Bus.VbbTail45

/-!
# The bus's contracts, their callees' discharged

`verify_bus_balance::{closure#2}` closed, down to the allocator's and `dot`'s proofs.
`table_sumcheck` and `verify_bus_balance` are stated in `Contracts.lean`. Of `table_sumcheck`,
the frame (`TsBase.lean`), the prologue with the heights' maximum (`TsStart.lean`), the epilogue
and the call of `vec![None; n_rounds]` (`TsCalls.lean`) are proved. Of `verify_bus_balance`, the
mirror lemmas for the compiled loops (`VbbModel.lean`), the frame (`VbbBase.lean`), the prologue and
the three `bus_layout` calls (`VbbLayouts.lean`), the epilogue and the `Err` exit (`VbbEnd.lean`),
the transcript callees' steps with the call of `samples` (`VbbSteps.lean`), the mirror's run in the
code's order (`Tracks`, `VbbRun.lean`), the calls of `eq_kernel`, `duplex`, `next_scalar` and
`alloc` (`VbbCalls.lean`), the challenges and the GKR loop's start (`VbbHead.lean`,
`VbbValues.lean`, `start` in `VbbInit.lean`), and the contract from the GKR loop's and the rest's
stages (`verify_bus_balance_spec` in `VbbSpine.lean`): the GKR loop's (`gkrStage`, `VbbGkr*.lean`, closed), the rest's from the scalar reads on (`tailStage`, `VbbTail*.lean`, the reads, the claims' points proved).
`table_sumcheck` is closed down to `vec![None; n]` (`OptFromElemBelowSpec`), `sumcheck`
and `Form::evaluate` (`FormEvaluateSpecE`).
Of the rest, from `0x80006ca0` to `concat`'s entry (`restToConcat`, `VbbTail10.lean` to `VbbTail19.lean`), and on through `concat`, `Bytecode::evaluate`, `final_pc`, the framework fingerprints, `vec![Form::default(); 3]` and the forms' buffer to the clone loop's test (`restToRows`, `VbbTail20.lean` to `VbbTail22.lean`), the forms' rows and the sides' array (`restToSides`, `VbbTail23.lean` to `VbbTail26.lean`). The side loop's invariant (`Sides`), its entry and the return with the result (`finalStage`, `VbbTail27.lean` to `VbbTail30.lean`) are proved: `TailStage` holds given the way into the side loop with the empty buffers' pointers (`SidesEntry`) and one iteration of it (`SideStage`), both stated in `VbbTail27.lean`.
-/

namespace Rv64Verifier.Proofs.Bus
open Rv64Verifier.Bus Rv64Verifier.Runtime

theorem fingerprints : FingerprintsSpec :=
  Fingerprints.fingerprints_spec alloc_spec Multilinear.dot

theorem tableSumcheck (hOF : TableSumcheck.OptFromElemBelowSpec) : TableSumcheckSpec :=
  TableSumcheck.table_sumcheck_spec hOF Transcript.sumcheck tryAllocZeroed Runtime.reserveFresh_80008a10
    Multilinear.fromElem Field.mul memcpy Transcript.nextScalars alloc_spec Multilinear.dot
    Layout.form_evaluate_e_proved

open RiscvZkvm.Rv64 LeanVM.Parameters in
/-- `verify_bus_balance`'s GKR loop, closed (`SumcheckSpec`). -/
theorem gkrStage (bev : MachineState → Word → List E → Option E) :
    VerifyBusBalance.GkrStage bev :=
  VerifyBusBalance.gkrStage bev (VerifyBusBalance.iter Transcript.duplex Multilinear.polyEval
    tryAllocZeroed reserveFast_8001086c Transcript.sumcheck Transcript.nextScalars Field.mul memcpy
    Transcript.samples Multilinear.mleEvalVbb Multilinear.concat bev)

open RiscvZkvm.Rv64 LeanVM.Parameters in
/-- `verify_bus_balance` from `0x80006b60` on, given the side loop's entry and iteration. -/
theorem vbbTailStage {BcOk : MachineState → Nat → Word → Prop}
    {bev : MachineState → Word → List E → Option E} (hE : VerifyBusBalance.SidesEntry BcOk bev)
    (hS : VerifyBusBalance.SideStage bev) : VerifyBusBalance.TailStage BcOk bev :=
  VerifyBusBalance.tailStage Transcript.nextScalars Transcript.nextScalar
    (VerifyBusBalance.restStage hE hS (VerifyBusBalance.finalStage bev))

end Rv64Verifier.Proofs.Bus

/-! Lean's three axioms, nothing native. -/

/-- info: 'Rv64Verifier.Proofs.Bus.fingerprints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.fingerprints

/-- info: 'Rv64Verifier.Proofs.Bus.TableSumcheck.maxLoop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.TableSumcheck.maxLoop

/-- info: 'Rv64Verifier.Proofs.Bus.TableSumcheck.stageP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.TableSumcheck.stageP

/-- info: 'Rv64Verifier.Proofs.Bus.TableSumcheck.stageA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.TableSumcheck.stageA

/-- info: 'Rv64Verifier.Proofs.Bus.TableSumcheck.epilogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.TableSumcheck.epilogue

/-- info: 'Rv64Verifier.Proofs.Bus.TableSumcheck.Inv.transcript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.TableSumcheck.Inv.transcript

/-- info: 'Rv64Verifier.Model.paddingWeightRust_eq_padLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.paddingWeightRust_eq_padLow

/-- info: 'Rv64Verifier.Model.sumE_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.sumE_append

/-- info: 'Rv64Verifier.Model.gkrLoopM_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.gkrLoopM_pos

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.layouts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.layouts

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.errExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.errExit

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.exit

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.samplesCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.samplesCall

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.LayoutAt.keepT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.LayoutAt.keepT

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.start

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.depthZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.depthZero

/--
info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.verify_bus_balance_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.verify_bus_balance_spec

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.scalarsStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.scalarsStage

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.tailStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.tailStage

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.copy1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.copy1

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.copy2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.copy2

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.copy3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.copy3

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.growOneCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.growOneCall

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.ClaimsAt.grow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.ClaimsAt.grow

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.ClaimsAt.keepR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.ClaimsAt.keepR

/-- info: 'Rv64Verifier.Proofs.Bus.tableSumcheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.tableSumcheck

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrStage

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrEntry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrEntry

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrExit

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.combStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.combStep

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.eqsStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.eqsStep

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.Kept.stepV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.Kept.stepV

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.Ctx.stepV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.Ctx.stepV

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.err7100' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.err7100

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.ClaimsOk.push' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.ClaimsOk.push

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.restToConcat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.restToConcat

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.restToRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.restToRows

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrIter_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.gkrIter_eq

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.iter

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.smTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.smTail

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.samplesStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.samplesStep

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.mleCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.mleCall

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.mleRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.mleRun

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.push0Step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.push0Step

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.push1Step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.push1Step

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.ccStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.ccStep

/-- info: 'Rv64Verifier.Proofs.Bus.gkrStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.gkrStage

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.finalStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.finalStage

/-- info: 'Rv64Verifier.Proofs.Bus.vbbTailStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.vbbTailStage

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.sideFront' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.sideFront

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.sideShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.sideShift

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.sideDot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.sideDot

/-- info: 'Rv64Verifier.Proofs.Bus.VerifyBusBalance.blkHead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Bus.VerifyBusBalance.blkHead


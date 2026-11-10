import Rv64Verifier.Proofs.Bus.Fingerprints
import Rv64Verifier.Proofs.Bus.TsSpec
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Transcript.All
import Rv64Verifier.Proofs.Bus.VbbSpine
import Rv64Verifier.Proofs.Bus.VbbTail9

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
stages (`verify_bus_balance_spec` in `VbbSpine.lean`; `GkrStage` and `TailStage` still to prove), and
of the rest, from `0x80006b60` to `0x80006ca0`: the count's check, `next_scalars(3)` and the two
`next_scalar`s (`scalarsStage`, `VbbTail1.lean` to `VbbTail4.lean`), `TailStage` from the stage after
them (`tailStage`, given `s3` = `values`' buffer, which `AfterGkr` does not yet say); for the stage after
them, the calls of `try_allocate_in`, `memcpy` and the claims' `grow_one` (`VbbTail5.lean`,
`VbbTail7.lean`), the claims in memory (`VbbTail6.lean`) and the three copies of the point's prefix
(`copy1` to `copy3`, `VbbTail8.lean`, `VbbTail9.lean`).
`table_sumcheck` is closed down to `vec![None; n]` (`OptFromElemBelowSpec`), `sumcheck`
and `Form::evaluate` (`FormEvaluateSpecE`).
-/

namespace Rv64Verifier.Proofs.Bus
open Rv64Verifier.Bus Rv64Verifier.Runtime

theorem fingerprints : FingerprintsSpec :=
  Fingerprints.fingerprints_spec alloc_spec Multilinear.dot

theorem tableSumcheck (hOF : TableSumcheck.OptFromElemBelowSpec) (hS : Transcript.SumcheckSpec)
    (hFEv : TableSumcheck.FormEvaluateSpecE) : TableSumcheckSpec :=
  TableSumcheck.table_sumcheck_spec hOF hS tryAllocZeroed Runtime.reserveFresh_80008a10
    Multilinear.fromElem Field.mul memcpy Transcript.nextScalars alloc_spec Multilinear.dot hFEv

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

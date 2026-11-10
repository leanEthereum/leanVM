import Rv64Verifier.Proofs.Bus.Fingerprints
import Rv64Verifier.Proofs.Bus.TsCalls
import Rv64Verifier.Proofs.Multilinear.All
import Rv64Verifier.Proofs.Bus.VbbSteps

/-!
# The bus's contracts, their callees' discharged

`verify_bus_balance::{closure#2}` closed, down to the allocator's and `dot`'s proofs.
`table_sumcheck` and `verify_bus_balance` are stated in `Contracts.lean`. Of `table_sumcheck`,
the frame (`TsBase.lean`), the prologue with the heights' maximum (`TsStart.lean`), the epilogue
and the call of `vec![None; n_rounds]` (`TsCalls.lean`) are proved. Of `verify_bus_balance`, the
mirror lemmas for the compiled loops (`VbbModel.lean`), the frame (`VbbBase.lean`), the prologue and
the three `bus_layout` calls (`VbbLayouts.lean`), the epilogue and the `Err` exit (`VbbEnd.lean`),
and the transcript callees' steps with the call of `samples` (`VbbSteps.lean`).
-/

namespace Rv64Verifier.Proofs.Bus
open Rv64Verifier.Bus Rv64Verifier.Runtime

theorem fingerprints : FingerprintsSpec :=
  Fingerprints.fingerprints_spec alloc_spec Multilinear.dot

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

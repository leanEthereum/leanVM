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

import Rv64Verifier.Proofs.Pcs.ExtendSpec
import Rv64Verifier.Proofs.Pcs.VsoClimb
import Rv64Verifier.Proofs.Pcs.VsoLamPowers
import Rv64Verifier.Proofs.Pcs.VsoQueries
import Rv64Verifier.Proofs.Pcs.VsoLevelQ
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

theorem extend : ExtendSpec :=
  Extend.extend_spec Multilinear.selectorPoint Multilinear.sliceConcat Runtime.growAmortized

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

/-- info: 'Rv64Verifier.Proofs.Pcs.extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.extend

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.reassemble' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.reassemble

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.climb_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.climb_tail

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.climb_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.climb_step

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.climb_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.climb_loop

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.cmp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.cmp_eq

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.pathTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.pathTail

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.paths_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.paths_loop

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.scan1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.scan1

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.scan2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.scan2

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.errTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.errTail

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.front' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.front

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.scans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.scans

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.enterPaths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.enterPaths

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.reload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.reload

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.Clear.misses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.Clear.misses

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.MW.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.MW.inv

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.openingAt_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.openingAt_keep

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.pathOk_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.pathOk_of

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkle_err' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkle_err

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkle_scans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkle_scans

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkle_enter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkle_enter

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.roots_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.roots_keep

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkle_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkle_loop

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkle

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkleRust_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkleRust_out

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.phaseAt_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.phaseAt_keep

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkle_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkle_model

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.phaseOk_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.phaseOk_of

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.frontIn_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.frontIn_of

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.merkleIn_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.merkleIn_of

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.lamPowers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.lamPowers

/-- info: 'Rv64Verifier.Model.Pcs.afterFolds_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Model.Pcs.afterFolds_eq

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.grind

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.qsetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.qsetup

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.chunk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.chunk

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.qloop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.qloop

/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.queries
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.open304' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.open304
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.openLast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.openLast
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.commitRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.commitRead
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.oodPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.oodPoint
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.oodValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.oodValue
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.oodIntro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.oodIntro
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.growPend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.growPend
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.pushPend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.pushPend
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.openLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.openLevel
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.queriesU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.queriesU
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.lamPowersU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.lamPowersU
/-- info: 'Rv64Verifier.Proofs.Pcs.Vso.Opened.slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Rv64Verifier.Proofs.Pcs.Vso.Opened.slots
